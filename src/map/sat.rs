//! Register-correspondence refinement by SAT (`map --refine sat`, the default with the `sat`
//! feature): the same fixed point as the BDD keys of [`super::refine_within`], proved the way
//! ABC's `&scorr` proves it (`cecCorr.c` `Cec_ManLSCorrespondenceClasses`, `cecSolve.c`).
//!
//! The rule set, in ABC's order:
//! 1. Each round reads the speculatively reduced one-frame model: every register's state is its
//!    class's value (one variable per class, complemented for a member inverted in it), every
//!    primary input is free (ABC `Gia_ManCorrSpecReduce`, `nFrames` = 1).
//! 2. Only the classes [`super::active_classes`] names are proved again (ABC's incremental
//!    filter); each is split exactly as the BDD keys would split it: members in order, each
//!    proved against the head of every earlier part it is not already told apart from, joining
//!    the first part it equals; parts in order of their first member ([`split_class`]).
//! 3. One incremental solver per round ([`RoundSolver`], ABC: one `Cec_ManSat_t` for the whole
//!    miter): every gate encoded once per round, each obligation solved under the assumption of
//!    its difference literal, with a conflict limit ([`PAIR_CONFLICTS`]; ABC `nBTLimit`).
//! 4. UNSAT: the member joins the part. SAT: the assignment is a counter-example, resimulated over
//!    every register ([`resimulate_counter_examples`], ABC `Cec_ManResimulateCounterExamples`), so
//!    a pair it already tells apart is never proved. Over the limit: the member stands alone,
//!    undecided, never in the map (ABC `Gia_ManCheckRefinements`, status -1).
//! 5. The fixed point is a round in which nothing split.
//!
//! 🔑 Equality is transitive and each proof is exact, so a class splits into the same parts as
//! under the BDD keys; only a member undecided within a budget can differ (a BDD over
//! [`super::BDD_LIMIT`] against a SAT call over [`PAIR_CONFLICTS`]).
use rustc_hash::{FxHashMap, FxHashSet};
use vyges_loom::liberty_func::Func;

use super::{class_index, ClassOf, Key, Model, Polarity, RegId, SatEffort};
use crate::lec::{next_net, state_net, Logic, Op, Src};

/// Conflicts one obligation may take before its member is undecided. ABC's `&scorr` default is
/// 100; 1000 decided every pair the BDD path decides on the CoralNPU leaves measured
/// (2026-11-19: `rvv_backend_alu_unit_0` maps 363 at 1000, 352 at 100).
pub const PAIR_CONFLICTS: i32 = 1000;

/// DIAGNOSTIC (branch sat-diag only): per-round attribution of rejections, `LEC_DIAG_SAT=1`.
#[derive(Default)]
struct Diag {
    on: bool,
    round: usize,
    /// registers whose class split in the previous round
    split_prev: FxHashSet<RegId>,
    undecided: FxHashSet<RegId>,
    /// per model: state net -> register
    reg_of: Vec<FxHashMap<String, usize>>,
    logged: usize,
    dumped: usize,
}
thread_local! {
    static DIAG: std::cell::RefCell<Diag> = std::cell::RefCell::new(Diag::default());
}
/// DIAGNOSTIC ONLY (branch sat-diag): `LEC_DIAG_ASSUME=io_te=0,io_aresetn=1` fixes those inputs in
/// the PROOF too (CNF and resimulation), to measure whether they cause the CoralNPU collapse.
fn diag_assume(name: &str) -> Option<bool> {
    static FIX: std::sync::OnceLock<Vec<(String, bool)>> = std::sync::OnceLock::new();
    let fix = FIX.get_or_init(|| {
        let s = std::env::var("LEC_DIAG_ASSUME").unwrap_or_default();
        let v: Vec<(String, bool)> = s.split(',').filter_map(|kv| kv.split_once('=').map(|(k, v)| (k.to_string(), v == "1"))).collect();
        if !v.is_empty() {
            eprintln!("SATDIAG ASSUME (diagnostic, proof constrained): {v:?}");
        }
        v
    });
    fix.iter().find(|(k, _)| k == name).map(|x| x.1)
}

fn diag_on() -> bool {
    DIAG.with(|d| d.borrow().on)
}
fn xor_gates(model: &Model, gates: &[usize]) -> usize {
    // by truth table: a gate whose output is the parity (or its complement) of two or more of its
    // inputs, however its Liberty function is written (ASAP7 writes XOR as a sum of products)
    const W: [u64; 4] = [0xaaaa_aaaa_aaaa_aaaa, 0xcccc_cccc_cccc_cccc, 0xf0f0_f0f0_f0f0_f0f0, 0xff00_ff00_ff00_ff00];
    gates
        .iter()
        .filter(|&&g| {
            let gate = &model.cone.gates[g];
            let n = gate.ins.len();
            if !(2..=4).contains(&n) {
                return false;
            }
            let Ok(prog) = program(&gate.logic, &gate.pins, n) else { return false };
            let y = run(&prog, &W[..n], &mut Vec::new());
            let mask = if n == 4 { !0u64 } else { (1u64 << (1 << n)) - 1 };
            (3u32..(1 << n)).filter(|s| s.count_ones() >= 2).any(|s| {
                let par = (0..n).filter(|k| s >> k & 1 == 1).fold(0u64, |a, k| a ^ W[k]);
                (y ^ par) & mask == 0 || (y ^ !par) & mask == 0
            })
        })
        .count()
}

/// Stage 4 by SAT: the fixed point ([`self`]); returns the rounds and the undecided registers, as
/// [`super::refine_within`] does. Thin sequencer, one stage per line.
pub(crate) fn refine_sat(models: &[&Model], classes: &mut Vec<Vec<RegId>>, inv: &Polarity, limit: i32, effort: &mut SatEffort) -> Result<(usize, Vec<RegId>), String> {
    let readers = super::readers_of(models);
    let sim: Vec<Compiled> = models.iter().map(|m| Compiled::of(m)).collect::<Result<_, _>>()?;
    let mut undecided: Vec<RegId> = Vec::new();
    let mut seeds: Option<Vec<RegId>> = None;
    let mut rounds = 0;
    if std::env::var_os("LEC_DIAG_SAT").is_some() {
        DIAG.with(|d| {
            let mut d = d.borrow_mut();
            d.on = true;
            d.reg_of = models.iter().map(|m| m.regs.iter().enumerate().map(|(k, r)| (state_net(&r.instance), k)).collect()).collect();
        });
    }
    loop {
        rounds += 1;
        let before = *effort;
        if diag_on() {
            DIAG.with(|d| {
                let mut d = d.borrow_mut();
                d.round = rounds;
                d.split_prev = seeds.iter().flatten().copied().collect();
                d.undecided = undecided.iter().copied().collect();
                d.logged = 0;
            });
        }
        let class_of = class_index(models, classes, &|r: RegId| inv[r.0][r.1]);
        let active = super::active_classes(models, classes, &readers, seeds.as_deref());
        let split = sat_round(models, &sim, classes, &active, &class_of, limit, &mut undecided, effort)?;
        if diag_on() {
            eprintln!(
                "SATDIAG round {rounds} active {} proved {} structural {} disproved {} gave_up {} split_members {} undecided_total {}",
                active.iter().zip(classes.iter()).filter(|(a, _)| **a).count(),
                effort.proved - before.proved,
                effort.structural - before.structural,
                effort.disproved - before.disproved,
                effort.gave_up - before.gave_up,
                split.len(),
                undecided.len()
            );
        }
        if split.is_empty() {
            return Ok((rounds, undecided));
        }
        seeds = Some(split);
    }
}

/// One round: each active class split by [`split_class`] under the round's classes `class_of`,
/// one solver and one set of counter-examples for the round. Returns every member of a class
/// that split, the next round's seeds.
#[allow(clippy::too_many_arguments)]
fn sat_round(models: &[&Model], sim: &[Compiled], classes: &mut Vec<Vec<RegId>>, active: &[bool], class_of: &[ClassOf], limit: i32, undecided: &mut Vec<RegId>, effort: &mut SatEffort) -> Result<Vec<RegId>, String> {
    let mut rs = RoundSolver::new(models.len(), limit);
    let mut sims = Signatures::new(models);
    let mut next: Vec<Vec<RegId>> = Vec::with_capacity(classes.len());
    let mut split = Vec::new();
    for (cl, &act) in classes.iter().zip(active) {
        if cl.len() < 2 || !act {
            next.push(cl.clone());
            continue;
        }
        let parts = split_class(models, sim, cl, class_of, &mut rs, &mut sims, undecided, effort)?;
        if parts.len() > 1 {
            split.extend(cl.iter().copied());
        }
        next.extend(parts);
    }
    // the round's last counter-examples, checked like every batch
    if !sims.pending.is_empty() {
        resimulate_counter_examples(models, sim, class_of, &mut sims, effort)?;
    }
    *classes = next;
    Ok(split)
}

/// One class split into the parts of members that load the same next value under `class_of`, in
/// order of their first member. A member is proved only against the head of a part whose
/// counter-example signature it shares ([`Signatures`]); counter-examples are resimulated over
/// every register 64 at a time (one word) and at the round's end, as ABC resimulates per batch:
/// a pass costs the whole model, which per class dominated a core's run.
#[allow(clippy::too_many_arguments)]
fn split_class<'m>(
    models: &[&'m Model],
    sim: &[Compiled],
    cl: &[RegId],
    class_of: &[ClassOf],
    rs: &mut RoundSolver<'m>,
    sims: &mut Signatures,
    undecided: &mut Vec<RegId>,
    effort: &mut SatEffort,
) -> Result<Vec<Vec<RegId>>, String> {
    let mut parts: Vec<Vec<RegId>> = Vec::new();
    // an undecided member's part takes nobody else
    let mut closed: Vec<bool> = Vec::new();
    // a part whose head an obligation over the limit was posed against
    let mut unsure: Vec<bool> = Vec::new();
    for &r in cl {
        let mut home = None;
        for (p, part) in parts.iter().enumerate() {
            let head = part[0];
            if closed[p] || !sims.same(head, r) {
                continue;
            }
            match rs.prove(models, head, r, class_of)? {
                Outcome::Structural => {
                    effort.structural += 1;
                    home = Some(Some(p));
                }
                Outcome::Unsat => {
                    effort.proved += 1;
                    home = Some(Some(p));
                }
                Outcome::Sat(cex) => {
                    effort.disproved += 1;
                    if diag_on() {
                        diag_rejection(models, head, r, &cex, rs, class_of);
                    }
                    sims.pending.push((cex, head, r));
                    if sims.pending.len() == 64 {
                        resimulate_counter_examples(models, sim, class_of, sims, effort)?;
                    }
                }
                Outcome::GaveUp => {
                    effort.gave_up += 1;
                    if diag_on() {
                        let n = |x: RegId| models[x.0].regs[x.1].name.clone();
                        let (gh, gm) = (cone_gates(models[head.0], head, &|_| false), cone_gates(models[r.0], r, &|_| false));
                        eprintln!(
                            "SATDIAG gaveup r={} {} / {} gates {}/{} xor {}/{}",
                            DIAG.with(|d| d.borrow().round),
                            n(head),
                            n(r),
                            gh.len(),
                            gm.len(),
                            xor_gates(models[head.0], &gh),
                            xor_gates(models[r.0], &gm)
                        );
                    }
                    if let Some(dir) = std::env::var_os("LEC_DUMP_DIR") {
                        dump_obligation(models, head, r, class_of, std::path::Path::new(&dir));
                    }
                    unsure[p] = true;
                    home = Some(None);
                }
            }
            if home.is_some() {
                break;
            }
        }
        match home {
            Some(Some(p)) => parts[p].push(r),
            // ⛔ over the limit: alone and undecided, never in a part with another register
            Some(None) => {
                undecided.push(r);
                parts.push(vec![r]);
                closed.push(true);
                unsure.push(false);
            }
            None => {
                parts.push(vec![r]);
                closed.push(false);
                unsure.push(false);
            }
        }
    }
    // a head left alone after an undecided obligation is undecided too, not disproved: nothing
    // told it apart from that member (the BDD path lists both of an undecided pair)
    for (part, _) in parts.iter().zip(&unsure).filter(|(part, &u)| u && part.len() == 1) {
        if !undecided.contains(&part[0]) {
            undecided.push(part[0]);
        }
    }
    Ok(parts)
}

/// Each register's values under the round's counter-examples so far, one bit per
/// counter-example; `pending` are the counter-examples not yet resimulated, each with the pair it
/// was found for.
struct Signatures {
    words: Vec<Vec<Vec<u64>>>,
    pending: Vec<(Vec<Var>, RegId, RegId)>,
}

impl Signatures {
    fn new(models: &[&Model]) -> Signatures {
        Signatures { words: models.iter().map(|m| vec![Vec::new(); m.regs.len()]).collect(), pending: Vec::new() }
    }

    /// `a` and `b` agree under every counter-example resimulated so far.
    fn same(&self, a: RegId, b: RegId) -> bool {
        self.words[a.0][a.1] == self.words[b.0][b.1]
    }
}

/// One model's cone by index, compiled once per refinement so a resimulation is one pass over
/// words (resolving every input by name per pass cost a core minutes per class).
struct Compiled {
    ins: Vec<Vec<In>>,
    /// each gate's function over its inputs by position ([`program`])
    prog: Vec<Vec<Ins>>,
    /// state nets read (by [`In::State`]), looked up in the round's classes per resimulation
    states: Vec<String>,
    /// free-input variable names read (by [`In::Free`])
    frees: Vec<String>,
    /// each register's next value
    next: Vec<In>,
    /// each register's state net
    reg_state: Vec<String>,
}

#[derive(Clone, Copy)]
enum In {
    Const(bool),
    Gate(usize),
    State(usize),
    Free(usize),
}

impl Compiled {
    /// Each gate input resolved as the BDD and CNF builders resolve it: a gate already computed,
    /// then a state, then a free input; anything else is an error.
    fn of(model: &Model) -> Result<Compiled, String> {
        let c = &model.cone;
        let mut out = Compiled { ins: Vec::with_capacity(c.gates.len()), prog: Vec::with_capacity(c.gates.len()), states: Vec::new(), frees: Vec::new(), next: Vec::new(), reg_state: Vec::new() };
        let mut st: FxHashMap<&str, usize> = FxHashMap::default();
        let mut fr: FxHashMap<&str, usize> = FxHashMap::default();
        let mut done: FxHashMap<&str, usize> = FxHashMap::default();
        let mut resolve = |n: &str, done: &FxHashMap<&str, usize>, out: &mut Compiled| -> Option<In> {
            if let Some(&g) = done.get(n) {
                return Some(In::Gate(g));
            }
            if let Some(k) = model.state.get(n) {
                let i = *st.entry(k.as_str()).or_insert_with(|| {
                    out.states.push(k.to_string());
                    out.states.len() - 1
                });
                return Some(In::State(i));
            }
            let v = c.free.get(n)?;
            if let Some(b) = diag_assume(v) {
                return Some(In::Const(b));
            }
            let i = *fr.entry(v.as_str()).or_insert_with(|| {
                out.frees.push(v.clone());
                out.frees.len() - 1
            });
            Some(In::Free(i))
        };
        for (g, gate) in c.gates.iter().enumerate() {
            let mut ins = Vec::with_capacity(gate.ins.len());
            for s in &gate.ins {
                ins.push(match s {
                    Src::Const(v) => In::Const(*v),
                    Src::Net(n) => resolve(n, &done, &mut out).ok_or_else(|| format!("cone gate `{}` reads `{n}` before it is computed", gate.out))?,
                });
            }
            out.prog.push(program(&gate.logic, &gate.pins, ins.len()).map_err(|e| format!("cone gate `{}`: {e}", gate.out))?);
            out.ins.push(ins);
            done.insert(gate.out.as_str(), g);
        }
        for r in &model.regs {
            let n = next_net(&r.instance);
            // a next net nothing computes reads 0, as the word evaluation always did
            let i = resolve(&n, &done, &mut out).unwrap_or(In::Const(false));
            out.next.push(i);
            out.reg_state.push(state_net(&r.instance));
        }
        Ok(out)
    }
}

/// One step of a gate program, a stack machine over words: `Arg(k)` pushes input `k`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ins {
    Arg(u32),
    One,
    Zero,
    Not,
    And,
    Or,
    Xor,
}

/// A gate's function as a program over its inputs by position, pins resolved once: the same
/// rules as [`super::func_word`] and [`super::prim_word`], which resolve them on every call.
fn program(logic: &Logic, pins: &[String], n: usize) -> Result<Vec<Ins>, String> {
    fn func(f: &Func, pins: &[String], out: &mut Vec<Ins>) -> Result<(), String> {
        match f {
            Func::Port(p) => out.push(Ins::Arg(pins.iter().position(|q| q == p).ok_or_else(|| format!("function reads `{p}`, not a pin"))? as u32)),
            Func::Not(a) => {
                func(a, pins, out)?;
                out.push(Ins::Not);
            }
            Func::And(a, b) | Func::Or(a, b) | Func::Xor(a, b) => {
                func(a, pins, out)?;
                func(b, pins, out)?;
                out.push(match f {
                    Func::And(..) => Ins::And,
                    Func::Or(..) => Ins::Or,
                    _ => Ins::Xor,
                });
            }
            Func::One => out.push(Ins::One),
            Func::Zero => out.push(Ins::Zero),
        }
        Ok(())
    }
    let mut out = Vec::new();
    match logic {
        Logic::Func(f) => func(f, pins, &mut out)?,
        Logic::Prim(op) => {
            if n == 0 {
                return Err("primitive needs inputs".into());
            }
            let need = |k: usize| if n == k { Ok(()) } else { Err(format!("primitive expected {k} input(s), got {n}")) };
            let fold = |out: &mut Vec<Ins>, op: Ins| {
                out.push(Ins::Arg(0));
                for k in 1..n {
                    out.push(Ins::Arg(k as u32));
                    out.push(op);
                }
            };
            match op {
                Op::Buf | Op::Not => {
                    need(1)?;
                    out.push(Ins::Arg(0));
                }
                Op::And | Op::Nand => fold(&mut out, Ins::And),
                Op::Or | Op::Nor => fold(&mut out, Ins::Or),
                Op::Xor | Op::Xnor => fold(&mut out, Ins::Xor),
                Op::Mux => {
                    need(3)?;
                    let idx = |want: &str| pins.iter().position(|p| p.eq_ignore_ascii_case(want));
                    let (Some(a), Some(b), Some(s)) = (idx("A"), idx("B"), idx("S")) else { return Err("MUX needs pins A, B, S".into()) };
                    out.extend([Ins::Arg(s as u32), Ins::Arg(b as u32), Ins::And, Ins::Arg(s as u32), Ins::Not, Ins::Arg(a as u32), Ins::And, Ins::Or]);
                }
            }
            if matches!(op, Op::Not | Op::Nand | Op::Nor | Op::Xnor) {
                out.push(Ins::Not);
            }
        }
    }
    Ok(out)
}

/// A gate program run over the input words `x`.
fn run(prog: &[Ins], x: &[u64], stack: &mut Vec<u64>) -> u64 {
    stack.clear();
    for &i in prog {
        match i {
            Ins::Arg(k) => stack.push(x[k as usize]),
            Ins::One => stack.push(!0),
            Ins::Zero => stack.push(0),
            Ins::Not => {
                let a = stack.pop().unwrap_or(0);
                stack.push(!a);
            }
            Ins::And | Ins::Or | Ins::Xor => {
                let b = stack.pop().unwrap_or(0);
                let a = stack.pop().unwrap_or(0);
                stack.push(match i {
                    Ins::And => a & b,
                    Ins::Or => a | b,
                    _ => a ^ b,
                });
            }
        }
    }
    stack.pop().unwrap_or(0)
}

/// Every model evaluated under the pending counter-examples (one per bit; a name one does not
/// assign reads 0), states read as the ROUND's class values, and each register's next value
/// (complemented when inverted in its class) appended to its signature.
///
/// ⛔ A counter-example tells apart the pair it came from; one that does not is an error (the
/// CNF and the simulation disagree on a gate), never a silent merge.
fn resimulate_counter_examples(models: &[&Model], sim: &[Compiled], class_of: &[ClassOf], sims: &mut Signatures, effort: &mut SatEffort) -> Result<(), String> {
    let pending = std::mem::take(&mut sims.pending);
    // each variable's word: bit i set when counter-example i sets it (a variable one does not
    // name reads 0 there)
    let mut words: FxHashMap<Var, u64> = FxHashMap::default();
    for (i, (cex, _, _)) in pending.iter().enumerate() {
        for v in cex {
            *words.entry(v.clone()).or_default() |= 1 << i;
        }
    }
    let word = |v: &Var| -> u64 { words.get(v).copied().unwrap_or(0) };
    let mask = if pending.len() == 64 { !0 } else { (1u64 << pending.len()) - 1 };
    for (mi, model) in models.iter().enumerate() {
        let (c, cs) = (&model.cone, &sim[mi]);
        let co = &class_of[mi];
        let state: Vec<u64> = cs
            .states
            .iter()
            .map(|n| {
                let (ci, neg) = co.get(n.as_str()).copied().unwrap_or((usize::MAX, false));
                let w = word(&Var::Class(ci));
                if neg { !w } else { w }
            })
            .collect();
        let free: Vec<u64> = cs.frees.iter().map(|v| word(&Var::Input(v.clone()))).collect();
        let mut val: Vec<u64> = Vec::with_capacity(c.gates.len());
        let mut x: Vec<u64> = Vec::new();
        let mut stack: Vec<u64> = Vec::new();
        let read = |i: In, val: &[u64]| -> u64 {
            match i {
                In::Const(v) => if v { !0 } else { 0 },
                In::Gate(g) => val[g],
                In::State(s) => state[s],
                In::Free(f) => free[f],
            }
        };
        for g in 0..c.gates.len() {
            x.clear();
            x.extend(cs.ins[g].iter().map(|&i| read(i, &val)));
            val.push(run(&cs.prog[g], &x, &mut stack));
        }
        for k in 0..model.regs.len() {
            let w = read(cs.next[k], &val);
            let neg = co.get(cs.reg_state[k].as_str()).is_some_and(|x| x.1);
            sims.words[mi][k].push((if neg { !w } else { w }) & mask);
        }
    }
    effort.resimulated += 1;
    for (i, (_, a, b)) in pending.iter().enumerate() {
        let (wa, wb) = (sims.words[a.0][a.1].last(), sims.words[b.0][b.1].last());
        if wa.zip(wb).is_none_or(|(x, y)| (x ^ y) >> i & 1 == 0) {
            let n = |r: &RegId| models[r.0].regs[r.1].name.as_str();
            return Err(format!("SAT refinement: the counter-example for {} / {} does not tell them apart in simulation", n(a), n(b)));
        }
    }
    Ok(())
}

/// A CNF input variable: a class's value this round, or a free input by its variable name. Two
/// kinds, so no input name can alias a class.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Var {
    Class(usize),
    Input(String),
}

/// DIAGNOSTIC: one rejected obligation: the counter-example's io_te / io_aresetn, the same pair
/// re-proved with io_te=0 and io_aresetn=1 assumed, and (rounds after the first) the fan-in
/// registers that were undecided or split last round.
fn diag_rejection<'m>(models: &[&'m Model], h: RegId, m: RegId, cex: &[Var], rs: &mut RoundSolver<'m>, class_of: &[ClassOf]) {
    let n = |x: RegId| models[x.0].regs[x.1].name.clone();
    let (round, logged) = DIAG.with(|d| {
        let mut d = d.borrow_mut();
        d.logged += 1;
        (d.round, d.logged)
    });
    let val = |name: &str| -> &str {
        let v = Var::Input(name.to_string());
        if !rs.vars.contains_key(&v) {
            "-"
        } else if cex.contains(&v) {
            "1"
        } else {
            "0"
        }
    };
    let (te, ar) = (val("io_te"), val("io_aresetn"));
    // the constrained recheck and the fan-in census cost a solve and a cone walk: first 3000 per round
    let mut constrained = "skip";
    let mut fan = String::new();
    if logged <= 3000 {
        constrained = match rs.prove_assuming(models, h, m, class_of, &[("io_te", false), ("io_aresetn", true)]) {
            Ok(Outcome::Unsat) | Ok(Outcome::Structural) => "unsat",
            Ok(Outcome::Sat(_)) => "sat",
            Ok(Outcome::GaveUp) => "gaveup",
            Err(_) => "err",
        };
        if round > 1 {
            DIAG.with(|d| {
                let d = d.borrow();
                let (mut und, mut spl) = (0, 0);
                for x in [h, m] {
                    for s in super::states_read(models[x.0], x.1) {
                        if let Some(&k) = d.reg_of[x.0].get(&s) {
                            let id = (x.0, k);
                            if d.undecided.contains(&id) {
                                und += 1;
                            } else if d.split_prev.contains(&id) {
                                spl += 1;
                            }
                        }
                    }
                }
                fan = format!(" fanin_undecided {und} fanin_split {spl}");
            });
        }
    }
    let same = models[h.0].regs[h.1].name == models[m.0].regs[m.1].name;
    eprintln!("SATDIAG rej r={round} same={same} {} / {} te={te} aresetn={ar} constrained={constrained}{fan}", n(h), n(m));
}

/// DIAGNOSTIC: one obligation re-encoded on its own (fresh CNF: the two cones, class variables,
/// the difference literal asserted) and written as DIMACS (`.cnf`, SAT = the pair differs) and
/// as bit-level SMT-LIB (`.smt2`, the same AND/XOR structure), with one manifest line.
fn dump_obligation(models: &[&Model], h: RegId, m: RegId, class_of: &[ClassOf], dir: &std::path::Path) {
    use std::io::Write;
    let n = |x: RegId| models[x.0].regs[x.1].name.clone();
    let mut cnf = Cnf::new();
    let mut vars: FxHashMap<Var, i32> = FxHashMap::default();
    let (mut lh, mut lm) = (FxHashMap::default(), FxHashMap::default());
    let (Ok(a), Ok(b)) = (next_lit(&mut cnf, &mut vars, &mut lh, models[h.0], h, &class_of[h.0]), next_lit(&mut cnf, &mut vars, &mut lm, models[m.0], m, &class_of[m.0])) else { return };
    let d = cnf.xor2(a, b);
    let k = DIAG.with(|x| {
        let mut x = x.borrow_mut();
        x.dumped += 1;
        x.dumped
    });
    let base = dir.join(format!("ob-{}-{k}", DIAG.with(|x| x.borrow().round)));
    let _ = std::fs::create_dir_all(dir);
    if let Ok(mut f) = std::fs::File::create(base.with_extension("cnf")) {
        let _ = writeln!(f, "c lec obligation {} / {} (SAT = they differ)", n(h), n(m));
        let _ = writeln!(f, "p cnf {} {}", cnf.n, cnf.clauses.len() + 1);
        for c in &cnf.clauses {
            let s: Vec<String> = c.iter().map(|l| l.to_string()).collect();
            let _ = writeln!(f, "{} 0", s.join(" "));
        }
        let _ = writeln!(f, "{d} 0");
    }
    let mut def: FxHashMap<i32, String> = FxHashMap::default();
    let lit = |l: i32| -> String {
        if l == T {
            "true".into()
        } else if l == -T {
            "false".into()
        } else if l < 0 {
            format!("(not v{})", -l)
        } else {
            format!("v{l}")
        }
    };
    for (&(x, y), &o) in &cnf.and {
        def.insert(o, format!("(and {} {})", lit(x), lit(y)));
    }
    for (&(x, y), &o) in &cnf.xor {
        def.insert(o, format!("(xor {} {})", lit(x), lit(y)));
    }
    if let Ok(mut f) = std::fs::File::create(base.with_extension("smt2")) {
        let _ = writeln!(f, "; lec obligation {} / {} (sat = they differ)\n(set-logic QF_BV)", n(h), n(m));
        for v in 2..=cnf.n {
            match def.get(&v) {
                Some(e) => {
                    let _ = writeln!(f, "(define-fun v{v} () Bool {e})");
                }
                None => {
                    let _ = writeln!(f, "(declare-const v{v} Bool)");
                }
            }
        }
        let _ = writeln!(f, "(assert {})\n(check-sat)\n(exit)", lit(d));
    }
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(dir.join("manifest.tsv")) {
        let (gh, gm) = (cone_gates(models[h.0], h, &|_| false), cone_gates(models[m.0], m, &|_| false));
        let _ = writeln!(f, "{}\t{}\t{}\t{}/{}\t{}/{}\t{}\t{}", base.display(), n(h), n(m), gh.len(), gm.len(), xor_gates(models[h.0], &gh), xor_gates(models[m.0], &gm), cnf.n, cnf.clauses.len() + 1);
    }
}

enum Outcome {
    Structural,
    Unsat,
    /// the variables the counter-example sets (every other one is 0)
    Sat(Vec<Var>),
    GaveUp,
}

/// One round's incremental solver: one CNF shared by every obligation of the round, each gate
/// encoded once (`lit`), only the clauses added since the last call sent to the solver.
pub(crate) struct RoundSolver<'m> {
    cnf: Cnf,
    sent: usize,
    sat: cadical::Solver,
    vars: FxHashMap<Var, i32>,
    /// per model: each net's literal this round
    lit: Vec<FxHashMap<&'m str, i32>>,
    limit: i32,
    /// obligations since the solver was last recycled
    calls: usize,
}

/// ABC recycles its sweeping solver (`Cec_ManSatSolverRecycle`) once it holds more than
/// `nSatVarMax` variables and has answered more than `nCallsRecycle` calls since the last
/// recycle (`Cec_ManSatSetDefaultParams`: 2000 and 200). A solver that only grows makes every
/// satisfiable answer extend a model over the whole round's CNF: on a core that was 30% of the
/// run (2026-11-19).
///
/// ⚠️ DIVERGENCE: the variable cap is 2^17, not 2000. CaDiCaL keeps what it learned across
/// calls, and at 2000 a cold solver gave up on a pair the warm one proves (rvv_backend_rob
/// `u_uop_valid_fifo.mem[0]`, BDD-undecided too), which cost 1,834 of 5,514 pairs; at 2^17 a
/// leaf's round is never recycled and only a core's is.
const SAT_VAR_MAX: i32 = 1 << 17;
const CALLS_RECYCLE: usize = 200;

/// ABC's recycle condition (`cecSolve.c`): BOTH over the variable cap and past the call count.
fn needs_recycle(vars: i32, calls: usize) -> bool {
    vars > SAT_VAR_MAX && calls > CALLS_RECYCLE
}

impl<'m> RoundSolver<'m> {
    pub(crate) fn new(models: usize, limit: i32) -> RoundSolver<'m> {
        RoundSolver { cnf: Cnf::new(), sent: 0, sat: cadical::Solver::new(), vars: FxHashMap::default(), lit: vec![FxHashMap::default(); models], limit, calls: 0 }
    }

    /// A fresh solver and CNF, every literal forgotten (ABC `Cec_ManSatSolverRecycle`): the next
    /// obligation encodes its cones again.
    fn recycle(&mut self) {
        *self = RoundSolver::new(self.lit.len(), self.limit);
    }

    /// One obligation: `h` and `m` load different values (each complemented when inverted in its
    /// class), every state read as its class's variable, every input free.
    fn prove(&mut self, models: &[&'m Model], h: RegId, m: RegId, class_of: &[ClassOf]) -> Result<Outcome, String> {
        self.calls += 1;
        if needs_recycle(self.cnf.n, self.calls) {
            self.recycle();
        }
        let a = next_lit(&mut self.cnf, &mut self.vars, &mut self.lit[h.0], models[h.0], h, &class_of[h.0])?;
        let b = next_lit(&mut self.cnf, &mut self.vars, &mut self.lit[m.0], models[m.0], m, &class_of[m.0])?;
        let d = self.cnf.xor2(a, b);
        if d == -T {
            return Ok(Outcome::Structural);
        }
        for c in &self.cnf.clauses[self.sent..] {
            self.sat.add_clause(c.iter().copied());
        }
        self.sent = self.cnf.clauses.len();
        self.sat.set_limit("conflicts", self.limit).map_err(|e| format!("SAT refinement: {e:?}"))?;
        Ok(match self.sat.solve_with([d]) {
            Some(false) => Outcome::Unsat,
            Some(true) => Outcome::Sat(self.vars.iter().filter(|(_, &v)| self.sat.value(v).unwrap_or(false)).map(|(name, _)| name.clone()).collect()),
            None => Outcome::GaveUp,
        })
    }

    /// DIAGNOSTIC: [`Self::prove`] with input values assumed (an input not in the CNF is left).
    fn prove_assuming(&mut self, models: &[&'m Model], h: RegId, m: RegId, class_of: &[ClassOf], fix: &[(&str, bool)]) -> Result<Outcome, String> {
        let a = next_lit(&mut self.cnf, &mut self.vars, &mut self.lit[h.0], models[h.0], h, &class_of[h.0])?;
        let b = next_lit(&mut self.cnf, &mut self.vars, &mut self.lit[m.0], models[m.0], m, &class_of[m.0])?;
        let d = self.cnf.xor2(a, b);
        for c in &self.cnf.clauses[self.sent..] {
            self.sat.add_clause(c.iter().copied());
        }
        self.sent = self.cnf.clauses.len();
        let mut assume = vec![d];
        for (name, v) in fix {
            if let Some(&x) = self.vars.get(&Var::Input(name.to_string())) {
                assume.push(if *v { x } else { -x });
            }
        }
        self.sat.set_limit("conflicts", self.limit).map_err(|e| format!("{e:?}"))?;
        Ok(match self.sat.solve_with(assume) {
            Some(false) => Outcome::Unsat,
            Some(true) => Outcome::Sat(Vec::new()),
            None => Outcome::GaveUp,
        })
    }

    /// `a` and `b` load the same next value under `class_of`: proved (not over the limit).
    pub(crate) fn same_next(&mut self, models: &[&'m Model], a: RegId, b: RegId, class_of: &[ClassOf]) -> Result<bool, String> {
        Ok(matches!(self.prove(models, a, b, class_of)?, Outcome::Unsat | Outcome::Structural))
    }
}

/// `--refine both`: the SAT fixed point re-keyed by one BDD round ([`super::round_keys`]). A class
/// the BDD keys split, every key decided, is an error; a member over the BDD budget is counted
/// unchecked. Returns (classes checked, members unchecked).
pub(crate) fn cross_check_with_bdd(models: &[&Model], classes: &[Vec<RegId>], inv: &Polarity) -> Result<(usize, usize), String> {
    let class_of = class_index(models, classes, &|r: RegId| inv[r.0][r.1]);
    let all = vec![true; classes.len()];
    let keys = super::round_keys(models, classes, &all, &class_of, super::BDD_LIMIT)?;
    let (mut checked, mut unchecked) = (0usize, 0usize);
    for (cl, k) in classes.iter().zip(keys) {
        let Some(k) = k else { continue };
        let decided: Vec<&Key> = k.iter().flatten().collect();
        unchecked += cl.len() - decided.len();
        checked += 1;
        if decided.windows(2).any(|w| w[0] != w[1]) {
            let n = |r: &RegId| models[r.0].regs[r.1].name.clone();
            return Err(format!("map --refine both: the BDD keys split a class the SAT refinement proved: {:?}", cl.iter().map(n).collect::<Vec<_>>()));
        }
    }
    Ok((checked, unchecked))
}

/// The gates of register `r`'s next-state cone that `done` does not hold, in cone order.
fn cone_gates(model: &Model, r: RegId, done: &dyn Fn(&str) -> bool) -> Vec<usize> {
    let c = &model.cone;
    let net = next_net(&model.regs[r.1].instance);
    let mut need: FxHashSet<usize> = FxHashSet::default();
    let mut stack: Vec<usize> = if done(&net) { Vec::new() } else { model.gate.get(&net).copied().into_iter().collect() };
    while let Some(k) = stack.pop() {
        if !need.insert(k) {
            continue;
        }
        for s in &c.gates[k].ins {
            if let Src::Net(n) = s {
                if let Some(&j) = model.gate.get(n) {
                    if !done(n) {
                        stack.push(j);
                    }
                }
            }
        }
    }
    let mut order: Vec<usize> = need.into_iter().collect();
    order.sort_unstable();
    order
}

/// Register `r`'s next value as a literal, complemented when it is inverted in its class; the
/// gates already in `lit` (this round) are not encoded again. A state reads its class's variable
/// before a free input of the same net, as the BDD builder does.
fn next_lit<'m>(cnf: &mut Cnf, vars: &mut FxHashMap<Var, i32>, lit: &mut FxHashMap<&'m str, i32>, model: &'m Model, r: RegId, co: &ClassOf) -> Result<i32, String> {
    let c = &model.cone;
    let inst = &model.regs[r.1].instance;
    let net = next_net(inst);
    let order = cone_gates(model, r, &|n| lit.contains_key(n));
    let mut var = |cnf: &mut Cnf, name: Var| -> i32 { *vars.entry(name).or_insert_with(|| cnf.fresh()) };
    for k in order {
        let g = &c.gates[k];
        let mut ins = Vec::with_capacity(g.ins.len());
        for s in &g.ins {
            ins.push(match s {
                Src::Const(v) => if *v { T } else { -T },
                Src::Net(n) => match lit.get(n.as_str()) {
                    Some(&x) => x,
                    None => {
                        let x = if model.state.contains(n.as_str()) {
                            let (ci, neg) = co.get(n.as_str()).copied().unwrap_or((usize::MAX, false));
                            let x = var(cnf, Var::Class(ci));
                            if neg { -x } else { x }
                        } else if let Some(v) = c.free.get(n) {
                            match diag_assume(v) {
                                Some(b) => if b { T } else { -T },
                                None => var(cnf, Var::Input(v.clone())),
                            }
                        } else {
                            return Err(format!("cone gate `{}` reads `{n}` before it is computed (gate {k})", g.out));
                        };
                        lit.insert(n.as_str(), x);
                        x
                    }
                },
            });
        }
        let y = match &g.logic {
            Logic::Prim(op) => prim_lit(cnf, *op, &ins, &g.pins)?,
            Logic::Func(f) => func_lit(cnf, f, &g.pins, &ins),
        };
        lit.insert(g.out.as_str(), y);
    }
    let y = lit.get(net.as_str()).copied().ok_or_else(|| format!("net `{net}` is not in the cone"))?;
    let neg = co.get(&state_net(inst)).is_some_and(|x| x.1);
    Ok(if neg { -y } else { y })
}

/// A CNF under construction: clauses over variables 1..=n, literal -v is NOT v; variable 1 is the
/// constant true. AND and XOR nodes are hashed, so a node built twice is one variable (as the
/// parked splr engine's encoder).
struct Cnf {
    n: i32,
    clauses: Vec<Vec<i32>>,
    and: FxHashMap<(i32, i32), i32>,
    xor: FxHashMap<(i32, i32), i32>,
}

const T: i32 = 1;

impl Cnf {
    fn new() -> Cnf {
        Cnf { n: 1, clauses: vec![vec![T]], and: FxHashMap::default(), xor: FxHashMap::default() }
    }

    fn fresh(&mut self) -> i32 {
        self.n += 1;
        self.n
    }

    fn and2(&mut self, a: i32, b: i32) -> i32 {
        if a == -T || b == -T || a == -b {
            return -T;
        }
        if a == T || a == b {
            return b;
        }
        if b == T {
            return a;
        }
        let key = (a.min(b), a.max(b));
        if let Some(&o) = self.and.get(&key) {
            return o;
        }
        let o = self.fresh();
        self.clauses.extend([vec![-o, a], vec![-o, b], vec![o, -a, -b]]);
        self.and.insert(key, o);
        o
    }

    fn or2(&mut self, a: i32, b: i32) -> i32 {
        -self.and2(-a, -b)
    }

    fn xor2(&mut self, a: i32, b: i32) -> i32 {
        if a == -T {
            return b;
        }
        if b == -T {
            return a;
        }
        if a == T {
            return -b;
        }
        if b == T {
            return -a;
        }
        if a == b {
            return -T;
        }
        if a == -b {
            return T;
        }
        let neg = (a < 0) != (b < 0);
        let (x, y) = (a.abs(), b.abs());
        let key = (x.min(y), x.max(y));
        let o = match self.xor.get(&key) {
            Some(&o) => o,
            None => {
                let o = self.fresh();
                let (x, y) = key;
                self.clauses.extend([vec![-o, x, y], vec![-o, -x, -y], vec![o, -x, y], vec![o, x, -y]]);
                self.xor.insert(key, o);
                o
            }
        };
        if neg {
            -o
        } else {
            o
        }
    }

    fn mux(&mut self, s: i32, b: i32, a: i32) -> i32 {
        let sb = self.and2(s, b);
        let sa = self.and2(-s, a);
        self.or2(sb, sa)
    }
}

fn func_lit(cnf: &mut Cnf, f: &Func, pins: &[String], ins: &[i32]) -> i32 {
    match f {
        Func::Port(p) => ins[pins.iter().position(|x| x == p).expect("logic_of keeps every named pin")],
        Func::Not(a) => -func_lit(cnf, a, pins, ins),
        Func::And(a, b) | Func::Or(a, b) | Func::Xor(a, b) => {
            let (x, y) = (func_lit(cnf, a, pins, ins), func_lit(cnf, b, pins, ins));
            match f {
                Func::And(..) => cnf.and2(x, y),
                Func::Or(..) => cnf.or2(x, y),
                _ => cnf.xor2(x, y),
            }
        }
        Func::One => T,
        Func::Zero => -T,
    }
}

fn prim_lit(cnf: &mut Cnf, op: Op, ins: &[i32], pins: &[String]) -> Result<i32, String> {
    let need = |n: usize| if ins.len() == n { Ok(()) } else { Err(format!("primitive expected {n} input(s), got {}", ins.len())) };
    let fold = |cnf: &mut Cnf, f: fn(&mut Cnf, i32, i32) -> i32, what: &str| -> Result<i32, String> {
        let mut acc = *ins.first().ok_or_else(|| format!("{what} needs inputs"))?;
        for &x in &ins[1..] {
            acc = f(cnf, acc, x);
        }
        Ok(acc)
    };
    Ok(match op {
        Op::Buf => {
            need(1)?;
            ins[0]
        }
        Op::Not => {
            need(1)?;
            -ins[0]
        }
        Op::Mux => {
            need(3)?;
            let idx = |want: &str| pins.iter().position(|p| p.eq_ignore_ascii_case(want));
            let (Some(a), Some(b), Some(s)) = (idx("A"), idx("B"), idx("S")) else { return Err("MUX needs pins A, B, S".into()) };
            cnf.mux(ins[s], ins[b], ins[a])
        }
        Op::And => fold(cnf, Cnf::and2, "AND/NAND")?,
        Op::Nand => -fold(cnf, Cnf::and2, "AND/NAND")?,
        Op::Or => fold(cnf, Cnf::or2, "OR/NOR")?,
        Op::Nor => -fold(cnf, Cnf::or2, "OR/NOR")?,
        Op::Xor => fold(cnf, Cnf::xor2, "XOR/XNOR")?,
        Op::Xnor => -fold(cnf, Cnf::xor2, "XOR/XNOR")?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A gate program computes what the word evaluators compute, for every primitive (both
    /// polarities, two and three inputs, the mux by pin name in any order) and a Liberty
    /// function, on words that cover every input combination.
    #[test]
    fn a_gate_program_agrees_with_the_word_evaluators() {
        let pins = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<String>>();
        let x = [0xaaaa_aaaa_aaaa_aaaa_u64, 0xcccc_cccc_cccc_cccc, 0xf0f0_f0f0_f0f0_f0f0];
        let mut stack = Vec::new();
        for op in [Op::And, Op::Nand, Op::Or, Op::Nor, Op::Xor, Op::Xnor] {
            for n in [2, 3] {
                let p = pins(&["A", "B", "C"][..n]);
                let got = run(&program(&Logic::Prim(op), &p, n).unwrap(), &x[..n], &mut stack);
                assert_eq!(got, super::super::prim_word(op, &p, &x[..n]).unwrap(), "{op:?}/{n}");
            }
        }
        for op in [Op::Buf, Op::Not] {
            let p = pins(&["A"]);
            assert_eq!(run(&program(&Logic::Prim(op), &p, 1).unwrap(), &x[..1], &mut stack), super::super::prim_word(op, &p, &x[..1]).unwrap());
        }
        let p = pins(&["S", "A", "B"]);
        assert_eq!(run(&program(&Logic::Prim(Op::Mux), &p, 3).unwrap(), &x, &mut stack), super::super::prim_word(Op::Mux, &p, &x).unwrap());
        let f = Func::Xor(Box::new(Func::And(Box::new(Func::Port("B".into())), Box::new(Func::Not(Box::new(Func::Port("A".into())))))), Box::new(Func::Or(Box::new(Func::Port("C".into())), Box::new(Func::Zero))));
        let p = pins(&["A", "B", "C"]);
        assert_eq!(run(&program(&Logic::Func(f.clone()), &p, 3).unwrap(), &x, &mut stack), super::super::func_word(&f, &p, &x));
        assert!(program(&Logic::Prim(Op::Not), &p, 3).is_err());
    }

    /// ABC recycles only when the solver is over `nSatVarMax` variables AND has answered more
    /// than `nCallsRecycle` calls since the last recycle: a small solver is kept however many
    /// calls it answers, and a large one until it has been used 200 times (our cap: 2^17).
    #[test]
    fn the_solver_is_recycled_past_both_abc_limits_only() {
        assert!(!needs_recycle(SAT_VAR_MAX, CALLS_RECYCLE + 1));
        assert!(!needs_recycle(SAT_VAR_MAX + 1, CALLS_RECYCLE));
        assert!(needs_recycle(SAT_VAR_MAX + 1, CALLS_RECYCLE + 1));
        assert_eq!((SAT_VAR_MAX, CALLS_RECYCLE), (1 << 17, 200));
    }
}
