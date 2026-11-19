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

use super::{class_index, func_word, prim_word, ClassOf, Key, Model, Polarity, RegId, SatEffort};
use crate::lec::{next_net, state_net, Logic, Op, Src};

/// Conflicts one obligation may take before its member is undecided. ABC's `&scorr` default is
/// 100; 1000 decided every pair the BDD path decides on the CoralNPU leaves measured
/// (2026-11-19: `rvv_backend_alu_unit_0` maps 363 at 1000, 352 at 100).
pub const PAIR_CONFLICTS: i32 = 1000;

/// Stage 4 by SAT: the fixed point ([`self`]); returns the rounds and the undecided registers, as
/// [`super::refine_within`] does. Thin sequencer, one stage per line.
pub(crate) fn refine_sat(models: &[&Model], classes: &mut Vec<Vec<RegId>>, inv: &Polarity, limit: i32, effort: &mut SatEffort) -> Result<(usize, Vec<RegId>), String> {
    let readers = super::readers_of(models);
    let mut undecided: Vec<RegId> = Vec::new();
    let mut seeds: Option<Vec<RegId>> = None;
    let mut rounds = 0;
    loop {
        rounds += 1;
        let class_of = class_index(models, classes, &|r: RegId| inv[r.0][r.1]);
        let active = super::active_classes(classes, &readers, seeds.as_deref());
        let split = sat_round(models, classes, &active, &class_of, limit, &mut undecided, effort)?;
        if split.is_empty() {
            return Ok((rounds, undecided));
        }
        seeds = Some(split);
    }
}

/// One round: each active class split by [`split_class`] under the round's classes `class_of`,
/// one solver and one set of counter-examples for the round. Returns every member of a class
/// that split, the next round's seeds.
fn sat_round(models: &[&Model], classes: &mut Vec<Vec<RegId>>, active: &[bool], class_of: &[ClassOf], limit: i32, undecided: &mut Vec<RegId>, effort: &mut SatEffort) -> Result<Vec<RegId>, String> {
    let mut rs = RoundSolver::new(models.len(), limit);
    let mut sims = Signatures::new(models);
    let mut next: Vec<Vec<RegId>> = Vec::with_capacity(classes.len());
    let mut split = Vec::new();
    for (cl, &act) in classes.iter().zip(active) {
        if cl.len() < 2 || !act {
            next.push(cl.clone());
            continue;
        }
        let parts = split_class(models, cl, class_of, &mut rs, &mut sims, undecided, effort)?;
        if parts.len() > 1 {
            split.extend(cl.iter().copied());
        }
        next.extend(parts);
    }
    *classes = next;
    Ok(split)
}

/// One class split into the parts of members that load the same next value under `class_of`, in
/// order of their first member. A member is proved only against the head of a part whose
/// counter-example signature it shares ([`Signatures`]); the counter-examples a class produced
/// are resimulated before the next class (and every 64).
fn split_class<'m>(
    models: &[&'m Model],
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
                    sims.pending.push((cex, head, r));
                    if sims.pending.len() == 64 {
                        resimulate_counter_examples(models, class_of, sims, effort)?;
                    }
                }
                Outcome::GaveUp => {
                    effort.gave_up += 1;
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
    if !sims.pending.is_empty() {
        resimulate_counter_examples(models, class_of, sims, effort)?;
    }
    Ok(parts)
}

/// Each register's values under the round's counter-examples so far, one bit per
/// counter-example; `pending` are the counter-examples not yet resimulated, each with the pair it
/// was found for.
struct Signatures {
    words: Vec<Vec<Vec<u64>>>,
    pending: Vec<(FxHashMap<String, bool>, RegId, RegId)>,
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

/// Every model evaluated under the pending counter-examples (one per bit; a name one does not
/// assign reads 0), states read as the ROUND's class values, and each register's next value
/// (complemented when inverted in its class) appended to its signature.
///
/// ⛔ A counter-example tells apart the pair it came from; one that does not is an error (the
/// CNF and the simulation disagree on a gate), never a silent merge.
fn resimulate_counter_examples(models: &[&Model], class_of: &[ClassOf], sims: &mut Signatures, effort: &mut SatEffort) -> Result<(), String> {
    let pending = std::mem::take(&mut sims.pending);
    let word = |name: &str| -> u64 { pending.iter().enumerate().fold(0u64, |w, (i, c)| if c.0.get(name).copied().unwrap_or(false) { w | (1 << i) } else { w }) };
    let mask = if pending.len() == 64 { !0 } else { (1u64 << pending.len()) - 1 };
    for (mi, model) in models.iter().enumerate() {
        let c = &model.cone;
        let co = &class_of[mi];
        let mut val: FxHashMap<&str, u64> = FxHashMap::default();
        let mut words: FxHashMap<String, u64> = FxHashMap::default();
        for g in &c.gates {
            let mut x = Vec::with_capacity(g.ins.len());
            for s in &g.ins {
                x.push(match s {
                    Src::Const(v) => if *v { !0 } else { 0 },
                    Src::Net(n) => match val.get(n.as_str()) {
                        Some(&w) => w,
                        None => {
                            let w = if model.state.contains(n.as_str()) {
                                let (ci, neg) = co.get(n.as_str()).copied().unwrap_or((usize::MAX, false));
                                let name = format!("class {ci}");
                                let w = *words.entry(name.clone()).or_insert_with(|| word(&name));
                                if neg { !w } else { w }
                            } else if let Some(v) = c.free.get(n) {
                                *words.entry(v.clone()).or_insert_with(|| word(v))
                            } else {
                                return Err(format!("cone gate `{}` reads `{n}` before it is computed", g.out));
                            };
                            val.insert(n.as_str(), w);
                            w
                        }
                    },
                });
            }
            let y = match &g.logic {
                Logic::Prim(op) => prim_word(*op, &g.pins, &x)?,
                Logic::Func(f) => func_word(f, &g.pins, &x),
            };
            val.insert(g.out.as_str(), y);
        }
        for (k, r) in model.regs.iter().enumerate() {
            let w = val.get(next_net(&r.instance).as_str()).copied().unwrap_or(0);
            let neg = co.get(&state_net(&r.instance)).is_some_and(|x| x.1);
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

enum Outcome {
    Structural,
    Unsat,
    Sat(FxHashMap<String, bool>),
    GaveUp,
}

/// One round's incremental solver: one CNF shared by every obligation of the round, each gate
/// encoded once (`lit`), only the clauses added since the last call sent to the solver.
pub(crate) struct RoundSolver<'m> {
    cnf: Cnf,
    sent: usize,
    sat: cadical::Solver,
    vars: FxHashMap<String, i32>,
    /// per model: each net's literal this round
    lit: Vec<FxHashMap<&'m str, i32>>,
    limit: i32,
}

impl<'m> RoundSolver<'m> {
    pub(crate) fn new(models: usize, limit: i32) -> RoundSolver<'m> {
        RoundSolver { cnf: Cnf::new(), sent: 0, sat: cadical::Solver::new(), vars: FxHashMap::default(), lit: vec![FxHashMap::default(); models], limit }
    }

    /// One obligation: `h` and `m` load different values (each complemented when inverted in its
    /// class), every state read as its class's variable, every input free.
    fn prove(&mut self, models: &[&'m Model], h: RegId, m: RegId, class_of: &[ClassOf]) -> Result<Outcome, String> {
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
            Some(true) => Outcome::Sat(self.vars.iter().map(|(name, &v)| (name.clone(), self.sat.value(v).unwrap_or(false))).collect()),
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
fn next_lit<'m>(cnf: &mut Cnf, vars: &mut FxHashMap<String, i32>, lit: &mut FxHashMap<&'m str, i32>, model: &'m Model, r: RegId, co: &ClassOf) -> Result<i32, String> {
    let c = &model.cone;
    let inst = &model.regs[r.1].instance;
    let net = next_net(inst);
    let order = cone_gates(model, r, &|n| lit.contains_key(n));
    let mut var = |cnf: &mut Cnf, name: String| -> i32 { *vars.entry(name).or_insert_with(|| cnf.fresh()) };
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
                            let x = var(cnf, format!("class {ci}"));
                            if neg { -x } else { x }
                        } else if let Some(v) = c.free.get(n) {
                            var(cnf, v.clone())
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
