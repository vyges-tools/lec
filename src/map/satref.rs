//! PROTOTYPE (branch only): register-correspondence refinement by SAT, as ABC's `&scorr` does it,
//! in place of the BDD keys of [`super::refine_within`]. Selected with `LEC_REFINE=sat`.
//!
//! The rule set (ABC `cecCorr.c` `Cec_ManLSCorrespondenceClasses`, `cecSolve.c`):
//! 1. Each round, the speculatively reduced one-frame model: every register's state is replaced
//!    by its class's value (one variable per class, complemented for a member inverted in it),
//!    every primary input is free. (ABC: `Gia_ManCorrSpecReduce`, `nFrames` = 1 by default.)
//! 2. One proof obligation per candidate pair, in class order: a class's head against each other
//!    member (ABC without rings: representative vs member; with rings, consecutive members). Two
//!    sides that hash to one literal are proved without a solver call (ABC skips the output).
//! 3. Each obligation is solved with a resource limit (ABC: 100 conflicts per output, `nBTLimit`).
//!    UNSAT: the pair holds this round. SAT: the assignment is a counter-example. Limit reached:
//!    the member leaves its class and stands alone, undecided (ABC `Gia_ManCheckRefinements`,
//!    status -1: `Cec_ManSimClassRemoveOne`).
//! 4. Counter-examples are resimulated, 64 at a time, over EVERY member's next-state function, and
//!    every class is split by the values (ABC `Cec_ManResimulateCounterExamples`). A pair already
//!    split is not solved again this round (ABC `Cec_ManObjsStillMerged`).
//! 5. The fixed point is a round in which nothing split: every remaining pair was proved under
//!    that round's partition, which is the same inductive invariant as the BDD keys prove.
//!
//! ⛔ Differences from ABC, prototype only: splr has no incremental mode and no conflict limit,
//! so each obligation is a fresh solver over the two cones with a CPU-time limit
//! ([`PAIR_TIMEOUT_S`]); the partition is the same coarsest fixed point as the BDD path, except
//! for members undecided within a limit.
use std::collections::HashMap;

use rustc_hash::{FxHashMap, FxHashSet};
use splr::{Certificate, Config, SolveIF, Solver, SolverError};
use vyges_loom::liberty_func::Func;

use super::{active_classes, class_index, func_word, prim_word, readers_of, ClassOf, Model, Polarity, RegId};
use crate::lec::{next_net, state_net, Logic, Op, Src};

/// CPU seconds one obligation may take before its member is undecided.
pub const PAIR_TIMEOUT_S: f64 = 2.0;

/// The fixed point by SAT ([`self`]); returns the rounds and the undecided registers, as
/// [`super::refine_within`] does. Thin sequencer, one stage per line.
pub(crate) fn refine_sat(models: &[&Model], classes: &mut Vec<Vec<RegId>>, inv: &Polarity) -> Result<(usize, Vec<RegId>), String> {
    let readers = readers_of(models);
    let mut undecided: Vec<RegId> = Vec::new();
    let mut seeds: Option<Vec<RegId>> = None;
    let mut rounds = 0;
    let mut stats = Stats::default();
    loop {
        rounds += 1;
        let class_of = class_index(models, classes, &|r: RegId| inv[r.0][r.1]);
        let active = active_classes(classes, &readers, seeds.as_deref());
        let split = sat_round(models, classes, &active, &class_of, &mut undecided, &mut stats)?;
        if std::env::var_os("LEC_SAT_STATS").is_some() {
            eprintln!("SATREF round {rounds} classes {} active {} {stats:?} split {}", classes.len(), active.iter().filter(|a| **a).count(), split.len());
        }
        if split.is_empty() {
            return Ok((rounds, undecided));
        }
        seeds = Some(split);
    }
}

#[derive(Debug, Default)]
struct Stats {
    structural: usize,
    unsat: usize,
    sat: usize,
    gave_up: usize,
    resims: usize,
}

/// One round: every obligation of the active classes, counter-examples resimulated in batches of
/// 64. Returns every member of a class that split (the next round's seeds).
fn sat_round(models: &[&Model], classes: &mut Vec<Vec<RegId>>, active: &[bool], class_of: &[ClassOf], undecided: &mut Vec<RegId>, st: &mut Stats) -> Result<Vec<RegId>, String> {
    let pairs: Vec<(RegId, RegId)> = classes
        .iter()
        .zip(active)
        .filter(|(c, a)| **a && c.len() > 1)
        .flat_map(|(c, _)| c[1..].iter().map(move |&m| (c[0], m)))
        .collect();
    let mut at = position(classes);
    let mut split: FxHashSet<RegId> = FxHashSet::default();
    let mut cexs: Vec<FxHashMap<String, bool>> = Vec::new();
    for (h, m) in pairs {
        if at[&h] != at[&m] {
            continue;
        }
        match prove_pair(models, h, m, class_of)? {
            Outcome::Structural => st.structural += 1,
            Outcome::Unsat => st.unsat += 1,
            Outcome::Sat(cex) => {
                st.sat += 1;
                cexs.push(cex);
                if cexs.len() == 64 {
                    resimulate(models, classes, class_of, &std::mem::take(&mut cexs), &mut split)?;
                    st.resims += 1;
                    at = position(classes);
                }
            }
            Outcome::GaveUp => {
                st.gave_up += 1;
                let c = at[&m];
                split.extend(classes[c].iter().copied());
                classes[c].retain(|r| *r != m);
                classes.push(vec![m]);
                undecided.push(m);
                at = position(classes);
            }
        }
    }
    if !cexs.is_empty() {
        resimulate(models, classes, class_of, &cexs, &mut split)?;
        st.resims += 1;
    }
    let mut out: Vec<RegId> = split.into_iter().collect();
    out.sort_unstable();
    Ok(out)
}

fn position(classes: &[Vec<RegId>]) -> HashMap<RegId, usize> {
    classes.iter().enumerate().flat_map(|(i, c)| c.iter().map(move |r| (*r, i))).collect()
}

enum Outcome {
    Structural,
    Unsat,
    Sat(FxHashMap<String, bool>),
    GaveUp,
}

/// One obligation: `h` and `m` load different values (each complemented when inverted in its
/// class), every state read as its class's variable, every input free.
fn prove_pair(models: &[&Model], h: RegId, m: RegId, class_of: &[ClassOf]) -> Result<Outcome, String> {
    let mut cnf = Cnf::new();
    let mut vars: FxHashMap<String, i32> = FxHashMap::default();
    let a = next_lit(&mut cnf, &mut vars, models[h.0], h, &class_of[h.0])?;
    let b = next_lit(&mut cnf, &mut vars, models[m.0], m, &class_of[m.0])?;
    let d = cnf.xor2(a, b);
    if d == -T {
        return Ok(Outcome::Structural);
    }
    cnf.clauses.push(vec![d]);
    let config = Config { quiet_mode: true, c_timeout: PAIR_TIMEOUT_S, ..Config::default() };
    let n = cnf.n;
    let got = match Solver::try_from((config, cnf.clauses.as_slice())) {
        Ok(mut s) => s.solve(),
        Err(Ok(c)) => Ok(c),
        Err(Err(e)) => Err(e),
    };
    let model = match got {
        Ok(Certificate::SAT(v)) => v,
        Ok(Certificate::UNSAT) | Err(SolverError::EmptyClause) | Err(SolverError::RootLevelConflict(_)) | Err(SolverError::Inconsistent) => {
            return Ok(Outcome::Unsat)
        }
        Err(SolverError::TimeOut) | Err(SolverError::OutOfMemory) => return Ok(Outcome::GaveUp),
        Err(e) => return Err(format!("SAT refinement: {e}")),
    };
    let mut val = vec![false; n as usize + 1];
    for l in model {
        if l > 0 && l <= n {
            val[l as usize] = true;
        }
    }
    Ok(Outcome::Sat(vars.into_iter().map(|(name, v)| (name, val[v as usize])).collect()))
}

/// Register `r`'s next value as a literal, complemented when it is inverted in its class.
fn next_lit(cnf: &mut Cnf, vars: &mut FxHashMap<String, i32>, model: &Model, r: RegId, co: &ClassOf) -> Result<i32, String> {
    let c = &model.cone;
    let inst = &model.regs[r.1].instance;
    let net = next_net(inst);
    let mut need: FxHashSet<usize> = FxHashSet::default();
    let mut stack: Vec<usize> = model.gate.get(&net).copied().into_iter().collect();
    while let Some(k) = stack.pop() {
        if !need.insert(k) {
            continue;
        }
        for s in &c.gates[k].ins {
            if let Src::Net(n) = s {
                if let Some(&j) = model.gate.get(n) {
                    stack.push(j);
                }
            }
        }
    }
    let mut order: Vec<usize> = need.into_iter().collect();
    order.sort_unstable();
    let mut lit: FxHashMap<&str, i32> = FxHashMap::default();
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
                        // as the BDD builder: a register's state first, then a free input
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

/// Every model evaluated under up to 64 counter-examples (one per bit; a name a counter-example
/// does not assign reads 0), the states read as the ROUND's class values, and every class with
/// two or more members split by its members' next values (complemented when inverted). A
/// counter-example always separates the pair it came from; one that does not is an error.
fn resimulate(models: &[&Model], classes: &mut Vec<Vec<RegId>>, class_of: &[ClassOf], cexs: &[FxHashMap<String, bool>], split: &mut FxHashSet<RegId>) -> Result<(), String> {
    let word = |name: &str| -> u64 { cexs.iter().enumerate().fold(0u64, |w, (i, c)| if c.get(name).copied().unwrap_or(false) { w | (1 << i) } else { w }) };
    let mut next: Vec<Vec<u64>> = Vec::with_capacity(models.len());
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
        let mut nx = Vec::with_capacity(model.regs.len());
        for r in &model.regs {
            let w = val.get(next_net(&r.instance).as_str()).copied().unwrap_or(0);
            let neg = co.get(&state_net(&r.instance)).is_some_and(|x| x.1);
            nx.push(if neg { !w } else { w });
        }
        next.push(nx);
    }
    let mask = if cexs.len() == 64 { !0 } else { (1u64 << cexs.len()) - 1 };
    let mut out: Vec<Vec<RegId>> = Vec::with_capacity(classes.len());
    for cl in classes.iter() {
        if cl.len() < 2 {
            out.push(cl.clone());
            continue;
        }
        let mut parts: Vec<Vec<RegId>> = Vec::new();
        let mut at: HashMap<u64, usize> = HashMap::new();
        for &r in cl {
            let k = next[r.0][r.1] & mask;
            match at.get(&k) {
                Some(&p) => parts[p].push(r),
                None => {
                    at.insert(k, parts.len());
                    parts.push(vec![r]);
                }
            }
        }
        if parts.len() > 1 {
            split.extend(cl.iter().copied());
        }
        out.extend(parts);
    }
    *classes = out;
    Ok(())
}

/// A CNF under construction: clauses over variables 1..=n, literal -v is NOT v; variable 1 is the
/// constant true. AND and XOR nodes are hashed, so a node built twice is one variable (from the
/// parked splr engine, `docs/formal/sat-engine-prototype/sat.rs`).
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
