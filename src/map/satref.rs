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
//! Solver: CaDiCaL (`cadical` crate, bundled source), one incremental instance per round with a
//! deterministic conflict limit per obligation ([`PAIR_CONFLICTS`]). The partition is the same
//! coarsest fixed point as the BDD path, except for members undecided within a limit.
use std::collections::HashMap;

use rustc_hash::{FxHashMap, FxHashSet};
use vyges_loom::liberty_func::Func;

use super::{active_classes, class_index, func_word, prim_word, readers_of, ClassOf, Key, Model, Polarity, RegId};
use crate::lec::{next_net, state_net, Logic, Op, Src};


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
            if std::env::var_os("LEC_SAT_VERIFY").is_some() {
                verify_with_bdd(models, classes, inv)?;
            }
            return Ok((rounds, undecided));
        }
        seeds = Some(split);
    }
}

/// Independent check of the SAT fixed point: one BDD round ([`super::round_keys`]) over the final
/// classes. A class the BDD keys split, every key decided, is a soundness bug; a member over the
/// BDD budget is only unchecked.
fn verify_with_bdd(models: &[&Model], classes: &[Vec<RegId>], inv: &Polarity) -> Result<(), String> {
    let class_of = class_index(models, classes, &|r: RegId| inv[r.0][r.1]);
    let all = vec![true; classes.len()];
    let keys = super::round_keys(models, classes, &all, &class_of, super::BDD_LIMIT)?;
    let (mut checked, mut disagree, mut unchecked) = (0usize, 0usize, 0usize);
    for (cl, k) in classes.iter().zip(keys) {
        let Some(k) = k else { continue };
        let decided: Vec<&Key> = k.iter().flatten().collect();
        unchecked += cl.len() - decided.len();
        checked += 1;
        if decided.windows(2).any(|w| w[0] != w[1]) {
            disagree += 1;
            let n = |r: &RegId| models[r.0].regs[r.1].name.clone();
            eprintln!("SATVERIFY DISAGREE class {:?}", cl.iter().map(n).collect::<Vec<_>>());
        }
    }
    eprintln!("SATVERIFY classes checked {checked} bdd-disagree {disagree} members-over-bdd-budget {unchecked}");
    Ok(())
}

#[derive(Debug, Default)]
struct Stats {
    structural: usize,
    unsat: usize,
    sat: usize,
    gave_up: usize,
    resims: usize,
    /// seconds: CNF encoding, solver construction, solving, resimulation
    t_encode: f64,
    t_build: f64,
    t_solve: f64,
    t_resim: f64,
    vars: usize,
    clauses: usize,
}

/// One round: every obligation of the active classes, counter-examples resimulated in batches of
/// 64. Returns every member of a class that split (the next round's seeds).
fn sat_round<'m>(models: &[&'m Model], classes: &mut Vec<Vec<RegId>>, active: &[bool], class_of: &[ClassOf], undecided: &mut Vec<RegId>, st: &mut Stats) -> Result<Vec<RegId>, String> {
    let pairs: Vec<(RegId, RegId)> = classes
        .iter()
        .zip(active)
        .filter(|(c, a)| **a && c.len() > 1)
        .flat_map(|(c, _)| c[1..].iter().map(move |&m| (c[0], m)))
        .collect();
    let mut rs = RoundSolver::new(models.len());
    let mut at = position(classes);
    let mut split: FxHashSet<RegId> = FxHashSet::default();
    let mut cexs: Vec<FxHashMap<String, bool>> = Vec::new();
    for (h, m) in pairs {
        if at[&h] != at[&m] {
            continue;
        }
        match rs.prove(models, h, m, class_of, st)? {
            Outcome::Structural => st.structural += 1,
            Outcome::Unsat => st.unsat += 1,
            Outcome::Sat(cex) => {
                st.sat += 1;
                cexs.push(cex);
                if cexs.len() == 64 {
                    let t3 = std::time::Instant::now();
                    resimulate(models, classes, class_of, &std::mem::take(&mut cexs), &mut split)?;
                    st.t_resim += t3.elapsed().as_secs_f64();
                    st.resims += 1;
                    at = position(classes);
                }
            }
            Outcome::GaveUp(sz) => {
                st.gave_up += 1;
                if std::env::var_os("LEC_SAT_STATS").is_some() {
                    let n = |r: RegId| models[r.0].regs[r.1].name.as_str();
                    eprintln!("SATREF undecided {} / {} gates {}/{} xor {}/{}", n(h), n(m), sz[0].gates, sz[1].gates, sz[0].xors, sz[1].xors);
                }
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
        let t3 = std::time::Instant::now();
        resimulate(models, classes, class_of, &cexs, &mut split)?;
        st.t_resim += t3.elapsed().as_secs_f64();
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
    /// Over the conflict limit: each side's cone size and its XOR-type gates (an arithmetic hint).
    GaveUp([Cone2; 2]),
}

/// A cone's size: gates, and the XOR/XNOR gates among them.
#[derive(Debug, Clone, Copy)]
struct Cone2 {
    gates: usize,
    xors: usize,
}

/// Conflicts one obligation may take before its member is undecided (ABC `&scorr`: `nBTLimit`,
/// 100 by default); `LEC_SAT_CONFLICTS` overrides it in the prototype.
pub const PAIR_CONFLICTS: i32 = 1000;

/// One round's incremental solver (ABC: one `Cec_ManSat_t` for the whole speculatively reduced
/// miter, `Cec_ManSatSolveMiter`). Every gate is encoded once per round, into one CNF shared by
/// all obligations, and only the clauses added since the last call are sent to the solver; each
/// obligation is solved under the assumption of its difference literal, so what the solver
/// learned proving one pair helps the next.
struct RoundSolver<'m> {
    cnf: Cnf,
    sent: usize,
    sat: cadical::Solver,
    vars: FxHashMap<String, i32>,
    /// per model: each net's literal so far
    lit: Vec<FxHashMap<&'m str, i32>>,
    limit: i32,
}

impl<'m> RoundSolver<'m> {
    fn new(models: usize) -> RoundSolver<'m> {
        let limit = std::env::var("LEC_SAT_CONFLICTS").ok().and_then(|s| s.parse().ok()).unwrap_or(PAIR_CONFLICTS);
        RoundSolver { cnf: Cnf::new(), sent: 0, sat: cadical::Solver::new(), vars: FxHashMap::default(), lit: vec![FxHashMap::default(); models], limit }
    }

    /// One obligation: `h` and `m` load different values (each complemented when inverted in its
    /// class), every state read as its class's variable, every input free.
    fn prove(&mut self, models: &[&'m Model], h: RegId, m: RegId, class_of: &[ClassOf], st: &mut Stats) -> Result<Outcome, String> {
        let t0 = std::time::Instant::now();
        let a = next_lit(&mut self.cnf, &mut self.vars, &mut self.lit[h.0], models[h.0], h, &class_of[h.0])?;
        let b = next_lit(&mut self.cnf, &mut self.vars, &mut self.lit[m.0], models[m.0], m, &class_of[m.0])?;
        let d = self.cnf.xor2(a, b);
        st.t_encode += t0.elapsed().as_secs_f64();
        if d == -T {
            return Ok(Outcome::Structural);
        }
        let t1 = std::time::Instant::now();
        for c in &self.cnf.clauses[self.sent..] {
            self.sat.add_clause(c.iter().copied());
        }
        self.sent = self.cnf.clauses.len();
        st.vars = self.cnf.n as usize;
        st.clauses = self.sent;
        st.t_build += t1.elapsed().as_secs_f64();
        let t2 = std::time::Instant::now();
        self.sat.set_limit("conflicts", self.limit).map_err(|e| format!("SAT refinement: {e:?}"))?;
        let got = self.sat.solve_with([d]);
        st.t_solve += t2.elapsed().as_secs_f64();
        match got {
            Some(false) => Ok(Outcome::Unsat),
            Some(true) => Ok(Outcome::Sat(self.vars.iter().map(|(name, &v)| (name.clone(), self.sat.value(v).unwrap_or(false))).collect())),
            None => Ok(Outcome::GaveUp([cone_size(models[h.0], h), cone_size(models[m.0], m)])),
        }
    }
}

/// The gates of register `r`'s next-state cone, by depth-first search, in cone order.
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

fn cone_size(model: &Model, r: RegId) -> Cone2 {
    let order = cone_gates(model, r, &|_| false);
    let xors = order
        .iter()
        .filter(|&&k| match &model.cone.gates[k].logic {
            Logic::Prim(op) => matches!(op, Op::Xor | Op::Xnor),
            Logic::Func(f) => has_xor(f),
        })
        .count();
    Cone2 { gates: order.len(), xors }
}

/// Register `r`'s next value as a literal, complemented when it is inverted in its class;
/// gates already in `lit` (this round) are not encoded again.
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

fn has_xor(f: &Func) -> bool {
    match f {
        Func::Xor(..) => true,
        Func::Not(a) => has_xor(a),
        Func::And(a, b) | Func::Or(a, b) => has_xor(a) || has_xor(b),
        _ => false,
    }
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
