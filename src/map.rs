//! Register map: which register of one netlist holds the same state as which register of another,
//! **proved**, never guessed from a name.
//!
//! This is what a timing-constraint file written against one netlist (an RTL elaboration, a
//! pre-repair netlist) needs before it can be compared with one written against another: the
//! rename map from each register to its counterpart. A name can propose a pair; only a proof
//! puts it in the map.
//!
//! The method is register correspondence (the van Eijk fixed point):
//!
//! 1. [`model`]: each design in the sequential model of [`crate::sec`] (registers are state, one
//!    clock, every register starting at 0, asynchronous clear and preset acting at the edge).
//! 2. [`simulate`]: both designs from the all-zero state on the SAME random inputs (each primary
//!    input by name), 64 runs at once for [`CYCLES`] cycles. A register's signature is its state
//!    in every run and cycle.
//! 3. [`candidate_classes`]: registers with one signature form a class, whichever design they
//!    are in. Two registers that ever differed in simulation are never assumed equal.
//! 4. [`refine`]: assume every class holds one value (one BDD variable per class) and build each
//!    member's next-state function over the primary inputs and the class variables. Members whose
//!    functions differ are split. Repeat until nothing splits.
//! 5. [`report`]: a class left with exactly one register of each design is a MAPPED pair.
//!
//! 🔑 Why the fixed point is a proof: every member of a final class starts at 0, and in any state
//! where every class holds one value, every member of a class loads the same next value. By
//! induction over the clock edges, the members of a class hold the same value in every state the
//! two designs reach from 0 on the same inputs.
//!
//! ⛔ What is NOT in the map, and why each is reported rather than resolved:
//! - a register whose class holds no register of the other design (`unmatched`): it has no
//!   counterpart that provably holds its value;
//! - a class with several registers of one design (`duplicated` or `ambiguous`): the map gives one
//!   name per name, and choosing one would be a guess;
//! - a register stored inverted (its counterpart holds the complement): not matched by this model;
//! - a register whose next-state BDD outgrew [`BDD_LIMIT`] (`undecided`): its class is split
//!   into single registers, which only weakens what the others may assume, so the rest stays sound.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::bdd::Bdd;
use crate::lec::{apply_op, func_bdd, next_net, seq_cone, state_net, Cone, Design, Logic, Op, Src};
use crate::liberty::{Dir, Lib};
use crate::netlist::Netlist;
use vyges_loom::liberty_func::Func;

/// Simulated clock cycles; each cycle runs 64 input sequences at once (one per bit).
pub const CYCLES: usize = 32;

/// Nodes (plus memo entries) one class's next-state BDDs may take before its registers are
/// reported undecided.
pub const BDD_LIMIT: usize = 1 << 20;

/// Unmatched golden x revised register pairs [`attribute`] compares by simulation at most.
pub const ATTRIBUTION_CAP: usize = 1 << 22;

/// Leftover golden x revised x pair checks [`attribute`] spends pairing what simulation left.
pub const LEFTOVER_CAP: usize = 1 << 16;

/// Which name a register is known by in the map.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Naming {
    /// The register's instance name.
    Instance,
    /// The net on the register's stored-value output (the pin whose function is the `ff`'s first
    /// state variable): the RTL register's name in a netlist that keeps RTL names on nets only.
    Net,
}

/// Which design a register is in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Side {
    Golden,
    Revised,
}

/// One register: its design, its instance and the name the map uses for it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegName {
    pub side: Side,
    pub instance: String,
    pub name: String,
}

/// The register map and what could not be put in it.
#[derive(Debug, Clone, Default)]
pub struct MapReport {
    /// Golden name -> revised name, each pair proved to hold the same value.
    pub mapped: BTreeMap<String, String>,
    /// A golden register with several revised registers that all hold its value (a register the
    /// revised design duplicated): golden name -> revised names.
    pub duplicated: BTreeMap<String, Vec<String>>,
    /// A class with several golden registers (they hold one value; which one a revised register
    /// stands for is not decided): golden names, revised names.
    pub ambiguous: Vec<(Vec<String>, Vec<String>)>,
    /// Golden registers with no counterpart (`true`: a candidate shared their simulation
    /// signature and was disproved).
    pub unmatched_golden: BTreeMap<String, bool>,
    /// Revised registers with no counterpart (same flag).
    pub unmatched_revised: BTreeMap<String, bool>,
    /// Registers whose class outgrew the BDD limit.
    pub undecided: Vec<RegName>,
    /// Registers with no connected output: nothing reads them, so nothing to map.
    pub unobserved: Vec<RegName>,
    pub golden_registers: usize,
    pub revised_registers: usize,
    /// Refinement rounds until nothing split.
    pub rounds: usize,
    /// Where the difference starts ([`attribute`]): unmatched golden and revised registers paired
    /// by their simulation, whose next-state logic differs even with every register it reads
    /// assumed equal. ⛔ For diagnosis only: these pairs are never in the map.
    pub causes: Vec<(String, String)>,
    /// Unmatched pairs (paired as for `causes`) whose next-state logic is the same once what they
    /// read is assumed equal: they differ only through a cause.
    pub follows: Vec<(String, String)>,
    /// Unmatched pairs that differ but read a register left unpaired: they may differ only
    /// through it, so they are not called causes.
    pub unexplained: Vec<(String, String)>,
    /// Unmatched registers that could not be paired, so not attributed.
    pub unattributed: usize,
    /// The attribution was skipped: more unmatched pairs to compare than [`ATTRIBUTION_CAP`].
    pub attribution_skipped: bool,
}

impl MapReport {
    /// Every register of both designs is in a one-to-one pair.
    pub fn one_to_one(&self) -> bool {
        self.mapped.len() == self.golden_registers
            && self.mapped.len() == self.revised_registers
            && self.unobserved.is_empty()
    }
}

/// The register map of `golden` to `revised`: the thin sequence of the stages the module doc
/// names, in its order.
pub fn register_map(golden: &Netlist, revised: &Netlist, lib: &Lib, names: (Naming, Naming)) -> Result<MapReport, String> {
    if lib.cells.is_empty() {
        return Err("no cells in the Liberty".into());
    }
    let (g, r) = (Design::sequential(golden, lib), Design::sequential(revised, lib));
    let (gm, rm) = (model(&g, Side::Golden, names.0)?, model(&r, Side::Revised, names.1)?);
    let sigs = simulate(&[&gm, &rm])?;
    let mut classes = candidate_classes(&[&gm, &rm], &sigs);
    let candidates = classes.clone();
    let (rounds, undecided) = refine(&[&gm, &rm], &mut classes)?;
    let mut rep = report(&[&gm, &rm], &candidates, &classes, &undecided, rounds);
    attribute(&[&gm, &rm], &sigs, &classes, &mut rep)?;
    Ok(rep)
}

/// One design in the sequential model: its cone, the registers in it, and where each gate is.
pub(crate) struct Model {
    side: Side,
    cone: Cone,
    /// Registers in cone order (`cone.regs`), each with its map name.
    regs: Vec<RegName>,
    /// Gate index by the net it drives.
    gate: HashMap<String, usize>,
    /// Every register's state net ([`state_net`]).
    state: HashSet<String>,
    unobserved: Vec<RegName>,
}

/// Stage 1: the cone of every register's outputs, with each register's next-state gate.
pub(crate) fn model(d: &Design, side: Side, naming: Naming) -> Result<Model, String> {
    let (nl, lib) = (d.netlist(), d.liberty());
    let mut endpoints = Vec::new();
    let mut name_of: HashMap<&str, String> = HashMap::new();
    let mut unobserved = Vec::new();
    for inst in &nl.insts {
        let Some(cell) = lib.cells.get(&inst.cell).filter(|c| c.is_seq) else { continue };
        let outs: Vec<(&str, &str)> = inst
            .conns
            .iter()
            .filter(|(p, _)| cell.pins.get(p).map(|x| x.direction) == Some(Dir::Out))
            .map(|(p, n)| (p.as_str(), n.as_str()))
            .collect();
        let q = cell.seq_group.as_ref().and_then(|g| {
            outs.iter().find(|(p, _)| cell.pins[*p].function.as_deref().map(str::trim) == Some(g.iq.as_str())).map(|&(_, n)| n)
        });
        let name = match naming {
            Naming::Instance => Some(inst.name.clone()),
            Naming::Net => q.map(str::to_string),
        };
        match (outs.first(), name) {
            (Some(&(_, n)), Some(name)) => {
                endpoints.push(n.to_string());
                name_of.insert(inst.name.as_str(), name);
            }
            _ => unobserved.push(RegName { side, instance: inst.name.clone(), name: inst.name.clone() }),
        }
    }
    let cone = seq_cone(d, &endpoints)?;
    let regs = cone
        .regs
        .iter()
        .map(|i| RegName { side, instance: i.clone(), name: name_of.get(i.as_str()).cloned().unwrap_or_else(|| i.clone()) })
        .collect();
    let gate = cone.gates.iter().enumerate().map(|(k, g)| (g.out.clone(), k)).collect();
    let state = cone.regs.iter().map(|r| state_net(r)).collect();
    Ok(Model { side, cone, regs, gate, state, unobserved })
}

/// A register across both models: (model index, register index).
type RegId = (usize, usize);

/// One 64-bit word of input `name` in `cycle`: the same in every design, so two designs see the
/// same input sequences (splitmix64 over an FNV-1a hash of the name).
fn input_word(name: &str, cycle: usize) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in name.bytes() {
        h = (h ^ u64::from(b)).wrapping_mul(0x0000_0100_0000_01b3);
    }
    let mut z = h ^ (cycle as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// A `function` over 64 runs at once, `x[k]` standing for `pins[k]`.
fn func_word(f: &Func, pins: &[String], x: &[u64]) -> u64 {
    match f {
        Func::Port(p) => x[pins.iter().position(|q| q == p).expect("logic_of keeps every named pin")],
        Func::Not(a) => !func_word(a, pins, x),
        Func::And(a, b) => func_word(a, pins, x) & func_word(b, pins, x),
        Func::Or(a, b) => func_word(a, pins, x) | func_word(b, pins, x),
        Func::Xor(a, b) => func_word(a, pins, x) ^ func_word(b, pins, x),
        Func::One => !0,
        Func::Zero => 0,
    }
}

/// A primitive over 64 runs at once (the rules of [`crate::lec::prim_value`]).
fn prim_word(op: Op, pins: &[String], x: &[u64]) -> Result<u64, String> {
    let need = |n: usize| if x.len() == n { Ok(()) } else { Err(format!("primitive expected {n} input(s), got {}", x.len())) };
    if x.is_empty() {
        return Err("primitive needs inputs".into());
    }
    let and = x.iter().fold(!0, |a, &v| a & v);
    let or = x.iter().fold(0, |a, &v| a | v);
    let xor = x.iter().fold(0, |a, &v| a ^ v);
    Ok(match op {
        Op::Buf => { need(1)?; x[0] }
        Op::Not => { need(1)?; !x[0] }
        Op::And => and,
        Op::Nand => !and,
        Op::Or => or,
        Op::Nor => !or,
        Op::Xor => xor,
        Op::Xnor => !xor,
        Op::Mux => {
            need(3)?;
            let idx = |want: &str| pins.iter().position(|p| p.eq_ignore_ascii_case(want));
            let (Some(a), Some(b), Some(s)) = (idx("A"), idx("B"), idx("S")) else { return Err("MUX needs pins A, B, S".into()) };
            (x[s] & x[b]) | (!x[s] & x[a])
        }
    })
}

/// Stage 2: each register's state in 64 runs over [`CYCLES`] cycles from the all-zero state,
/// every design on the same inputs. `sigs[m][k]` is model `m`'s register `k`.
pub(crate) fn simulate(models: &[&Model]) -> Result<Vec<Vec<Vec<u64>>>, String> {
    let mut out = Vec::new();
    for m in models {
        let c = &m.cone;
        let mut state = vec![0u64; m.regs.len()];
        let mut sig = vec![Vec::with_capacity(CYCLES); m.regs.len()];
        let states: Vec<String> = c.regs.iter().map(|r| state_net(r)).collect();
        let nexts: Vec<String> = c.regs.iter().map(|r| next_net(r)).collect();
        let mut val: HashMap<&str, u64> = HashMap::new();
        for cycle in 0..CYCLES {
            val.clear();
            // free inputs first, then the states over them (see `next_state_bdds`)
            for (net, var) in &c.free {
                val.insert(net.as_str(), input_word(var, cycle));
            }
            for (k, s) in states.iter().enumerate() {
                val.insert(s.as_str(), state[k]);
                sig[k].push(state[k]);
            }
            for g in &c.gates {
                let x: Vec<u64> = g
                    .ins
                    .iter()
                    .map(|s| match s {
                        Src::Net(n) => val.get(n.as_str()).copied().ok_or_else(|| format!("cone gate `{}` reads `{n}` before it is computed", g.out)),
                        Src::Const(v) => Ok(if *v { !0 } else { 0 }),
                    })
                    .collect::<Result<_, _>>()?;
                let y = match &g.logic {
                    Logic::Prim(op) => prim_word(*op, &g.pins, &x)?,
                    Logic::Func(f) => func_word(f, &g.pins, &x),
                };
                val.insert(g.out.as_str(), y);
            }
            for (k, r) in c.regs.iter().enumerate() {
                state[k] = val.get(nexts[k].as_str()).copied().ok_or_else(|| format!("register `{r}` has no next-state gate"))?;
            }
        }
        out.push(sig);
    }
    Ok(out)
}

/// Stage 3: the registers of all models grouped by signature, each class in (model, register)
/// order, the classes in order of their first member.
pub(crate) fn candidate_classes(models: &[&Model], sigs: &[Vec<Vec<u64>>]) -> Vec<Vec<RegId>> {
    let mut by_sig: BTreeMap<&[u64], usize> = BTreeMap::new();
    let mut classes: Vec<Vec<RegId>> = Vec::new();
    for (m, model) in models.iter().enumerate() {
        for (k, sig) in sigs[m].iter().enumerate().take(model.regs.len()) {
            let c = *by_sig.entry(sig.as_slice()).or_insert_with(|| {
                classes.push(Vec::new());
                classes.len() - 1
            });
            classes[c].push((m, k));
        }
    }
    classes
}

/// The BDD of each of `nets` in one model, in `bdd`, a free input by its variable name and a
/// register's state by its class: `var(name)` gives the variable. `None` once the manager is
/// exhausted.
fn next_state_bdds(
    model: &Model,
    nets: &[String],
    bdd: &mut Bdd,
    var: &mut dyn FnMut(&mut Bdd, &str) -> u32,
    class_var: &dyn Fn(&str) -> String,
) -> Result<Option<Vec<u32>>, String> {
    let c = &model.cone;
    // the gates the nets need, by depth-first search without recursion, then in cone order
    let mut need = vec![false; c.gates.len()];
    let mut stack: Vec<usize> = nets.iter().filter_map(|n| model.gate.get(n).copied()).collect();
    while let Some(k) = stack.pop() {
        if std::mem::replace(&mut need[k], true) {
            continue;
        }
        for s in &c.gates[k].ins {
            if let Src::Net(n) = s {
                if let Some(&j) = model.gate.get(n) {
                    if !need[j] {
                        stack.push(j);
                    }
                }
            }
        }
    }
    let mut f: HashMap<&str, u32> = HashMap::new();
    for (k, g) in c.gates.iter().enumerate().filter(|(k, _)| need[*k]) {
        let mut ins = Vec::with_capacity(g.ins.len());
        for s in &g.ins {
            ins.push(match s {
                Src::Const(v) => if *v { bdd.one() } else { bdd.zero() },
                Src::Net(n) => match f.get(n.as_str()) {
                    Some(&x) => x,
                    None => {
                        // ⛔ A register's state first: `seq_cone` also lists the state net of a
                        // register whose `next_state` reads its own state (an enable register)
                        // as a free input, and as one it would be a variable of its own, not its
                        // class's: an enable register then never matched its own copy.
                        let name = if model.state.contains(n.as_str()) {
                            class_var(n)
                        } else if let Some(v) = c.free.get(n) {
                            v.clone()
                        } else {
                            return Err(format!("cone gate `{}` reads `{n}` before it is computed (gate {k})", g.out));
                        };
                        let x = var(bdd, &name);
                        f.insert(n.as_str(), x);
                        x
                    }
                },
            });
        }
        let y = match &g.logic {
            Logic::Prim(op) => apply_op(bdd, *op, &ins, &g.pins)?,
            Logic::Func(func) => func_bdd(bdd, func, &g.pins, &ins),
        };
        if bdd.exhausted() {
            return Ok(None);
        }
        f.insert(g.out.as_str(), y);
    }
    nets.iter().map(|n| f.get(n.as_str()).copied().ok_or_else(|| format!("net `{n}` is not in the cone"))).collect::<Result<Vec<_>, _>>().map(Some)
}

/// The next-state BDD node of each of `members` in one fresh manager, a register's state read as
/// its class's variable (`class_of[model][state net]`); `None` once the manager is exhausted.
/// Members with the same node load the same value whenever every class holds one value.
fn next_nodes(models: &[&Model], members: &[RegId], class_of: &[HashMap<String, usize>]) -> Result<Option<Vec<u32>>, String> {
    let mut bdd = Bdd::with_limit(BDD_LIMIT);
    let mut names: HashMap<String, u32> = HashMap::new();
    let mut var = |bdd: &mut Bdd, name: &str| -> u32 {
        let n = names.len() as u32;
        let k = *names.entry(name.to_string()).or_insert(n);
        bdd.var(k)
    };
    let mut node = Vec::with_capacity(members.len());
    for &(m, k) in members {
        let co = &class_of[m];
        let cv = |s: &str| format!("class {}", co.get(s).copied().unwrap_or(usize::MAX));
        let net = next_net(&models[m].regs[k].instance);
        match next_state_bdds(models[m], &[net], &mut bdd, &mut var, &cv)? {
            Some(v) if !bdd.exhausted() => node.push(v[0]),
            _ => return Ok(None),
        }
    }
    Ok(Some(node))
}

/// Each register's class, by its state net, per model.
fn class_index(models: &[&Model], classes: &[Vec<RegId>]) -> Vec<HashMap<String, usize>> {
    let mut class_of: Vec<HashMap<String, usize>> = vec![HashMap::new(); models.len()];
    for (ci, cl) in classes.iter().enumerate() {
        for &(m, k) in cl {
            class_of[m].insert(state_net(&models[m].regs[k].instance), ci);
        }
    }
    class_of
}

/// Stage 4: split every class whose members load different next values when every class holds
/// one value, until nothing splits. Returns the rounds taken and the registers left undecided.
pub(crate) fn refine(models: &[&Model], classes: &mut Vec<Vec<RegId>>) -> Result<(usize, Vec<RegId>), String> {
    let mut undecided: Vec<RegId> = Vec::new();
    let mut rounds = 0;
    loop {
        rounds += 1;
        let class_of = class_index(models, classes);
        let mut next: Vec<Vec<RegId>> = Vec::with_capacity(classes.len());
        let mut split = false;
        for cl in classes.iter() {
            if cl.len() < 2 {
                next.push(cl.clone());
                continue;
            }
            let Some(node) = next_nodes(models, cl, &class_of)? else {
                undecided.extend(cl.iter().copied());
                next.extend(cl.iter().map(|&r| vec![r]));
                split = true;
                continue;
            };
            // members grouped by their next-state node, in order of first appearance
            let mut parts: Vec<(u32, Vec<RegId>)> = Vec::new();
            for (i, &r) in cl.iter().enumerate() {
                let n = node[i];
                match parts.iter_mut().find(|(x, _)| *x == n) {
                    Some((_, v)) => v.push(r),
                    None => parts.push((n, vec![r])),
                }
            }
            split |= parts.len() > 1;
            next.extend(parts.into_iter().map(|(_, v)| v));
        }
        *classes = next;
        if !split {
            return Ok((rounds, undecided));
        }
    }
}

/// Stage 5: the map from the final classes; `candidates` (stage 3) tells a register that never
/// had a counterpart from one whose counterpart was disproved.
pub(crate) fn report(models: &[&Model], candidates: &[Vec<RegId>], classes: &[Vec<RegId>], undecided: &[RegId], rounds: usize) -> MapReport {
    let name = |r: &RegId| models[r.0].regs[r.1].name.clone();
    let golden = |r: &&RegId| models[r.0].side == Side::Golden;
    let mut had_candidate: HashMap<RegId, bool> = HashMap::new();
    for cl in candidates {
        let both = cl.iter().any(|r| golden(&r)) && cl.iter().any(|r| !golden(&r));
        for &r in cl {
            had_candidate.insert(r, both);
        }
    }
    let mut rep = MapReport {
        golden_registers: models.iter().filter(|m| m.side == Side::Golden).map(|m| m.regs.len()).sum(),
        revised_registers: models.iter().filter(|m| m.side == Side::Revised).map(|m| m.regs.len()).sum(),
        rounds,
        ..MapReport::default()
    };
    for cl in classes {
        let (g, r): (Vec<&RegId>, Vec<&RegId>) = cl.iter().partition(golden);
        let (gn, rn): (Vec<String>, Vec<String>) = (g.iter().map(|x| name(x)).collect(), r.iter().map(|x| name(x)).collect());
        match (g.len(), r.len()) {
            (0, _) => {
                for x in r.iter().filter(|x| !undecided.contains(x)) {
                    rep.unmatched_revised.insert(name(x), had_candidate[x]);
                }
            }
            (_, 0) => {
                for x in g.iter().filter(|x| !undecided.contains(x)) {
                    rep.unmatched_golden.insert(name(x), had_candidate[x]);
                }
            }
            (1, 1) => {
                rep.mapped.insert(gn[0].clone(), rn[0].clone());
            }
            (1, _) => {
                rep.duplicated.insert(gn[0].clone(), rn);
            }
            _ => rep.ambiguous.push((gn, rn)),
        }
    }
    rep.undecided = undecided.iter().map(|r| models[r.0].regs[r.1].clone()).collect();
    for m in models {
        rep.unobserved.extend(m.unobserved.iter().cloned());
    }
    rep
}

/// How long two signatures agree: the cycles each run agrees from the start (summed over the 64
/// runs), then the bits that agree in all.
fn agreement(a: &[u64], b: &[u64]) -> (u32, u32) {
    let (mut alive, mut lead, mut same) = (!0u64, 0u32, 0u32);
    for (x, y) in a.iter().zip(b) {
        alive &= !(x ^ y);
        lead += alive.count_ones();
        same += (!(x ^ y)).count_ones();
    }
    (lead, same)
}

/// Stage 6: where the difference starts. One wrong register makes every register it reaches hold
/// a different value too, so all of them are unmatched; this names the wrong one.
///
/// 1. Pair the unmatched registers by simulation: a golden and a revised register that agree for
///    the most cycles from the all-zero state, run by run (then on the most bits) are each
///    other's best partner. A register downstream of the difference agrees with its counterpart
///    until the difference reaches it, so it pairs with it; mutual best pairs are taken, removed,
///    and the rest paired again until no pair is mutual and unique.
/// 2. Registers the simulation left unpaired are paired by what the pairing explains: the pair
///    that makes the most other pairs follow (step 3), one at a time, while it helps.
/// 3. Assume every class AND every such pair holds one value, and compare each pair's next-state
///    functions. A pair that still differs is a CAUSE: its own logic differs. A pair that is then
///    equal FOLLOWS: it differs only because it reads a register that differs. A pair that
///    differs but reads a register still unpaired is UNEXPLAINED, never a cause.
///
/// 🔑 Every follower differs only through a cause: were every pair equal under the assumption,
/// all would start at 0 and stay equal by induction, and the registers would have mapped.
/// ⛔ The pairing is a diagnosis, not a proof: none of these pairs enters the map.
///
/// Each rule is pinned by a unit test that states it (`the_register_where_*`, `agreement_*`,
/// `mutual_best_*`, `leftovers_*`, `a_pair_reading_*`) and by the corpus witness (a gcd netlist
/// with one register's D tied to its Q names exactly that register, 33 pairs following).
pub(crate) fn attribute(models: &[&Model], sigs: &[Vec<Vec<u64>>], classes: &[Vec<RegId>], rep: &mut MapReport) -> Result<(), String> {
    let only = |cl: &Vec<RegId>, side: Side| cl.iter().all(|r| models[r.0].side == side);
    let gold: Vec<RegId> = classes.iter().filter(|c| only(c, Side::Golden)).flatten().copied().collect();
    let rev: Vec<RegId> = classes.iter().filter(|c| only(c, Side::Revised)).flatten().copied().collect();
    if gold.is_empty() || rev.is_empty() {
        rep.unattributed = gold.len() + rev.len();
        return Ok(());
    }
    if gold.len().saturating_mul(rev.len()) > ATTRIBUTION_CAP {
        rep.attribution_skipped = true;
        rep.unattributed = gold.len() + rev.len();
        return Ok(());
    }
    let sig = |r: &RegId| &sigs[r.0][r.1];
    // per golden x revised: (cycles agreed from the start, summed over the 64 runs; bits agreed
    // in all). Per run, not per word: a word differs as soon as one run does, and a register
    // downstream of the difference is reached in different cycles in different runs.
    let score: Vec<Vec<(u32, u32)>> = gold
        .iter()
        .map(|g| rev.iter().map(|r| agreement(sig(g), sig(r))).collect())
        .collect();
    let mut pairs = mutual_best(&score);
    // 3. what the simulation left unpaired: pair by what the pairing explains
    let (gn, rn) = (gold.len(), rev.len());
    let left = |pairs: &[(usize, usize)]| (gn - pairs.len()) * (rn - pairs.len());
    if left(&pairs) * (pairs.len() + 1) <= LEFTOVER_CAP {
        pair_leftovers(gn, rn, &mut pairs, &mut |p: &[(usize, usize)]| follows(models, classes, &gold, &rev, p))?;
    }
    let (mut gfree, mut rfree) = (vec![true; gn], vec![true; rn]);
    for &(i, j) in &pairs {
        gfree[i] = false;
        rfree[j] = false;
    }
    // 4. each pair's verdict, every class and pair assumed equal
    let class_of = class_index(models, &assumed_classes(models, classes, &gold, &rev, &pairs));
    let unpaired: HashSet<String> = gold
        .iter()
        .zip(&gfree)
        .chain(rev.iter().zip(&rfree))
        .filter(|(_, f)| **f)
        .map(|(r, _)| state_net(&models[r.0].regs[r.1].instance))
        .collect();
    let name = |r: &RegId| models[r.0].regs[r.1].name.clone();
    for &(i, j) in &pairs {
        let pair = (name(&gold[i]), name(&rev[j]));
        match next_nodes(models, &[gold[i], rev[j]], &class_of)? {
            Some(n) if n[0] == n[1] => rep.follows.push(pair),
            // a pair that reads an unpaired register may differ only through it: not a cause
            _ if [gold[i], rev[j]].iter().any(|r| states_read(models[r.0], r.1).iter().any(|s| unpaired.contains(s))) => {
                rep.unexplained.push(pair)
            }
            // a pair whose BDDs outgrew the budget is not known to follow: listed as a cause
            _ => rep.causes.push(pair),
        }
    }
    rep.unattributed = gfree.iter().chain(&rfree).filter(|f| **f).count();
    Ok(())
}

/// Step 1 of [`attribute`]: golden `i` and revised `j` pair when each is the other's UNIQUE best
/// by `score[i][j]` among the registers still free; the pairs found are removed and the rest
/// matched again, until a round finds none. A tie pairs nothing.
fn mutual_best(score: &[Vec<(u32, u32)>]) -> Vec<(usize, usize)> {
    let (gn, rn) = (score.len(), score.first().map_or(0, Vec::len));
    let (mut gfree, mut rfree) = (vec![true; gn], vec![true; rn]);
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    // the unique best of `cands` by `key`, or none on a tie
    fn unique_best(cands: Vec<usize>, key: impl Fn(usize) -> (u32, u32)) -> Option<usize> {
        let mut c = cands;
        c.sort_by_key(|&x| std::cmp::Reverse(key(x)));
        match c.as_slice() {
            [a, b, ..] if key(*a) == key(*b) => None,
            [a, ..] => Some(*a),
            [] => None,
        }
    }
    loop {
        let mut found: Vec<(usize, usize)> = Vec::new();
        for i in (0..gn).filter(|&i| gfree[i]) {
            let Some(j) = unique_best((0..rn).filter(|&j| rfree[j]).collect(), |j| score[i][j]) else { continue };
            if unique_best((0..gn).filter(|&k| gfree[k]).collect(), |k| score[k][j]) == Some(i) {
                found.push((i, j));
            }
        }
        if found.is_empty() {
            return pairs;
        }
        for &(i, j) in &found {
            gfree[i] = false;
            rfree[j] = false;
        }
        pairs.extend(found);
    }
}

/// How many of a candidate set of pairs follow (see [`follows`]).
type FollowCount<'a> = dyn FnMut(&[(usize, usize)]) -> Result<usize, String> + 'a;

/// Step 2 of [`attribute`]: among the golden and revised registers no pair holds, add the pair
/// after which `follows` counts the most pairs following, one pair at a time, and only while that
/// count GROWS: a pair that explains nothing more is a guess, and is left unpaired.
fn pair_leftovers(
    gn: usize,
    rn: usize,
    pairs: &mut Vec<(usize, usize)>,
    follows: &mut FollowCount,
) -> Result<(), String> {
    let mut base = follows(pairs)?;
    loop {
        let (gfree, rfree): (Vec<usize>, Vec<usize>) = (
            (0..gn).filter(|i| !pairs.iter().any(|p| p.0 == *i)).collect(),
            (0..rn).filter(|j| !pairs.iter().any(|p| p.1 == *j)).collect(),
        );
        let mut best: Option<((usize, usize), usize)> = None;
        for &i in &gfree {
            for &j in &rfree {
                let mut trial = pairs.clone();
                trial.push((i, j));
                let n = follows(&trial)?;
                if n > base && best.is_none_or(|(_, b)| n > b) {
                    best = Some(((i, j), n));
                }
            }
        }
        let Some((p, n)) = best else { return Ok(()) };
        pairs.push(p);
        base = n;
    }
}

/// The classes that are not one-sided, every unmatched register alone, and each pair one class.
fn assumed_classes(models: &[&Model], classes: &[Vec<RegId>], gold: &[RegId], rev: &[RegId], pairs: &[(usize, usize)]) -> Vec<Vec<RegId>> {
    let paired: HashSet<RegId> = pairs.iter().flat_map(|&(i, j)| [gold[i], rev[j]]).collect();
    let mut out: Vec<Vec<RegId>> = Vec::new();
    for cl in classes {
        let sides: HashSet<Side> = cl.iter().map(|r| models[r.0].side).collect();
        if sides.len() == 2 {
            out.push(cl.clone());
        } else {
            out.extend(cl.iter().filter(|r| !paired.contains(r)).map(|&r| vec![r]));
        }
    }
    out.extend(pairs.iter().map(|&(i, j)| vec![gold[i], rev[j]]));
    out
}

/// How many of `pairs` load the same next value with every class and pair assumed equal.
fn follows(models: &[&Model], classes: &[Vec<RegId>], gold: &[RegId], rev: &[RegId], pairs: &[(usize, usize)]) -> Result<usize, String> {
    let class_of = class_index(models, &assumed_classes(models, classes, gold, rev, pairs));
    let mut n = 0;
    for &(i, j) in pairs {
        if matches!(next_nodes(models, &[gold[i], rev[j]], &class_of)?, Some(v) if v[0] == v[1]) {
            n += 1;
        }
    }
    Ok(n)
}

/// The state nets register `k`'s next-state logic reads (the registers it depends on in one cycle).
fn states_read(model: &Model, k: usize) -> HashSet<String> {
    let c = &model.cone;
    let mut out = HashSet::new();
    let mut seen = vec![false; c.gates.len()];
    let mut stack: Vec<usize> = model.gate.get(&next_net(&model.regs[k].instance)).copied().into_iter().collect();
    while let Some(g) = stack.pop() {
        if std::mem::replace(&mut seen[g], true) {
            continue;
        }
        for src in &c.gates[g].ins {
            if let Src::Net(n) = src {
                if model.state.contains(n) {
                    out.insert(n.clone());
                } else if let Some(&j) = model.gate.get(n) {
                    stack.push(j);
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lib() -> Lib {
        Lib::load(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/seq.lib")).expect("seq.lib")
    }
    fn nl(src: &str) -> Netlist {
        crate::netlist::parse(src).unwrap()
    }
    fn map(a: &Netlist, b: &Netlist) -> MapReport {
        register_map(a, b, &lib(), (Naming::Instance, Naming::Instance)).unwrap()
    }

    /// A 2-bit counter with a synchronous enable; `r0`/`r1` name the registers, `body` the rest.
    fn counter(r0: &str, r1: &str, q0: &str, q1: &str) -> Netlist {
        nl(&format!(
            "module t(clk,en,y);\ninput clk,en; output y;\nwire d0,d1,{q0},{q1},c;\n\
             XOR2 x0(.A(en),.B({q0}),.Y(d0));\nDFF {r0}(.CK(clk),.D(d0),.Q({q0}));\n\
             AND2 a(.A(en),.B({q0}),.Y(c));\nXOR2 x1(.A(c),.B({q1}),.Y(d1));\nDFF {r1}(.CK(clk),.D(d1),.Q({q1}));\n\
             AND2 o(.A({q0}),.B({q1}),.Y(y));\nendmodule\n"
        ))
    }

    /// Two registers renamed (instances AND their nets) map to each other, by proof: the names
    /// share nothing.
    #[test]
    fn renamed_registers_map_by_proof() {
        let rep = map(&counter("cnt_reg0", "cnt_reg1", "q0", "q1"), &counter("u7", "u3", "n12", "n9"));
        assert!(rep.one_to_one(), "{rep:?}");
        assert_eq!(rep.mapped.get("cnt_reg0").map(String::as_str), Some("u7"));
        assert_eq!(rep.mapped.get("cnt_reg1").map(String::as_str), Some("u3"));
    }

    /// With `Naming::Net` a register is named by the net on its stored-value output (what a
    /// netlist that keeps RTL names on nets only calls the register).
    #[test]
    fn a_register_can_be_named_by_its_output_net() {
        let a = counter("u1", "u2", "count[0]", "count[1]");
        let b = counter("count_reg_0_", "count_reg_1_", "n1", "n2");
        let rep = register_map(&a, &b, &lib(), (Naming::Net, Naming::Instance)).unwrap();
        assert_eq!(rep.mapped.get("count[0]").map(String::as_str), Some("count_reg_0_"));
        assert_eq!(rep.mapped.get("count[1]").map(String::as_str), Some("count_reg_1_"));
    }

    /// An enable register (`next_state` reads its own state) against a plain register behind a
    /// hold mux: the same state, so mapped, though the cells differ.
    #[test]
    fn an_enable_register_maps_to_a_register_behind_a_hold_mux() {
        let edf = nl("module t(clk,de,d,q);\ninput clk,de,d; output q;\nEDF r(.CK(clk),.D(d),.DE(de),.Q(q));\nendmodule\n");
        let mux = nl("module t(clk,de,d,q);\ninput clk,de,d; output q;\nwire n, s;\n\
             MUX2 m(.A0(s),.A1(d),.S(de),.Y(n));\nDFF u(.CK(clk),.D(n),.Q(s));\nBUF b(.A(s),.Y(q));\nendmodule\n");
        let rep = map(&edf, &mux);
        assert_eq!(rep.mapped.get("r").map(String::as_str), Some("u"), "{rep:?}");
    }

    /// One wrong gate in the revised netlist: the register it feeds is unmatched (its candidate
    /// disproved or never proposed), and every other register still maps. Here the high bit's
    /// carry reads `!en`: bit 1 differs, bit 0 does not.
    #[test]
    fn one_wrong_gate_leaves_only_its_register_unmapped() {
        let good = counter("r0", "r1", "q0", "q1");
        let bad = nl("module t(clk,en,y);\ninput clk,en; output y;\nwire d0,d1,q0,q1,c,ne;\n\
             XOR2 x0(.A(en),.B(q0),.Y(d0));\nDFF r0(.CK(clk),.D(d0),.Q(q0));\n\
             INV i(.A(en),.Y(ne));\nAND2 a(.A(ne),.B(q0),.Y(c));\nXOR2 x1(.A(c),.B(q1),.Y(d1));\nDFF r1(.CK(clk),.D(d1),.Q(q1));\n\
             AND2 o(.A(q0),.B(q1),.Y(y));\nendmodule\n");
        let rep = map(&good, &bad);
        assert_eq!(rep.mapped.len(), 1, "{rep:?}");
        assert_eq!(rep.mapped.get("r0").map(String::as_str), Some("r0"));
        assert!(rep.unmatched_golden.contains_key("r1") && rep.unmatched_revised.contains_key("r1"), "{rep:?}");
        assert!(!rep.one_to_one());
        assert_eq!(rep.causes, [("r1".to_string(), "r1".to_string())], "{rep:?}");
        assert!(rep.follows.is_empty(), "{rep:?}");
    }

    /// 🔑 The proof, not the simulation, decides. Two registers that agree on every simulated
    /// cycle but not in every reachable state: a 6-bit counter's top bit against a register that
    /// stays 0, compared over fewer cycles than the counter takes to reach 32. Simulation proposes
    /// the pair (both 0 throughout); the induction splits it.
    #[test]
    fn a_pair_simulation_cannot_tell_apart_is_split_by_the_proof() {
        // a counter that counts every cycle: bit 5 first rises in cycle 32, past the simulation
        let mut body = String::new();
        let mut wires = vec!["c0".to_string()];
        body.push_str("BUF b0(.A(one),.Y(c0));\n");
        for i in 0..6 {
            wires.extend([format!("q{i}"), format!("d{i}"), format!("c{}", i + 1)]);
            body.push_str(&format!(
                "XOR2 x{i}(.A(c{i}),.B(q{i}),.Y(d{i}));\nDFF r{i}(.CK(clk),.D(d{i}),.Q(q{i}));\nAND2 a{i}(.A(c{i}),.B(q{i}),.Y(c{}));\n",
                i + 1
            ));
        }
        let top = |extra: &str| {
            nl(&format!(
                "module t(clk,one,y);\ninput clk,one; output y;\nwire {};\n{body}{extra}endmodule\n",
                wires.join(",")
            ))
        };
        let a = top("BUF o(.A(q5),.Y(y));\n");
        // the revised design: the same counter, and its output from a register that holds 0
        let b = top("wire z, zd;\nAND2 h(.A(z),.B(one),.Y(zd));\nDFF hold(.CK(clk),.D(zd),.Q(z));\nBUF o(.A(z),.Y(y));\n");
        let rep = map(&a, &b);
        // r5 must not map to `hold`; r0..r5 map to themselves
        assert_ne!(rep.mapped.get("r5").map(String::as_str), Some("hold"), "{rep:?}");
        assert!(rep.unmatched_revised.contains_key("hold"), "{rep:?}");
        for i in 0..6 {
            assert_eq!(rep.mapped.get(&format!("r{i}")).map(String::as_str), Some(format!("r{i}").as_str()), "{rep:?}");
        }
    }

    /// 🔑 One wrong register takes the registers it reaches with it, but is named as the one
    /// cause. A four-stage shift register whose first stage loads `a & b` instead of `a`: every
    /// stage is unmatched (each holds a different value in some state), and only the first
    /// stage's logic differs once what each stage reads is assumed equal.
    #[test]
    fn the_register_where_the_difference_starts_is_named() {
        let shift = |first: &str| {
            nl(&format!(
                "module t(clk,a,b,y);\ninput clk,a,b; output y;\nwire d0,q0,q1,q2;\n{first}\n\
                 DFF s0(.CK(clk),.D(d0),.Q(q0));\nDFF s1(.CK(clk),.D(q0),.Q(q1));\n\
                 DFF s2(.CK(clk),.D(q1),.Q(q2));\nDFF s3(.CK(clk),.D(q2),.Q(y));\nendmodule\n"
            ))
        };
        let rep = map(&shift("BUF g(.A(a),.Y(d0));"), &shift("AND2 g(.A(a),.B(b),.Y(d0));"));
        assert!(rep.mapped.is_empty(), "{rep:?}");
        let s = |a: &str| (a.to_string(), a.to_string());
        assert_eq!(rep.causes, [s("s0")], "{rep:?}");
        let mut f = rep.follows.clone();
        f.sort();
        assert_eq!(f, [s("s1"), s("s2"), s("s3")], "{rep:?}");
        assert!(rep.unexplained.is_empty() && rep.unattributed == 0, "{rep:?}");
    }

    /// The score counts, run by run, the cycles two registers agree FROM THE START, before the
    /// bits they agree on overall: a register downstream of a difference agrees with its
    /// counterpart until the difference reaches it, and may agree less often afterwards than an
    /// unrelated register does. Here `near` agrees for 3 cycles in every run, then never; `far`
    /// differs from cycle 1 but agrees on more bits; `near` must score higher.
    #[test]
    fn agreement_counts_the_lead_before_the_bits() {
        let g = [0u64, 0, 0, !0, !0, !0, !0, !0];
        let near = [0u64, 0, 0, 0, 0, 0, 0, 0];
        let far = [0u64, !0, 0, !0, !0, !0, !0, !0];
        assert_eq!(agreement(&g, &near), (3 * 64, 3 * 64));
        assert_eq!(agreement(&g, &far), (64, 7 * 64));
        assert!(agreement(&g, &near) > agreement(&g, &far));
    }

    /// Mutual unique best, REPEATED: golden 1's best is revised 0, which golden 0 wins in the
    /// first round; only once that pair is removed is revised 1 golden 1's unique best.
    #[test]
    fn mutual_best_is_repeated_on_what_is_left() {
        let score = vec![vec![(10, 0), (1, 0)], vec![(9, 0), (5, 0)]];
        assert_eq!(mutual_best(&score), [(0, 0), (1, 1)]);
        // and a tie pairs nothing
        assert!(mutual_best(&[vec![(4, 0), (4, 0)]]).is_empty());
    }

    /// A leftover pair is taken only when it makes MORE pairs follow. Two leftover registers per
    /// side: pairing (1, 0) makes one more pair follow and is taken; after it no pairing helps,
    /// so golden 0 and revised 1 stay unpaired rather than paired by default.
    #[test]
    fn leftovers_are_paired_only_while_it_explains_more() {
        let mut pairs: Vec<(usize, usize)> = Vec::new();
        let mut follows = |p: &[(usize, usize)]| -> Result<usize, String> { Ok(usize::from(p.contains(&(1, 0)))) };
        pair_leftovers(2, 2, &mut pairs, &mut follows).unwrap();
        assert_eq!(pairs, [(1, 0)]);
    }

    /// A pair that differs but reads a register left unpaired may differ only through it, so it
    /// is UNEXPLAINED, never a cause. The golden design XORs a second shift stage with a register
    /// the revised design lacks (`u`, rarely 1): stage 1 differs, but because it reads `u`.
    #[test]
    fn a_pair_reading_an_unpaired_register_is_unexplained() {
        let g = nl("module t(clk,a,b,c,y);\ninput clk,a,b,c; output y;\nwire q0,u,d1,ab,abc;\n\
             DFF s0(.CK(clk),.D(a),.Q(q0));\nAND2 x(.A(a),.B(b),.Y(ab));\nAND2 z(.A(ab),.B(c),.Y(abc));\n\
             DFF u0(.CK(clk),.D(abc),.Q(u));\nXOR2 m(.A(q0),.B(u),.Y(d1));\nDFF s1(.CK(clk),.D(d1),.Q(y));\nendmodule\n");
        let r = nl("module t(clk,a,b,c,y);\ninput clk,a,b,c; output y;\nwire q0;\n\
             DFF s0(.CK(clk),.D(a),.Q(q0));\nDFF s1(.CK(clk),.D(q0),.Q(y));\nendmodule\n");
        let rep = map(&g, &r);
        assert_eq!(rep.mapped.get("s0").map(String::as_str), Some("s0"), "{rep:?}");
        assert_eq!(rep.unexplained, [("s1".to_string(), "s1".to_string())], "{rep:?}");
        assert!(rep.causes.is_empty(), "{rep:?}");
        assert_eq!(rep.unattributed, 1, "{rep:?}");
    }

    /// A register only the revised design has leaves the map short of one-to-one, even with every
    /// golden register mapped.
    #[test]
    fn an_extra_revised_register_is_not_one_to_one() {
        let a = counter("r0", "r1", "q0", "q1");
        let b = nl("module t(clk,en,y,z);\ninput clk,en; output y,z;\nwire d0,d1,q0,q1,c,ne;\n\
             XOR2 x0(.A(en),.B(q0),.Y(d0));\nDFF r0(.CK(clk),.D(d0),.Q(q0));\n\
             AND2 a(.A(en),.B(q0),.Y(c));\nXOR2 x1(.A(c),.B(q1),.Y(d1));\nDFF r1(.CK(clk),.D(d1),.Q(q1));\n\
             AND2 o(.A(q0),.B(q1),.Y(y));\nINV i(.A(en),.Y(ne));\nDFF extra(.CK(clk),.D(ne),.Q(z));\nendmodule\n");
        let rep = map(&a, &b);
        assert_eq!(rep.mapped.len(), 2, "{rep:?}");
        assert_eq!(rep.unmatched_revised.get("extra"), Some(&false), "{rep:?}");
        assert!(!rep.one_to_one());
    }

    /// A register the revised design duplicated is listed with both copies, not mapped to one.
    #[test]
    fn a_duplicated_register_is_listed_not_guessed() {
        let one = nl("module t(clk,en,y);\ninput clk,en; output y;\nwire d;\n\
             XOR2 x(.A(en),.B(y),.Y(d));\nDFF r(.CK(clk),.D(d),.Q(y));\nendmodule\n");
        let dup = nl("module t(clk,en,y);\ninput clk,en; output y;\nwire d1,d2,q1,q2;\n\
             XOR2 x1(.A(en),.B(q1),.Y(d1));\nDFF r1(.CK(clk),.D(d1),.Q(q1));\n\
             XOR2 x2(.A(en),.B(q2),.Y(d2));\nDFF r2(.CK(clk),.D(d2),.Q(q2));\n\
             AND2 a(.A(q1),.B(q2),.Y(y));\nendmodule\n");
        let rep = map(&one, &dup);
        assert!(rep.mapped.is_empty(), "{rep:?}");
        assert_eq!(rep.duplicated.get("r"), Some(&vec!["r1".to_string(), "r2".to_string()]));
    }

    /// The same inputs reach both designs: an input word depends on the name and the cycle only.
    #[test]
    fn input_words_depend_on_name_and_cycle_only() {
        assert_eq!(input_word("en", 3), input_word("en", 3));
        assert_ne!(input_word("en", 3), input_word("en", 4));
        assert_ne!(input_word("en", 3), input_word("rst", 3));
    }
}
