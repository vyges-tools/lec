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
//! 2. [`simulate`]: both designs from the all-zero state on the SAME inputs (each primary input
//!    by name: random, except the asynchronous-reset inputs, held active and then inactive,
//!    [`Stimulus`]), 64 runs at once for [`CYCLES`] cycles; a clock-gate enable that never
//!    asserts is then driven at random and the simulation rerun
//!    ([`simulate_freeing_stuck_enables`]). A register's signature is its state in every run and
//!    cycle.
//! 3. [`candidate_classes`]: registers with one signature form a class, whichever design they
//!    are in. Two registers that ever differed in simulation are never assumed equal.
//! 4. [`refine`]: assume every class holds one value (one BDD variable per class) and build each
//!    member's next-state function over the primary inputs and the class variables. Members whose
//!    functions differ are split. Repeat until nothing splits.
//! 5. [`report`]: a class left with exactly one register of each design is a MAPPED pair (an
//!    INVERTED pair when one stores the other's complement).
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
//! - a register stored inverted is NOT left out: it shares a class with the complement of its
//!   value (`inverted`, [`candidate_classes`]) and is proved like any member, read and compared
//!   complemented. ⚠️ Such a pair does not hold at the all-zero start (both are 0 there); it
//!   holds in every state reached from one where every class holds, i.e. after a reset that
//!   clears one and presets the other, and so does every pair whose proof reads it;
//! - a LATCH or a MEMORY macro (`cut`; any state that is not one `ff` group): not a register of
//!   the map. It is cut as `check` cuts it, its outputs free inputs named by instance
//!   ([`Design::register_model`]), so the map holds under `check`'s own assumption that two such
//!   cells of one name hold one value;
//! - a register whose next-state BDD outgrew a fresh manager of [`BDD_LIMIT`] alone, or whose
//!   class's canonical keys passed [`CANON_LIMIT`] (`undecided`): it stands alone, which only
//!   weakens what the others may assume, so the rest stays sound. A class too big for ONE
//!   manager is built in chunks ([`chunked_keys`]) and still refined exactly.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::bdd::Bdd;
use crate::lec::{apply_op, func_bdd, gate_of, next_net, outside_edge_model, seq_cone, state_net, Cone, Design, Logic, Op, Src};
use crate::liberty::{Dir, Lib};
use crate::netlist::Netlist;
use vyges_loom::liberty_func::Func;

/// Simulated clock cycles; each cycle runs 64 input sequences at once (one per bit).
pub const CYCLES: usize = 128;

/// The first cycles of the simulation hold every asynchronous-reset input ACTIVE; after them
/// it is held inactive ([`Stimulus`]).
pub const RESET_CYCLES: usize = 2;

/// The input name whose random words drive every clock-gate enable in [`simulate`] (a name no
/// netlist input can have).
pub(crate) const FREE_ENABLE: &str = "<clock-gate enable>";

/// Nodes (plus memo entries) one BDD manager may take; a class that outgrows it continues in a
/// fresh manager ([`chunked_keys`]).
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
    /// Golden name -> revised name, each pair proved to hold COMPLEMENTED values: the revised
    /// register stores the negation (its clear acts where the golden's preset does, and the other
    /// way round). Not in `mapped`, so a consumer that takes `mapped` as same-value pairs is
    /// never handed one.
    pub inverted: BTreeMap<String, String>,
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
    /// Latches and memories cut as `check` cuts them (an output is a free input shared by instance
    /// name), not mapped: the map holds under the assumption that same-named cells hold one value.
    pub cut: Vec<RegName>,
    /// The asynchronous-reset inputs the simulation held, each with its inactive value
    /// ([`Stimulus`]).
    pub reset_inputs: Vec<(String, bool)>,
    /// Clock gates whose enable the simulation drove at random ([`simulate`]), by instance.
    pub free_enables: Vec<String>,
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
        let n = self.mapped.len() + self.inverted.len();
        n == self.golden_registers
            && n == self.revised_registers
            && self.unobserved.is_empty()
    }
}

/// The register map of `golden` to `revised`: the thin sequence of the stages the module doc
/// names, in its order.
pub fn register_map(golden: &Netlist, revised: &Netlist, lib: &Lib, names: (Naming, Naming)) -> Result<MapReport, String> {
    if lib.cells.is_empty() {
        return Err("no cells in the Liberty".into());
    }
    let (g, r) = (Design::register_model(golden, lib), Design::register_model(revised, lib));
    let (gm, rm) = (model(&g, Side::Golden, names.0)?, model(&r, Side::Revised, names.1)?);
    let stim = Stimulus::of(&[&g, &r]);
    let (sigs, freed) = simulate_freeing_stuck_enables(&[&gm, &rm], &stim)?;
    let (mut classes, inv) = candidate_classes(&[&gm, &rm], &sigs);
    let candidates = classes.clone();
    let (rounds, undecided) = refine(&[&gm, &rm], &mut classes, &inv)?;
    let mut rep = report(&[&gm, &rm], &candidates, &classes, &inv, &undecided, rounds);
    attribute(&[&gm, &rm], &sigs, &classes, &inv, &mut rep)?;
    rep.reset_inputs = stim.held.into_iter().collect();
    rep.free_enables = freed.iter().flatten().filter_map(|n| gate_of(n).map(str::to_string)).collect::<BTreeSet<_>>().into_iter().collect();
    Ok(rep)
}

/// One design in the sequential model: its cone, the registers in it, and where each gate is.
pub(crate) struct Model {
    side: Side,
    cone: Cone,
    /// Registers in cone order (`cone.regs`), each with its map name.
    regs: Vec<RegName>,
    /// Gate index by the net it drives.
    gate: FxHashMap<String, usize>,
    /// Every register's state net ([`state_net`]).
    state: FxHashSet<String>,
    unobserved: Vec<RegName>,
    /// Latches and memories the model cut ([`Design::register_model`]), in netlist order.
    cut: Vec<RegName>,
}

/// Stage 1: the cone of every register's outputs, with each register's next-state gate.
pub(crate) fn model(d: &Design, side: Side, naming: Naming) -> Result<Model, String> {
    let (nl, lib) = (d.netlist(), d.liberty());
    let mut endpoints = Vec::new();
    let mut name_of: HashMap<&str, String> = HashMap::new();
    let mut unobserved = Vec::new();
    let mut cut = Vec::new();
    for inst in &nl.insts {
        let Some(cell) = lib.cells.get(&inst.cell).filter(|c| c.is_seq) else { continue };
        if outside_edge_model(cell) {
            cut.push(RegName { side, instance: inst.name.clone(), name: inst.name.clone() });
            continue;
        }
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
    Ok(Model { side, cone, regs, gate, state, unobserved, cut })
}

/// A register across both models: (model index, register index).
type RegId = (usize, usize);

/// What the simulation drives, the same in every design: each input a random word per cycle,
/// except the asynchronous-reset inputs (`held`, input -> its inactive value), which are ACTIVE
/// for [`RESET_CYCLES`] and inactive after.
///
/// 🔑 Why: driven at random, a reset input asserts in about half the cycles, and a core behind
/// a reset synchronizer stays in reset: CoralNPU's registers kept the all-zero signature in 32
/// cycles, 119,516 of them in one candidate class that no BDD budget held. The stimulus only
/// proposes candidates; every pair is still proved by `refine`, so it cannot make the map wrong.
#[derive(Debug, Clone, Default)]
pub(crate) struct Stimulus {
    pub held: BTreeMap<String, bool>,
}

impl Stimulus {
    /// The inputs both designs agree are asynchronous-reset inputs with one inactive value
    /// ([`Design::reset_inputs`]); one detected in a single design is held too, as the stimulus
    /// must be the same in both; two designs disagreeing on the inactive value hold neither.
    pub(crate) fn of(designs: &[&Design]) -> Stimulus {
        let mut held: BTreeMap<String, bool> = BTreeMap::new();
        let mut clash = Vec::new();
        for d in designs {
            for (k, v) in d.reset_inputs() {
                match held.get(&k) {
                    Some(&w) if w != v => clash.push(k),
                    _ => {
                        held.insert(k, v);
                    }
                }
            }
        }
        for k in clash {
            held.remove(&k);
        }
        Stimulus { held }
    }

    /// Input `name`'s word in `cycle`.
    pub(crate) fn word(&self, name: &str, cycle: usize) -> u64 {
        match self.held.get(name) {
            Some(&inactive) => {
                let v = if cycle < RESET_CYCLES { !inactive } else { inactive };
                if v { !0 } else { 0 }
            }
            None => input_word(name, cycle),
        }
    }
}

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
/// The signatures (`sigs[model][register]`, one word per cycle) and, per model, the clock-gate
/// enable nets that never asserted (or were freed).
pub(crate) type Simulated = (Vec<Vec<Vec<u64>>>, Vec<BTreeSet<String>>);

/// Stage 2 as run: [`simulate`] with every clock-gate enable computed; then, if some gate's
/// enable never asserted after reset (in any run, any cycle), again with exactly those enables
/// FREE. Returns the signatures and, per model, the enable nets freed.
///
/// 🔑 A core whose clock gate is enabled only by a register sequence random inputs never produce
/// (CoralNPU: an enable written over AXI) never leaves reset behind that gate: 119,482 registers
/// shared one all-zero class. Driving that enable at random (one stream for every freed gate,
/// [`FREE_ENABLE`], so two designs see the same enables whatever their gates are called) moves
/// them. Only an enable that NEVER asserts is freed: one that does is left computed, so a gated
/// register still meets its plain enable-mux equivalent in the other design. Only the
/// candidates change: `refine` builds the REAL enable ([`next_state_bdds`]), so a pair that
/// differs under it is still split.
pub(crate) fn simulate_freeing_stuck_enables(models: &[&Model], stim: &Stimulus) -> Result<Simulated, String> {
    let none: Vec<BTreeSet<String>> = vec![BTreeSet::new(); models.len()];
    let (sigs, stuck) = simulate(models, stim, &none)?;
    if stuck.iter().all(BTreeSet::is_empty) {
        return Ok((sigs, stuck));
    }
    let (sigs, _) = simulate(models, stim, &stuck)?;
    Ok((sigs, stuck))
}

/// Stage 2: each register's state in 64 runs over [`CYCLES`] cycles from the all-zero state,
/// every design on the same inputs, the enable nets in `free[m]` driven at random. Returns
/// `sigs[m][k]` (model `m`'s register `k`) and, per model, the clock-gate enable nets that
/// never asserted after [`RESET_CYCLES`].
pub(crate) fn simulate(models: &[&Model], stim: &Stimulus, free: &[BTreeSet<String>]) -> Result<Simulated, String> {
    let mut out = Vec::new();
    let mut stuck_all = Vec::new();
    for (mi, m) in models.iter().enumerate() {
        let mut asserted: BTreeSet<&str> = BTreeSet::new();
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
                val.insert(net.as_str(), stim.word(var, cycle));
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
                // a freed clock-gate enable ([`simulate_freeing_stuck_enables`]): the shared random stream
                let y = if free[mi].contains(&g.out) {
                    stim.word(FREE_ENABLE, cycle)
                } else {
                    match &g.logic {
                        Logic::Prim(op) => prim_word(*op, &g.pins, &x)?,
                        Logic::Func(f) => func_word(f, &g.pins, &x),
                    }
                };
                if y != 0 && cycle >= RESET_CYCLES && gate_of(&g.out).is_some() {
                    asserted.insert(g.out.as_str());
                }
                val.insert(g.out.as_str(), y);
            }
            for (k, r) in c.regs.iter().enumerate() {
                state[k] = val.get(nexts[k].as_str()).copied().ok_or_else(|| format!("register `{r}` has no next-state gate"))?;
            }
        }
        out.push(sig);
        stuck_all.push(c.gates.iter().filter(|g| gate_of(&g.out).is_some() && !asserted.contains(g.out.as_str())).map(|g| g.out.clone()).collect());
    }
    Ok((out, stuck_all))
}

/// Each register's polarity in its class, per model: `true` when the register holds the
/// COMPLEMENT of its class's value.
pub(crate) type Polarity = Vec<Vec<bool>>;

/// Stage 3: the registers of all models grouped by signature UP TO COMPLEMENT, each class in
/// (model, register) order, the classes in order of their first member; with each register's
/// polarity in its class.
///
/// 🔑 A signature is compared from cycle 1: cycle 0 is the all-zero start, the same in every
/// register, so leaving it out separates nothing that it separated. A signature whose first bit
/// (cycle 1, run 0) is 1 is complemented and its register marked inverted, so a register and one
/// that stores its negation (a golden register cleared where the revised one is preset) share a
/// class; two registers with the same signature always get the same polarity.
pub(crate) fn candidate_classes(models: &[&Model], sigs: &[Vec<Vec<u64>>]) -> (Vec<Vec<RegId>>, Polarity) {
    let mut by_sig: HashMap<Vec<u64>, usize> = HashMap::new();
    let mut classes: Vec<Vec<RegId>> = Vec::new();
    let mut inv: Polarity = models.iter().map(|m| vec![false; m.regs.len()]).collect();
    for (m, model) in models.iter().enumerate() {
        for (k, sig) in sigs[m].iter().enumerate().take(model.regs.len()) {
            let tail = sig.get(1..).unwrap_or(&[]);
            let flip = tail.first().is_some_and(|w| w & 1 == 1);
            let key: Vec<u64> = if flip { tail.iter().map(|w| !w).collect() } else { tail.to_vec() };
            inv[m][k] = flip;
            let c = *by_sig.entry(key).or_insert_with(|| {
                classes.push(Vec::new());
                classes.len() - 1
            });
            classes[c].push((m, k));
        }
    }
    (classes, inv)
}

/// The BDD of each of `nets` in one model, in `bdd`, a free input by its variable name and a
/// register's state by its class: `var(name)` gives the variable. `None` once the manager is
/// exhausted.
fn next_state_bdds(
    model: &Model,
    nets: &[String],
    bdd: &mut Bdd,
    var: &mut dyn FnMut(&mut Bdd, &str) -> u32,
    class_var: &dyn Fn(&str) -> (String, bool),
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
    let mut f: FxHashMap<&str, u32> = FxHashMap::default();
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
                        // a register inverted in its class reads as the class value's complement
                        let (name, neg) = if model.state.contains(n.as_str()) {
                            class_var(n)
                        } else if let Some(v) = c.free.get(n) {
                            (v.clone(), false)
                        } else {
                            return Err(format!("cone gate `{}` reads `{n}` before it is computed (gate {k})", g.out));
                        };
                        let x = var(bdd, &name);
                        let x = if neg { bdd.not(x) } else { x };
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


/// What a class member's next-state function is compared by: its node, while the whole class
/// fits one manager; its [`Bdd::canonical`] list once the class needed several.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Key {
    Node(u32),
    Canon(Vec<u32>),
}

/// The `u32` entries of canonical lists one class may keep (1 GiB) before its remaining members
/// are reported undecided: with one manager of [`BDD_LIMIT`] alive at a time, this bounds a
/// class's memory well under the box budget whatever its size.
pub const CANON_LIMIT: usize = 1 << 28;

/// Builds member `i` of a class into the given manager, numbering variables through the given
/// name map; `None` when the manager is exhausted.
pub(crate) type BuildMember<'a> = dyn FnMut(usize, &mut Bdd, &mut dyn FnMut(&mut Bdd, &str) -> u32) -> Result<Option<u32>, String> + 'a;

/// [`next_keys`] over any member builder, so the chunk rule is testable on its own.
///
/// 🔑 The chunk rule: members are built in order into one manager of `limit`; when a member
/// overflows it, the members already built are listed canonically, a fresh manager is started
/// and the member is built again there. A member that overflows a fresh manager ALONE is
/// undecided (`None`). Every manager numbers variables through ONE map of names shared by all
/// chunks, so a canonical list means the same function in every chunk; a class that never
/// overflowed keeps plain nodes. Returns the keys and the number of managers used.
pub(crate) fn chunked_keys(
    n: usize,
    limit: usize,
    build: &mut BuildMember<'_>,
) -> Result<(Vec<Option<Key>>, usize), String> {
    let mut names: FxHashMap<String, u32> = FxHashMap::default();
    let mut keys: Vec<Option<Key>> = vec![None; n];
    let mut bdd = Bdd::with_limit(limit);
    let (mut managers, mut kept) = (1, 0usize);
    let mut chunk: Vec<(usize, u32)> = Vec::new();
    let flush = |bdd: &Bdd, chunk: &mut Vec<(usize, u32)>, keys: &mut Vec<Option<Key>>, kept: &mut usize| {
        for (i, node) in chunk.drain(..) {
            if *kept > CANON_LIMIT {
                continue;
            }
            let c = bdd.canonical(node);
            *kept += c.len();
            keys[i] = Some(Key::Canon(c));
        }
    };
    let mut i = 0;
    while i < n {
        let got = {
            let mut var = |bdd: &mut Bdd, name: &str| -> u32 {
                let next = names.len() as u32;
                let k = *names.entry(name.to_string()).or_insert(next);
                bdd.var(k)
            };
            build(i, &mut bdd, &mut var)?
        };
        match got {
            Some(node) if !bdd.exhausted() => {
                chunk.push((i, node));
                i += 1;
            }
            _ => {
                if chunk.is_empty() {
                    i += 1; // alone in a fresh manager: undecided
                } else {
                    flush(&bdd, &mut chunk, &mut keys, &mut kept);
                }
                bdd = Bdd::with_limit(limit);
                managers += 1;
            }
        }
    }
    if managers == 1 {
        for (i, node) in chunk {
            keys[i] = Some(Key::Node(node));
        }
    } else {
        flush(&bdd, &mut chunk, &mut keys, &mut kept);
    }
    Ok((keys, managers))
}

/// The next-state key of each of `members` ([`chunked_keys`]), a register's state read as its
/// class's variable (`class_of[model][state net]`); `None` for a member undecided within the
/// budget. Members with the same key load the same value whenever every class holds one value.
fn next_keys(models: &[&Model], members: &[RegId], class_of: &[ClassOf], limit: usize) -> Result<Vec<Option<Key>>, String> {
    let mut build = |i: usize, bdd: &mut Bdd, var: &mut dyn FnMut(&mut Bdd, &str) -> u32| -> Result<Option<u32>, String> {
        let (m, k) = members[i];
        let co = &class_of[m];
        let cv = |s: &str| {
            let (c, neg) = co.get(s).copied().unwrap_or((usize::MAX, false));
            (format!("class {c}"), neg)
        };
        let net = next_net(&models[m].regs[k].instance);
        let neg = co.get(&state_net(&models[m].regs[k].instance)).is_some_and(|x| x.1);
        // an inverted member's next value is compared complemented, as the class's value
        Ok(next_state_bdds(models[m], &[net], bdd, var, &cv)?.map(|v| if neg { bdd.not(v[0]) } else { v[0] }))
    };
    Ok(chunked_keys(members.len(), limit, &mut build)?.0)
}

/// `a` and `b` load the same next value with every class holding one value: proved, not
/// undecided within the budget.
fn same_next(models: &[&Model], a: RegId, b: RegId, class_of: &[ClassOf]) -> Result<bool, String> {
    let k = next_keys(models, &[a, b], class_of, BDD_LIMIT)?;
    Ok(matches!((&k[0], &k[1]), (Some(x), Some(y)) if x == y))
}

/// Each register's class, by its state net, per model.
/// A register's class and its polarity in it, by its state net.
type ClassOf = FxHashMap<String, (usize, bool)>;

fn class_index(models: &[&Model], classes: &[Vec<RegId>], inv: &dyn Fn(RegId) -> bool) -> Vec<ClassOf> {
    let mut class_of: Vec<ClassOf> = vec![FxHashMap::default(); models.len()];
    for (ci, cl) in classes.iter().enumerate() {
        for &(m, k) in cl {
            class_of[m].insert(state_net(&models[m].regs[k].instance), (ci, inv((m, k))));
        }
    }
    class_of
}

/// Stage 4: split every class whose members load different next values when every class holds
/// one value, until nothing splits. Returns the rounds taken and the registers left undecided.
pub(crate) fn refine(models: &[&Model], classes: &mut Vec<Vec<RegId>>, inv: &Polarity) -> Result<(usize, Vec<RegId>), String> {
    refine_within(models, classes, inv, BDD_LIMIT)
}

/// [`refine`] with each manager limited to `limit` nodes plus memo entries.
pub(crate) fn refine_within(models: &[&Model], classes: &mut Vec<Vec<RegId>>, inv: &Polarity, limit: usize) -> Result<(usize, Vec<RegId>), String> {
    let mut undecided: Vec<RegId> = Vec::new();
    let mut rounds = 0;
    loop {
        rounds += 1;
        let class_of = class_index(models, classes, &|r: RegId| inv[r.0][r.1]);
        let mut next: Vec<Vec<RegId>> = Vec::with_capacity(classes.len());
        let mut split = false;
        for cl in classes.iter() {
            if cl.len() < 2 {
                next.push(cl.clone());
                continue;
            }
            let keys = next_keys(models, cl, &class_of, limit)?;
            // members grouped by their next-state key, in order of first appearance; a member
            // undecided within the budget stands alone
            let mut parts: Vec<Vec<RegId>> = Vec::new();
            let mut at: HashMap<&Key, usize> = HashMap::new();
            for (i, &r) in cl.iter().enumerate() {
                match &keys[i] {
                    Some(key) => match at.get(key) {
                        Some(&p) => parts[p].push(r),
                        None => {
                            at.insert(key, parts.len());
                            parts.push(vec![r]);
                        }
                    },
                    None => {
                        undecided.push(r);
                        parts.push(vec![r]);
                    }
                }
            }
            split |= parts.len() > 1;
            next.extend(parts);
        }
        *classes = next;
        if !split {
            return Ok((rounds, undecided));
        }
    }
}

/// Stage 5: the map from the final classes; `candidates` (stage 3) tells a register that never
/// had a counterpart from one whose counterpart was disproved.
pub(crate) fn report(models: &[&Model], candidates: &[Vec<RegId>], classes: &[Vec<RegId>], inv: &Polarity, undecided: &[RegId], rounds: usize) -> MapReport {
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
    // 🔑 A class's registers of one polarity are reported as before; only when NEITHER polarity
    // holds registers of both designs are the two taken together, the pairs then inverted. A
    // register and a revised one of its own polarity therefore never lose their pairing to one
    // stored inverted.
    let mut groups: Vec<(Vec<RegId>, bool)> = Vec::new();
    for cl in classes {
        let (pos, neg): (Vec<RegId>, Vec<RegId>) = cl.iter().partition(|r| !inv[r.0][r.1]);
        let both = |v: &[RegId]| v.iter().any(|r| golden(&r)) && v.iter().any(|r| !golden(&r));
        if !both(&pos) && !both(&neg) && both(cl) {
            groups.push((cl.clone(), true));
        } else {
            groups.extend([pos, neg].into_iter().filter(|v| !v.is_empty()).map(|v| (v, false)));
        }
    }
    for (cl, inverted) in &groups {
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
            (1, 1) if *inverted => {
                rep.inverted.insert(gn[0].clone(), rn[0].clone());
            }
            (1, 1) => {
                rep.mapped.insert(gn[0].clone(), rn[0].clone());
            }
            // an inverted class that is not one-to-one is not decided
            _ if *inverted => rep.ambiguous.push((gn, rn)),
            (1, _) => {
                rep.duplicated.insert(gn[0].clone(), rn);
            }
            _ => rep.ambiguous.push((gn, rn)),
        }
    }
    rep.undecided = undecided.iter().map(|r| models[r.0].regs[r.1].clone()).collect();
    for m in models {
        rep.unobserved.extend(m.unobserved.iter().cloned());
        rep.cut.extend(m.cut.iter().cloned());
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
pub(crate) fn attribute(models: &[&Model], sigs: &[Vec<Vec<u64>>], classes: &[Vec<RegId>], inv: &Polarity, rep: &mut MapReport) -> Result<(), String> {
    // polarity as proved for a register in a class of both designs; every other register is
    // assumed as itself (the pairs below are by its raw signature)
    let mapped: HashSet<RegId> = classes.iter().filter(|c| c.iter().any(|r| models[r.0].side == Side::Golden) && c.iter().any(|r| models[r.0].side == Side::Revised)).flatten().copied().collect();
    let pol = |r: RegId| inv[r.0][r.1] && mapped.contains(&r);
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
        pair_leftovers(gn, rn, &mut pairs, &mut |p: &[(usize, usize)]| follows(models, classes, &pol, &gold, &rev, p))?;
    }
    let (mut gfree, mut rfree) = (vec![true; gn], vec![true; rn]);
    for &(i, j) in &pairs {
        gfree[i] = false;
        rfree[j] = false;
    }
    // 4. each pair's verdict, every class and pair assumed equal
    let class_of = class_index(models, &assumed_classes(models, classes, &gold, &rev, &pairs), &pol);
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
        match same_next(models, gold[i], rev[j], &class_of)? {
            true => rep.follows.push(pair),
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
fn follows(models: &[&Model], classes: &[Vec<RegId>], pol: &dyn Fn(RegId) -> bool, gold: &[RegId], rev: &[RegId], pairs: &[(usize, usize)]) -> Result<usize, String> {
    let class_of = class_index(models, &assumed_classes(models, classes, gold, rev, pairs), pol);
    let mut n = 0;
    for &(i, j) in pairs {
        if same_next(models, gold[i], rev[j], &class_of)? {
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

    /// 🔑 A latch or a memory macro is cut in the map exactly as `check` cuts it: each output is
    /// the free variable `inst/<pin>`, shared by INSTANCE name across the designs, whatever its
    /// output net is called. A clock-gate enable latch, then an SRAM macro (CoralNPU has both)
    /// used to stop the whole map ("a latch is not modelled", "no single `ff` group") while
    /// `check` ran the same netlists. With them cut, the renamed register reading them maps by
    /// proof and each cut cell is listed, never silently assumed. The same cell under another
    /// instance name is another free input, so the register reading it is NOT mapped: the
    /// pairing is `check`'s, by name, no more.
    #[test]
    fn a_latch_or_memory_is_cut_and_paired_by_instance_name_as_check_does() {
        let with = |latch: &str, ram: &str, e: &str, m: &str, r: &str, d: &str, q: &str| {
            nl(&format!(
                "module t(clk,en,y);\ninput clk,en; output y;\nwire {e},{m},x,{d},{q};\n\
                 LAT {latch}(.G(clk),.D(en),.Q({e}));\nRAM1 {ram}(.CK(clk),.D(en),.Q({m}));\n\
                 XOR2 x0(.A({e}),.B({m}),.Y(x));\nXOR2 x1(.A(x),.B({q}),.Y({d}));\n\
                 DFF {r}(.CK(clk),.D({d}),.Q({q}));\nBUF b(.A({q}),.Y(y));\nendmodule\n"
            ))
        };
        let golden = with("cg_lt", "mem", "e", "m", "r0", "d0", "q0");
        let rep = map(&golden, &with("cg_lt", "mem", "n5", "n8", "u9", "n6", "n7"));
        assert_eq!(rep.mapped.get("r0").map(String::as_str), Some("u9"), "{rep:?}");
        assert!(rep.one_to_one(), "{rep:?}");
        let cut: Vec<(Side, &str)> = rep.cut.iter().map(|x| (x.side, x.instance.as_str())).collect();
        assert_eq!(cut, [(Side::Golden, "cg_lt"), (Side::Golden, "mem"), (Side::Revised, "cg_lt"), (Side::Revised, "mem")]);
        for (latch, ram) in [("other_lt", "mem"), ("cg_lt", "other_mem")] {
            let rep = map(&golden, &with(latch, ram, "n5", "n8", "u9", "n6", "n7"));
            assert!(rep.mapped.is_empty(), "{latch}/{ram}: a cell of another name is another input: {rep:?}");
            assert!(rep.unmatched_golden.contains_key("r0") && rep.unmatched_revised.contains_key("u9"), "{rep:?}");
        }
    }

    /// 🔑 An asynchronous-reset input is found from the Liberty, not its name: forward through
    /// buffers and inverters only, every pin it reaches is a register's `clear` / `preset` pin,
    /// and the value that holds them all inactive is the pin's inactive level through the path's
    /// parity. `rst_n` (to `RESET_B`, clear `!RESET_B`) is inactive at 1; `arst` through an
    /// inverter to `RESET_B` is inactive at 0. An input that also reaches a data pin (`en`), one
    /// that passes other logic (`gated`), and the clock are not reset inputs.
    #[test]
    fn async_reset_inputs_are_found_from_clear_and_preset_pins() {
        let n = nl("module t(clk,rst_n,arst,en,gated,d,q0,q1,q2,q3);\ninput clk,rst_n,arst,en,gated,d; output q0,q1,q2,q3;\nwire b,na,x;\n\
             BUF bb(.A(rst_n),.Y(b));\nDFR r0(.CK(clk),.D(d),.RESET_B(b),.Q(q0));\n\
             INV ia(.A(arst),.Y(na));\nDFR r1(.CK(clk),.D(d),.RESET_B(na),.Q(q1));\n\
             DFS r2(.CK(clk),.D(en),.SET_B(en),.Q(q2));\n\
             AND2 g(.A(gated),.B(d),.Y(x));\nDFR r3(.CK(clk),.D(d),.RESET_B(x),.Q(q3));\nendmodule\n");
        let l = lib();
        let d = Design::sequential(&n, &l);
        let found: Vec<(String, bool)> = d.reset_inputs().into_iter().collect();
        assert_eq!(found, [("arst".to_string(), false), ("rst_n".to_string(), true)]);
    }

    /// The stimulus is the same in both designs: a held reset input is ACTIVE for
    /// [`RESET_CYCLES`] and inactive after, every other input random per name and cycle; an
    /// input two designs hold at different inactive values is not held at all.
    #[test]
    fn the_stimulus_holds_reset_inputs_active_then_inactive() {
        let st = Stimulus { held: [("rst_n".to_string(), true)].into_iter().collect() };
        for c in 0..RESET_CYCLES {
            assert_eq!(st.word("rst_n", c), 0, "active (low) in cycle {c}");
        }
        for c in RESET_CYCLES..CYCLES {
            assert_eq!(st.word("rst_n", c), !0, "inactive in cycle {c}");
        }
        assert_eq!(st.word("en", 7), input_word("en", 7));
        let l = lib();
        let low = nl("module t(clk,r,d,q);\ninput clk,r,d; output q;\nDFR u(.CK(clk),.D(d),.RESET_B(r),.Q(q));\nendmodule\n");
        let high = nl("module t(clk,r,d,q);\ninput clk,r,d; output q;\nwire n;\nINV i(.A(r),.Y(n));\nDFR u(.CK(clk),.D(d),.RESET_B(n),.Q(q));\nendmodule\n");
        let (a, b) = (Design::sequential(&low, &l), Design::sequential(&high, &l));
        assert_eq!(Stimulus::of(&[&a, &a]).held.get("r"), Some(&true));
        assert!(Stimulus::of(&[&a, &b]).held.is_empty(), "the designs disagree: not held");
    }

    /// 🔑 An overflowing class is built in chunks (L6 b): members go into one manager until one
    /// overflows it; the members built so far are listed canonically and a fresh manager starts.
    /// Every manager numbers variables through ONE name map, so equal functions give equal keys
    /// across chunks and different functions different keys; a member that overflows a fresh
    /// manager alone is undecided (`None`). A class that fits keeps plain nodes.
    #[test]
    fn an_overflowing_class_is_built_in_chunks_over_one_variable_order() {
        // member i: the AND of its inputs, built in the order given (`b a` and `a b` are one
        // function); `wide` is too big for any manager of the small limit
        let funs: Vec<Vec<&str>> = vec![vec!["a", "b"], vec!["c", "d"], vec!["b", "a"], vec!["a", "c"], vec!["wide"], vec!["d", "c"]];
        let mut build = |i: usize, bdd: &mut Bdd, var: &mut dyn FnMut(&mut Bdd, &str) -> u32| -> Result<Option<u32>, String> {
            if funs[i] == ["wide"] {
                let mut f = bdd.zero();
                for k in 0..40 {
                    let (x, y) = (var(bdd, &format!("w{k}")), var(bdd, &format!("v{k}")));
                    let t = bdd.and(x, y);
                    f = bdd.xor(f, t);
                }
                return Ok(Some(f));
            }
            let mut f = bdd.one();
            for n in &funs[i] {
                let v = var(bdd, n);
                f = bdd.and(f, v);
            }
            Ok(Some(f))
        };
        let (keys, managers) = chunked_keys(funs.len(), 16, &mut build).unwrap();
        assert!(managers > 2, "the small limit forces several chunks, got {managers}");
        assert!(keys.iter().all(|k| !matches!(k, Some(Key::Node(_)))), "chunked keys are canonical");
        assert_eq!(keys[4], None, "too big for a fresh manager: undecided");
        assert_eq!(keys[0], keys[2], "one function in two chunks, one key");
        assert_eq!(keys[1], keys[5]);
        assert_ne!(keys[0], keys[1]);
        assert_ne!(keys[0], keys[3]);
        assert!(keys.iter().enumerate().all(|(i, k)| i == 4 || k.is_some()));
        let (keys, managers) = chunked_keys(4, BDD_LIMIT, &mut build).unwrap();
        assert_eq!(managers, 1);
        assert!(matches!(keys[0], Some(Key::Node(_))));
        assert_eq!(keys[0], keys[2]);
        assert_ne!(keys[0], keys[1]);
    }

    /// The chunked refinement proves the same classes as one manager: a class too big for one
    /// small manager is no longer undecided, it splits exactly as it does under the full budget.
    #[test]
    fn chunked_refinement_proves_what_one_manager_proves() {
        let l = lib();
        let g = nl("module t(clk,a,b,q);\ninput clk,a,b; output q;\nwire x,y,s0,s1,s2;\n\
             AND2 g0(.A(a),.B(b),.Y(x));\nDFF r0(.CK(clk),.D(x),.Q(s0));\nDFF r1(.CK(clk),.D(s0),.Q(s1));\n\
             XOR2 g1(.A(s1),.B(a),.Y(y));\nDFF r2(.CK(clk),.D(y),.Q(s2));\nBUF o(.A(s2),.Y(q));\nendmodule\n");
        let r = nl("module t(clk,a,b,q);\ninput clk,a,b; output q;\nwire x,y,s0,s1,s2;\n\
             AND2 h0(.A(b),.B(a),.Y(x));\nDFF u0(.CK(clk),.D(x),.Q(s0));\nDFF u1(.CK(clk),.D(s0),.Q(s1));\n\
             XOR2 h1(.A(a),.B(s1),.Y(y));\nDFF u2(.CK(clk),.D(y),.Q(s2));\nBUF o(.A(s2),.Y(q));\nendmodule\n");
        let (gd, rd) = (Design::register_model(&g, &l), Design::register_model(&r, &l));
        let (gm, rm) = (model(&gd, Side::Golden, Naming::Instance).unwrap(), model(&rd, Side::Revised, Naming::Instance).unwrap());
        let models = [&gm, &rm];
        // every register in ONE candidate class: refinement alone must separate them
        let all: Vec<RegId> = (0..2).flat_map(|m| (0..models[m].regs.len()).map(move |k| (m, k))).collect();
        let sorted = |mut c: Vec<Vec<RegId>>| {
            c.iter_mut().for_each(|x| x.sort());
            c.sort();
            c
        };
        let flat: Polarity = models.iter().map(|m| vec![false; m.regs.len()]).collect();
        let mut full = vec![all.clone()];
        let (_, u) = refine(&models, &mut full, &flat).unwrap();
        assert!(u.is_empty());
        let mut small = vec![all];
        // 8 nodes plus memo entries: each member fits a manager alone, the class does not (7 makes
        // a member undecided; with the old rule, any overflow undecided the whole class)
        let (_, u) = refine_within(&models, &mut small, &flat, 8).unwrap();
        assert!(u.is_empty(), "chunks, not undecided: {u:?}");
        assert_eq!(sorted(small), sorted(full.clone()));
        assert_eq!(full.iter().filter(|c| c.len() == 2).count(), 3, "r0=u0, r1=u1, r2=u2");
    }

    /// The golden pair `r0` (cleared, loads `d`) and `r1` (cleared, loads `r0`), against a
    /// revised design whose `u0` stores the complement: preset where `r0` is cleared, loading
    /// `!d`, `u1` loading `!u0`. `u0_kind` is u0's cell and reset pin, `u0_d` its data input.
    fn complement(u0: &str) -> (Netlist, Netlist) {
        let g = nl("module t(clk,rst_n,d,q);\ninput clk,rst_n,d; output q;\nwire s0;\n\
             DFR r0(.CK(clk),.D(d),.RESET_B(rst_n),.Q(s0));\nDFR r1(.CK(clk),.D(s0),.RESET_B(rst_n),.Q(q));\nendmodule\n");
        let r = nl(&format!(
            "module t(clk,rst_n,d,q);\ninput clk,rst_n,d; output q;\nwire nd,s0,ns0;\n\
             INV i0(.A(d),.Y(nd));\n{u0}\nINV i1(.A(s0),.Y(ns0));\nDFR u1(.CK(clk),.D(ns0),.RESET_B(rst_n),.Q(q));\nendmodule\n"
        ));
        (g, r)
    }

    /// 🔑 L1: a register maps to one storing its COMPLEMENT, with clear and preset swapped (the
    /// golden `r0` cleared where the revised `u0` is preset): proved like any pair, with `u0`
    /// read as the complement of the class value, and reported under `inverted`, never `mapped`.
    /// `r1` maps to `u1` as itself THROUGH that pair (u1 reads `!u0` = `r0`).
    #[test]
    fn a_register_storing_the_complement_maps_inverted_with_clear_and_preset_swapped() {
        let (g, r) = complement("DFS u0(.CK(clk),.D(nd),.SET_B(rst_n),.Q(s0));");
        let rep = map(&g, &r);
        assert_eq!(rep.inverted, [("r0".to_string(), "u0".to_string())].into_iter().collect());
        assert_eq!(rep.mapped, [("r1".to_string(), "u1".to_string())].into_iter().collect());
        assert!(rep.one_to_one());
        // clear NOT swapped for preset: in reset both are 0, so u0 is not the complement of r0
        let (g, r) = complement("DFR u0(.CK(clk),.D(nd),.RESET_B(rst_n),.Q(s0));");
        let rep = map(&g, &r);
        assert!(rep.inverted.is_empty() && rep.mapped.is_empty(), "{rep:?}");
    }

    /// The proof, not the signature, decides an inverted member: a class holding `r0` and an
    /// inverted `u0` stays one class only when u0's next value is the complement of r0's with u0
    /// READ complemented; a u0 that is cleared, not preset, splits off.
    #[test]
    fn an_inverted_member_is_proved_complemented() {
        let l = lib();
        for (u0, holds) in [("DFS u0(.CK(clk),.D(nd),.SET_B(rst_n),.Q(s0));", true), ("DFR u0(.CK(clk),.D(nd),.RESET_B(rst_n),.Q(s0));", false)] {
            let (g, r) = complement(u0);
            let (gd, rd) = (Design::register_model(&g, &l), Design::register_model(&r, &l));
            let (gm, rm) = (model(&gd, Side::Golden, Naming::Instance).unwrap(), model(&rd, Side::Revised, Naming::Instance).unwrap());
            let models = [&gm, &rm];
            let at = |m: usize, n: &str| (m, models[m].regs.iter().position(|x| x.name == n).unwrap());
            let mut inv: Polarity = models.iter().map(|m| vec![false; m.regs.len()]).collect();
            inv[1][at(1, "u0").1] = true;
            let mut classes = vec![vec![at(0, "r0"), at(1, "u0")], vec![at(0, "r1"), at(1, "u1")]];
            refine(&models, &mut classes, &inv).unwrap();
            assert_eq!(classes.iter().all(|c| c.len() == 2), holds, "{u0}: {classes:?}");
        }
    }

    /// Candidates up to complement: from cycle 1 a register and its complement share a class with
    /// opposite polarity; a register keeps its own-polarity partner when one exists (`u` maps to
    /// `r` as itself, and `w`, the complement, is left unmatched rather than making it ambiguous).
    #[test]
    fn a_same_polarity_partner_wins_over_a_complement() {
        let g = nl("module t(clk,rst_n,d,q);\ninput clk,rst_n,d; output q;\nDFR r(.CK(clk),.D(d),.RESET_B(rst_n),.Q(q));\nendmodule\n");
        let r = nl("module t(clk,rst_n,d,q,p);\ninput clk,rst_n,d; output q,p;\nwire nd;\n\
             DFR u(.CK(clk),.D(d),.RESET_B(rst_n),.Q(q));\nINV i(.A(d),.Y(nd));\nDFS w(.CK(clk),.D(nd),.SET_B(rst_n),.Q(p));\nendmodule\n");
        let rep = map(&g, &r);
        assert_eq!(rep.mapped, [("r".to_string(), "u".to_string())].into_iter().collect());
        assert!(rep.inverted.is_empty());
        assert!(rep.unmatched_revised.contains_key("w"), "{rep:?}");
    }

    /// A gated-clock design: `r` on `clk` gated by `gate` (the netlist text making `gclk`), with
    /// data `d`, against a plain enable register `u` on `clk` behind a hold mux selected by `en`.
    fn gated(gate: &str) -> (Netlist, Netlist) {
        let g = nl(&format!(
            "module t(clk,en,se,d,q);\ninput clk,en,se,d; output q;\nwire le,gclk,s;\n{gate}\nDFF r(.CK(gclk),.D(d),.Q(s));\nBUF b(.A(s),.Y(q));\nendmodule\n"
        ));
        let m = nl("module t(clk,en,se,d,q);\ninput clk,en,se,d; output q;\nwire n,s;\n\
             MUX2 m(.A0(s),.A1(d),.S(en),.Y(n));\nDFF u(.CK(clk),.D(n),.Q(s));\nBUF b(.A(s),.Y(q));\nendmodule\n");
        (g, m)
    }
    const LATCH_AND: &str = "LATN l(.G(clk),.D(en),.Q(le));\nAND2 g(.A(clk),.B(le),.Y(gclk));";

    /// 🔑 The standard clock gate: an enable latch transparent while the clock is LOW, ANDed with
    /// the clock. At the clock's rising edge the latch holds its D, and the gated clock rises iff
    /// it is 1, so the register loads `en ? D : state`: the same state as an enable register
    /// behind a hold mux, MAPPED by proof. The library clock-gate cell
    /// (`clock_gating_integrated_cell : latch_posedge*`, its non-clock inputs ORed) is the same
    /// gate; with test enable `se` held 0 it maps the same way, and with `se` free it is
    /// `en | se`, which the mux on `en` alone is not.
    #[test]
    fn a_register_behind_the_standard_clock_gate_loads_under_its_enable() {
        let (g, m) = gated(LATCH_AND);
        let rep = map(&g, &m);
        assert_eq!(rep.mapped.get("r").map(String::as_str), Some("u"), "{rep:?}");
        assert!(rep.one_to_one(), "{rep:?}");
        assert_eq!(rep.cut.iter().map(|x| x.instance.as_str()).collect::<Vec<_>>(), ["l"]);
        let (g, _) = gated("ICG c(.CK(clk),.E(en),.SE(1'b0),.GCK(gclk));");
        assert_eq!(map(&g, &m).mapped.get("r").map(String::as_str), Some("u"));
        let (g, _) = gated("ICG c(.CK(clk),.E(en),.SE(se),.GCK(gclk));");
        assert!(map(&g, &m).mapped.is_empty(), "the test enable gates the clock too");
        // the enable is not ignored: an ungated register never maps to the hold register
        let plain = nl("module t(clk,en,se,d,q);\ninput clk,en,se,d; output q;\nwire s;\n\
             DFF r(.CK(clk),.D(d),.Q(s));\nBUF b(.A(s),.Y(q));\nendmodule\n");
        assert!(map(&plain, &m).mapped.is_empty());
    }

    /// 🔑 A clock-gate enable that NEVER asserts in simulation is freed for the candidates only.
    /// Here the gate's enable comes from `e`, a register stuck at 0, so `r` behind it never
    /// loads and its signature is all zero; freed, the enable is the shared random stream and `r`
    /// moves. The proof keeps the real enable: two designs whose enables are both stuck in
    /// simulation but are different functions (`e` against `e & k`) are candidates, and `refine`
    /// still splits `r` from `r`.
    #[test]
    fn a_stuck_clock_gate_enable_is_free_in_simulation_only() {
        let gated = |en: &str| {
            nl(&format!(
                "module t(clk,k,d,q,p);\ninput clk,k,d; output q,p;\nwire eq,en,le,gclk,s;\n\
                 DFF e(.CK(clk),.D(eq),.Q(eq));\nBUF o(.A(eq),.Y(p));\n{en}\nLATN l(.G(clk),.D(en),.Q(le));\n\
                 AND2 g(.A(clk),.B(le),.Y(gclk));\nDFF r(.CK(gclk),.D(d),.Q(s));\nBUF b(.A(s),.Y(q));\nendmodule\n"
            ))
        };
        let (g, r) = (gated("BUF n(.A(eq),.Y(en));"), gated("AND2 n(.A(eq),.B(k),.Y(en));"));
        let l = lib();
        let (gd, rd) = (Design::register_model(&g, &l), Design::register_model(&r, &l));
        let (gm, rm) = (model(&gd, Side::Golden, Naming::Instance).unwrap(), model(&rd, Side::Revised, Naming::Instance).unwrap());
        let stim = Stimulus::of(&[&gd, &rd]);
        let (sigs, freed) = simulate_freeing_stuck_enables(&[&gm, &rm], &stim).unwrap();
        assert_eq!(freed[0].iter().map(String::as_str).collect::<Vec<_>>(), ["l <enable>"]);
        let at = |m: &Model, n: &str| m.regs.iter().position(|x| x.name == n).unwrap();
        assert!(sigs[0][at(&gm, "r")].iter().any(|w| *w != 0), "freed, r loads");
        assert_eq!(sigs[0][at(&gm, "r")], sigs[1][at(&rm, "r")], "both designs see one enable stream");
        let (plain, _) = simulate(&[&gm, &rm], &stim, &[BTreeSet::new(), BTreeSet::new()]).unwrap();
        assert!(plain[0][at(&gm, "r")].iter().all(|w| *w == 0), "computed, the enable never asserts");
        let rep = map(&g, &r);
        assert_eq!(rep.free_enables, ["l"]);
        assert_eq!(rep.mapped.get("e").map(String::as_str), Some("e"), "{rep:?}");
        assert!(!rep.mapped.contains_key("r"), "the proof reads e against e & k: {rep:?}");
        assert_eq!(map(&g, &g).mapped.get("r").map(String::as_str), Some("r"));
    }

    /// Two gates in a row (an outer gate whose output clocks the inner gate's latch) as a chain
    /// of ANDs against one AND3 of the clock and both latches: one gate, `en1 & en2`. A latch on
    /// a gated clock that the register's gate does not also gate may open while the gated clock
    /// is high, and is refused.
    #[test]
    fn nested_clock_gates_are_one_enable_and_an_unsafe_latch_is_refused() {
        let outer = "LATN l1(.G(clk),.D(en),.Q(e1));\nAND2 g1(.A(clk),.B(e1),.Y(c1));\nLATN l2(.G(c1),.D(se),.Q(e2));";
        let with = |gate: &str| {
            nl(&format!(
                "module t(clk,en,se,d,q);\ninput clk,en,se,d; output q;\nwire e1,e2,c1,gclk,s;\n{outer}\n{gate}\n\
                 DFF r(.CK(gclk),.D(d),.Q(s));\nBUF b(.A(s),.Y(q));\nendmodule\n"
            ))
        };
        let chain = with("AND2 g2(.A(c1),.B(e2),.Y(gclk));");
        let and3 = with("AND3 g2(.A(clk),.B(e1),.C(e2),.Y(gclk));");
        let rep = map(&chain, &and3);
        assert_eq!(rep.mapped.get("r").map(String::as_str), Some("r"), "{rep:?}");
        let mux = nl("module t(clk,en,se,d,q);\ninput clk,en,se,d; output q;\nwire k,n,s;\n\
             AND2 a(.A(en),.B(se),.Y(k));\nMUX2 m(.A0(s),.A1(d),.S(k),.Y(n));\nDFF u(.CK(clk),.D(n),.Q(s));\nBUF b(.A(s),.Y(q));\nendmodule\n");
        assert_eq!(map(&chain, &mux).mapped.get("r").map(String::as_str), Some("u"));
        let unsafe_ = with("AND2 g2(.A(clk),.B(e2),.Y(gclk));");
        let e = register_map(&unsafe_, &and3, &lib(), (Naming::Instance, Naming::Instance)).unwrap_err();
        assert!(e.contains("may open while the gated clock is high"), "{e}");
    }

    /// ⛔ Anything else on a clock path is refused, by name: a latch open on the HIGH phase (it
    /// would pass a new enable while the clock is high: a glitch), an inverter, other logic, a
    /// clock-gate cell latched on the falling edge.
    #[test]
    fn any_other_clock_structure_is_refused_by_name() {
        let (_, m) = gated(LATCH_AND);
        for (gate, says) in [
            ("LAT l(.G(clk),.D(en),.Q(le));\nAND2 g(.A(clk),.B(le),.Y(gclk));", "not while its clock is low"),
            ("INV g(.A(clk),.Y(gclk));", "an inverter"),
            ("OR2 g(.A(clk),.B(en),.Y(gclk));", "not an AND"),
            ("AND2 g(.A(clk),.B(en),.Y(gclk));", "an AND of two clocks"),
            ("ICGN c(.CK(clk),.E(en),.GCK(gclk));", "latch_negedge"),
        ] {
            let (g, _) = gated(gate);
            let e = register_map(&g, &m, &lib(), (Naming::Instance, Naming::Instance)).unwrap_err();
            assert!(e.contains(says), "{gate}: {e}");
        }
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
