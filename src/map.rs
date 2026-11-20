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
//! 2. [`simulate`]: both designs, every register UNDEFINED at the start (three-valued: a register
//!    with a clear or preset is defined by reset, one without reset once it loads,
//!    [`defined_signature`]), on the SAME inputs (each primary input
//!    by name: random, except the asynchronous-reset inputs, held active and then inactive,
//!    [`Stimulus`]), 64 runs at once for [`CYCLES`] cycles; a clock-gate enable that never
//!    asserts is then driven at random and the simulation rerun
//!    ([`simulate_freeing_stuck_enables`]). A register's signature is its state in every run and
//!    cycle, its undefined bits filled canonically.
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

#[cfg(feature = "sat")]
mod sat;
#[cfg(feature = "sat")]
pub use sat::PAIR_CONFLICTS;

/// How stage 4 proves the classes (`map --refine`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Refine {
    /// BDD keys per class ([`refine_within`]).
    Bdd,
    /// SAT, as ABC's `&scorr` (`sat` feature): one incremental solver per round.
    Sat,
    /// SAT, then the fixed point re-keyed by BDDs; a class they split is an error.
    Both,
}

impl Default for Refine {
    /// SAT when the `sat` feature is built in (as released), BDD otherwise.
    fn default() -> Refine {
        if cfg!(feature = "sat") {
            Refine::Sat
        } else {
            Refine::Bdd
        }
    }
}

impl Refine {
    pub fn name(self) -> &'static str {
        match self {
            Refine::Bdd => "bdd",
            Refine::Sat => "sat",
            Refine::Both => "both",
        }
    }
}

/// The proof effort of a SAT refinement, for the report (all 0 under `--refine bdd`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SatEffort {
    /// Obligations the solver proved (the two sides equal under the round's classes).
    pub proved: usize,
    /// Obligations proved by structure alone (both sides one literal), no solver call.
    pub structural: usize,
    /// Obligations the solver disproved, each with a counter-example.
    pub disproved: usize,
    /// Obligations over the conflict limit: their member is undecided.
    pub gave_up: usize,
    /// Counter-example batches resimulated.
    pub resimulated: usize,
    /// `--refine both`: classes the BDD keys re-checked, and members over the BDD budget.
    pub bdd_checked: usize,
    pub bdd_unchecked: usize,
}

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
    /// Candidate pairs PROPOSED by name ([`split_constant_classes_by_name`]): how many.
    pub name_pairs: usize,
    /// How the classes were proved (`--refine`), and the SAT proof effort.
    pub refine: Refine,
    pub sat: SatEffort,
    /// Of those, the pairs refinement disproved (golden name, revised name): proposed by name,
    /// split by the proof, never in the map.
    pub name_pairs_rejected: Vec<(String, String)>,
    /// Inputs the simulation held constant (`--hold`, [`SimHolds`]): input, value.
    pub holds: Vec<(String, bool)>,
    /// Inputs given as resets (`--reset`): input, inactive value. Also in `reset_inputs`.
    pub resets_given: Vec<(String, bool)>,
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
    register_map_with(golden, revised, lib, names, &SimHolds::default(), Refine::default())
}

/// What the user fixes in the candidate-class simulation (`lec map --hold`, `--reset`), by
/// primary-input name, in both designs: `hold` an input at a constant, `reset` an input as an
/// asynchronous reset with its INACTIVE value (active for [`RESET_CYCLES`], then inactive, as
/// [`Design::reset_inputs`] finds them).
///
/// ⛔ Simulation ONLY. A hold proposes candidates; it is never an assumption of the proof:
/// `refine` and [`next_state_bdds`] read every primary input as a free variable whatever is held,
/// so a pair that holds only under a held input is still split. The report lists the holds
/// (`holds`, `resets_given`), so a result is never read without them.
#[derive(Debug, Clone, Default)]
pub struct SimHolds {
    pub hold: BTreeMap<String, bool>,
    pub reset: BTreeMap<String, bool>,
}

/// [`register_map`] with the simulation holds `holds` ([`SimHolds`]). A name that is not a
/// primary input of both designs, or that is both held and a reset, is refused.
pub fn register_map_with(golden: &Netlist, revised: &Netlist, lib: &Lib, names: (Naming, Naming), holds: &SimHolds, engine: Refine) -> Result<MapReport, String> {
    register_map_at(golden, revised, lib, names, holds, engine, SAT_CONFLICTS)
}

/// The conflict limit of one SAT obligation in stage 4 ([`Refine::Sat`]).
#[cfg(feature = "sat")]
const SAT_CONFLICTS: i32 = PAIR_CONFLICTS;
#[cfg(not(feature = "sat"))]
const SAT_CONFLICTS: i32 = 0;

/// [`register_map_with`] with stage 4's SAT conflict limit `limit` (a test lowers it to reach the
/// undecided path). Thin sequencer: the stages in order, no work of its own.
fn register_map_at(golden: &Netlist, revised: &Netlist, lib: &Lib, names: (Naming, Naming), holds: &SimHolds, engine: Refine, limit: i32) -> Result<MapReport, String> {
    if lib.cells.is_empty() {
        return Err("no cells in the Liberty".into());
    }
    for (flag, set) in [("--hold", &holds.hold), ("--reset", &holds.reset)] {
        for n in set.keys() {
            for (side, nl) in [("golden", golden), ("revised", revised)] {
                if !nl.inputs.iter().any(|p| p == n) {
                    return Err(format!("{flag} {n}: `{n}` is not a primary input of the {side} netlist"));
                }
            }
            if flag == "--hold" && holds.reset.contains_key(n) {
                return Err(format!("`{n}` is given both --hold and --reset"));
            }
        }
    }
    let (g, r) = (Design::register_model(golden, lib), Design::register_model(revised, lib));
    let (gm, rm) = (model(&g, Side::Golden, names.0)?, model(&r, Side::Revised, names.1)?);
    let stim = Stimulus::of(&[&g, &r]).with(holds);
    let (sigs, freed) = simulate_freeing_stuck_enables(&[&gm, &rm], &stim)?;
    let (classes, mut inv) = candidate_classes(&[&gm, &rm], &sigs);
    let (mut classes, by_name) = split_constant_classes_by_name(&[&gm, &rm], &sigs, classes, &mut inv);
    let candidates = classes.clone();
    let mut effort = SatEffort::default();
    let (rounds, undecided) = refine_by(engine, &[&gm, &rm], &mut classes, &inv, limit, &mut effort)?;
    let mut rep = report(&[&gm, &rm], &candidates, &classes, &inv, &undecided, rounds);
    rep.refine = engine;
    rep.sat = effort;
    name_pairs_kept(&[&gm, &rm], &classes, &by_name, &mut rep);
    attribute(&[&gm, &rm], &sigs, &classes, &inv, &mut rep)?;
    rep.reset_inputs = stim.held.into_iter().collect();
    rep.holds = stim.fixed.into_iter().collect();
    rep.resets_given = holds.reset.clone().into_iter().collect();
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
    /// Inputs held constant throughout (`--hold`): input -> value.
    pub fixed: BTreeMap<String, bool>,
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
        Stimulus { held, fixed: BTreeMap::new() }
    }

    /// The user's holds on top ([`SimHolds`]): a given reset replaces whatever was detected for
    /// that input; a held input is constant and no longer a reset.
    pub(crate) fn with(mut self, holds: &SimHolds) -> Stimulus {
        self.held.extend(holds.reset.iter().map(|(k, v)| (k.clone(), *v)));
        for (k, v) in &holds.hold {
            self.held.remove(k);
            self.fixed.insert(k.clone(), *v);
        }
        self
    }

    /// Input `name`'s word in `cycle`.
    pub(crate) fn word(&self, name: &str, cycle: usize) -> u64 {
        if let Some(&v) = self.fixed.get(name) {
            return if v { !0 } else { 0 };
        }
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

/// Stage 2: each register's state in 64 runs over [`CYCLES`] cycles from an undefined start
/// ([`defined_signature`]),
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

/// Stage 2: each register's state in 64 runs over [`CYCLES`] cycles from an undefined start
/// ([`defined_signature`]),
/// every design on the same inputs, the enable nets in `free[m]` driven at random. Returns
/// `sigs[m][k]` (model `m`'s register `k`) and, per model, the clock-gate enable nets that
/// never asserted after [`RESET_CYCLES`].
pub(crate) fn simulate(models: &[&Model], stim: &Stimulus, free: &[BTreeSet<String>]) -> Result<Simulated, String> {
    let mut out = Vec::new();
    let mut stuck_all = Vec::new();
    for (mi, m) in models.iter().enumerate() {
        let mut asserted: BTreeSet<&str> = BTreeSet::new();
        let c = &m.cone;
        // every register starts UNDEFINED (`known` 0): see [`defined_signature`]
        let mut state = vec![0u64; m.regs.len()];
        let mut known = vec![0u64; m.regs.len()];
        let mut sig = vec![Vec::with_capacity(CYCLES); m.regs.len()];
        let mut sig_known = vec![Vec::with_capacity(CYCLES); m.regs.len()];
        let states: Vec<String> = c.regs.iter().map(|r| state_net(r)).collect();
        let nexts: Vec<String> = c.regs.iter().map(|r| next_net(r)).collect();
        let mut val: HashMap<&str, (u64, u64)> = HashMap::new();
        for cycle in 0..CYCLES {
            val.clear();
            // free inputs first, then the states over them (see `next_state_bdds`)
            for (net, var) in &c.free {
                val.insert(net.as_str(), (stim.word(var, cycle), !0));
            }
            for (k, s) in states.iter().enumerate() {
                val.insert(s.as_str(), (state[k], known[k]));
                sig[k].push(state[k]);
                sig_known[k].push(known[k]);
            }
            for g in &c.gates {
                let (x, kx): (Vec<u64>, Vec<u64>) = g
                    .ins
                    .iter()
                    .map(|s| match s {
                        Src::Net(n) => val.get(n.as_str()).copied().ok_or_else(|| format!("cone gate `{}` reads `{n}` before it is computed", g.out)),
                        Src::Const(v) => Ok((if *v { !0 } else { 0 }, !0)),
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .unzip();
                // a freed clock-gate enable ([`simulate_freeing_stuck_enables`]): the shared random stream
                let (y, ky) = if free[mi].contains(&g.out) {
                    (stim.word(FREE_ENABLE, cycle), !0)
                } else {
                    ternary_word(&x, &kx, |x| match &g.logic {
                        Logic::Prim(op) => prim_word(*op, &g.pins, x),
                        Logic::Func(f) => Ok(func_word(f, &g.pins, x)),
                    })?
                };
                if y & ky != 0 && cycle >= RESET_CYCLES && gate_of(&g.out).is_some() {
                    asserted.insert(g.out.as_str());
                }
                val.insert(g.out.as_str(), (y, ky));
            }
            for (k, r) in c.regs.iter().enumerate() {
                (state[k], known[k]) = val.get(nexts[k].as_str()).copied().ok_or_else(|| format!("register `{r}` has no next-state gate"))?;
            }
        }
        out.push(sig.iter().zip(&sig_known).map(|(v, k)| defined_signature(v, k)).collect());
        stuck_all.push(c.gates.iter().filter(|g| gate_of(&g.out).is_some() && !asserted.contains(g.out.as_str())).map(|g| g.out.clone()).collect());
    }
    Ok((out, stuck_all))
}

/// Inputs with more undefined words than this are not enumerated: the output is then defined only
/// where every input is (pessimistic, never wrong).
const TERNARY_MAX: usize = 6;

/// One gate in three-valued simulation over 64 runs: `x` the input values, `k` where each is
/// defined. A bit of the output is defined iff it is the same for EVERY value of the undefined
/// inputs at that bit, found by evaluating every assignment of the inputs that have an undefined
/// bit (exact per gate; a 1 on one input of an AND defines nothing, a 0 defines the output).
fn ternary_word(x: &[u64], k: &[u64], eval: impl Fn(&[u64]) -> Result<u64, String>) -> Result<(u64, u64), String> {
    let unk: Vec<usize> = (0..x.len()).filter(|&i| k[i] != !0).collect();
    if unk.is_empty() {
        return Ok((eval(x)?, !0));
    }
    let base: Vec<u64> = x.iter().zip(k).map(|(v, k)| v & k).collect();
    if unk.len() > TERNARY_MAX {
        return Ok((eval(&base)?, k.iter().fold(!0, |a, b| a & b)));
    }
    let y0 = eval(&base)?;
    let mut diff = 0u64;
    let mut xs = base.clone();
    for a in 1u32..(1 << unk.len()) {
        for (j, &i) in unk.iter().enumerate() {
            xs[i] = if a >> j & 1 == 1 { base[i] | !k[i] } else { base[i] };
        }
        diff |= eval(&xs)? ^ y0;
    }
    Ok((y0, !diff))
}

/// A register's candidate signature from its simulated values `v` and where they are defined `k`
/// (per cycle, one bit per run).
///
/// 🔑 Every register starts UNDEFINED, as in silicon: a register with an asynchronous clear or
/// preset is defined from the first edge of reset; one WITHOUT reset only once it loads a defined
/// value. The old all-zero start gave such a register an arbitrary first value that depended on
/// how each synthesis stored it: CoralNPU's AXI and debug request queues (RTL `ram` without reset)
/// are stored one way by the reference flow and the complement by ours, so before the first write
/// the two started at DIFFERENT values, matched neither equal nor complemented, and fell into no
/// shared class.
///
/// Undefined bits are filled canonically so that two registers equal (or complementary) wherever
/// defined, with the same defined pattern, get equal (or complementary) signatures: in each run
/// the last defined value is carried forward and the first defined value backward; a run never
/// defined takes the register's first defined bit (lowest run, earliest cycle) or 0.
///
/// ⛔ Soundness is unchanged: the signature only PROPOSES candidate classes; every pair is still
/// proved by refinement (`refine` / the SAT rounds) before it is mapped.
pub(crate) fn defined_signature(v: &[u64], k: &[u64]) -> Vec<u64> {
    let (mut seen, mut first, mut last) = (0u64, 0u64, 0u64);
    let mut fwd = Vec::with_capacity(v.len());
    let mut seen_at = Vec::with_capacity(v.len());
    for (&v, &k) in v.iter().zip(k) {
        first |= v & k & !seen;
        seen |= k;
        last = (v & k) | (last & !k);
        fwd.push(last);
        seen_at.push(seen);
    }
    let flip = if seen == 0 { 0 } else { (first >> seen.trailing_zeros()) & 1 };
    let never = if flip == 1 { !seen } else { 0 };
    fwd.iter().zip(&seen_at).map(|(f, s)| (f & s) | (first & !s & seen) | never).collect()
}

/// Each register's polarity in its class, per model: `true` when the register holds the
/// COMPLEMENT of its class's value.
pub(crate) type Polarity = Vec<Vec<bool>>;

/// Stage 3: the registers of all models grouped by signature UP TO COMPLEMENT, each class in
/// (model, register) order, the classes in order of their first member; with each register's
/// polarity in its class.
///
/// 🔑 A signature is compared from cycle 1: cycle 0 is the undefined start, filled the same in
/// every register defined later, so leaving it out separates nothing that it separated. A signature whose first bit
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

/// Stage 3b: a candidate class whose members NEVER toggled (every register constant in every
/// simulated cycle after the all-zero start) is split by name. Simulation tells such registers
/// nothing apart, so one class can hold most of a core whose state random inputs never write;
/// each golden register with exactly one same-named revised register in the class becomes a
/// class of its own with it, and the rest stay together as one residual class.
///
/// ⛔ A name only PROPOSES a pair. Every class, these included, goes through the same refinement
/// (`refine`): a same-named pair whose next-state functions differ is split and never mapped
/// (`name_pairs_rejected` lists it). Splitting a candidate class is sound (any partition that
/// refinement leaves unsplit is an inductive invariant); it can only lose pairs the residual
/// class would have found.
///
/// 🔑 Polarity comes from each register's constant: a register constantly 1 holds the complement
/// of one constantly 0, so a pair with complementary constants is proposed INVERTED.
pub(crate) fn split_constant_classes_by_name(
    models: &[&Model],
    sigs: &[Vec<Vec<u64>>],
    classes: Vec<Vec<RegId>>,
    inv: &mut Polarity,
) -> (Vec<Vec<RegId>>, Vec<(RegId, RegId)>) {
    let tail = |r: &RegId| sigs[r.0][r.1].get(1..).unwrap_or(&[]);
    let constant = |r: &RegId| tail(r).iter().all(|w| *w == 0) || tail(r).iter().all(|w| *w == !0);
    let mut out = Vec::with_capacity(classes.len());
    let mut pairs = Vec::new();
    for cl in classes {
        if cl.len() < 2 || !cl.iter().all(constant) {
            out.push(cl);
            continue;
        }
        // each name with its registers on each side; only a name once on each side pairs
        let mut by: HashMap<&str, (Vec<RegId>, Vec<RegId>)> = HashMap::new();
        for r in &cl {
            let e = by.entry(models[r.0].regs[r.1].name.as_str()).or_default();
            if models[r.0].side == Side::Golden { e.0.push(*r) } else { e.1.push(*r) }
        }
        let mut paired: HashSet<RegId> = HashSet::new();
        let mut own = Vec::new();
        for &r in &cl {
            let Some((g, v)) = by.get(models[r.0].regs[r.1].name.as_str()) else { continue };
            if models[r.0].side != Side::Golden || g.len() != 1 || v.len() != 1 {
                continue;
            }
            let m = v[0];
            for x in [r, m] {
                inv[x.0][x.1] = tail(&x).first().is_some_and(|w| w & 1 == 1);
            }
            paired.extend([r, m]);
            pairs.push((r, m));
            own.push(vec![r, m]);
        }
        let rest: Vec<RegId> = cl.into_iter().filter(|r| !paired.contains(r)).collect();
        if !rest.is_empty() {
            out.push(rest);
        }
        out.extend(own);
    }
    (out, pairs)
}

/// The name-proposed pairs ([`split_constant_classes_by_name`]) in the report: how many, and
/// which refinement split (a pair is kept only while both stay in one class).
fn name_pairs_kept(models: &[&Model], classes: &[Vec<RegId>], pairs: &[(RegId, RegId)], rep: &mut MapReport) {
    let at: HashMap<RegId, usize> = classes.iter().enumerate().flat_map(|(i, c)| c.iter().map(move |r| (*r, i))).collect();
    let name = |r: &RegId| models[r.0].regs[r.1].name.clone();
    rep.name_pairs = pairs.len();
    rep.name_pairs_rejected = pairs.iter().filter(|(g, r)| at.get(g) != at.get(r)).map(|(g, r)| (name(g), name(r))).collect();
}

/// The BDD of each of `nets` in one model, in `bdd`, a free input by its variable name and a
/// register's state by its class: `var(name)` gives the variable. `None` once the manager is
/// exhausted. `f` holds the nodes already built in `bdd` by net: a gate whose output is in it is
/// neither searched through nor built again. It is valid only for this manager and this
/// numbering of classes (one refinement round, [`SharedRound`]); pass an empty map otherwise.
fn next_state_bdds<'m>(
    model: &'m Model,
    nets: &[String],
    bdd: &mut Bdd,
    var: &mut dyn FnMut(&mut Bdd, &str) -> u32,
    class_var: &dyn Fn(&str) -> (String, bool),
    f: &mut FxHashMap<&'m str, u32>,
) -> Result<Option<Vec<u32>>, String> {
    let c = &model.cone;
    // the gates the nets need and `f` lacks, by depth-first search without recursion, then in
    // cone order
    let mut need: FxHashSet<usize> = FxHashSet::default();
    let mut stack: Vec<usize> = nets.iter().filter(|n| !f.contains_key(n.as_str())).filter_map(|n| model.gate.get(n).copied()).collect();
    while let Some(k) = stack.pop() {
        if !need.insert(k) {
            continue;
        }
        for s in &c.gates[k].ins {
            if let Src::Net(n) = s {
                if let Some(&j) = model.gate.get(n) {
                    if !need.contains(&j) && !f.contains_key(n.as_str()) {
                        stack.push(j);
                    }
                }
            }
        }
    }
    let mut order: Vec<usize> = need.into_iter().collect();
    order.sort_unstable();
    for k in order {
        let g = &c.gates[k];
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
        member_next(models, members[i], bdd, var, class_of, &mut FxHashMap::default())
    };
    Ok(chunked_keys(members.len(), limit, &mut build)?.0)
}

/// Register `r`'s next-state function, its state read as its class's variable and complemented
/// when it is inverted in its class, built into `bdd` reusing `built` ([`next_state_bdds`]).
fn member_next<'m>(
    models: &[&'m Model],
    r: RegId,
    bdd: &mut Bdd,
    var: &mut dyn FnMut(&mut Bdd, &str) -> u32,
    class_of: &[ClassOf],
    built: &mut FxHashMap<&'m str, u32>,
) -> Result<Option<u32>, String> {
    let (m, k) = r;
    let co = &class_of[m];
    let cv = |s: &str| {
        let (c, neg) = co.get(s).copied().unwrap_or((usize::MAX, false));
        (format!("class {c}"), neg)
    };
    let net = next_net(&models[m].regs[k].instance);
    let neg = co.get(&state_net(&models[m].regs[k].instance)).is_some_and(|x| x.1);
    // an inverted member's next value is compared complemented, as the class's value
    Ok(next_state_bdds(models[m], &[net], bdd, var, &cv, built)?.map(|v| if neg { bdd.not(v[0]) } else { v[0] }))
}

/// `a` and `b` load the same next value with every class holding one value: proved, not
/// undecided within the budget. One prover per set of assumed classes: under SAT its solver
/// keeps the gates it encoded for every pair asked of it (one incremental solver, as a round).
struct SameNext<'m> {
    #[cfg_attr(not(feature = "sat"), allow(dead_code))]
    engine: Refine,
    #[cfg(feature = "sat")]
    sat: sat::RoundSolver<'m>,
    #[cfg(not(feature = "sat"))]
    _m: std::marker::PhantomData<&'m ()>,
}

impl<'m> SameNext<'m> {
    fn new(engine: Refine, models: usize) -> SameNext<'m> {
        #[cfg(feature = "sat")]
        return SameNext { engine, sat: sat::RoundSolver::new(models, PAIR_CONFLICTS) };
        #[cfg(not(feature = "sat"))]
        {
            let _ = models;
            SameNext { engine, _m: std::marker::PhantomData }
        }
    }

    fn same(&mut self, models: &[&'m Model], a: RegId, b: RegId, class_of: &[ClassOf]) -> Result<bool, String> {
        #[cfg(feature = "sat")]
        if self.engine != Refine::Bdd {
            return self.sat.same_next(models, a, b, class_of);
        }
        let k = next_keys(models, &[a, b], class_of, BDD_LIMIT)?;
        Ok(matches!((&k[0], &k[1]), (Some(x), Some(y)) if x == y))
    }
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
/// Stage 4 by the chosen engine ([`Refine`]).
fn refine_by(engine: Refine, models: &[&Model], classes: &mut Vec<Vec<RegId>>, inv: &Polarity, limit: i32, effort: &mut SatEffort) -> Result<(usize, Vec<RegId>), String> {
    match engine {
        Refine::Bdd => refine(models, classes, inv),
        #[cfg(feature = "sat")]
        Refine::Sat => sat::refine_sat(models, classes, inv, limit, effort),
        #[cfg(feature = "sat")]
        Refine::Both => {
            let got = sat::refine_sat(models, classes, inv, limit, effort)?;
            (effort.bdd_checked, effort.bdd_unchecked) = sat::cross_check_with_bdd(models, classes, inv)?;
            Ok(got)
        }
        #[cfg(not(feature = "sat"))]
        Refine::Sat | Refine::Both => {
            let _ = (effort, limit);
            Err("map --refine sat|both needs the `sat` feature (built without it)".into())
        }
    }
}

pub(crate) fn refine(models: &[&Model], classes: &mut Vec<Vec<RegId>>, inv: &Polarity) -> Result<(usize, Vec<RegId>), String> {
    refine_within(models, classes, inv, BDD_LIMIT)
}

/// [`refine`] with each manager limited to `limit` nodes plus memo entries.
pub(crate) fn refine_within(models: &[&Model], classes: &mut Vec<Vec<RegId>>, inv: &Polarity, limit: usize) -> Result<(usize, Vec<RegId>), String> {
    let readers = readers_of(models);
    let mut undecided: Vec<RegId> = Vec::new();
    let mut seeds: Option<Vec<RegId>> = None;
    let mut rounds = 0;
    loop {
        rounds += 1;
        let class_of = class_index(models, classes, &|r: RegId| inv[r.0][r.1]);
        let active = active_classes(models, classes, &readers, seeds.as_deref());
        let keys = round_keys(models, classes, &active, &class_of, limit)?;
        let split = split_on_keys(classes, keys, &mut undecided);
        if split.is_empty() {
            return Ok((rounds, undecided));
        }
        seeds = Some(split);
    }
}

/// Per model, the one-frame fanout graph [`active_classes`] walks forward from a round's seeds:
/// which gates read each net, and which registers load each net. Static: built once per
/// refinement, in time linear in the cone (a per-register walk of each cone is quadratic on a
/// core: every register re-walks the shared logic).
pub(crate) struct Fanout<'m> {
    /// per model: net -> gates reading it
    readers: Vec<FxHashMap<&'m str, Vec<usize>>>,
    /// per model: net -> registers whose next-state net it is
    loads: Vec<FxHashMap<String, Vec<usize>>>,
    /// per model: each register's state net
    state: Vec<Vec<String>>,
}

fn readers_of<'m>(models: &[&'m Model]) -> Fanout<'m> {
    let mut f = Fanout { readers: Vec::new(), loads: Vec::new(), state: Vec::new() };
    for model in models {
        let mut readers: FxHashMap<&str, Vec<usize>> = FxHashMap::default();
        for (g, gate) in model.cone.gates.iter().enumerate() {
            for s in &gate.ins {
                if let Src::Net(n) = s {
                    readers.entry(n.as_str()).or_default().push(g);
                }
            }
        }
        let mut loads: FxHashMap<String, Vec<usize>> = FxHashMap::default();
        for (k, r) in model.regs.iter().enumerate() {
            loads.entry(next_net(&r.instance)).or_default().push(k);
        }
        f.readers.push(readers);
        f.loads.push(loads);
        f.state.push(model.regs.iter().map(|r| state_net(&r.instance)).collect());
    }
    f
}

/// Which classes a round re-keys: every class in the first round; afterwards, a class with a
/// member that READS a register of a class the previous round split (`seeds`, [`readers_of`]).
///
/// 🔑 The rule is ABC's incremental `&scorr` filter (`cecCorrIncr.c`): seeds are the nodes whose
/// representative changed since the last round, their one-frame transitive fanout is marked,
/// and only a candidate pair with an endpoint in it is proved again. Here every member of a
/// split class is a seed (its class variable changed: the alias edge from representative to
/// member), and a class's key reads only the classes of the registers in its next-state cones.
/// A class none of whose members reads a seed has the same keys as last round, which did not
/// split it, so it would not split now: skipping it changes no partition and no round count.
///
/// Per round, as ABC marks it: forward from each seed's state net through the gates that read
/// it, to the registers that load what it reaches; one mark per gate, so a round costs at most
/// one pass over the cone.
fn active_classes(models: &[&Model], classes: &[Vec<RegId>], fanout: &Fanout<'_>, seeds: Option<&[RegId]>) -> Vec<bool> {
    let Some(seeds) = seeds else { return vec![true; classes.len()] };
    let mut hit: Vec<Vec<bool>> = models.iter().map(|m| vec![false; m.regs.len()]).collect();
    let mut seen: Vec<Vec<bool>> = models.iter().map(|m| vec![false; m.cone.gates.len()]).collect();
    for &(m, j) in seeds {
        let mut stack: Vec<&str> = vec![fanout.state[m][j].as_str()];
        while let Some(n) = stack.pop() {
            for &k in fanout.loads[m].get(n).into_iter().flatten() {
                hit[m][k] = true;
            }
            for &g in fanout.readers[m].get(n).into_iter().flatten() {
                if !std::mem::replace(&mut seen[m][g], true) {
                    stack.push(models[m].cone.gates[g].out.as_str());
                }
            }
        }
    }
    classes.iter().map(|c| c.iter().any(|&(m, k)| hit[m][k])).collect()
}

/// Each active class's member keys ([`next_keys`]), `None` for a class not re-keyed.
///
/// 🔑 One manager is shared by the classes of a round ([`SharedRound`]), so a cone two classes
/// read is built once. A class that exhausts it is keyed on its own exactly as before
/// ([`next_keys`], fresh managers) and a fresh shared manager follows: a key is still compared
/// only within its class, and within one manager equal nodes are equal functions.
fn round_keys(models: &[&Model], classes: &[Vec<RegId>], active: &[bool], class_of: &[ClassOf], limit: usize) -> Result<Vec<Option<Vec<Option<Key>>>>, String> {
    let mut out: Vec<Option<Vec<Option<Key>>>> = vec![None; classes.len()];
    let mut shared = SharedRound::new(models.len(), limit);
    for (ci, cl) in classes.iter().enumerate() {
        if cl.len() < 2 || !active[ci] {
            continue;
        }
        out[ci] = Some(match shared.keys(models, cl, class_of)? {
            Some(k) => k,
            None => {
                shared = SharedRound::new(models.len(), limit);
                next_keys(models, cl, class_of, limit)?
            }
        });
    }
    Ok(out)
}

/// A round's shared manager: the BDD, its variable numbering by name, and per model the nodes
/// built so far by net ([`next_state_bdds`]).
struct SharedRound<'m> {
    bdd: Bdd,
    names: FxHashMap<String, u32>,
    built: Vec<FxHashMap<&'m str, u32>>,
}

impl<'m> SharedRound<'m> {
    fn new(models: usize, limit: usize) -> SharedRound<'m> {
        SharedRound { bdd: Bdd::with_limit(limit), names: FxHashMap::default(), built: vec![FxHashMap::default(); models] }
    }

    /// Every member's key in this manager, or `None` once it is exhausted.
    fn keys(&mut self, models: &[&'m Model], members: &[RegId], class_of: &[ClassOf]) -> Result<Option<Vec<Option<Key>>>, String> {
        let mut keys = Vec::with_capacity(members.len());
        for &r in members {
            let names = &mut self.names;
            let mut var = |bdd: &mut Bdd, name: &str| -> u32 {
                let next = names.len() as u32;
                let k = *names.entry(name.to_string()).or_insert(next);
                bdd.var(k)
            };
            match member_next(models, r, &mut self.bdd, &mut var, class_of, &mut self.built[r.0])? {
                Some(node) if !self.bdd.exhausted() => keys.push(Some(Key::Node(node))),
                _ => return Ok(None),
            }
        }
        Ok(Some(keys))
    }
}

/// Splits each re-keyed class by its members' keys, in order of first appearance (a member
/// undecided within the budget stands alone and is added to `undecided`); returns every member
/// of a class that split, the next round's seeds ([`active_classes`]).
fn split_on_keys(classes: &mut Vec<Vec<RegId>>, keys: Vec<Option<Vec<Option<Key>>>>, undecided: &mut Vec<RegId>) -> Vec<RegId> {
    let mut next: Vec<Vec<RegId>> = Vec::with_capacity(classes.len());
    let mut split = Vec::new();
    for (cl, keys) in classes.iter().zip(keys) {
        let Some(keys) = keys else {
            next.push(cl.clone());
            continue;
        };
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
        if parts.len() > 1 {
            split.extend(cl.iter().copied());
        }
        next.extend(parts);
    }
    *classes = next;
    split
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
    // a pair is proved by the engine that proved the classes
    let engine = rep.refine;
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
        pair_leftovers(gn, rn, &mut pairs, &mut |p: &[(usize, usize)]| follows(models, classes, &pol, &gold, &rev, p, engine))?;
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
    let mut prover = SameNext::new(engine, models.len());
    for &(i, j) in &pairs {
        let pair = (name(&gold[i]), name(&rev[j]));
        match prover.same(models, gold[i], rev[j], &class_of)? {
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
fn follows(models: &[&Model], classes: &[Vec<RegId>], pol: &dyn Fn(RegId) -> bool, gold: &[RegId], rev: &[RegId], pairs: &[(usize, usize)], engine: Refine) -> Result<usize, String> {
    let class_of = class_index(models, &assumed_classes(models, classes, gold, rev, pairs), pol);
    let mut n = 0;
    let mut prover = SameNext::new(engine, models.len());
    for &(i, j) in pairs {
        if prover.same(models, gold[i], rev[j], &class_of)? {
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
        let st = Stimulus { held: [("rst_n".to_string(), true)].into_iter().collect(), ..Default::default() };
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

    /// 🔑 A register WITHOUT reset is undefined until it loads ([`defined_signature`]). Golden `r`
    /// holds `d` under `en`; revised `u` holds the complement (`!d` in, read through an inverter),
    /// as two syntheses may store one RTL register. Neither has a reset, so from an all-zero
    /// start `r` read 0 and `u` read 1 until the first load: the signatures were neither equal
    /// nor complementary and the pair was never proposed. Undefined until loaded, they share a
    /// class (inverted) and the proof maps them.
    #[test]
    fn a_register_without_reset_stored_complemented_maps_inverted() {
        let g = nl("module t(clk,en,d,q);\ninput clk,en,d; output q;\nwire n,s;\n\
             MUX2 m(.A0(s),.A1(d),.S(en),.Y(n));\nDFF r(.CK(clk),.D(n),.Q(s));\nBUF b(.A(s),.Y(q));\nendmodule\n");
        let m = nl("module t(clk,en,d,q);\ninput clk,en,d; output q;\nwire nd,n,s;\n\
             INV i(.A(d),.Y(nd));\nMUX2 m(.A0(s),.A1(nd),.S(en),.Y(n));\nDFF u(.CK(clk),.D(n),.Q(s));\nINV o(.A(s),.Y(q));\nendmodule\n");
        let rep = map(&g, &m);
        assert_eq!(rep.inverted, [("r".to_string(), "u".to_string())].into_iter().collect(), "{rep:?}");
        assert!(rep.one_to_one(), "{rep:?}");
    }

    /// Three-valued gate evaluation is exact per gate: AND with a 0 is defined, with a 1 is not;
    /// an XOR of an undefined input is never defined; a MUX whose select is defined passes the
    /// selected input's definedness.
    #[test]
    fn a_gate_output_is_defined_only_where_every_undefined_input_agrees() {
        let and = |x: &[u64]| -> Result<u64, String> { Ok(x[0] & x[1]) };
        // bit 0: a=0 defined, b undefined -> defined 0; bit 1: a=1, b undefined -> undefined
        assert_eq!(ternary_word(&[0b10, 0], &[!0, !0b11], and).unwrap().1 & 0b11, 0b01);
        let xor = |x: &[u64]| -> Result<u64, String> { Ok(x[0] ^ x[1]) };
        assert_eq!(ternary_word(&[0, 0], &[!0, !1], xor).unwrap().1 & 1, 0);
        let mux = |x: &[u64]| -> Result<u64, String> { Ok((x[2] & x[1]) | (!x[2] & x[0])) };
        // select 1 picks the defined input 1; the undefined input 0 does not matter
        let (y, k) = ternary_word(&[0, 1, 1], &[!1, !0, !0], mux).unwrap();
        assert_eq!((y & 1, k & 1), (1, 1));
    }

    /// The canonical fill: two registers complementary wherever defined, with the same defined
    /// pattern, get complementary signatures, including a run never defined.
    #[test]
    fn complementary_registers_get_complementary_signatures_whatever_their_undefined_start() {
        // run 0 defined from cycle 2, run 1 never defined; storage starts 0 in both (undefined)
        let k = [0b00, 0b00, 0b01, 0b01];
        let a = defined_signature(&[0, 0, 1, 0], &k);
        let b = defined_signature(&[0, 0, 0, 1], &k);
        assert!(a.iter().zip(&b).all(|(x, y)| x ^ y == !0), "{a:?} {b:?}");
        // never defined at all: constant 0
        assert!(defined_signature(&[5, 7], &[0, 0]).iter().all(|w| *w == 0));
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

    /// ⛔ A never-toggling class is split by NAME, and a name only proposes. All six registers
    /// below stay 0 (or 1) while `te` is held at 0, so simulation puts them in one class.
    /// `s` (D = te both sides) is proved; `r` (D = te vs te & d) is same-named but NOT
    /// equivalent with te free, so refinement splits it and the report lists it; `p` stores te
    /// in the golden and !te in the revised (constants 0 and 1), so it pairs INVERTED.
    #[test]
    fn a_never_toggling_class_is_split_by_name_and_each_pair_still_proved() {
        let holds = SimHolds { hold: [("te".to_string(), false)].into_iter().collect(), ..Default::default() };
        let g = nl("module t(clk,te,d,q1,q2,q3);\ninput clk,te,d; output q1,q2,q3;\n\
             DFF s(.CK(clk),.D(te),.Q(q1));\nDFF r(.CK(clk),.D(te),.Q(q2));\nDFF p(.CK(clk),.D(te),.Q(q3));\nendmodule\n");
        let m = nl("module t(clk,te,d,q1,q2,q3);\ninput clk,te,d; output q1,q2,q3;\nwire a, n;\n\
             AND2 x(.A(te),.B(d),.Y(a));\nINV i(.A(te),.Y(n));\n\
             DFF s(.CK(clk),.D(te),.Q(q1));\nDFF r(.CK(clk),.D(a),.Q(q2));\nDFF p(.CK(clk),.D(n),.Q(q3));\nendmodule\n");
        let rep = register_map_with(&g, &m, &lib(), (Naming::Instance, Naming::Instance), &holds, Refine::Bdd).unwrap();
        assert_eq!(rep.name_pairs, 3, "{rep:?}");
        assert_eq!(rep.mapped.get("s").map(String::as_str), Some("s"), "{rep:?}");
        assert!(!rep.mapped.contains_key("r") && !rep.inverted.contains_key("r"), "same name, not equivalent: {rep:?}");
        assert_eq!(rep.name_pairs_rejected, [("r".to_string(), "r".to_string())], "{rep:?}");
        assert_eq!(rep.inverted.get("p").map(String::as_str), Some("p"), "complementary constants pair inverted: {rep:?}");
    }

    /// 🔑 Refinement re-keys a class when a class its members READ split the round before (ABC's
    /// incremental `&scorr` filter), with one manager per round. `a` (D = te vs te & d) splits in
    /// round 1; `b` reads `a` and only splits in round 2, once `a`'s two registers are separate
    /// classes; round 3 splits nothing. A filter that skipped `b`, or a key kept from the round
    /// before, would map `b` although it is not equivalent.
    #[test]
    fn a_class_whose_fanin_split_is_keyed_again_in_the_next_round() {
        let holds = SimHolds { hold: [("te".to_string(), false)].into_iter().collect(), ..Default::default() };
        let g = nl("module t(clk,te,d,q);\ninput clk,te,d; output q;\nwire qa;\n\
             DFF a(.CK(clk),.D(te),.Q(qa));\nDFF b(.CK(clk),.D(qa),.Q(q));\nendmodule\n");
        let m = nl("module t(clk,te,d,q);\ninput clk,te,d; output q;\nwire n, qa;\n\
             AND2 x(.A(te),.B(d),.Y(n));\nDFF a(.CK(clk),.D(n),.Q(qa));\nDFF b(.CK(clk),.D(qa),.Q(q));\nendmodule\n");
        let rep = register_map_with(&g, &m, &lib(), (Naming::Instance, Naming::Instance), &holds, Refine::Bdd).unwrap();
        assert!(rep.mapped.is_empty(), "{rep:?}");
        assert_eq!(rep.rounds, 3, "{rep:?}");
        let rejected: Vec<&str> = rep.name_pairs_rejected.iter().map(|p| p.0.as_str()).collect();
        assert_eq!(rejected, ["a", "b"], "{rep:?}");
    }

    /// ⛔ `--hold` / `--reset` act on the candidate simulation ONLY. A held input is constant and a
    /// given reset is active for [`RESET_CYCLES`] then inactive, in both designs; the proof keeps
    /// every input free. Here `u` loads `d` only while the test enable `te` is 0: held at 0, `r`
    /// and `u` simulate alike, yet `refine` (te free) splits them, so nothing maps. A name that is
    /// not a primary input of both designs is refused, naming it; the report lists the holds.
    #[test]
    fn simulation_holds_shape_candidates_and_never_the_proof() {
        let holds = SimHolds {
            hold: [("te".to_string(), false)].into_iter().collect(),
            reset: [("rst_n".to_string(), true)].into_iter().collect(),
        };
        let st = Stimulus::default().with(&holds);
        for c in 0..CYCLES {
            assert_eq!(st.word("te", c), 0, "held in cycle {c}");
            assert_eq!(st.word("rst_n", c), if c < RESET_CYCLES { 0 } else { !0 }, "reset in cycle {c}");
        }
        let g = nl("module t(clk,rst_n,te,si,d,q);\ninput clk,rst_n,te,si,d; output q;\n\
             DFR r(.CK(clk),.D(d),.RESET_B(rst_n),.Q(q));\nendmodule\n");
        let m = nl("module t(clk,rst_n,te,si,d,q);\ninput clk,rst_n,te,si,d; output q;\nwire n;\n\
             MUX2 x(.A0(d),.A1(si),.S(te),.Y(n));\nDFR u(.CK(clk),.D(n),.RESET_B(rst_n),.Q(q));\nendmodule\n");
        let l = lib();
        let (gd, md) = (Design::register_model(&g, &l), Design::register_model(&m, &l));
        let (gm, mm) = (model(&gd, Side::Golden, Naming::Instance).unwrap(), model(&md, Side::Revised, Naming::Instance).unwrap());
        let held = Stimulus::of(&[&gd, &md]).with(&holds);
        let (sigs, _) = simulate_freeing_stuck_enables(&[&gm, &mm], &held).unwrap();
        assert_eq!(sigs[0][0], sigs[1][0], "held, r and u are candidates");
        let rep = register_map_with(&g, &m, &l, (Naming::Instance, Naming::Instance), &holds, Refine::Bdd).unwrap();
        assert!(rep.mapped.is_empty(), "the proof keeps te free: {rep:?}");
        assert_eq!(rep.holds, [("te".to_string(), false)]);
        assert_eq!(rep.resets_given, [("rst_n".to_string(), true)]);
        let bad = SimHolds { hold: [("tee".to_string(), false)].into_iter().collect(), ..Default::default() };
        let e = register_map_with(&g, &m, &l, (Naming::Instance, Naming::Instance), &bad, Refine::Bdd).unwrap_err();
        assert!(e.contains("`tee` is not a primary input"), "{e}");
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

    /// 🔑 By SAT (ABC `&scorr`): a pair simulation cannot tell apart shares a candidate class,
    /// the solver finds the state that tells them apart, and that counter-example is resimulated
    /// over every register before the class is split (`Cec_ManResimulateCounterExamples`). The
    /// revised design adds `h`, which loads `d0 ^ c6`: it toggles with `r0` until the 8-bit
    /// counter's carry out first rises (cycle 255, past the [`CYCLES`] simulated). The counter has
    /// a reset: without one it is undefined forever ([`defined_signature`]), so simulation would
    /// propose nothing for the solver to disprove.
    #[cfg(feature = "sat")]
    #[test]
    fn a_pair_the_solver_disproves_is_split_and_its_counter_example_resimulated() {
        let mut body = String::new();
        // counts every cycle: `c0` is tied high, not an input simulation drives at random
        let mut wires = vec!["c0".to_string(), "lo".to_string()];
        body.push_str("TIE0 t0(.LO(lo));\nINV b0(.A(lo),.Y(c0));\n");
        for i in 0..8 {
            wires.extend([format!("q{i}"), format!("d{i}"), format!("c{}", i + 1)]);
            body.push_str(&format!(
                "XOR2 x{i}(.A(c{i}),.B(q{i}),.Y(d{i}));\nDFR r{i}(.CK(clk),.D(d{i}),.RESET_B(rst_n),.Q(q{i}));\nAND2 a{i}(.A(c{i}),.B(q{i}),.Y(c{}));\n",
                i + 1
            ));
        }
        let top = |extra: &str| nl(&format!("module t(clk,rst_n,y);\ninput clk,rst_n; output y;\nwire {};\n{body}{extra}endmodule\n", wires.join(",")));
        let a = top("BUF o(.A(q5),.Y(y));\n");
        let b = top("wire h, hd;\nXOR2 hx(.A(d0),.B(c8),.Y(hd));\nDFR h(.CK(clk),.D(hd),.RESET_B(rst_n),.Q(h));\nAND2 o(.A(q5),.B(h),.Y(y));\n");
        let names = (Naming::Instance, Naming::Instance);
        let rep = register_map_with(&a, &b, &lib(), names, &SimHolds::default(), Refine::Sat).unwrap();
        assert!(rep.sat.disproved > 0 && rep.sat.resimulated > 0, "{:?}", rep.sat);
        assert!(rep.unmatched_revised.contains_key("h"), "{rep:?}");
        for i in 0..8 {
            assert_eq!(rep.mapped.get(&format!("r{i}")).map(String::as_str), Some(format!("r{i}").as_str()), "{rep:?}");
        }
        // the same classes as the BDD keys, and `both` re-checks every class
        let bdd = register_map_with(&a, &b, &lib(), names, &SimHolds::default(), Refine::Bdd).unwrap();
        let both = register_map_with(&a, &b, &lib(), names, &SimHolds::default(), Refine::Both).unwrap();
        assert_eq!((&rep.mapped, &rep.unmatched_revised), (&bdd.mapped, &bdd.unmatched_revised));
        assert!(both.sat.bdd_checked > 0 && both.sat.bdd_unchecked == 0, "{:?}", both.sat);
    }

    /// ⛔ An obligation over its conflict limit leaves its member undecided and alone, never
    /// mapped (ABC `Gia_ManCheckRefinements`, status -1: `Cec_ManSimClassRemoveOne`). Golden
    /// loads `a ^ q`, revised the same value as `(a | q) & !(a & q)`: equal, but only by search,
    /// so at a limit of 0 conflicts neither is mapped and both are undecided.
    #[cfg(feature = "sat")]
    #[test]
    fn a_pair_over_the_conflict_limit_is_undecided_and_never_mapped() {
        let a = nl("module t(clk,a,y);\ninput clk,a; output y;\nwire q,d;\nXOR2 x(.A(a),.B(q),.Y(d));\nDFF r(.CK(clk),.D(d),.Q(q));\nBUF o(.A(q),.Y(y));\nendmodule\n");
        let b = nl("module t(clk,a,y);\ninput clk,a; output y;\nwire q,d,o1,a1,n1;\nOR2 g1(.A(a),.B(q),.Y(o1));\nAND2 g2(.A(a),.B(q),.Y(a1));\nINV g3(.A(a1),.Y(n1));\nAND2 g4(.A(o1),.B(n1),.Y(d));\nDFF r(.CK(clk),.D(d),.Q(q));\nBUF o(.A(q),.Y(y));\nendmodule\n");
        let names = (Naming::Instance, Naming::Instance);
        let proved = register_map_at(&a, &b, &lib(), names, &SimHolds::default(), Refine::Sat, PAIR_CONFLICTS).unwrap();
        assert_eq!(proved.mapped.get("r").map(String::as_str), Some("r"), "{proved:?}");
        let capped = register_map_at(&a, &b, &lib(), names, &SimHolds::default(), Refine::Sat, 0).unwrap();
        assert!(capped.sat.gave_up > 0, "{:?}", capped.sat);
        assert!(capped.mapped.is_empty(), "{capped:?}");
        // both of the pair: the head is not disproved, nothing told it apart
        assert_eq!(capped.undecided.len(), 2, "{capped:?}");
        assert!(capped.unmatched_golden.is_empty() && capped.unmatched_revised.is_empty(), "{capped:?}");
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
