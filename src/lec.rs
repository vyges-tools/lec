//! Combinational **logic equivalence** check.
//!
//! Build a canonical ROBDD for every endpoint (primary output / flop data pin) of
//! the golden and the revised netlist in **one shared package over one shared
//! variable order**, then compare: two endpoints are equivalent *iff* their BDDs
//! are the same node. When they differ, the miter (their XOR) yields a concrete
//! input **counter-example**.
//!
//! Gate functions come from the Liberty `function` of the output pin, else from a
//! built-in standard-cell primitive map (keyed on the cell name's logic prefix —
//! INV/BUF/AND/OR/NAND/NOR/XOR/XNOR/MUX); the Liberty gives pin directions and tells
//! combinational cells from sequential. Sequential
//! state is cut at the registers: flop outputs are free inputs (`inst/Q`), flop data
//! pins are endpoints (`inst/D`) — i.e. this proves the *combinational* logic between
//! registers, the standard combinational-LEC model (registers matched by instance name).

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::bdd::Bdd;
use crate::liberty::{Cell, Dir, Lib};
use crate::netlist::{Inst, Netlist};
use vyges_loom::liberty_func::Func;

#[derive(Debug, Clone)]
pub struct Mismatch {
    pub endpoint: String,
    /// a primary-input assignment under which the two designs differ
    pub counterexample: Vec<(String, bool)>,
}

#[derive(Debug, Default)]
pub struct LecReport {
    pub equivalent: bool,
    pub compared: usize,
    pub mismatches: Vec<Mismatch>,
    pub only_in_golden: Vec<String>,
    pub only_in_revised: Vec<String>,
    /// The engine gave up within its limits (the ABC engine only): neither proved nor disproved.
    pub undecided: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Op {
    Buf,
    Not,
    And,
    Or,
    Nand,
    Nor,
    Xor,
    Xnor,
    Mux,
}

/// Map a cell name to a primitive logic op by its prefix (longer keywords first so
/// NAND beats AND, XNOR beats XOR, …).
fn op_of(cell: &str) -> Option<Op> {
    let c = cell.to_ascii_uppercase();
    let has = |k: &str| c.contains(k);
    if has("XNOR") {
        Some(Op::Xnor)
    } else if has("NAND") {
        Some(Op::Nand)
    } else if has("XOR") {
        Some(Op::Xor)
    } else if has("NOR") {
        Some(Op::Nor)
    } else if has("MUX") {
        Some(Op::Mux)
    } else if has("INV") || c.starts_with("NOT") {
        Some(Op::Not)
    } else if has("BUF") {
        Some(Op::Buf)
    } else if has("AND") {
        Some(Op::And)
    } else if has("OR") {
        Some(Op::Or)
    } else {
        None
    }
}

fn net_of<'a>(inst: &'a Inst, pin: &str) -> Option<&'a str> {
    inst.conns
        .iter()
        .find(|(p, _)| p == pin)
        .map(|(_, n)| n.as_str())
}

/// A gate's logic: the Liberty `function` of the pin it drives, else the primitive its cell name
/// says (a library with no `function` attributes).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Logic {
    Prim(Op),
    Func(Func),
}

/// The logic of `inst` at output `out_pin`, and its input pins in the cell's pin order. With a
/// `function`, the inputs are the pins it names (a tie cell's `"1"` names none); without one, every
/// input pin but a clock. ⛔ A `function` that does not parse over the cell's input pins is an
/// error, never a fall back to the name: the name is only a guess.
fn logic_of(inst: &Inst, cell: &Cell, out_pin: &str) -> Result<(Logic, Vec<String>), String> {
    let inputs: Vec<&str> = cell
        .pins
        .iter()
        .filter(|(n, p)| p.direction == Dir::In && cell.clock_pin.as_deref() != Some(n))
        .map(|(n, _)| n.as_str())
        .collect();
    if let Some(f) = cell.pins.get(out_pin).and_then(|p| p.function.as_deref()) {
        let func = Func::parse_in(f, |p| inputs.contains(&p)).ok_or_else(|| {
            format!("cell `{}` pin `{out_pin}`: function `{f}` does not parse over its input pins", inst.cell)
        })?;
        let named = func.ports();
        let pins = inputs.iter().filter(|p| named.contains(p)).map(|p| p.to_string()).collect();
        return Ok((Logic::Func(func), pins));
    }
    let op = op_of(&inst.cell).ok_or_else(|| format!("cell `{}` is not a known logic primitive", inst.cell))?;
    Ok((Logic::Prim(op), inputs.iter().map(|p| p.to_string()).collect()))
}

/// A `function` over BDDs, `ins[k]` standing for `pins[k]`.
fn func_bdd(bdd: &mut Bdd, f: &Func, pins: &[String], ins: &[u32]) -> u32 {
    match f {
        Func::Port(p) => ins[pins.iter().position(|x| x == p).expect("logic_of keeps every named pin")],
        Func::Not(a) => {
            let a = func_bdd(bdd, a, pins, ins);
            bdd.not(a)
        }
        Func::And(a, b) | Func::Or(a, b) | Func::Xor(a, b) => {
            let (x, y) = (func_bdd(bdd, a, pins, ins), func_bdd(bdd, b, pins, ins));
            match f {
                Func::And(..) => bdd.and(x, y),
                Func::Or(..) => bdd.or(x, y),
                _ => bdd.xor(x, y),
            }
        }
        Func::One => bdd.one(),
        Func::Zero => bdd.zero(),
    }
}

/// A `function`'s value, `x[k]` standing for `pins[k]`.
#[cfg_attr(not(feature = "abc"), allow(dead_code))]
pub(crate) fn func_value(f: &Func, pins: &[String], x: &[bool]) -> bool {
    match f {
        Func::Port(p) => x[pins.iter().position(|q| q == p).expect("logic_of keeps every named pin")],
        Func::Not(a) => !func_value(a, pins, x),
        Func::And(a, b) => func_value(a, pins, x) && func_value(b, pins, x),
        Func::Or(a, b) => func_value(a, pins, x) || func_value(b, pins, x),
        Func::Xor(a, b) => func_value(a, pins, x) != func_value(b, pins, x),
        Func::One => true,
        Func::Zero => false,
    }
}

/// A primitive's value, `x[k]` standing for `pins[k]` (the same rules as [`apply_op`]).
#[cfg_attr(not(feature = "abc"), allow(dead_code))]
pub(crate) fn prim_value(op: Op, pins: &[String], x: &[bool]) -> Result<bool, String> {
    let need = |n: usize| if x.len() == n { Ok(()) } else { Err(format!("primitive expected {n} input(s), got {}", x.len())) };
    if x.is_empty() && !matches!(op, Op::Mux) {
        return Err("primitive needs inputs".into());
    }
    let (and, or, odd) = (x.iter().all(|&v| v), x.iter().any(|&v| v), x.iter().filter(|&&v| v).count() % 2 == 1);
    Ok(match op {
        Op::Buf => { need(1)?; x[0] }
        Op::Not => { need(1)?; !x[0] }
        Op::And => and,
        Op::Nand => !and,
        Op::Or => or,
        Op::Nor => !or,
        Op::Xor => odd,
        Op::Xnor => !odd,
        Op::Mux => {
            need(3)?;
            let idx = |want: &str| pins.iter().position(|p| p.eq_ignore_ascii_case(want));
            let (Some(a), Some(b), Some(s)) = (idx("A"), idx("B"), idx("S")) else { return Err("MUX needs pins A, B, S".into()) };
            if x[s] { x[b] } else { x[a] }
        }
    })
}

/// What drives a gate's input pin: a net, or a constant the netlist ties the pin to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Src {
    Net(String),
    Const(bool),
}

/// The source of input `pin`: its net, else its tie (`.B(1'b0)`).
/// ⛔ A tie is an input like any other: dropping it would turn `AND2(a, 1'b0)` into `a`.
/// ⛔ An unconnected input is an error, not a dropped input: it floats, and skipping it would turn
/// `AND2(a, <open>)` into `a` just the same.
fn src_of(inst: &Inst, pin: &str) -> Result<Src, String> {
    net_of(inst, pin)
        .map(|n| Src::Net(n.to_string()))
        .or_else(|| inst.ties.iter().find(|(p, _)| p == pin).map(|&(_, v)| Src::Const(v)))
        .ok_or_else(|| format!("input pin `{pin}` of instance `{}` ({}) is unconnected", inst.name, inst.cell))
}

/// One design's view: net -> (inst index, output pin); plus the netlist + lib.
pub(crate) struct Design<'a> {
    nl: &'a Netlist,
    lib: &'a Lib,
    driver: BTreeMap<&'a str, (usize, &'a str)>,
    /// Nets touching an instance whose cell is NOT in the Liberty: net -> that instance. Without
    /// the cell's pin directions nothing says whether the instance drives the net.
    unknown: BTreeMap<&'a str, &'a str>,
    /// Nets a `supply0` / `supply1` declaration holds constant (loom `Netlist.constants`).
    constants: BTreeMap<&'a str, bool>,
    /// Registers are state, not cut points: a register output is a gate over the register's
    /// stored value ([`seq_cone`]) instead of a free input.
    sequential: bool,
}

impl<'a> Design<'a> {
    pub(crate) fn new(nl: &'a Netlist, lib: &'a Lib) -> Design<'a> {
        let mut driver = BTreeMap::new();
        let mut unknown = BTreeMap::new();
        for (i, inst) in nl.insts.iter().enumerate() {
            if let Some(cell) = lib.cells.get(&inst.cell) {
                for (pin, net) in &inst.conns {
                    if cell.pins.get(pin).map(|p| p.direction) == Some(Dir::Out) {
                        driver.insert(net.as_str(), (i, pin.as_str()));
                    }
                }
            } else {
                for (_, net) in &inst.conns {
                    unknown.entry(net.as_str()).or_insert(inst.name.as_str());
                }
            }
        }
        let constants = nl.constants.iter().map(|(n, v)| (n.as_str(), *v)).collect();
        Design { nl, lib, driver, unknown, constants, sequential: false }
    }

    /// The design with its registers kept as state (the sequential model, [`seq_cone`]).
    #[cfg_attr(not(feature = "abc"), allow(dead_code))]
    pub(crate) fn sequential(nl: &'a Netlist, lib: &'a Lib) -> Design<'a> {
        Design { sequential: true, ..Design::new(nl, lib) }
    }

    /// Is `net` a free input of the model (a primary input, a register output, or undriven)?
    /// ⛔ An "undriven" net that touches an instance of a cell missing from the Liberty is an
    /// error, not a free input: that instance may well drive it, and treating it as free in both
    /// designs would compare it equal whatever the cell computes.
    fn is_free(&self, net: &str) -> Result<bool, String> {
        if self.nl.inputs.iter().any(|p| p == net) || (!self.sequential && self.is_seq_driver(net)) {
            return Ok(true);
        }
        if self.driver.contains_key(net) {
            return Ok(false);
        }
        match self.unknown.get(net) {
            Some(inst) => Err(format!(
                "net `{net}` connects to instance `{inst}`, whose cell `{}` is not in the Liberty",
                self.nl.insts.iter().find(|i| i.name == *inst).map(|i| i.cell.as_str()).unwrap_or("?")
            )),
            None => Ok(true),
        }
    }

    fn is_seq_driver(&self, net: &str) -> bool {
        self.seq_driver(net).is_some()
    }

    /// The register (instance, output pin) driving `net`, if a sequential cell drives it.
    fn seq_driver(&self, net: &str) -> Option<(&'a str, &'a str)> {
        let &(i, pin) = self.driver.get(net)?;
        let inst = &self.nl.insts[i];
        self.lib.cells.get(&inst.cell).filter(|c| c.is_seq).map(|_| (inst.name.as_str(), pin))
    }

    /// The name of free input `net`, shared by both designs: a register output is `inst/pin`, so a
    /// register matches by its INSTANCE name whatever its output net is called (repair renames it
    /// when it buffers an output port); any other free input is its net.
    fn var_of(&self, net: &str) -> String {
        match self.seq_driver(net) {
            Some((inst, pin)) => format!("{inst}/{pin}"),
            None => net.to_string(),
        }
    }

    /// The primary input a register's clock pin reaches through buffers (cells whose function is
    /// one input pin). ⛔ Anything else on the way (an inverter, a clock gate, logic) is an error:
    /// the sequential model has ONE clock, the same rising edge for every register.
    #[cfg_attr(not(feature = "abc"), allow(dead_code))]
    fn clock_root(&self, inst: &Inst, pin: &str) -> Result<String, String> {
        let mut net = match src_of(inst, pin)? {
            Src::Net(n) => n,
            Src::Const(_) => return Err(format!("register `{}`: clock pin `{pin}` is tied to a constant", inst.name)),
        };
        let mut seen = BTreeSet::new();
        while let Some(&(i, out)) = self.driver.get(net.as_str()) {
            let b = &self.nl.insts[i];
            let cell = &self.lib.cells[&b.cell];
            let via = match logic_of(b, cell, out) {
                Ok((Logic::Func(Func::Port(p)), _)) if !cell.is_seq => p,
                Ok((Logic::Prim(Op::Buf), pins)) if !cell.is_seq && pins.len() == 1 => pins[0].clone(),
                _ => break,
            };
            if !seen.insert(net.clone()) {
                return Err(format!("register `{}`: its clock buffers form a loop at `{net}`", inst.name));
            }
            net = match src_of(b, &via)? {
                Src::Net(n) => n,
                Src::Const(_) => return Err(format!("register `{}`: its clock is a constant", inst.name)),
            };
        }
        if self.nl.inputs.iter().any(|p| p == &net) {
            Ok(net)
        } else {
            Err(format!(
                "register `{}`: its clock reaches net `{net}`, which is not a primary input (an inverted, gated or generated clock is not modelled)",
                inst.name
            ))
        }
    }

    /// Endpoints to compare, as (key, net): primary outputs by port name, flop data pins
    /// (setup-constrained) as `inst/pin` — matched by the register, not by its data net.
    fn endpoints(&self) -> BTreeMap<String, String> {
        let mut e: BTreeMap<String, String> = self.nl.outputs.iter().map(|o| (o.clone(), o.clone())).collect();
        for inst in &self.nl.insts {
            if let Some(cell) = self.lib.cells.get(&inst.cell) {
                if cell.is_seq {
                    for (pin, p) in &cell.pins {
                        if !p.setup.is_empty() {
                            if let Some(n) = net_of(inst, pin) {
                                e.insert(format!("{}/{pin}", inst.name), n.to_string());
                            }
                        }
                    }
                }
            }
        }
        e
    }
}

/// Shared variable registry: a free net name -> a BDD variable index, consistent
/// across both designs (same name -> same variable).
struct Vars {
    map: HashMap<String, u32>,
    rev: Vec<String>,
}

impl Vars {
    fn new() -> Vars {
        Vars {
            map: HashMap::new(),
            rev: Vec::new(),
        }
    }
    fn get(&mut self, name: &str) -> u32 {
        if let Some(&i) = self.map.get(name) {
            return i;
        }
        let i = self.rev.len() as u32;
        self.map.insert(name.to_string(), i);
        self.rev.push(name.to_string());
        i
    }
    fn name(&self, idx: u32) -> &str {
        &self.rev[idx as usize]
    }
}

#[allow(clippy::too_many_arguments)]
fn build(
    net: &str,
    d: &Design,
    bdd: &mut Bdd,
    vars: &mut Vars,
    memo: &mut HashMap<String, u32>,
    visiting: &mut BTreeSet<String>,
) -> Result<u32, String> {
    if let Some(&f) = memo.get(net) {
        return Ok(f);
    }
    // a supply net: its constant, whatever touches it
    if let Some(&v) = d.constants.get(net) {
        return Ok(if v { bdd.one() } else { bdd.zero() });
    }
    // a free input: primary input, an undriven net, or a register (flop Q) output
    if d.is_free(net)? {
        let idx = vars.get(&d.var_of(net));
        let f = bdd.var(idx);
        memo.insert(net.to_string(), f);
        return Ok(f);
    }
    if !visiting.insert(net.to_string()) {
        return Err(format!("combinational loop through net `{net}`"));
    }
    let &(i, out_pin) = d.driver.get(net).unwrap();
    let inst = &d.nl.insts[i];
    let cell = d
        .lib
        .cells
        .get(&inst.cell)
        .ok_or_else(|| format!("no cell `{}` in Liberty", inst.cell))?;
    let (logic, pins) = logic_of(inst, cell, out_pin)?;
    let mut child = Vec::new();
    for p in &pins {
        let f = match src_of(inst, p)? {
            Src::Net(n) => build(&n, d, bdd, vars, memo, visiting)?,
            Src::Const(v) => if v { bdd.one() } else { bdd.zero() },
        };
        child.push(f);
    }
    let f = match &logic {
        Logic::Prim(op) => apply_op(bdd, *op, &child, &pins)?,
        Logic::Func(func) => func_bdd(bdd, func, &pins, &child),
    };
    visiting.remove(net);
    memo.insert(net.to_string(), f);
    Ok(f)
}

fn apply_op(bdd: &mut Bdd, op: Op, ins: &[u32], pins: &[String]) -> Result<u32, String> {
    let need = |n: usize| -> Result<(), String> {
        if ins.len() == n {
            Ok(())
        } else {
            Err(format!(
                "primitive expected {n} input(s), got {}",
                ins.len()
            ))
        }
    };
    Ok(match op {
        Op::Buf => {
            need(1)?;
            ins[0]
        }
        Op::Not => {
            need(1)?;
            bdd.not(ins[0])
        }
        Op::Mux => {
            // out = S ? B : A, pins named A/B/S
            need(3)?;
            let idx = |want: &str| pins.iter().position(|p| p.eq_ignore_ascii_case(want));
            let (a, b, s) = match (idx("A"), idx("B"), idx("S")) {
                (Some(a), Some(b), Some(s)) => (ins[a], ins[b], ins[s]),
                _ => return Err("MUX needs pins A, B, S".into()),
            };
            bdd.ite(s, b, a)
        }
        // n-ary reductions
        Op::And | Op::Nand => {
            let mut acc = ins.first().copied().ok_or("AND/NAND needs inputs")?;
            for &x in &ins[1..] {
                acc = bdd.and(acc, x);
            }
            if matches!(op, Op::Nand) {
                bdd.not(acc)
            } else {
                acc
            }
        }
        Op::Or | Op::Nor => {
            let mut acc = ins.first().copied().ok_or("OR/NOR needs inputs")?;
            for &x in &ins[1..] {
                acc = bdd.or(acc, x);
            }
            if matches!(op, Op::Nor) {
                bdd.not(acc)
            } else {
                acc
            }
        }
        Op::Xor | Op::Xnor => {
            let mut acc = ins.first().copied().ok_or("XOR/XNOR needs inputs")?;
            for &x in &ins[1..] {
                acc = bdd.xor(acc, x);
            }
            if matches!(op, Op::Xnor) {
                bdd.not(acc)
            } else {
                acc
            }
        }
    })
}

/// The endpoints both designs have (compared, by key, with each design's net), and the keys only
/// one has (reported, not compared).
pub(crate) struct Endpoints {
    pub shared: Vec<String>,
    pub golden_nets: Vec<String>,
    pub revised_nets: Vec<String>,
    pub only_in_golden: Vec<String>,
    pub only_in_revised: Vec<String>,
}

pub(crate) fn endpoints(g: &Design, r: &Design) -> Endpoints {
    let (ge, re) = (g.endpoints(), r.endpoints());
    let shared: Vec<String> = ge.keys().filter(|k| re.contains_key(*k)).cloned().collect();
    Endpoints {
        golden_nets: shared.iter().map(|k| ge[k].clone()).collect(),
        revised_nets: shared.iter().map(|k| re[k].clone()).collect(),
        only_in_golden: ge.keys().filter(|k| !re.contains_key(*k)).cloned().collect(),
        only_in_revised: re.keys().filter(|k| !ge.contains_key(*k)).cloned().collect(),
        shared,
    }
}

/// One gate of a cone: the net it drives, its logic, and its input pins with their sources (nets or
/// ties), in the cell's pin order (the order `build` applies them in).
#[cfg_attr(not(feature = "abc"), allow(dead_code))]
pub(crate) struct Gate {
    pub out: String,
    pub logic: Logic,
    pub pins: Vec<String>,
    pub ins: Vec<Src>,
}

/// The logic feeding a set of endpoints, as `build` sees it: gates in dependency order (every
/// gate after the gates driving its inputs), and the free inputs (primary inputs, undriven nets,
/// register outputs) the cone reads, as net -> the variable `build` names it.
#[cfg_attr(not(feature = "abc"), allow(dead_code))]
#[derive(Default)]
pub(crate) struct Cone {
    pub gates: Vec<Gate>,
    pub free: BTreeMap<String, String>,
    /// Sequential model only: the registers the cone reads, by instance name in the order found.
    /// Each has a state signal ([`state_net`]) and a gate computing its next value ([`next_net`]).
    pub regs: Vec<String>,
    /// Sequential model only: the primary input each register's clock reaches.
    #[cfg_attr(not(feature = "abc"), allow(dead_code))]
    pub clocks: BTreeSet<String>,
}

/// The signal holding register `inst`'s stored value, and the one computing its next value. A
/// space cannot occur in a netlist name, so neither can collide with a net.
pub(crate) fn state_net(inst: &str) -> String {
    format!("{inst} <state>")
}
#[cfg_attr(not(feature = "abc"), allow(dead_code))]
pub(crate) fn next_net(inst: &str) -> String {
    format!("{inst} <next>")
}

/// The stored value in a register's expressions: a name no pin can have.
const STATE: &str = "<state>";

/// Collect the cone of `endpoints` with exactly `build`'s rules: the same free-input test, the
/// same cell-to-primitive map, the same input pins, the same errors.
#[cfg_attr(not(feature = "abc"), allow(dead_code))]
pub(crate) fn cone(d: &Design, endpoints: &[String]) -> Result<Cone, String> {
    let mut c = Cone::default();
    let mut done = BTreeSet::new();
    for ep in endpoints {
        collect(ep, d, &mut c, &mut done, &mut BTreeSet::new())?;
    }
    Ok(c)
}

/// The sequential model's cone: [`cone`] of `endpoints` on a [`Design::sequential`], then, for
/// every register it reaches, the gate computing that register's next value and ITS cone, until no
/// new register appears. Every register is clocked by the same primary input on the same edge.
#[cfg_attr(not(feature = "abc"), allow(dead_code))]
pub(crate) fn seq_cone(d: &Design, endpoints: &[String]) -> Result<Cone, String> {
    debug_assert!(d.sequential);
    let mut c = Cone::default();
    let mut done = BTreeSet::new();
    for ep in endpoints {
        collect(ep, d, &mut c, &mut done, &mut BTreeSet::new())?;
    }
    let index: HashMap<&str, usize> = d.nl.insts.iter().enumerate().map(|(i, x)| (x.name.as_str(), i)).collect();
    let mut k = 0;
    while k < c.regs.len() {
        let inst = &d.nl.insts[index[c.regs[k].as_str()]];
        k += 1;
        let reg = Reg::of(inst, &d.lib.cells[&inst.cell])?;
        c.clocks.insert(d.clock_root(inst, &reg.clock)?);
        let (pins, ins) = reg.reads(inst, &reg.next)?;
        for src in &ins {
            if let Src::Net(n) = src {
                collect(n, d, &mut c, &mut done, &mut BTreeSet::new())?;
            }
        }
        c.gates.push(Gate { out: next_net(&inst.name), logic: Logic::Func(reg.next.clone()), pins, ins });
    }
    Ok(c)
}

/// A register as the sequential model reads it: one `ff` group, its clock pin, and over its input
/// pins plus [`STATE`] (the stored value): the value it loads on the clock edge and the value each
/// state variable shows.
///
/// ⛔ An asynchronous `clear` / `preset` is modelled synchronously: while it is active the outputs
/// show the forced value AND the forced value is what the edge loads. That is exact at every clock
/// edge (which is all the model observes) for a reset held across an edge; a pulse between two
/// edges is not seen. Both active at once follow `clear_preset_var1` / `_var2` (`L`, `H`, `N` no
/// change, `T` toggle); a library that leaves them out leaves that case undefined, an error here.
#[cfg_attr(not(feature = "abc"), allow(dead_code))]
struct Reg {
    clock: String,
    next: Func,
    iq: (String, Func),
    iqn: (String, Func),
}

fn ite(c: &Func, t: Func, e: Func) -> Func {
    use Func::*;
    Or(Box::new(And(Box::new(c.clone()), Box::new(t))), Box::new(And(Box::new(Not(Box::new(c.clone()))), Box::new(e))))
}

/// `f` with each port `p` for which `by(p)` gives an expression replaced by it.
fn subst(f: &Func, by: &dyn Fn(&str) -> Option<Func>) -> Func {
    use Func::*;
    match f {
        Port(p) => by(p).unwrap_or_else(|| f.clone()),
        Not(a) => Not(Box::new(subst(a, by))),
        And(a, b) => And(Box::new(subst(a, by)), Box::new(subst(b, by))),
        Or(a, b) => Or(Box::new(subst(a, by)), Box::new(subst(b, by))),
        Xor(a, b) => Xor(Box::new(subst(a, by)), Box::new(subst(b, by))),
        One | Zero => f.clone(),
    }
}

impl Reg {
    fn of(inst: &Inst, cell: &Cell) -> Result<Reg, String> {
        let what = || format!("register `{}` ({})", inst.name, inst.cell);
        let g = cell.seq_group.as_ref().ok_or_else(|| format!("{}: no single `ff` group to model (a bank or a `statetable`)", what()))?;
        if g.latch {
            return Err(format!("{}: a latch is not modelled", what()));
        }
        if g.attrs.contains_key("clocked_on_also") {
            return Err(format!("{}: a second clock (`clocked_on_also`) is not modelled", what()));
        }
        let inputs: Vec<&str> = cell.pins.iter().filter(|(_, p)| p.direction == Dir::In).map(|(n, _)| n.as_str()).collect();
        let parse = |key: &str| -> Result<Option<Func>, String> {
            g.attrs
                .get(key)
                .map(|e| Func::parse_in(e, |p| inputs.contains(&p)).ok_or_else(|| format!("{}: `{key}` `{e}` does not parse over its input pins", what())))
                .transpose()
        };
        let clock = match parse("clocked_on")? {
            Some(Func::Port(p)) => p,
            Some(_) => return Err(format!("{}: clock `{}` is not one pin's rising edge", what(), g.attrs["clocked_on"])),
            None => return Err(format!("{}: its `ff` has no `clocked_on`", what())),
        };
        let next_state = parse("next_state")?.ok_or_else(|| format!("{}: its `ff` has no `next_state`", what()))?;
        let state = Func::Port(STATE.into());
        let (clear, preset) = (parse("clear")?, parse("preset")?);
        // the value under clear / preset (one of them, or neither), else `normal`
        let forced = |normal: Func| match (&clear, &preset) {
            (Some(c), Some(p)) => ite(c, Func::Zero, ite(p, Func::One, normal)),
            (Some(c), None) => ite(c, Func::Zero, normal),
            (None, Some(p)) => ite(p, Func::One, normal),
            (None, None) => normal,
        };
        // both at once: `clear_preset_var1` for IQ (and the value loaded), `_var2` for IQN
        let both = |key: &str, keep: Func| -> Result<Option<(Func, Func)>, String> {
            let (Some(c), Some(p)) = (&clear, &preset) else { return Ok(None) };
            let v = match g.attrs.get(key).map(|v| v.trim()) {
                Some("L") => Func::Zero,
                Some("H") => Func::One,
                Some("N") => keep.clone(),
                Some("T") => Func::Not(Box::new(keep)),
                Some(v) => return Err(format!("{}: `{key}` `{v}` is not modelled", what())),
                None => return Err(format!("{}: clear and preset with no `{key}` (both active is undefined)", what())),
            };
            Ok(Some((Func::And(Box::new(c.clone()), Box::new(p.clone())), v)))
        };
        let iq_shown = forced(state.clone());
        let not_state = Func::Not(Box::new(state.clone()));
        let (iq, iqn, next) = match (both("clear_preset_var1", state.clone())?, both("clear_preset_var2", not_state)?) {
            (Some((cp, v1)), Some((_, v2))) => (
                ite(&cp, v1.clone(), iq_shown.clone()),
                ite(&cp, v2, Func::Not(Box::new(iq_shown))),
                ite(&cp, v1, forced(next_state)),
            ),
            _ => (iq_shown.clone(), Func::Not(Box::new(iq_shown)), forced(next_state)),
        };
        Ok(Reg { clock, next, iq: (g.iq.clone(), iq), iqn: (g.iqn.clone(), iqn) })
    }

    /// Output pin `out`'s function over the input pins and [`STATE`]: the pin's Liberty function with
    /// each state variable replaced by the value it shows.
    fn output(&self, inst: &Inst, cell: &Cell, out: &str) -> Result<Func, String> {
        let f = cell
            .pins
            .get(out)
            .and_then(|p| p.function.as_deref())
            .ok_or_else(|| format!("register `{}` ({}): output `{out}` has no function", inst.name, inst.cell))?;
        let known = |p: &str| p == self.iq.0 || p == self.iqn.0 || cell.pins.get(p).is_some_and(|x| x.direction == Dir::In);
        let f = Func::parse_in(f, known)
            .ok_or_else(|| format!("register `{}` ({}): output `{out}` function `{f}` does not parse", inst.name, inst.cell))?;
        Ok(subst(&f, &|p| {
            if p == self.iq.0 {
                Some(self.iq.1.clone())
            } else if p == self.iqn.0 {
                Some(self.iqn.1.clone())
            } else {
                None
            }
        }))
    }

    /// The pins `f` reads, in the order the gate lists them (input pins in name order, then
    /// [`STATE`]), and their sources (the register's own state signal for [`STATE`]).
    fn reads(&self, inst: &Inst, f: &Func) -> Result<(Vec<String>, Vec<Src>), String> {
        let mut pins: Vec<String> = f.ports().into_iter().map(str::to_string).collect();
        pins.sort_by_key(|p| (p == STATE, p.clone()));
        pins.dedup();
        let ins = pins
            .iter()
            .map(|p| if p == STATE { Ok(Src::Net(state_net(&inst.name))) } else { src_of(inst, p) })
            .collect::<Result<_, _>>()?;
        Ok((pins, ins))
    }
}

fn collect(
    net: &str,
    d: &Design,
    c: &mut Cone,
    done: &mut BTreeSet<String>,
    visiting: &mut BTreeSet<String>,
) -> Result<(), String> {
    if done.contains(net) {
        return Ok(());
    }
    // a supply net: a buffer of its constant, as `build` reads it
    if let Some(&v) = d.constants.get(net) {
        done.insert(net.to_string());
        c.gates.push(Gate { out: net.to_string(), logic: Logic::Prim(Op::Buf), pins: vec!["A".into()], ins: vec![Src::Const(v)] });
        return Ok(());
    }
    if d.is_free(net)? {
        c.free.insert(net.to_string(), d.var_of(net));
        done.insert(net.to_string());
        return Ok(());
    }
    if !visiting.insert(net.to_string()) {
        return Err(format!("combinational loop through net `{net}`"));
    }
    let &(i, out_pin) = d.driver.get(net).unwrap();
    let inst = &d.nl.insts[i];
    let cell = d
        .lib
        .cells
        .get(&inst.cell)
        .ok_or_else(|| format!("no cell `{}` in Liberty", inst.cell))?;
    // the sequential model: a register output is its pin's function of the stored value
    let (logic, pins) = if d.sequential && cell.is_seq {
        if !c.regs.contains(&inst.name) {
            c.regs.push(inst.name.clone());
        }
        let reg = Reg::of(inst, cell)?;
        let f = reg.output(inst, cell, out_pin)?;
        let (pins, ins) = reg.reads(inst, &f)?;
        for src in &ins {
            if let Src::Net(n) = src {
                if *n != state_net(&inst.name) {
                    collect(n, d, c, done, visiting)?;
                }
            }
        }
        visiting.remove(net);
        done.insert(net.to_string());
        c.gates.push(Gate { out: net.to_string(), logic: Logic::Func(f), pins, ins });
        return Ok(());
    } else {
        logic_of(inst, cell, out_pin)?
    };
    let mut ins = Vec::new();
    for p in &pins {
        let src = src_of(inst, p)?;
        if let Src::Net(net) = &src {
            collect(net, d, c, done, visiting)?;
        }
        ins.push(src);
    }
    visiting.remove(net);
    done.insert(net.to_string());
    c.gates.push(Gate { out: net.to_string(), logic, pins, ins });
    Ok(())
}

/// Check golden vs revised for combinational equivalence.
pub fn equivalence(golden: &Netlist, revised: &Netlist, lib: &Lib) -> Result<LecReport, String> {
    if lib.cells.is_empty() {
        return Err("no cells in the Liberty".into());
    }
    let g = Design::new(golden, lib);
    let r = Design::new(revised, lib);

    let mut bdd = Bdd::new();
    let mut vars = Vars::new();
    // seed the variable order with the shared primary inputs (sorted, stable)
    let mut pis: Vec<&String> = golden.inputs.iter().chain(revised.inputs.iter()).collect();
    pis.sort();
    pis.dedup();
    for p in pis {
        vars.get(p);
    }

    let Endpoints { shared, golden_nets, revised_nets, only_in_golden, only_in_revised } = endpoints(&g, &r);

    let mut mismatches = Vec::new();
    for (k, ep) in shared.iter().enumerate() {
        let mut gm = HashMap::new();
        let mut rm = HashMap::new();
        let fg = build(&golden_nets[k], &g, &mut bdd, &mut vars, &mut gm, &mut BTreeSet::new())?;
        let fr = build(&revised_nets[k], &r, &mut bdd, &mut vars, &mut rm, &mut BTreeSet::new())?;
        if fg != fr {
            let miter = bdd.xor(fg, fr);
            let cex = bdd
                .sat_one(miter)
                .unwrap_or_default()
                .into_iter()
                .map(|(v, val)| (vars.name(v).to_string(), val))
                .collect();
            mismatches.push(Mismatch {
                endpoint: ep.clone(),
                counterexample: cex,
            });
        }
    }

    Ok(LecReport {
        equivalent: mismatches.is_empty()
            && only_in_golden.is_empty()
            && only_in_revised.is_empty(),
        compared: shared.len(),
        mismatches,
        only_in_golden,
        only_in_revised,
        undecided: false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lib() -> Lib {
        Lib::load("examples/cells.lib").expect("cells.lib")
    }
    fn nl(src: &str) -> Netlist {
        crate::netlist::parse(src).unwrap()
    }

    #[test]
    fn de_morgan_rewrite_is_equivalent() {
        // golden: f = a & b   |   revised: f = !(!a | !b)
        let g =
            nl("module t(a,b,f);\ninput a,b; output f;\nAND2 g(.A(a),.B(b),.Z(f));\nendmodule\n");
        let r = nl(
            "module t(a,b,f);\ninput a,b; output f;\nwire na,nb,o;\n\
             INV i1(.A(a),.Y(na));\nINV i2(.A(b),.Y(nb));\nOR2 o1(.A(na),.B(nb),.Z(o));\nINV i3(.A(o),.Y(f));\nendmodule\n",
        );
        let rep = equivalence(&g, &r, &lib()).unwrap();
        assert!(rep.equivalent, "{:?}", rep.mismatches);
        assert_eq!(rep.compared, 1);
    }

    #[test]
    fn a_real_bug_is_caught_with_a_counterexample() {
        // golden: f = a & b   |   revised (buggy): f = a | b
        let g =
            nl("module t(a,b,f);\ninput a,b; output f;\nAND2 g(.A(a),.B(b),.Z(f));\nendmodule\n");
        let r =
            nl("module t(a,b,f);\ninput a,b; output f;\nOR2 g(.A(a),.B(b),.Z(f));\nendmodule\n");
        let rep = equivalence(&g, &r, &lib()).unwrap();
        assert!(!rep.equivalent);
        assert_eq!(rep.mismatches.len(), 1);
        let cex = &rep.mismatches[0].counterexample;
        // and != or exactly when a,b are not both 1 and not both 0 — i.e. they differ
        let val = |n: &str| cex.iter().find(|(k, _)| k == n).map(|(_, v)| *v);
        // at least one of a,b is in the counterexample and they aren't equal-true
        assert!(val("a").is_some() || val("b").is_some());
    }

    /// A cell the Liberty lacks may drive the net it touches: an error, never a free input. As a
    /// free input in both designs, `f` would compare equal although the cells differ (XOR2 vs
    /// XNOR2, neither in the example Liberty).
    #[test]
    fn a_cell_missing_from_the_liberty_is_an_error() {
        let g = nl("module t(a,b,f);\ninput a,b; output f;\nXOR2 g(.A(a),.B(b),.Z(f));\nendmodule\n");
        let r = nl("module t(a,b,f);\ninput a,b; output f;\nXNOR2 g(.A(a),.B(b),.Z(f));\nendmodule\n");
        let e = equivalence(&g, &r, &lib()).unwrap_err();
        assert!(e.contains("`XOR2` is not in the Liberty"), "{e}");
        // A missing cell outside every compared cone (here: on an unused net) is no error.
        let g2 = nl("module t(a,b,f);\ninput a,b; output f;\nwire u;\n\
             AND2 g(.A(a),.B(b),.Z(f));\nFILL x(.A(u));\nendmodule\n");
        assert!(equivalence(&g2, &g2, &lib()).unwrap().equivalent);
    }

    /// A pin tied to a constant is an input of its gate: `AND2(a, 1'b0)` is 0, never `a`, and
    /// `AND2(a, 1'b1)` is `a`. Dropped, the first would compare equal to a buffer.
    #[test]
    fn a_tied_pin_is_an_input() {
        let buf = nl("module t(a,f);\ninput a; output f;\nBUF b(.A(a),.Y(f));\nendmodule\n");
        let and0 = nl("module t(a,f);\ninput a; output f;\nAND2 g(.A(a),.B(1'b0),.Z(f));\nendmodule\n");
        let and1 = nl("module t(a,f);\ninput a; output f;\nAND2 g(.A(a),.B(1'b1),.Z(f));\nendmodule\n");
        let rep = equivalence(&and0, &buf, &lib()).unwrap();
        assert!(!rep.equivalent);
        assert_eq!(rep.mismatches[0].counterexample, [("a".to_string(), true)]);
        assert!(equivalence(&and1, &buf, &lib()).unwrap().equivalent);
    }

    /// An unconnected input floats: an error, never a dropped input. Dropped, `AND2(a, <open>)`
    /// would read as `a` and compare equal to a buffer.
    #[test]
    fn an_unconnected_input_is_an_error() {
        let buf = nl("module t(a,f);\ninput a; output f;\nBUF b(.A(a),.Y(f));\nendmodule\n");
        let open = nl("module t(a,f);\ninput a; output f;\nAND2 g(.A(a),.Z(f));\nendmodule\n");
        let e = equivalence(&open, &buf, &lib()).unwrap_err();
        assert!(e.contains("input pin `B` of instance `g` (AND2) is unconnected"), "{e}");
    }

    /// A `supply0` / `supply1` net is its constant, not a free input: `AND2(a, vdd)` with `vdd`
    /// on `supply1` is `a`. Free, `vdd` would make it differ from a buffer.
    #[test]
    fn a_supply_net_is_its_constant() {
        let buf = nl("module t(a,f);\ninput a; output f;\nBUF b(.A(a),.Y(f));\nendmodule\n");
        let and1 = nl("module t(a,f);\ninput a; output f;\nsupply1 vdd;\nAND2 g(.A(a),.B(vdd),.Z(f));\nendmodule\n");
        assert!(equivalence(&and1, &buf, &lib()).unwrap().equivalent);
        let and0 = nl("module t(a,f);\ninput a; output f;\nsupply0 gnd;\nAND2 g(.A(a),.B(gnd),.Z(f));\nendmodule\n");
        assert!(!equivalence(&and0, &buf, &lib()).unwrap().equivalent);
    }

    fn func_lib() -> Lib {
        Lib::load("tests/data/func.lib").expect("func.lib")
    }

    /// Rule (Liberty `function`): a cell's logic is its output pin's function, so an AOI is the
    /// NOR of an AND and an input, and a half adder's CO and S are each their OWN pin's function.
    #[test]
    fn a_cell_is_its_liberty_function() {
        let l = func_lib();
        let g = nl("module t(a,b,c,y);\ninput a,b,c; output y;\nAOI21X g(.A1(a),.A2(b),.B1(c),.Y(y));\nendmodule\n");
        let r = nl("module t(a,b,c,y);\ninput a,b,c; output y;\nwire ab,o;\n\
             AND2X g1(.A(a),.B(b),.Y(ab));\nOR2X g2(.A(ab),.B(c),.Y(o));\nINVX g3(.A(o),.Y(y));\nendmodule\n");
        assert!(equivalence(&g, &r, &l).unwrap().equivalent);
        let ao = nl("module t(a,b,c,y);\ninput a,b,c; output y;\nAO21X g(.A1(a),.A2(b),.B1(c),.X(y));\nendmodule\n");
        assert!(!equivalence(&g, &ao, &l).unwrap().equivalent);
        let ha = nl("module t(a,b,c,s);\ninput a,b; output c,s;\nHAX h(.A(a),.B(b),.CO(c),.S(s));\nendmodule\n");
        let prim = nl("module t(a,b,c,s);\ninput a,b; output c,s;\nAND2X g1(.A(a),.B(b),.Y(c));\nXOR2X g2(.A(a),.B(b),.Y(s));\nendmodule\n");
        let rep = equivalence(&ha, &prim, &l).unwrap();
        assert!(rep.equivalent, "{:?}", rep.mismatches);
        assert_eq!(rep.compared, 2);
    }

    /// A tie cell's function is its constant; the function wins over a name that says otherwise;
    /// a function over a pin the cell lacks is an error, never a guess from the name.
    #[test]
    fn tie_cells_and_names_follow_the_function() {
        let l = func_lib();
        let buf = nl("module t(a,f);\ninput a; output f;\nBUFX b(.A(a),.Y(f));\nendmodule\n");
        let tie = |cell: &str, pin: &str| {
            nl(&format!("module t(a,f);\ninput a; output f;\nwire k;\n{cell} t(.{pin}(k));\nAND2X g(.A(a),.B(k),.Y(f));\nendmodule\n"))
        };
        assert!(equivalence(&tie("TIEHI", "HI"), &buf, &l).unwrap().equivalent);
        assert!(!equivalence(&tie("TIELO", "LO"), &buf, &l).unwrap().equivalent);
        let and = nl("module t(a,b,f);\ninput a,b; output f;\nAND2X g(.A(a),.B(b),.Y(f));\nendmodule\n");
        let named_or = nl("module t(a,b,f);\ninput a,b; output f;\nORACLE g(.A(a),.B(b),.Y(f));\nendmodule\n");
        assert!(equivalence(&and, &named_or, &l).unwrap().equivalent);
        let bad = nl("module t(a,f);\ninput a; output f;\nBAD g(.A(a),.Y(f));\nendmodule\n");
        let e = equivalence(&bad, &buf, &l).unwrap_err();
        assert!(e.contains("function `A&Q` does not parse"), "{e}");
    }

    /// Registers match by INSTANCE: a register output is the variable `inst/Q` and a data pin the
    /// endpoint `inst/D`, whatever the nets are called. Repair buffers an output port and renames
    /// the register's Q net (and here its D net): still equivalent. Two registers that trade
    /// their data inputs are not.
    #[test]
    fn registers_match_by_instance_not_by_net() {
        let g = nl("module t(a,b,clk,q);\ninput a,b,clk; output q;\nwire d;\n\
             AND2 g(.A(a),.B(q),.Z(d));\nDFF r(.CK(clk),.D(d),.Q(q));\nendmodule\n");
        let r = nl("module t(a,b,clk,q);\ninput a,b,clk; output q;\nwire d2,net9;\n\
             AND2 g(.A(a),.B(net9),.Z(d2));\nDFF r(.CK(clk),.D(d2),.Q(net9));\nBUF ob(.A(net9),.Y(q));\nendmodule\n");
        let rep = equivalence(&g, &r, &lib()).unwrap();
        assert!(rep.equivalent, "{:?} {:?} {:?}", rep.mismatches, rep.only_in_golden, rep.only_in_revised);
        assert_eq!(rep.compared, 2, "q and r/D");
        let two = |da: &str, db: &str| {
            nl(&format!("module t(a,b,clk,x,y);\ninput a,b,clk; output x,y;\n\
                 DFF ra(.CK(clk),.D({da}),.Q(x));\nDFF rb(.CK(clk),.D({db}),.Q(y));\nendmodule\n"))
        };
        let rep = equivalence(&two("a", "b"), &two("b", "a"), &lib()).unwrap();
        let mut at: Vec<&str> = rep.mismatches.iter().map(|m| m.endpoint.as_str()).collect();
        at.sort();
        assert_eq!(at, ["ra/D", "rb/D"]);
    }

    #[test]
    fn sequential_equivalence_cuts_at_registers() {
        // both register `a & b`; revised uses De Morgan in the cone feeding D.
        let g = nl("module t(a,b,clk,q);\ninput a,b,clk; output q;\nwire d;\n\
             AND2 g(.A(a),.B(b),.Z(d));\nDFF r(.CK(clk),.D(d),.Q(q));\nendmodule\n");
        let r = nl(
            "module t(a,b,clk,q);\ninput a,b,clk; output q;\nwire na,nb,o,d;\n\
             INV i1(.A(a),.Y(na));\nINV i2(.A(b),.Y(nb));\nOR2 o1(.A(na),.B(nb),.Z(o));\n\
             INV i3(.A(o),.Y(d));\nDFF r(.CK(clk),.D(d),.Q(q));\nendmodule\n",
        );
        let rep = equivalence(&g, &r, &lib()).unwrap();
        assert!(rep.equivalent, "{:?}", rep.mismatches);
        assert!(rep.compared >= 1, "compared the flop D endpoint");
    }
}
