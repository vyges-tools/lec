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
//! state is cut at the registers: flop Q nets are free inputs, flop D nets are
//! endpoints — i.e. this proves the *combinational* logic between registers, the
//! standard combinational-LEC model (registers matched by name).

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
        Design { nl, lib, driver, unknown, constants }
    }

    /// Is `net` a free input of the model (a primary input, a register output, or undriven)?
    /// ⛔ An "undriven" net that touches an instance of a cell missing from the Liberty is an
    /// error, not a free input: that instance may well drive it, and treating it as free in both
    /// designs would compare it equal whatever the cell computes.
    fn is_free(&self, net: &str) -> Result<bool, String> {
        if self.nl.inputs.iter().any(|p| p == net) || self.is_seq_driver(net) {
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
        self.driver
            .get(net)
            .and_then(|&(i, _)| self.lib.cells.get(&self.nl.insts[i].cell))
            .map(|c| c.is_seq)
            .unwrap_or(false)
    }

    /// Endpoints to compare: primary outputs + flop data pins (setup-constrained).
    fn endpoints(&self) -> Vec<String> {
        let mut e: Vec<String> = self.nl.outputs.clone();
        for inst in &self.nl.insts {
            if let Some(cell) = self.lib.cells.get(&inst.cell) {
                if cell.is_seq {
                    for (pin, p) in &cell.pins {
                        if !p.setup.is_empty() {
                            if let Some(n) = net_of(inst, pin) {
                                e.push(n.to_string());
                            }
                        }
                    }
                }
            }
        }
        e.sort();
        e.dedup();
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
        let idx = vars.get(net);
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

/// The endpoints both designs have (compared), and those only one has (reported, not compared).
pub(crate) struct Endpoints {
    pub shared: Vec<String>,
    pub only_in_golden: Vec<String>,
    pub only_in_revised: Vec<String>,
}

pub(crate) fn endpoints(g: &Design, r: &Design) -> Endpoints {
    let g_eps: BTreeSet<String> = g.endpoints().into_iter().collect();
    let r_eps: BTreeSet<String> = r.endpoints().into_iter().collect();
    Endpoints {
        shared: g_eps.intersection(&r_eps).cloned().collect(),
        only_in_golden: g_eps.difference(&r_eps).cloned().collect(),
        only_in_revised: r_eps.difference(&g_eps).cloned().collect(),
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
/// register outputs) the cone reads.
#[cfg_attr(not(feature = "abc"), allow(dead_code))]
pub(crate) struct Cone {
    pub gates: Vec<Gate>,
    pub free: BTreeSet<String>,
}

/// Collect the cone of `endpoints` with exactly `build`'s rules: the same free-input test, the
/// same cell-to-primitive map, the same input pins, the same errors.
#[cfg_attr(not(feature = "abc"), allow(dead_code))]
pub(crate) fn cone(d: &Design, endpoints: &[String]) -> Result<Cone, String> {
    let mut c = Cone { gates: Vec::new(), free: BTreeSet::new() };
    let mut done = BTreeSet::new();
    for ep in endpoints {
        collect(ep, d, &mut c, &mut done, &mut BTreeSet::new())?;
    }
    Ok(c)
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
        c.free.insert(net.to_string());
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
    let (logic, pins) = logic_of(inst, cell, out_pin)?;
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

    let Endpoints { shared, only_in_golden, only_in_revised } = endpoints(&g, &r);

    let mut mismatches = Vec::new();
    for ep in &shared {
        let mut gm = HashMap::new();
        let mut rm = HashMap::new();
        let fg = build(ep, &g, &mut bdd, &mut vars, &mut gm, &mut BTreeSet::new())?;
        let fr = build(ep, &r, &mut bdd, &mut vars, &mut rm, &mut BTreeSet::new())?;
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
