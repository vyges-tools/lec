//! Combinational **logic equivalence** check.
//!
//! Build a canonical ROBDD for every endpoint (primary output / flop data pin) of
//! the golden and the revised netlist in **one shared package over one shared
//! variable order**, then compare: two endpoints are equivalent *iff* their BDDs
//! are the same node. When they differ, the miter (their XOR) yields a concrete
//! input **counter-example**.
//!
//! Gate functions come from a built-in standard-cell primitive map (keyed on the
//! cell name's logic prefix — INV/BUF/AND/OR/NAND/NOR/XOR/XNOR/MUX); the Liberty
//! gives pin directions and tells combinational cells from sequential. Sequential
//! state is cut at the registers: flop Q nets are free inputs, flop D nets are
//! endpoints — i.e. this proves the *combinational* logic between registers, the
//! standard combinational-LEC model (registers matched by name).

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::bdd::Bdd;
use crate::liberty::{Dir, Lib};
use crate::netlist::{Inst, Netlist};

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
}

#[derive(Clone, Copy)]
enum Op {
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
    inst.conns.iter().find(|(p, _)| p == pin).map(|(_, n)| n.as_str())
}

/// One design's view: net -> (inst index, output pin); plus the netlist + lib.
struct Design<'a> {
    nl: &'a Netlist,
    lib: &'a Lib,
    driver: BTreeMap<&'a str, (usize, &'a str)>,
}

impl<'a> Design<'a> {
    fn new(nl: &'a Netlist, lib: &'a Lib) -> Design<'a> {
        let mut driver = BTreeMap::new();
        for (i, inst) in nl.insts.iter().enumerate() {
            if let Some(cell) = lib.cells.get(&inst.cell) {
                for (pin, net) in &inst.conns {
                    if cell.pins.get(pin).map(|p| p.direction) == Some(Dir::Out) {
                        driver.insert(net.as_str(), (i, pin.as_str()));
                    }
                }
            }
        }
        Design { nl, lib, driver }
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
        Vars { map: HashMap::new(), rev: Vec::new() }
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
    // a free input: primary input, an undriven net, or a register (flop Q) output
    let is_free = d.nl.inputs.iter().any(|p| p == net)
        || !d.driver.contains_key(net)
        || d.is_seq_driver(net);
    if is_free {
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
    let cell = d.lib.cells.get(&inst.cell).ok_or_else(|| format!("no cell `{}` in Liberty", inst.cell))?;
    let _ = out_pin;
    let op = op_of(&inst.cell).ok_or_else(|| format!("cell `{}` is not a known logic primitive", inst.cell))?;

    // input pins (combinational primitives have no clock pin); skip the cell's
    // clock pin defensively if one is ever present.
    let in_pins: Vec<&str> = cell
        .pins
        .iter()
        .filter(|(n, p)| p.direction == Dir::In && cell.clock_pin.as_deref() != Some(n))
        .map(|(n, _)| n.as_str())
        .collect();
    let mut child = Vec::new();
    let mut child_pins = Vec::new();
    for p in &in_pins {
        if let Some(n) = net_of(inst, p) {
            child.push(build(n, d, bdd, vars, memo, visiting)?);
            child_pins.push(p.to_string());
        }
    }
    let f = apply_op(bdd, op, &child, &child_pins)?;
    visiting.remove(net);
    memo.insert(net.to_string(), f);
    Ok(f)
}

fn apply_op(bdd: &mut Bdd, op: Op, ins: &[u32], pins: &[String]) -> Result<u32, String> {
    let need = |n: usize| -> Result<(), String> {
        if ins.len() == n {
            Ok(())
        } else {
            Err(format!("primitive expected {n} input(s), got {}", ins.len()))
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

    let g_eps: BTreeSet<String> = g.endpoints().into_iter().collect();
    let r_eps: BTreeSet<String> = r.endpoints().into_iter().collect();
    let only_in_golden: Vec<String> = g_eps.difference(&r_eps).cloned().collect();
    let only_in_revised: Vec<String> = r_eps.difference(&g_eps).cloned().collect();
    let shared: Vec<String> = g_eps.intersection(&r_eps).cloned().collect();

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
            mismatches.push(Mismatch { endpoint: ep.clone(), counterexample: cex });
        }
    }

    Ok(LecReport {
        equivalent: mismatches.is_empty() && only_in_golden.is_empty() && only_in_revised.is_empty(),
        compared: shared.len(),
        mismatches,
        only_in_golden,
        only_in_revised,
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
        let g = nl("module t(a,b,f);\ninput a,b; output f;\nAND2 g(.A(a),.B(b),.Z(f));\nendmodule\n");
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
        let g = nl("module t(a,b,f);\ninput a,b; output f;\nAND2 g(.A(a),.B(b),.Z(f));\nendmodule\n");
        let r = nl("module t(a,b,f);\ninput a,b; output f;\nOR2 g(.A(a),.B(b),.Z(f));\nendmodule\n");
        let rep = equivalence(&g, &r, &lib()).unwrap();
        assert!(!rep.equivalent);
        assert_eq!(rep.mismatches.len(), 1);
        let cex = &rep.mismatches[0].counterexample;
        // and != or exactly when a,b are not both 1 and not both 0 — i.e. they differ
        let val = |n: &str| cex.iter().find(|(k, _)| k == n).map(|(_, v)| *v);
        // at least one of a,b is in the counterexample and they aren't equal-true
        assert!(val("a").is_some() || val("b").is_some());
    }

    #[test]
    fn sequential_equivalence_cuts_at_registers() {
        // both register `a & b`; revised uses De Morgan in the cone feeding D.
        let g = nl(
            "module t(a,b,clk,q);\ninput a,b,clk; output q;\nwire d;\n\
             AND2 g(.A(a),.B(b),.Z(d));\nDFF r(.CK(clk),.D(d),.Q(q));\nendmodule\n",
        );
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
