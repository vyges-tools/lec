//! The second engine: the same check through ABC's SAT-based prover (`vyges-abc-lib`).
//!
//! The BDD engine in [`crate::lec`] is exact but builds a canonical diagram per endpoint, which
//! grows exponentially on some functions (multipliers above all). ABC proves the miter with SAT
//! sweeping instead. The netlist model is the SAME: [`crate::lec::cone`] collects each design's
//! logic with the BDD engine's rules (cut at registers, the same cell map, the same free inputs),
//! this module writes it as BLIF, and ABC compares the two files.
//!
//! The verdict is therefore comparable endpoint for endpoint with the BDD engine's, and on any
//! design both engines finish they must agree: two independent provers over one model.
//!
//! ⛔ ABC stops at the FIRST output it disproves, so a [`Verdict::Differs`] names one differing
//! endpoint, not all of them (the BDD engine lists every one).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use vyges_abc_lib::{Abc, ProbStatus};

use crate::lec::{self, Cone, Design, Logic, Op, Src};
use crate::liberty::Lib;
use crate::netlist::Netlist;

/// What ABC concluded about the shared endpoints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// Every shared endpoint computes the same function in both designs.
    Equivalent,
    /// This endpoint differs; the free-input assignment shows it (every input the miter reads).
    Differs { endpoint: String, counterexample: Vec<(String, bool)> },
    /// ABC gave up within its limits: neither proved nor disproved.
    Undecided,
}

#[derive(Debug, Clone)]
pub struct AbcReport {
    pub verdict: Verdict,
    pub compared: usize,
    pub only_in_golden: Vec<String>,
    pub only_in_revised: Vec<String>,
}

impl AbcReport {
    /// The same rule as the BDD report: equivalent only if every shared endpoint is proven AND
    /// both designs have the same endpoints.
    pub fn equivalent(&self) -> bool {
        self.verdict == Verdict::Equivalent && self.only_in_golden.is_empty() && self.only_in_revised.is_empty()
    }
}

impl From<AbcReport> for crate::lec::LecReport {
    /// The BDD engine's report shape: at most one mismatch (ABC stops at the first).
    fn from(a: AbcReport) -> Self {
        let equivalent = a.equivalent();
        let (mismatches, undecided) = match a.verdict {
            Verdict::Equivalent => (Vec::new(), false),
            Verdict::Differs { endpoint, counterexample } => {
                (vec![crate::lec::Mismatch { endpoint, counterexample }], false)
            }
            Verdict::Undecided => (Vec::new(), true),
        };
        crate::lec::LecReport {
            equivalent,
            compared: a.compared,
            mismatches,
            only_in_golden: a.only_in_golden,
            only_in_revised: a.only_in_revised,
            undecided,
        }
    }
}

/// The two engines over one model must agree: the same endpoints compared, ABC equivalent
/// exactly when the BDD engine found no mismatch, and the endpoint ABC disproves among the BDD
/// engine's mismatches. An undecided ABC run agrees with anything.
pub fn cross_check(bdd: &crate::lec::LecReport, abc: &AbcReport) -> Result<(), String> {
    if bdd.compared != abc.compared {
        return Err(format!("engines compared {} vs {} endpoints", bdd.compared, abc.compared));
    }
    match &abc.verdict {
        Verdict::Undecided => Ok(()),
        Verdict::Equivalent if bdd.mismatches.is_empty() => Ok(()),
        Verdict::Equivalent => Err(format!(
            "engines disagree: ABC proved every endpoint equivalent, the BDD engine found {} differing (first `{}`)",
            bdd.mismatches.len(),
            bdd.mismatches[0].endpoint
        )),
        Verdict::Differs { endpoint, .. } if bdd.mismatches.iter().any(|m| &m.endpoint == endpoint) => Ok(()),
        Verdict::Differs { endpoint, .. } => Err(format!(
            "engines disagree: ABC disproved `{endpoint}`, the BDD engine proved it equivalent"
        )),
    }
}

/// Signal names in the BLIF files are generated, not the netlist's: Verilog names may hold
/// characters BLIF reads as syntax, and ABC matches the two files' inputs and outputs BY NAME,
/// ordering them alphabetically. Fixed-width numbers make that order the numeric order.
pub(crate) fn pi_name(k: usize) -> String {
    format!("i{k:08}")
}
fn po_name(k: usize) -> String {
    format!("o{k:08}")
}

/// The single-output cover (BLIF `.names` rows) of a gate's logic over its inputs, in the pin
/// order `cone` recorded. A `function` is written as its on-set, one row per true assignment (a
/// constant `1` over no inputs is the single row `1`; a constant `0` has none).
fn cover(logic: &Logic, pins: &[String]) -> Result<(Vec<usize>, Vec<String>), String> {
    let op = match logic {
        Logic::Prim(op) => *op,
        Logic::Func(f) => {
            let n = pins.len();
            let rows = (0..1u64 << n)
                .map(|m| (0..n).map(|i| m >> (n - 1 - i) & 1 == 1).collect::<Vec<bool>>())
                .filter(|x| lec::func_value(f, pins, x))
                .map(|x| {
                    let cube: String = x.iter().map(|&b| if b { '1' } else { '0' }).collect();
                    if cube.is_empty() { "1".to_string() } else { format!("{cube} 1") }
                })
                .collect();
            return Ok(((0..n).collect(), rows));
        }
    };
    cover_prim(op, pins)
}

/// A primitive's cover; `pins` names its inputs (MUX finds A, B, S by name, as the BDD engine does).
fn cover_prim(op: Op, pins: &[String]) -> Result<(Vec<usize>, Vec<String>), String> {
    let n = pins.len();
    let order: Vec<usize> = (0..n).collect();
    let need = |k: usize| -> Result<(), String> {
        if n == k { Ok(()) } else { Err(format!("primitive expected {k} input(s), got {n}")) }
    };
    let all = |b: char| b.to_string().repeat(n);
    Ok(match op {
        Op::Buf => { need(1)?; (order, vec!["1 1".into()]) }
        Op::Not => { need(1)?; (order, vec!["0 1".into()]) }
        Op::And | Op::Nand | Op::Or | Op::Nor if n == 0 => return Err("AND/OR needs inputs".into()),
        Op::And => (order, vec![format!("{} 1", all('1'))]),
        Op::Nand => (order, vec![format!("{} 0", all('1'))]),
        Op::Or => (order, vec![format!("{} 0", all('0'))]),
        Op::Nor => (order, vec![format!("{} 1", all('0'))]),
        Op::Xor | Op::Xnor => {
            if n == 0 {
                return Err("XOR/XNOR needs inputs".into());
            }
            let odd = matches!(op, Op::Xor);
            let rows = (0..1u32 << n)
                .filter(|m| (m.count_ones() % 2 == 1) == odd)
                .map(|m| format!("{} 1", (0..n).map(|i| if m >> (n - 1 - i) & 1 == 1 { '1' } else { '0' }).collect::<String>()))
                .collect();
            (order, rows)
        }
        Op::Mux => {
            // out = S ? B : A; inputs written in the order A, B, S.
            need(3)?;
            let idx = |want: &str| pins.iter().position(|p| p.eq_ignore_ascii_case(want));
            let (Some(a), Some(b), Some(s)) = (idx("A"), idx("B"), idx("S")) else {
                return Err("MUX needs pins A, B, S".into());
            };
            (vec![a, b, s], vec!["1-0 1".into(), "-11 1".into()])
        }
    })
}

/// One design as BLIF: inputs `pis` (free-input variable -> index, the union over both designs),
/// outputs this design's nets of the shared endpoints in order, internal nets numbered per file.
/// A sequential cone's registers are latches from 0, loading their next-value gates.
pub(crate) fn write_blif(model: &str, c: &Cone, pis: &BTreeMap<String, usize>, outs: &[String]) -> Result<String, String> {
    let mut id: BTreeMap<String, String> = c.free.iter().map(|(n, v)| (n.clone(), pi_name(pis[v]))).collect();
    for (k, g) in c.gates.iter().enumerate() {
        id.insert(g.out.clone(), format!("n{k}"));
    }
    // the sequential model's registers: each state signal is a latch output
    for (k, r) in c.regs.iter().enumerate() {
        id.insert(lec::state_net(r), format!("s{k}"));
    }
    let mut s = String::new();
    let _ = writeln!(s, ".model {model}");
    let _ = writeln!(s, ".inputs {}", (0..pis.len()).map(pi_name).collect::<Vec<_>>().join(" "));
    let _ = writeln!(s, ".outputs {}", (0..outs.len()).map(po_name).collect::<Vec<_>>().join(" "));
    // A tied pin reads a constant net: `k0` has no cover row (always 0), `k1` the empty cube.
    let _ = writeln!(s, ".names k0\n.names k1\n1");
    let src = |x: &Src| match x {
        Src::Net(n) => id[n.as_str()].as_str(),
        Src::Const(v) => if *v { "k1" } else { "k0" },
    };
    for g in &c.gates {
        let (order, rows) = cover(&g.logic, &g.pins)?;
        let ins: Vec<&str> = order.iter().map(|&i| src(&g.ins[i])).collect();
        let _ = writeln!(s, ".names {} {}", ins.join(" "), id[g.out.as_str()]);
        for r in rows {
            let _ = writeln!(s, "{r}");
        }
    }
    // Each output through a buffer: an endpoint may be a free input (a register output wired
    // straight to another register's data pin), and an output may not share an input's name.
    for (k, ep) in outs.iter().enumerate() {
        let _ = writeln!(s, ".names {} {}\n1 1", id[ep.as_str()], po_name(k));
    }
    for r in &c.regs {
        let _ = writeln!(s, ".latch {} {} 0", id[&lec::next_net(r)], id[&lec::state_net(r)]);
    }
    s.push_str(".end\n");
    Ok(s)
}

/// A fresh directory for the two BLIF files, removed on drop.
pub(crate) struct Scratch(PathBuf);

impl Scratch {
    pub(crate) fn new() -> Result<Scratch, String> {
        use std::sync::atomic::{AtomicU64, Ordering};
        static N: AtomicU64 = AtomicU64::new(0);
        let p = std::env::temp_dir().join(format!("vyges-lec-{}-{}", std::process::id(), N.fetch_add(1, Ordering::Relaxed)));
        std::fs::create_dir_all(&p).map_err(|e| format!("{}: {e}", p.display()))?;
        Ok(Scratch(p))
    }
    pub(crate) fn path(&self) -> &Path {
        &self.0
    }
    pub(crate) fn write(&self, name: &str, text: &str) -> Result<PathBuf, String> {
        let p = self.0.join(name);
        std::fs::write(&p, text).map_err(|e| format!("{}: {e}", p.display()))?;
        Ok(p)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

pub(crate) fn arg(p: &Path) -> Result<String, String> {
    let s = p.to_str().ok_or_else(|| format!("non-UTF-8 path {}", p.display()))?;
    if s.chars().any(|c| c.is_whitespace() || c == ';' || c == '"') {
        return Err(format!("path not usable in an ABC command: {s}"));
    }
    Ok(s.to_string())
}

/// Check golden vs revised for combinational equivalence with ABC.
pub fn equivalence(golden: &Netlist, revised: &Netlist, lib: &Lib) -> Result<AbcReport, String> {
    if lib.cells.is_empty() {
        return Err("no cells in the Liberty".into());
    }
    let g = Design::new(golden, lib);
    let r = Design::new(revised, lib);
    let eps = lec::endpoints(&g, &r);
    let report = |verdict| AbcReport {
        verdict,
        compared: eps.shared.len(),
        only_in_golden: eps.only_in_golden.clone(),
        only_in_revised: eps.only_in_revised.clone(),
    };
    if eps.shared.is_empty() {
        return Ok(report(Verdict::Equivalent));
    }
    let gc = lec::cone(&g, &eps.golden_nets)?;
    let rc = lec::cone(&r, &eps.revised_nets)?;
    // Both files declare the same inputs: every free input variable either cone reads.
    let vars: BTreeSet<&String> = gc.free.values().chain(rc.free.values()).collect();
    let pis: BTreeMap<String, usize> = vars.into_iter().enumerate().map(|(k, v)| (v.clone(), k)).collect();
    let dir = Scratch::new()?;
    let gp = dir.write("golden.blif", &write_blif("golden", &gc, &pis, &eps.golden_nets)?)?;
    let rp = dir.write("revised.blif", &write_blif("revised", &rc, &pis, &eps.revised_nets)?)?;

    let mut abc = Abc::start().map_err(|e| e.to_string())?;
    // ⛔ A MULTI-output miter (one output per endpoint) and `iprove`, which names the output it
    // disproves. Not `&cec -m`: that assumes a single-output miter and checks output 0 only.
    // Captured: ABC prints its verdict to standard output, where this tool writes its report.
    abc.execute_captured(&format!("miter -m {} {}", arg(&gp)?, arg(&rp)?)).map_err(|e| e.to_string())?;
    abc.execute_captured("strash; iprove").map_err(|e| e.to_string())?;
    let verdict = match abc.prob_status() {
        ProbStatus::Unsat => Verdict::Equivalent,
        ProbStatus::Sat => {
            let cex = abc.cex().ok_or("ABC reported a difference without a counterexample")?;
            let endpoint = eps
                .shared
                .get(cex.po as usize)
                .cloned()
                .ok_or_else(|| format!("ABC disproved output {} of {}", cex.po, eps.shared.len()))?;
            let bits = abc.cex_inputs(0).ok_or("ABC's counterexample has no input values")?;
            let net: BTreeMap<String, &str> = pis.iter().map(|(n, &k)| (pi_name(k), n.as_str())).collect();
            let mut counterexample = Vec::new();
            for (i, v) in bits.into_iter().enumerate() {
                let name = abc.pi_name(i as i32).ok_or("counterexample input without a name")?;
                let n = net.get(&name).ok_or_else(|| format!("unknown miter input {name}"))?;
                counterexample.push((n.to_string(), v));
            }
            counterexample.sort();
            Verdict::Differs { endpoint, counterexample }
        }
        _ => Verdict::Undecided,
    };
    Ok(report(verdict))
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
    fn file(p: &str) -> Netlist {
        crate::netlist::load(p).unwrap()
    }

    /// The value a BLIF cover gives an input combination (rows of one phase, as `cover` writes).
    fn eval(rows: &[String], ins: &[bool]) -> bool {
        let mut phase = true;
        for r in rows {
            let (cube, out) = r.split_once(' ').unwrap_or(("", r));
            phase = out == "1";
            if cube.chars().zip(ins).all(|(c, &v)| c == '-' || (c == '1') == v) {
                return phase;
            }
        }
        !phase
    }

    /// An endpoint's value under an assignment of the free inputs, by simulating the cone the
    /// files were written from (unassigned free inputs are 0).
    fn value(nl: &Netlist, ep: &str, cex: &[(String, bool)]) -> bool {
        let l = lib();
        let d = Design::new(nl, &l);
        let c = lec::cone(&d, &[ep.to_string()]).unwrap();
        let cex: BTreeMap<&str, bool> = cex.iter().map(|(k, b)| (k.as_str(), *b)).collect();
        let mut v: BTreeMap<String, bool> = c.free.iter().map(|(n, var)| (n.clone(), *cex.get(var.as_str()).unwrap_or(&false))).collect();
        for g in &c.gates {
            let (order, rows) = cover(&g.logic, &g.pins).unwrap();
            let ins: Vec<bool> = order
                .iter()
                .map(|&i| match &g.ins[i] {
                    Src::Net(n) => *v.get(n).unwrap_or(&false),
                    Src::Const(b) => *b,
                })
                .collect();
            let out = eval(&rows, &ins);
            v.insert(g.out.clone(), out);
        }
        *v.get(ep).unwrap_or(&false)
    }

    #[test]
    fn de_morgan_rewrite_is_equivalent() {
        let g = nl("module t(a,b,f);\ninput a,b; output f;\nAND2 g(.A(a),.B(b),.Z(f));\nendmodule\n");
        let r = nl("module t(a,b,f);\ninput a,b; output f;\nwire na,nb,o;\n\
             INV i1(.A(a),.Y(na));\nINV i2(.A(b),.Y(nb));\nOR2 o1(.A(na),.B(nb),.Z(o));\nINV i3(.A(o),.Y(f));\nendmodule\n");
        let rep = equivalence(&g, &r, &lib()).unwrap();
        assert_eq!(rep.verdict, Verdict::Equivalent);
        assert!(rep.equivalent());
        assert_eq!(rep.compared, 1);
    }

    /// AND vs OR differs exactly when a != b: the counterexample must be such an assignment.
    #[test]
    fn a_real_bug_is_caught_with_a_counterexample_that_shows_it() {
        let g = nl("module t(a,b,f);\ninput a,b; output f;\nAND2 g(.A(a),.B(b),.Z(f));\nendmodule\n");
        let r = nl("module t(a,b,f);\ninput a,b; output f;\nOR2 g(.A(a),.B(b),.Z(f));\nendmodule\n");
        let rep = equivalence(&g, &r, &lib()).unwrap();
        let Verdict::Differs { endpoint, counterexample } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!(endpoint, "f");
        let v = |n: &str| counterexample.iter().find(|(k, _)| k == n).map(|(_, v)| *v).unwrap();
        assert_ne!(v("a"), v("b"), "{counterexample:?}");
        assert_ne!(value(&g, endpoint, counterexample), value(&r, endpoint, counterexample));
    }

    /// Only the last of three endpoints differs: the verdict names THAT endpoint, so the output
    /// order written to the files and the order read back agree (a reversed order names `x`).
    #[test]
    fn the_differing_endpoint_is_named() {
        // Cells the example Liberty has: one it lacks leaves its output undriven, a free input in
        // BOTH designs, and the endpoint compares equal whatever the cell was.
        let g = nl("module t(a,b,x,y,z);\ninput a,b; output x,y,z;\n\
             AND2 g1(.A(a),.B(b),.Z(x));\nOR2 g2(.A(a),.B(b),.Z(y));\nAND2 g3(.A(a),.B(b),.Z(z));\nendmodule\n");
        let r = nl("module t(a,b,x,y,z);\ninput a,b; output x,y,z;\n\
             AND2 g1(.A(a),.B(b),.Z(x));\nOR2 g2(.A(a),.B(b),.Z(y));\nOR2 g3(.A(a),.B(b),.Z(z));\nendmodule\n");
        let rep = equivalence(&g, &r, &lib()).unwrap();
        let Verdict::Differs { endpoint, counterexample } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!(endpoint, "z");
        assert_ne!(value(&g, endpoint, counterexample), value(&r, endpoint, counterexample));
    }

    /// A tied pin reads a constant net: `AND2(a, 1'b0)` against a buffer differs exactly at a = 1,
    /// and `AND2(a, 1'b1)` is the buffer.
    #[test]
    fn a_tied_pin_is_an_input() {
        let buf = nl("module t(a,f);\ninput a; output f;\nBUF b(.A(a),.Y(f));\nendmodule\n");
        let and0 = nl("module t(a,f);\ninput a; output f;\nAND2 g(.A(a),.B(1'b0),.Z(f));\nendmodule\n");
        let and1 = nl("module t(a,f);\ninput a; output f;\nAND2 g(.A(a),.B(1'b1),.Z(f));\nendmodule\n");
        let rep = equivalence(&and0, &buf, &lib()).unwrap();
        let Verdict::Differs { endpoint, counterexample } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!(counterexample, &[("a".to_string(), true)]);
        assert_ne!(value(&and0, endpoint, counterexample), value(&buf, endpoint, counterexample));
        assert_eq!(equivalence(&and1, &buf, &lib()).unwrap().verdict, Verdict::Equivalent);
    }

    /// An unconnected input floats: the cone this engine writes refuses it, as the BDD engine does.
    #[test]
    fn an_unconnected_input_is_an_error() {
        let buf = nl("module t(a,f);\ninput a; output f;\nBUF b(.A(a),.Y(f));\nendmodule\n");
        let open = nl("module t(a,f);\ninput a; output f;\nAND2 g(.A(a),.Z(f));\nendmodule\n");
        let e = equivalence(&open, &buf, &lib()).unwrap_err();
        assert!(e.contains("input pin `B` of instance `g` (AND2) is unconnected"), "{e}");
    }

    /// A supply net is its constant in the cone this engine writes, as in the BDD engine.
    #[test]
    fn a_supply_net_is_its_constant() {
        let buf = nl("module t(a,f);\ninput a; output f;\nBUF b(.A(a),.Y(f));\nendmodule\n");
        let and1 = nl("module t(a,f);\ninput a; output f;\nsupply1 vdd;\nAND2 g(.A(a),.B(vdd),.Z(f));\nendmodule\n");
        assert_eq!(equivalence(&and1, &buf, &lib()).unwrap().verdict, Verdict::Equivalent);
        let and0 = nl("module t(a,f);\ninput a; output f;\nsupply0 gnd;\nAND2 g(.A(a),.B(gnd),.Z(f));\nendmodule\n");
        let rep = equivalence(&and0, &buf, &lib()).unwrap();
        let Verdict::Differs { counterexample, .. } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!(counterexample, &[("a".to_string(), true)]);
    }

    /// The function path through ABC: an AOI, a half adder's two outputs and a tie cell, written
    /// as on-set covers, agree with the same logic in primitives; an AO21 for the AOI differs, and
    /// the counterexample shows it.
    #[test]
    fn cells_are_their_liberty_functions() {
        let l = Lib::load("tests/data/func.lib").unwrap();
        let g = nl("module t(a,b,c,y,co,s);\ninput a,b,c; output y,co,s;\nwire k;\n\
             AOI21X g(.A1(a),.A2(b),.B1(c),.Y(y));\nTIEHI t(.HI(k));\nHAX h(.A(a),.B(k),.CO(co),.S(s));\nendmodule\n");
        let r = nl("module t(a,b,c,y,co,s);\ninput a,b,c; output y,co,s;\nwire ab,o;\n\
             AND2X g1(.A(a),.B(b),.Y(ab));\nOR2X g2(.A(ab),.B(c),.Y(o));\nINVX g3(.A(o),.Y(y));\n\
             BUFX g4(.A(a),.Y(co));\nINVX g5(.A(a),.Y(s));\nendmodule\n");
        assert_eq!(equivalence(&g, &r, &l).unwrap().verdict, Verdict::Equivalent);
        let ao = nl("module t(a,b,c,y,co,s);\ninput a,b,c; output y,co,s;\n\
             AO21X g(.A1(a),.A2(b),.B1(c),.X(y));\nBUFX g4(.A(a),.Y(co));\nINVX g5(.A(a),.Y(s));\nendmodule\n");
        let rep = equivalence(&g, &ao, &l).unwrap();
        let Verdict::Differs { endpoint, counterexample } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!(endpoint, "y");
        let v = |nl: &Netlist| {
            let d = Design::new(nl, &l);
            let c = lec::cone(&d, std::slice::from_ref(endpoint)).unwrap();
            let cex: BTreeMap<&str, bool> = counterexample.iter().map(|(k, b)| (k.as_str(), *b)).collect();
            let mut v: BTreeMap<String, bool> = c.free.iter().map(|(n, var)| (n.clone(), *cex.get(var.as_str()).unwrap_or(&false))).collect();
            for g in &c.gates {
                let (order, rows) = cover(&g.logic, &g.pins).unwrap();
                let ins: Vec<bool> = order.iter().map(|&i| match &g.ins[i] { Src::Net(n) => *v.get(n).unwrap_or(&false), Src::Const(b) => *b }).collect();
                let out = eval(&rows, &ins);
                v.insert(g.out.clone(), out);
            }
            v[endpoint.as_str()]
        };
        assert_ne!(v(&g), v(&ao));
    }

    /// Registers match by instance through this engine too: a renamed Q net behind an output
    /// buffer and a renamed D net are still the same register; a rewired D is caught at `r/D`.
    #[test]
    fn registers_match_by_instance_not_by_net() {
        let g = nl("module t(a,b,clk,q);\ninput a,b,clk; output q;\nwire d;\n\
             AND2 g(.A(a),.B(q),.Z(d));\nDFF r(.CK(clk),.D(d),.Q(q));\nendmodule\n");
        let r = nl("module t(a,b,clk,q);\ninput a,b,clk; output q;\nwire d2,net9;\n\
             AND2 g(.A(a),.B(net9),.Z(d2));\nDFF r(.CK(clk),.D(d2),.Q(net9));\nBUF ob(.A(net9),.Y(q));\nendmodule\n");
        let rep = equivalence(&g, &r, &lib()).unwrap();
        assert_eq!(rep.verdict, Verdict::Equivalent);
        assert_eq!(rep.compared, 2);
        let w = nl("module t(a,b,clk,q);\ninput a,b,clk; output q;\nwire d2,net9;\n\
             OR2 g(.A(a),.B(net9),.Z(d2));\nDFF r(.CK(clk),.D(d2),.Q(net9));\nBUF ob(.A(net9),.Y(q));\nendmodule\n");
        let rep = equivalence(&g, &w, &lib()).unwrap();
        let Verdict::Differs { endpoint, counterexample } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!(endpoint, "r/D");
        let v = |n: &str| counterexample.iter().find(|(k, _)| k == n).map(|(_, v)| *v);
        assert_ne!(v("a"), v("r/Q"), "{counterexample:?}");
    }

    /// a AND b against (a AND b) AND c differs ONLY at a = b = 1, c = 0, so the counterexample is
    /// exactly that assignment (an inverted one, a = b = 0, c = 1, shows nothing).
    #[test]
    fn the_counterexample_is_the_one_distinguishing_assignment() {
        let g = nl("module t(a,b,c,f);\ninput a,b,c; output f;\nAND2 g(.A(a),.B(b),.Z(f));\nendmodule\n");
        let r = nl("module t(a,b,c,f);\ninput a,b,c; output f;\nwire ab;\n\
             AND2 g1(.A(a),.B(b),.Z(ab));\nAND2 g2(.A(ab),.B(c),.Z(f));\nendmodule\n");
        let rep = equivalence(&g, &r, &lib()).unwrap();
        let Verdict::Differs { endpoint, counterexample } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!(endpoint, "f");
        let want: Vec<(String, bool)> = vec![("a".into(), true), ("b".into(), true), ("c".into(), false)];
        assert_eq!(counterexample, &want);
    }

    /// Twelve endpoints over twelve inputs; only `y10` differs. ABC matches the two files' inputs
    /// and outputs by NAME in alphabetical order, so with unpadded names output 10 (`o10`) would
    /// sort before output 2 and the verdict would name the wrong endpoint.
    #[test]
    fn output_order_survives_ten_or_more_endpoints() {
        let ports: Vec<String> = (0..12).map(|i| format!("a{i:02}")).chain((0..12).map(|i| format!("y{i:02}"))).collect();
        let module = |odd: usize| {
            let mut s = format!("module t({});\ninput {};\noutput {};\n", ports.join(","), ports[..12].join(","), ports[12..].join(","));
            for i in 0..12 {
                let cell = if i == odd { "OR2" } else { "AND2" };
                s += &format!("{cell} g{i}(.A(a{i:02}),.B(a{:02}),.Z(y{i:02}));\n", (i + 1) % 12);
            }
            s + "endmodule\n"
        };
        let g = nl(&module(usize::MAX));
        let r = nl(&module(10));
        let rep = equivalence(&g, &r, &lib()).unwrap();
        let Verdict::Differs { endpoint, counterexample } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!(endpoint, "y10");
        assert_ne!(value(&g, endpoint, counterexample), value(&r, endpoint, counterexample), "{counterexample:?}");
    }

    #[test]
    fn sequential_designs_are_cut_at_registers() {
        let g = nl("module t(a,b,clk,q);\ninput a,b,clk; output q;\nwire d;\n\
             AND2 g(.A(a),.B(b),.Z(d));\nDFF r(.CK(clk),.D(d),.Q(q));\nendmodule\n");
        let r = nl("module t(a,b,clk,q);\ninput a,b,clk; output q;\nwire na,nb,o,d;\n\
             INV i1(.A(a),.Y(na));\nINV i2(.A(b),.Y(nb));\nOR2 o1(.A(na),.B(nb),.Z(o));\n\
             INV i3(.A(o),.Y(d));\nDFF r(.CK(clk),.D(d),.Q(q));\nendmodule\n");
        let rep = equivalence(&g, &r, &lib()).unwrap();
        assert_eq!(rep.verdict, Verdict::Equivalent);
        assert!(rep.compared >= 2, "q and the flop's D");
    }

    /// The shipped examples: both engines give the same verdict.
    #[test]
    fn the_examples_agree_with_the_bdd_engine() {
        let l = lib();
        let g = file("examples/golden.v");
        for rev in ["examples/revised_ok.v", "examples/revised_bug.v"] {
            let r = file(rev);
            let bdd = lec::equivalence(&g, &r, &l).unwrap();
            let abc = equivalence(&g, &r, &l).unwrap();
            assert_eq!(abc.equivalent(), bdd.equivalent, "{rev}");
            if let Verdict::Differs { endpoint, counterexample } = &abc.verdict {
                assert!(bdd.mismatches.iter().any(|m| &m.endpoint == endpoint), "{rev}: {endpoint}");
                assert_ne!(value(&g, endpoint, counterexample), value(&r, endpoint, counterexample), "{rev}");
            }
        }
    }

    #[test]
    fn cross_check_flags_a_disagreement() {
        let l = lib();
        let g = file("examples/golden.v");
        let ok = file("examples/revised_ok.v");
        let bug = file("examples/revised_bug.v");
        let bdd_ok = lec::equivalence(&g, &ok, &l).unwrap();
        let bdd_bug = lec::equivalence(&g, &bug, &l).unwrap();
        let abc_ok = equivalence(&g, &ok, &l).unwrap();
        let abc_bug = equivalence(&g, &bug, &l).unwrap();
        assert_eq!(cross_check(&bdd_ok, &abc_ok), Ok(()));
        assert_eq!(cross_check(&bdd_bug, &abc_bug), Ok(()));
        // Each verdict against the other case's BDD report must be a disagreement.
        assert!(cross_check(&bdd_bug, &abc_ok).is_err());
        assert!(cross_check(&bdd_ok, &abc_bug).is_err());
        let undecided = AbcReport { verdict: Verdict::Undecided, ..abc_ok };
        assert_eq!(cross_check(&bdd_bug, &undecided), Ok(()));
        let as_lec: crate::lec::LecReport = undecided.into();
        assert!(as_lec.undecided && !as_lec.equivalent && as_lec.mismatches.is_empty());
    }

    /// Every primitive's cover against its definition, on every input combination.
    #[test]
    fn covers_match_the_primitives() {
        let p = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        for n in 1..=4usize {
            let pins = p(&["A", "B", "C", "D"][..n]);
            for m in 0..1u32 << n {
                let x: Vec<bool> = (0..n).map(|i| m >> i & 1 == 1).collect();
                let and = x.iter().all(|&v| v);
                let or = x.iter().any(|&v| v);
                let xor = x.iter().filter(|&&v| v).count() % 2 == 1;
                for (op, want) in [(Op::And, and), (Op::Nand, !and), (Op::Or, or), (Op::Nor, !or), (Op::Xor, xor), (Op::Xnor, !xor)] {
                    let (order, rows) = cover(&Logic::Prim(op), &pins).unwrap();
                    let ins: Vec<bool> = order.iter().map(|&i| x[i]).collect();
                    assert_eq!(eval(&rows, &ins), want, "{op:?} {x:?}");
                    assert_eq!(lec::prim_value(op, &pins, &x), Ok(want), "{op:?} {x:?} (the replay's value)");
                }
            }
        }
        // MUX with its pins listed out of order: out = S ? B : A.
        let pins = p(&["S", "A", "B"]);
        for m in 0..8u32 {
            let (s, a, b) = (m & 1 == 1, m & 2 == 2, m & 4 == 4);
            let (order, rows) = cover(&Logic::Prim(Op::Mux), &pins).unwrap();
            let x = [s, a, b];
            let ins: Vec<bool> = order.iter().map(|&i| x[i]).collect();
            assert_eq!(eval(&rows, &ins), if s { b } else { a }, "s={s} a={a} b={b}");
            assert_eq!(lec::prim_value(Op::Mux, &pins, &x), Ok(if s { b } else { a }));
        }
        let (_, rows) = cover(&Logic::Prim(Op::Not), &p(&["A"])).unwrap();
        assert!(eval(&rows, &[false]) && !eval(&rows, &[true]));
    }
}
