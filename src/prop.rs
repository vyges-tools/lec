//! Property checking through ABC (`--features abc`): is a net of one netlist ever 1?
//!
//! The property is a safety one on the gate-level netlist: each named net must stay 0 on every
//! input sequence from the all-zero register state (an error flag, a "two grants at once" net, an
//! assertion synthesized into gates). The model is the sequential one [`crate::sec`] uses: registers
//! as their Liberty `ff` groups on one clock, a gate as its Liberty function.
//!
//! ABC gets the design as BLIF with one output per property net, and either
//! - `pdr`, which proves every net stays 0 or names the first one it drives to 1, its cycle and
//!   the inputs of every cycle up to it; or
//! - with a bound of N cycles, `bmc3 -F N+1`, which only looks at cycles 0 to N (`-F` counts
//!   frames 0 to F-1): no failure there is not a proof.

use std::collections::{BTreeMap, BTreeSet};

use vyges_abc_lib::{Abc, ProbStatus};

use crate::abc::{arg, write_blif, Scratch};
use crate::lec::{self, Design};
use crate::liberty::Lib;
use crate::netlist::Netlist;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropVerdict {
    /// Every net stays 0 on every input sequence from the all-zero state.
    Holds,
    /// No net is 1 in cycles 0 to `cycles` (a bounded check: not a proof).
    HoldsWithin { cycles: usize },
    /// `net` is 1 in clock cycle `cycle` (0: before any edge) under the inputs `trace[c]` of each
    /// cycle `c` up to it.
    Fails { net: String, cycle: usize, trace: Vec<Vec<(String, bool)>> },
    /// ABC gave up within its limits.
    Undecided,
}

#[derive(Debug, Clone)]
pub struct PropReport {
    pub verdict: PropVerdict,
    /// The property nets, in the order given.
    pub nets: Vec<String>,
    /// Registers the nets depend on.
    pub registers: usize,
    pub clock: Option<String>,
}

/// Check that each of `nets` stays 0: unbounded (`pdr`), or over cycles 0 to `bound`.
pub fn never(design: &Netlist, lib: &Lib, nets: &[String], bound: Option<usize>) -> Result<PropReport, String> {
    if lib.cells.is_empty() {
        return Err("no cells in the Liberty".into());
    }
    if nets.is_empty() {
        return Err("no property net given".into());
    }
    let d = Design::sequential(design, lib);
    let known: BTreeSet<&str> = design
        .inputs
        .iter()
        .chain(&design.outputs)
        .map(String::as_str)
        .chain(design.insts.iter().flat_map(|i| i.conns.iter().map(|(_, n)| n.as_str())))
        .collect();
    if let Some(n) = nets.iter().find(|n| !known.contains(n.as_str())) {
        return Err(format!("no net `{n}` in the design"));
    }
    let c = lec::seq_cone(&d, nets)?;
    let clock = crate::sec::one_clock("design", &c)?;
    let report = |verdict| PropReport { verdict, nets: nets.to_vec(), registers: c.regs.len(), clock: clock.clone() };
    let pis: BTreeMap<String, usize> =
        c.free.values().collect::<BTreeSet<_>>().into_iter().enumerate().map(|(k, v)| (v.clone(), k)).collect();
    let dir = Scratch::new()?;
    let path = dir.write("design.blif", &write_blif("design", &c, &pis, nets)?)?;

    let mut abc = Abc::start().map_err(|e| e.to_string())?;
    abc.execute_captured(&format!("read_blif {}", arg(&path)?)).map_err(|e| e.to_string())?;
    let cmd = match bound {
        None => "strash; pdr".to_string(),
        Some(n) => format!("strash; bmc3 -F {}", n + 1),
    };
    crate::sec::in_dir(&dir, || abc.execute_captured(&cmd))?.map_err(|e| e.to_string())?;
    let verdict = match abc.prob_status() {
        ProbStatus::Unsat => PropVerdict::Holds,
        ProbStatus::Sat => {
            let cex = abc.cex().ok_or("ABC reported a failure without a counterexample")?;
            let k = cex.po as usize;
            let net = nets.get(k).cloned().ok_or_else(|| format!("ABC disproved output {k} of {}", nets.len()))?;
            let trace = crate::sec::trace(&abc, &pis, cex.frame)?;
            // ⛔ Never report a failure the model does not show: replay it.
            let seen = crate::sec::replay(&c, std::slice::from_ref(&net), &trace)?;
            if seen.last().map(|o| o[0]) != Some(true) {
                return Err(format!("ABC's counterexample for `{net}` (cycle {}) does not replay: the net is 0 there", cex.frame));
            }
            PropVerdict::Fails { net, cycle: cex.frame as usize, trace }
        }
        _ => match bound {
            Some(cycles) => PropVerdict::HoldsWithin { cycles },
            None => PropVerdict::Undecided,
        },
    };
    Ok(report(verdict))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lib() -> Lib {
        Lib::load(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/seq.lib")).expect("seq.lib")
    }

    /// A 2-bit counter from 0 with an enable; `c3` is 1 when the count is 3, `c2` when it is 2.
    /// `wrap` sends it back to 0 after 2, so it never reaches 3.
    fn counter(wrap: bool) -> Netlist {
        let src = if wrap {
            // n0 = !q1 & (en ^ q0); n1 = (en & q0) | (!en & q1): 0 -> 1 -> 2 -> 0
            "module t(clk,en,c2,c3);\ninput clk,en; output c2,c3;\nwire q0,q1,nq0,nq1,ne,x,d0,a,b,d1;\n\
             INV i0(.A(q0),.Y(nq0));\nINV i1(.A(q1),.Y(nq1));\nINV ie(.A(en),.Y(ne));\n\
             XOR2 x0(.A(en),.B(q0),.Y(x));\nAND2 g0(.A(x),.B(nq1),.Y(d0));\nDFF r0(.CK(clk),.D(d0),.Q(q0));\n\
             AND2 ga(.A(en),.B(q0),.Y(a));\nAND2 gb(.A(ne),.B(q1),.Y(b));\nOR2 g1(.A(a),.B(b),.Y(d1));\nDFF r1(.CK(clk),.D(d1),.Q(q1));\n\
             AND2 o2(.A(nq0),.B(q1),.Y(c2));\nAND2 o3(.A(q0),.B(q1),.Y(c3));\nendmodule\n"
        } else {
            "module t(clk,en,c2,c3);\ninput clk,en; output c2,c3;\nwire q0,q1,nq0,d0,c,d1;\n\
             INV i0(.A(q0),.Y(nq0));\n\
             XOR2 x0(.A(en),.B(q0),.Y(d0));\nDFF r0(.CK(clk),.D(d0),.Q(q0));\n\
             AND2 g(.A(en),.B(q0),.Y(c));\nXOR2 x1(.A(c),.B(q1),.Y(d1));\nDFF r1(.CK(clk),.D(d1),.Q(q1));\n\
             AND2 o2(.A(nq0),.B(q1),.Y(c2));\nAND2 o3(.A(q0),.B(q1),.Y(c3));\nendmodule\n"
        };
        crate::netlist::parse(src).unwrap()
    }
    fn s(v: &[&str]) -> Vec<String> {
        v.iter().map(|x| x.to_string()).collect()
    }

    /// The wrapping counter never reaches 3: proven. The plain one does after three enabled cycles:
    /// the verdict names `c3`, cycle 3, and the trace enables it in cycles 0 to 2.
    #[test]
    fn a_property_holds_or_fails_at_its_cycle() {
        let rep = never(&counter(true), &lib(), &s(&["c3"]), None).unwrap();
        assert_eq!(rep.verdict, PropVerdict::Holds);
        assert_eq!((rep.registers, rep.clock.as_deref()), (2, Some("clk")));
        let rep = never(&counter(false), &lib(), &s(&["c3"]), None).unwrap();
        let PropVerdict::Fails { net, cycle, trace } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!((net.as_str(), *cycle), ("c3", 3));
        for c in &trace[..3] {
            assert_eq!(c, &[("en".to_string(), true)]);
        }
    }

    /// Of two nets, the one that fails is named: in the wrapping counter `c3` holds and `c2` rises
    /// in cycle 2. An internal net works as well as a port.
    #[test]
    fn the_failing_net_is_named() {
        let rep = never(&counter(true), &lib(), &s(&["c3", "c2"]), None).unwrap();
        let PropVerdict::Fails { net, cycle, .. } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!((net.as_str(), *cycle), ("c2", 2));
        let rep = never(&counter(true), &lib(), &s(&["q1"]), None).unwrap();
        let PropVerdict::Fails { net, cycle, .. } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!((net.as_str(), *cycle), ("q1", 2));
    }

    /// A bound of N cycles looks at cycles 0 to N: `c3` first rises in cycle 3, so a bound of 2 sees
    /// nothing (and says so, not "holds") and a bound of 3 finds it.
    #[test]
    fn a_bounded_check_covers_cycles_0_to_n() {
        let rep = never(&counter(false), &lib(), &s(&["c3"]), Some(2)).unwrap();
        assert_eq!(rep.verdict, PropVerdict::HoldsWithin { cycles: 2 });
        let rep = never(&counter(false), &lib(), &s(&["c3"]), Some(3)).unwrap();
        let PropVerdict::Fails { cycle, .. } = rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!(cycle, 3);
    }

    #[test]
    fn an_unknown_net_is_an_error() {
        let e = never(&counter(true), &lib(), &s(&["nope"]), None).unwrap_err();
        assert!(e.contains("no net `nope`"), "{e}");
    }
}
