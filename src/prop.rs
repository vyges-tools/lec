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
//!
//! Before ABC, a one-cycle BDD of the property nets (while it stays under [`BDD_LIMIT`] nodes)
//! decides the nets that are 0 in every state, and every net of a register-free design. Each net's
//! result names the engine that decided it ([`Engine`]) and, where that engine has one, a depth
//! ([`Depth`]), so a proof is never ambiguous between the pre-pass and ABC.

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

/// The engine that decided a property net.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Engine {
    /// The one-cycle BDD before ABC: 0 in every state, or (no register) 1 under some input.
    BddPrepass,
    /// ABC's `pdr` (unbounded).
    Pdr,
    /// ABC's `bmc3` (bounded; it proves outright only when it has visited every reachable state).
    Bmc,
}

impl Engine {
    /// The name in the JSON report.
    pub fn as_str(self) -> &'static str {
        match self {
            Engine::BddPrepass => "bdd-prepass",
            Engine::Pdr => "pdr",
            Engine::Bmc => "bmc",
        }
    }
}

/// How deep the deciding engine went, where it has a depth.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Depth {
    /// A clock cycle (0: before any edge): where a net fails, or the last cycle a bounded check
    /// covered.
    Cycle(usize),
    /// The frame `k` of `pdr`'s inductive invariant (`Invariant F[k]` in ABC's output).
    PdrFrame(usize),
}

/// What one property net came to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// Never 1.
    Holds,
    /// Not 1 in the cycles a bounded check covered (not a proof).
    HoldsWithin,
    /// 1 in some cycle.
    Fails,
    /// The engine gave up within its limits.
    Undecided,
    /// Not decided: the engine stopped at another net's failure first.
    NotReached,
}

impl Outcome {
    /// The name in the JSON report.
    pub fn as_str(self) -> &'static str {
        match self {
            Outcome::Holds => "holds",
            Outcome::HoldsWithin => "holds_within",
            Outcome::Fails => "fails",
            Outcome::Undecided => "undecided",
            Outcome::NotReached => "not_reached",
        }
    }
}

/// One property net's result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Property {
    pub net: String,
    pub outcome: Outcome,
    /// `None` when nothing decided it ([`Outcome::Undecided`], [`Outcome::NotReached`]).
    pub decided_by: Option<Engine>,
    pub depth: Option<Depth>,
}

#[derive(Debug, Clone)]
pub struct PropReport {
    pub verdict: PropVerdict,
    /// The property nets, in the order given.
    pub nets: Vec<String>,
    /// Registers the nets depend on.
    pub registers: usize,
    pub clock: Option<String>,
    /// Each net of `nets`, in that order: its outcome, the engine that decided it, its depth.
    pub properties: Vec<Property>,
}

/// Nodes the one-cycle BDD of the property nets may grow to before the question is left to ABC.
const BDD_LIMIT: usize = 1 << 20;

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
    let report = |verdict, properties| PropReport { verdict, nets: nets.to_vec(), registers: c.regs.len(), clock: clock.clone(), properties };
    let all_nets = nets;
    let property = |net: &String, outcome, decided_by, depth| Property { net: net.clone(), outcome, decided_by, depth };
    let pis: BTreeMap<String, usize> =
        c.free.values().collect::<BTreeSet<_>>().into_iter().enumerate().map(|(k, v)| (v.clone(), k)).collect();

    // One cycle's logic, exactly, while it stays small. ⛔ ABC cannot decide a property net that is
    // constant 0: `pdr` drops the output and reports UNDECIDED, and `bmc3` refuses a design with no
    // register. Both cases are decided here instead.
    // - A net that is 0 for every state and every input is 0 in every cycle: it holds.
    // - With no register every cycle is cycle 0, so a net that can be 1 is 1 in cycle 0, under the
    //   inputs of a satisfying assignment (replayed on the model, as ABC's are).
    let mut live: Vec<String> = nets.to_vec();
    if let Some((bdd, outs, names)) = lec::cone_bdds(&c, nets, BDD_LIMIT)? {
        if c.regs.is_empty() {
            let Some((k, &f)) = outs.iter().enumerate().find(|(_, &f)| f != bdd.zero()) else {
                let props = nets.iter().map(|n| property(n, Outcome::Holds, Some(Engine::BddPrepass), None)).collect();
                return Ok(report(PropVerdict::Holds, props));
            };
            let set: BTreeMap<u32, bool> = bdd.sat_one(f).expect("a non-zero BDD is satisfiable").into_iter().collect();
            let inputs: Vec<(String, bool)> = pis
                .keys()
                .map(|v| {
                    let val = names.iter().position(|n| n == v).and_then(|i| set.get(&(i as u32)).copied()).unwrap_or(false);
                    (v.clone(), val)
                })
                .collect();
            let net = nets[k].clone();
            let trace = vec![inputs];
            let seen = crate::sec::replay(&c, std::slice::from_ref(&net), &trace)?;
            if seen.last().map(|o| o[0]) != Some(true) {
                return Err(format!("the cycle-0 assignment for `{net}` does not replay: the net is 0 there"));
            }
            let props = nets
                .iter()
                .zip(&outs)
                .enumerate()
                .map(|(i, (n, &g))| match (i == k, g == bdd.zero()) {
                    (true, _) => property(n, Outcome::Fails, Some(Engine::BddPrepass), Some(Depth::Cycle(0))),
                    (false, true) => property(n, Outcome::Holds, Some(Engine::BddPrepass), None),
                    (false, false) => property(n, Outcome::NotReached, None, None),
                })
                .collect();
            return Ok(report(PropVerdict::Fails { net, cycle: 0, trace }, props));
        }
        live = nets.iter().zip(&outs).filter(|(_, &f)| f != bdd.zero()).map(|(n, _)| n.clone()).collect();
        if live.is_empty() {
            let props = nets.iter().map(|n| property(n, Outcome::Holds, Some(Engine::BddPrepass), None)).collect();
            return Ok(report(PropVerdict::Holds, props));
        }
    }
    let nets = live.as_slice();
    let dir = Scratch::new()?;
    let path = dir.write("design.blif", &write_blif("design", &c, &pis, nets)?)?;

    let mut abc = Abc::start().map_err(|e| e.to_string())?;
    abc.execute_captured(&format!("read_blif {}", arg(&path)?)).map_err(|e| e.to_string())?;
    let cmd = match bound {
        None => "strash; pdr".to_string(),
        Some(n) => format!("strash; bmc3 -F {}", n + 1),
    };
    let said = crate::sec::in_dir(&dir, || abc.execute_captured(&cmd))?.map_err(|e| e.to_string())?;
    let engine = if bound.is_some() { Engine::Bmc } else { Engine::Pdr };
    // ABC's depth for a proof or a bounded run, from what it printed.
    let proof_depth = match engine {
        Engine::Pdr => pdr_frame(&said).map(Depth::PdrFrame),
        _ => bmc_frames(&said).map(|f| Depth::Cycle(f.saturating_sub(1))),
    };
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
    // A net the BDD found 0 in every state was decided before ABC; ABC decided the live ones.
    let props = all_nets
        .iter()
        .map(|n| {
            if !nets.contains(n) {
                return property(n, Outcome::Holds, Some(Engine::BddPrepass), None);
            }
            match &verdict {
                PropVerdict::Holds => property(n, Outcome::Holds, Some(engine), proof_depth),
                PropVerdict::HoldsWithin { cycles } => {
                    property(n, Outcome::HoldsWithin, Some(engine), Some(proof_depth.unwrap_or(Depth::Cycle(*cycles))))
                }
                PropVerdict::Fails { net, cycle, .. } if net == n => {
                    property(n, Outcome::Fails, Some(engine), Some(Depth::Cycle(*cycle)))
                }
                PropVerdict::Fails { .. } => property(n, Outcome::NotReached, None, None),
                PropVerdict::Undecided => property(n, Outcome::Undecided, None, None),
            }
        })
        .collect();
    Ok(report(verdict, props))
}

/// `k` of `pdr`'s `Invariant F[k] : ...` line, printed when it proves the property.
fn pdr_frame(said: &str) -> Option<usize> {
    let rest = &said[said.find("Invariant F[")? + "Invariant F[".len()..];
    rest[..rest.find(']')?].parse().ok()
}

/// The frames `bmc3` covered: `No output asserted in N frames.` (the bound reached) or `after
/// completing N frames` (every reachable state visited, a proof).
fn bmc_frames(said: &str) -> Option<usize> {
    for key in ["No output asserted in ", "after completing "] {
        if let Some(i) = said.find(key) {
            let rest = &said[i + key.len()..];
            let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
            if let Ok(n) = rest[..end].parse() {
                return Some(n);
            }
        }
    }
    None
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

    /// A net tied to constant 0 holds, with or without registers in the design: ABC's `pdr` drops a
    /// constant output and says UNDECIDED, so the one-cycle BDD decides it. A net that is 0 in every
    /// state (q AND NOT q) holds the same way.
    #[test]
    fn a_constant_zero_net_holds() {
        let tie = crate::netlist::parse(
            "module t(clk,a,p);\ninput clk,a; output p;\nwire z;\nTIE0 t0(.LO(z));\nBUF b(.A(z),.Y(p));\nendmodule\n",
        )
        .unwrap();
        let rep = never(&tie, &lib(), &s(&["p"]), None).unwrap();
        assert_eq!((rep.verdict, rep.registers), (PropVerdict::Holds, 0));
        let qq = crate::netlist::parse(
            "module t(clk,en,p);\ninput clk,en; output p;\nwire q,d,nq;\n\
             XOR2 x(.A(en),.B(q),.Y(d));\nDFF r(.CK(clk),.D(d),.Q(q));\nINV i(.A(q),.Y(nq));\nAND2 a(.A(q),.B(nq),.Y(p));\nendmodule\n",
        )
        .unwrap();
        let rep = never(&qq, &lib(), &s(&["p"]), None).unwrap();
        assert_eq!((rep.verdict, rep.registers), (PropVerdict::Holds, 1));
        // and beside a net that does fail, the failing one is still named
        let rep = never(&qq, &lib(), &s(&["p", "q"]), None).unwrap();
        let PropVerdict::Fails { net, cycle, .. } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!((net.as_str(), *cycle), ("q", 1));
    }

    /// With no register every cycle is cycle 0: a net that can be 1 is 1 there, under the inputs
    /// that make it 1.
    #[test]
    fn a_register_free_net_fails_in_cycle_0() {
        let and = crate::netlist::parse(
            "module t(clk,a,b,p);\ninput clk,a,b; output p;\nAND2 g(.A(a),.B(b),.Y(p));\nendmodule\n",
        )
        .unwrap();
        let rep = never(&and, &lib(), &s(&["p"]), None).unwrap();
        let PropVerdict::Fails { net, cycle, trace } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!((net.as_str(), *cycle), ("p", 0));
        assert_eq!(trace, &vec![vec![("a".to_string(), true), ("b".to_string(), true)]]);
    }

    /// `assign p2 = p1;` is a wire: p2 is p1's value, never a free input of its own.
    #[test]
    fn an_aliased_output_is_its_net() {
        let src = |tie: &str| {
            crate::netlist::parse(&format!(
                "module t(clk,a,p1,p2);\ninput clk,a; output p1,p2;\nwire z;\n{tie}\nBUF b(.A(z),.Y(p1));\nassign p2 = p1;\nendmodule\n"
            ))
            .unwrap()
        };
        let rep = never(&src("TIE0 t0(.LO(z));"), &lib(), &s(&["p2"]), None).unwrap();
        assert_eq!(rep.verdict, PropVerdict::Holds);
        let rep = never(&src("BUF t0(.A(a),.Y(z));"), &lib(), &s(&["p2"]), None).unwrap();
        let PropVerdict::Fails { net, trace, .. } = &rep.verdict else { panic!("{:?}", rep.verdict) };
        assert_eq!((net.as_str(), trace[0].as_slice()), ("p2", [("a".to_string(), true)].as_slice()));
    }

    fn decided(rep: &PropReport) -> Vec<(&str, Outcome, Option<Engine>, Option<Depth>)> {
        rep.properties.iter().map(|p| (p.net.as_str(), p.outcome, p.decided_by, p.depth)).collect()
    }

    /// Each net names the engine that decided it, so a proof is never ambiguous between the BDD
    /// pre-pass and ABC. In `q AND NOT q` beside `q`: `p` is 0 in every state (the pre-pass), `q`
    /// rises in cycle 1 (`pdr`). In the wrapping counter, `c3` is proved by `pdr` with its
    /// invariant frame; beside `c2`, which fails first, it is not reached. A bound is `bmc`'s, its
    /// depth the last cycle covered; a register-free net fails in the pre-pass, in cycle 0.
    #[test]
    fn each_property_names_its_engine_and_depth() {
        use Depth::*;
        use Engine::*;
        use Outcome::*;
        let qq = crate::netlist::parse(
            "module t(clk,en,p);\ninput clk,en; output p;\nwire q,d,nq;\n\
             XOR2 x(.A(en),.B(q),.Y(d));\nDFF r(.CK(clk),.D(d),.Q(q));\nINV i(.A(q),.Y(nq));\nAND2 a(.A(q),.B(nq),.Y(p));\nendmodule\n",
        )
        .unwrap();
        let rep = never(&qq, &lib(), &s(&["p", "q"]), None).unwrap();
        assert_eq!(decided(&rep), [("p", Holds, Some(BddPrepass), None), ("q", Fails, Some(Pdr), Some(Cycle(1)))]);

        let rep = never(&counter(true), &lib(), &s(&["c3"]), None).unwrap();
        let [(_, Holds, Some(Pdr), Some(PdrFrame(k)))] = decided(&rep)[..] else { panic!("{:?}", rep.properties) };
        assert!(k >= 1, "pdr's invariant frame is at least 1, got {k}");
        let rep = never(&counter(true), &lib(), &s(&["c3", "c2"]), None).unwrap();
        assert_eq!(decided(&rep), [("c3", NotReached, None, None), ("c2", Fails, Some(Pdr), Some(Cycle(2)))]);

        let rep = never(&counter(false), &lib(), &s(&["c3"]), Some(2)).unwrap();
        assert_eq!(decided(&rep), [("c3", HoldsWithin, Some(Bmc), Some(Cycle(2)))]);
        let rep = never(&counter(false), &lib(), &s(&["c3"]), Some(3)).unwrap();
        assert_eq!(decided(&rep), [("c3", Fails, Some(Bmc), Some(Cycle(3)))]);

        let and = crate::netlist::parse(
            "module t(clk,a,b,p,z);\ninput clk,a,b; output p,z;\nwire t;\nAND2 g(.A(a),.B(b),.Y(p));\nTIE0 t0(.LO(t));\nBUF u(.A(t),.Y(z));\nendmodule\n",
        )
        .unwrap();
        let rep = never(&and, &lib(), &s(&["z", "p"]), None).unwrap();
        assert_eq!(decided(&rep), [("z", Holds, Some(BddPrepass), None), ("p", Fails, Some(BddPrepass), Some(Cycle(0)))]);
    }

    /// The depths as ABC prints them (lines from `pdr` and `bmc3` runs).
    #[test]
    fn abc_depths_are_read_from_its_output() {
        assert_eq!(pdr_frame("Invariant F[3] : 1 clauses with 0 flops (out of 4) (cex = 0, ave = 4.00)\nProperty proved."), Some(3));
        assert_eq!(pdr_frame("Property proved."), None);
        assert_eq!(bmc_frames("No output asserted in 3 frames. Resource limit reached (conf limit 0)."), Some(3));
        assert_eq!(bmc_frames("Explored all reachable states after completing 4 frames.  Time = 0.02 sec"), Some(4));
        assert_eq!(bmc_frames("Output 0 of miter \"t\" was asserted in frame 2."), None);
    }

    #[test]
    fn an_unknown_net_is_an_error() {
        let e = never(&counter(true), &lib(), &s(&["nope"]), None).unwrap_err();
        assert!(e.contains("no net `nope`"), "{e}");
    }
}
