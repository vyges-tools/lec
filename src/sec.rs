//! Sequential equivalence through ABC (`--features abc`): do two netlists produce the same
//! outputs on every input sequence, starting from the same register state?
//!
//! The combinational check ([`crate::lec`], [`crate::abc`]) cuts both designs at the registers and
//! needs them to correspond one to one by instance name. This one keeps the registers as state
//! ([`crate::lec::seq_cone`]), so it still holds when they do not: a register duplicated or merged,
//! one removed because it never changes, state re-encoded. It compares the primary outputs only.
//!
//! The model:
//! - every register starts at 0 and loads on the same rising edge of one primary-input clock
//!   (an inverted, gated or generated clock, a latch, a second clock are errors, never guesses);
//! - an asynchronous clear / preset acts at the clock edge (see `Reg` in [`crate::lec`]);
//! - a gate is its Liberty function, as in the combinational check.
//!
//! ABC gets both designs as BLIF with `.latch` lines, a multi-output sequential miter (`miter -m`)
//! and `dprove -b`, which names the output and the clock cycle where the two first differ and the
//! inputs of every cycle up to it. (`dsec` decides the same question but leaves no
//! counterexample.)

use std::collections::{BTreeMap, BTreeSet};

use vyges_abc_lib::{Abc, ProbStatus};

use crate::abc::{arg, pi_name, write_blif, Scratch};
use crate::lec::{self, Design};
use crate::liberty::Lib;
use crate::netlist::Netlist;

/// What ABC concluded about the shared outputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SecVerdict {
    /// Every shared output is the same on every input sequence from the all-zero state.
    Equivalent,
    /// This output differs first in clock cycle `cycle` (0: before any edge) under the inputs
    /// `trace[c]` of each cycle `c` up to it.
    Differs { output: String, cycle: usize, trace: Vec<Vec<(String, bool)>> },
    /// ABC gave up within its limits: neither proved nor disproved.
    Undecided,
}

#[derive(Debug, Clone)]
pub struct SecReport {
    pub verdict: SecVerdict,
    /// Shared primary outputs compared.
    pub compared: usize,
    pub only_in_golden: Vec<String>,
    pub only_in_revised: Vec<String>,
    /// Registers each design's compared outputs depend on.
    pub golden_registers: usize,
    pub revised_registers: usize,
    /// The clock both designs' registers share (none when neither has a register).
    pub clock: Option<String>,
}

impl SecReport {
    /// Equivalent only if every shared output is proven AND both designs have the same outputs.
    pub fn equivalent(&self) -> bool {
        self.verdict == SecVerdict::Equivalent && self.only_in_golden.is_empty() && self.only_in_revised.is_empty()
    }
}

/// The one clock of a design's registers.
pub(crate) fn one_clock(which: &str, c: &lec::Cone) -> Result<Option<String>, String> {
    let mut it = c.clocks.iter();
    let clock = it.next().cloned();
    if it.next().is_some() {
        let all: Vec<&str> = c.clocks.iter().map(String::as_str).collect();
        return Err(format!("{which}: registers on more than one clock ({}); one clock is modelled", all.join(", ")));
    }
    Ok(clock)
}

/// The values of `outputs` in each cycle of `trace` (each cycle's primary-input values), simulating
/// the cone this engine writes from the all-zero register state: the check that a counterexample
/// shows the difference ABC claims, independent of ABC and of the files' name mapping.
pub(crate) fn replay(c: &lec::Cone, outputs: &[String], trace: &[Vec<(String, bool)>]) -> Result<Vec<Vec<bool>>, String> {
    use lec::{Logic, Src};
    let mut state: BTreeMap<String, bool> = c.regs.iter().map(|r| (lec::state_net(r), false)).collect();
    let mut seen = Vec::new();
    for inputs in trace {
        let pi: BTreeMap<&str, bool> = inputs.iter().map(|(k, b)| (k.as_str(), *b)).collect();
        let mut v: BTreeMap<String, bool> = c.free.iter().map(|(n, var)| (n.clone(), *pi.get(var.as_str()).unwrap_or(&false))).collect();
        v.extend(state);
        // gates in cone order: each after the gates driving its inputs
        for g in &c.gates {
            let x: Vec<bool> = g.ins.iter().map(|s| match s { Src::Net(n) => v[n.as_str()], Src::Const(b) => *b }).collect();
            let val = match &g.logic {
                Logic::Func(f) => lec::func_value(f, &g.pins, &x),
                Logic::Prim(op) => lec::prim_value(*op, &g.pins, &x)?,
            };
            v.insert(g.out.clone(), val);
        }
        seen.push(outputs.iter().map(|o| v[o.as_str()]).collect());
        state = c.regs.iter().map(|r| (lec::state_net(r), v[&lec::next_net(r)])).collect();
    }
    Ok(seen)
}

/// Run `f` (an ABC command) with the working directory in `dir`, restoring it after.
/// ⛔ An UNDECIDED `dprove` writes the unsolved miter to `smNN.aig` in the working directory, and no
/// option turns that off. The directory is process-wide, like the session itself.
pub(crate) fn in_dir<T>(dir: &Scratch, f: impl FnOnce() -> T) -> Result<T, String> {
    let cwd = std::env::current_dir().map_err(|e| format!("working directory: {e}"))?;
    std::env::set_current_dir(dir.path()).map_err(|e| format!("{}: {e}", dir.path().display()))?;
    let out = f();
    std::env::set_current_dir(&cwd).map_err(|e| format!("{}: {e}", cwd.display()))?;
    Ok(out)
}

/// ABC's counterexample as each cycle's primary-input values (cycles 0 to `last`), by the names
/// `pis` gave the files' inputs.
pub(crate) fn trace(abc: &Abc, pis: &BTreeMap<String, usize>, last: i32) -> Result<Vec<Vec<(String, bool)>>, String> {
    let net: BTreeMap<String, &str> = pis.iter().map(|(n, &k)| (pi_name(k), n.as_str())).collect();
    let mut names = Vec::new();
    for i in 0.. {
        let Some(name) = abc.pi_name(i) else { break };
        names.push(net.get(&name).ok_or_else(|| format!("unknown input {name}"))?.to_string());
    }
    let mut trace = Vec::new();
    for f in 0..=last {
        let bits = abc.cex_inputs(f).ok_or_else(|| format!("ABC's counterexample has no inputs for cycle {f}"))?;
        let mut cycle: Vec<(String, bool)> = names.iter().cloned().zip(bits).collect();
        cycle.sort();
        trace.push(cycle);
    }
    Ok(trace)
}

/// Check golden vs revised for sequential equivalence with ABC.
pub fn equivalence(golden: &Netlist, revised: &Netlist, lib: &Lib) -> Result<SecReport, String> {
    if lib.cells.is_empty() {
        return Err("no cells in the Liberty".into());
    }
    let g = Design::sequential(golden, lib);
    let r = Design::sequential(revised, lib);
    let gouts: BTreeSet<&String> = golden.outputs.iter().collect();
    let routs: BTreeSet<&String> = revised.outputs.iter().collect();
    let shared: Vec<String> = gouts.intersection(&routs).map(|s| s.to_string()).collect();
    let gc = lec::seq_cone(&g, &shared)?;
    let rc = lec::seq_cone(&r, &shared)?;
    let (gclk, rclk) = (one_clock("golden", &gc)?, one_clock("revised", &rc)?);
    let clock = match (gclk, rclk) {
        (Some(a), Some(b)) if a != b => return Err(format!("the designs are clocked by different inputs: `{a}` and `{b}`")),
        (a, b) => a.or(b),
    };
    let report = |verdict| SecReport {
        verdict,
        compared: shared.len(),
        only_in_golden: gouts.difference(&routs).map(|s| s.to_string()).collect(),
        only_in_revised: routs.difference(&gouts).map(|s| s.to_string()).collect(),
        golden_registers: gc.regs.len(),
        revised_registers: rc.regs.len(),
        clock: clock.clone(),
    };
    if shared.is_empty() {
        return Ok(report(SecVerdict::Equivalent));
    }
    // Both files declare the same inputs: every free input either cone reads.
    let vars: BTreeSet<&String> = gc.free.values().chain(rc.free.values()).collect();
    let pis: BTreeMap<String, usize> = vars.into_iter().enumerate().map(|(k, v)| (v.clone(), k)).collect();
    let dir = Scratch::new()?;
    let gp = dir.write("golden.blif", &write_blif("golden", &gc, &pis, &shared)?)?;
    let rp = dir.write("revised.blif", &write_blif("revised", &rc, &pis, &shared)?)?;

    let mut abc = Abc::start().map_err(|e| e.to_string())?;
    abc.execute_captured(&format!("miter -m {} {}", arg(&gp)?, arg(&rp)?)).map_err(|e| e.to_string())?;
    // ⛔ `-b`: no BMC before the proof. dprove's default first step unrolls the miter 20 frames, and
    // on a real netlist (picorv32, 4,778 latches in the miter) building that unrolling ran past 10
    // minutes; latch correspondence then proves the same pair in about a second. A difference is
    // still found, by the engines dprove runs after correspondence.
    in_dir(&dir, || abc.execute_captured("strash; dprove -b"))?.map_err(|e| e.to_string())?;
    let verdict = match abc.prob_status() {
        ProbStatus::Unsat => SecVerdict::Equivalent,
        ProbStatus::Sat => {
            let cex = abc.cex().ok_or("ABC reported a difference without a counterexample")?;
            let output = shared
                .get(cex.po as usize)
                .cloned()
                .ok_or_else(|| format!("ABC disproved output {} of {}", cex.po, shared.len()))?;
            let trace = trace(&abc, &pis, cex.frame)?;
            // ⛔ Never report a difference the model does not show: replay the trace on both cones.
            let k = cex.po as usize;
            let at = |c: &lec::Cone| replay(c, std::slice::from_ref(&shared[k]), &trace).map(|v| v.last().map(|o| o[0]));
            let (a, b) = (at(&gc)?, at(&rc)?);
            if a == b {
                return Err(format!("ABC's counterexample for `{output}` (cycle {}) does not replay: both designs give {a:?}", cex.frame));
            }
            SecVerdict::Differs { output, cycle: cex.frame as usize, trace }
        }
        _ => SecVerdict::Undecided,
    };
    Ok(report(verdict))
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

    /// The outputs of `nl` over `trace` by simulating the cone this engine writes, one cycle at a
    /// time from the all-zero state: an independent check that a counterexample shows the
    /// difference ABC claims.
    fn simulate(nl: &Netlist, output: &str, trace: &[Vec<(String, bool)>]) -> Vec<bool> {
        let l = lib();
        let d = Design::sequential(nl, &l);
        let c = lec::seq_cone(&d, &[output.to_string()]).unwrap();
        replay(&c, &[output.to_string()], trace).unwrap().into_iter().map(|o| o[0]).collect()
    }

    fn differs(rep: &SecReport) -> (&str, usize, &[Vec<(String, bool)>]) {
        match &rep.verdict {
            SecVerdict::Differs { output, cycle, trace } => (output, *cycle, trace),
            v => panic!("{v:?}"),
        }
    }

    /// One toggle register against two that toggle together, ANDed: different with the registers
    /// cut (q1 = 1, q2 = 0), the same in every state the two reach from 0.
    #[test]
    fn a_duplicated_register_is_sequentially_equivalent() {
        let one = nl("module t(clk,en,y);\ninput clk,en; output y;\nwire d;\n\
             XOR2 x(.A(en),.B(y),.Y(d));\nDFF r(.CK(clk),.D(d),.Q(y));\nendmodule\n");
        let dup = nl("module t(clk,en,y);\ninput clk,en; output y;\nwire d1,d2,q1,q2;\n\
             XOR2 x1(.A(en),.B(q1),.Y(d1));\nDFF r1(.CK(clk),.D(d1),.Q(q1));\n\
             XOR2 x2(.A(en),.B(q2),.Y(d2));\nDFF r2(.CK(clk),.D(d2),.Q(q2));\n\
             AND2 a(.A(q1),.B(q2),.Y(y));\nendmodule\n");
        let rep = equivalence(&one, &dup, &lib()).unwrap();
        assert_eq!(rep.verdict, SecVerdict::Equivalent);
        assert!(rep.equivalent());
        assert_eq!((rep.compared, rep.golden_registers, rep.revised_registers), (1, 1, 2));
        assert_eq!(rep.clock.as_deref(), Some("clk"));
        // and the combinational check, which cuts them, cannot show it
        assert!(!lec::equivalence(&one, &dup, &lib()).unwrap().equivalent);
    }

    /// A 2-bit counter's low bit against low AND NOT high: equal until the count reaches 3, after
    /// three enabled cycles. The verdict names cycle 3, and simulating the trace shows it.
    #[test]
    fn a_late_difference_is_found_at_its_cycle() {
        let counter = |y: &str| {
            nl(&format!(
                "module t(clk,en,y);\ninput clk,en; output y;\nwire d0,d1,q0,q1,c,nq1;\n\
                 XOR2 x0(.A(en),.B(q0),.Y(d0));\nDFF r0(.CK(clk),.D(d0),.Q(q0));\n\
                 AND2 a(.A(en),.B(q0),.Y(c));\nXOR2 x1(.A(c),.B(q1),.Y(d1));\nDFF r1(.CK(clk),.D(d1),.Q(q1));\n\
                 INV i(.A(q1),.Y(nq1));\n{y}\nendmodule\n"
            ))
        };
        let low = counter("BUF b(.A(q0),.Y(y));");
        let late = counter("AND2 b(.A(q0),.B(nq1),.Y(y));");
        let rep = equivalence(&low, &late, &lib()).unwrap();
        let (output, cycle, trace) = differs(&rep);
        assert_eq!((output, cycle, trace.len()), ("y", 3, 4));
        let (a, b) = (simulate(&low, output, trace), simulate(&late, output, trace));
        assert_eq!(a[..3], b[..3], "the same until cycle 3");
        assert_ne!(a[3], b[3]);
    }

    /// An asynchronous clear acts at the edge: a register cleared by `rst_n` low against the same
    /// register with the clear folded into its data (D AND rst_n) and the output gated by rst_n.
    /// Equal; and with the clear's polarity wrong, different.
    #[test]
    fn a_clear_is_its_forced_value() {
        let dfr = nl("module t(clk,rst_n,d,q);\ninput clk,rst_n,d; output q;\n\
             DFR r(.CK(clk),.D(d),.RESET_B(rst_n),.Q(q));\nendmodule\n");
        let sync = nl("module t(clk,rst_n,d,q);\ninput clk,rst_n,d; output q;\nwire dd,qq;\n\
             AND2 a(.A(d),.B(rst_n),.Y(dd));\nDFF r(.CK(clk),.D(dd),.Q(qq));\nAND2 o(.A(qq),.B(rst_n),.Y(q));\nendmodule\n");
        assert_eq!(equivalence(&dfr, &sync, &lib()).unwrap().verdict, SecVerdict::Equivalent);
        let wrong = nl("module t(clk,rst_n,d,q);\ninput clk,rst_n,d; output q;\nwire n,dd,qq;\n\
             INV i(.A(rst_n),.Y(n));\nAND2 a(.A(d),.B(n),.Y(dd));\nDFF r(.CK(clk),.D(dd),.Q(qq));\nAND2 o(.A(qq),.B(n),.Y(q));\nendmodule\n");
        let rep = equivalence(&dfr, &wrong, &lib()).unwrap();
        let (output, cycle, trace) = differs(&rep);
        assert_ne!(simulate(&dfr, output, trace)[cycle], simulate(&wrong, output, trace)[cycle]);
    }

    /// A preset forces 1, and with both clear and preset active `clear_preset_var1` decides: L.
    #[test]
    fn preset_and_clear_with_preset() {
        // DFS: preset when SET_B low. Its sync form: D OR !SET_B, output OR !SET_B.
        let dfs = nl("module t(clk,s_n,d,q);\ninput clk,s_n,d; output q;\n\
             DFS r(.CK(clk),.D(d),.SET_B(s_n),.Q(q));\nendmodule\n");
        let sync = nl("module t(clk,s_n,d,q);\ninput clk,s_n,d; output q;\nwire s,dd,qq;\n\
             INV i(.A(s_n),.Y(s));\nOR2 a(.A(d),.B(s),.Y(dd));\nDFF r(.CK(clk),.D(dd),.Q(qq));\nOR2 o(.A(qq),.B(s),.Y(q));\nendmodule\n");
        assert_eq!(equivalence(&dfs, &sync, &lib()).unwrap().verdict, SecVerdict::Equivalent);
        // DFRS with var1 = L: clear wins, so the register is DFR's whatever SET_B does when RESET_B is low
        let both = nl("module t(clk,r_n,s_n,d,q);\ninput clk,r_n,s_n,d; output q;\n\
             DFRS r(.CK(clk),.D(d),.RESET_B(r_n),.SET_B(s_n),.Q(q));\nendmodule\n");
        let sync2 = nl("module t(clk,r_n,s_n,d,q);\ninput clk,r_n,s_n,d; output q;\nwire s,ds,dd,qq,qs;\n\
             INV i(.A(s_n),.Y(s));\nOR2 a(.A(d),.B(s),.Y(ds));\nAND2 b(.A(ds),.B(r_n),.Y(dd));\nDFF r(.CK(clk),.D(dd),.Q(qq));\n\
             OR2 o(.A(qq),.B(s),.Y(qs));\nAND2 p(.A(qs),.B(r_n),.Y(q));\nendmodule\n");
        assert_eq!(equivalence(&both, &sync2, &lib()).unwrap().verdict, SecVerdict::Equivalent);
    }

    /// An enable register's `next_state` reads its own state, `(D&DE) | (IQ&!DE)`: it is a plain
    /// register behind a hold mux. Equal to DFF + MUX2, and different when the mux selects wrongly.
    #[test]
    fn an_enable_register_holds_its_state() {
        let edf = nl("module t(clk,de,d,q);\ninput clk,de,d; output q;\n\
             EDF r(.CK(clk),.D(d),.DE(de),.Q(q));\nendmodule\n");
        let mux = |a0: &str, a1: &str| {
            nl(&format!(
                "module t(clk,de,d,q);\ninput clk,de,d; output q;\nwire n;\n\
                 MUX2 m(.A0({a0}),.A1({a1}),.S(de),.Y(n));\nDFF r(.CK(clk),.D(n),.Q(q));\nendmodule\n"
            ))
        };
        assert_eq!(equivalence(&edf, &mux("q", "d"), &lib()).unwrap().verdict, SecVerdict::Equivalent);
        let rep = equivalence(&edf, &mux("d", "q"), &lib()).unwrap();
        let (output, cycle, trace) = differs(&rep);
        assert_ne!(simulate(&edf, output, trace)[cycle], simulate(&mux("d", "q"), output, trace)[cycle]);
    }

    /// A scan register is its `next_state` mux; QN reads the inverted state.
    #[test]
    fn a_scan_register_and_an_inverted_output() {
        let sdf = nl("module t(clk,d,si,se,qn);\ninput clk,d,si,se; output qn;\nwire q;\n\
             SDF r(.CK(clk),.D(d),.SCD(si),.SCE(se),.Q(q),.QN(qn));\nendmodule\n");
        let mux = nl("module t(clk,d,si,se,qn);\ninput clk,d,si,se; output qn;\nwire m,q;\n\
             MUX2 x(.A0(d),.A1(si),.S(se),.Y(m));\nDFF r(.CK(clk),.D(m),.Q(q));\nINV i(.A(q),.Y(qn));\nendmodule\n");
        assert_eq!(equivalence(&sdf, &mux, &lib()).unwrap().verdict, SecVerdict::Equivalent);
    }

    /// The clock reaches the primary input through buffers; an inverter, a latch, a second clock
    /// and a register with no single `ff` are errors, never guessed.
    #[test]
    fn what_the_model_refuses() {
        let reg = |clk_logic: &str, cell: &str| {
            nl(&format!(
                "module t(clk,clk2,d,q);\ninput clk,clk2,d; output q;\nwire c;\n{clk_logic}\n{cell} r(.CK(c),.D(d),.Q(q));\nendmodule\n"
            ))
        };
        let plain = reg("BUF b(.A(clk),.Y(c));", "DFF");
        assert_eq!(equivalence(&plain, &plain, &lib()).unwrap().clock.as_deref(), Some("clk"));
        let e = equivalence(&reg("INV b(.A(clk),.Y(c));", "DFF"), &plain, &lib()).unwrap_err();
        assert!(e.contains("not a primary input"), "{e}");
        let lat = nl("module t(g,d,q);\ninput g,d; output q;\nLAT r(.G(g),.D(d),.Q(q));\nendmodule\n");
        let e = equivalence(&lat, &lat, &lib()).unwrap_err();
        assert!(e.contains("a latch is not modelled"), "{e}");
        let two = nl("module t(clk,clk2,d,q);\ninput clk,clk2,d; output q;\nwire m;\n\
             DFF r1(.CK(clk),.D(d),.Q(m));\nDFF r2(.CK(clk2),.D(m),.Q(q));\nendmodule\n");
        let e = equivalence(&two, &two, &lib()).unwrap_err();
        assert!(e.contains("more than one clock (clk, clk2)"), "{e}");
        let other = reg("BUF b(.A(clk2),.Y(c));", "DFF");
        let e = equivalence(&plain, &other, &lib()).unwrap_err();
        assert!(e.contains("different inputs: `clk` and `clk2`"), "{e}");
    }
}
