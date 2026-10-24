//! vyges-lec CLI.
//!
//!   vyges-lec check GOLDEN.v REVISED.v --lib L.lib [--engine bdd|abc|both] [-o OUT] [--json] [--fail-on-diff]
//!   vyges-lec sec   GOLDEN.v REVISED.v --lib L.lib [-o OUT] [--json] [--fail-on-diff]
//!   vyges-lec prove DESIGN.v --lib L.lib --never NET [--never NET ...] [--bound N] [-o OUT] [--json] [--fail-on-diff]
//!
//! Proves combinational equivalence of two gate-level netlists. Exit codes:
//! 0 equivalent · 1 runtime error (including the two engines disagreeing) · 2 usage ·
//! 3 NOT equivalent (only with --fail-on-diff) · 4 undecided (only with --fail-on-diff).

use std::process::exit;

use vyges_lec::lec::{self, LecReport};
use vyges_lec::{liberty::Lib, netlist};

/// A diagnostic as a structured event (`LEC-ERROR`, or `LEC-WARNING` for a warning; `vyges-events/1.0`)
/// instead of a bare stderr line; text after a blank line (the usage) stays plain help.
fn diag_line(msg: String) {
    let (head, help) = match msg.split_once("\n\n") {
        Some((h, rest)) => (h.to_string(), Some(rest.to_string())),
        None => (msg, None),
    };
    let warn = head.starts_with("warning: ");
    let text = head.strip_prefix("error: ").or_else(|| head.strip_prefix("warning: ")).unwrap_or(&head).to_string();
    let (severity, code) = if warn { (vyges_events::Severity::Warn, "LEC-WARNING") } else { (vyges_events::Severity::Error, "LEC-ERROR") };
    vyges_events::emit(&vyges_events::Event::new("vyges-lec", severity, text).with_code(code));
    if let Some(h) = help {
        eprintln!("{h}");
    }
}

macro_rules! diag {
    ($($t:tt)*) => { diag_line(format!($($t)*)) };
}


const USAGE: &str = "\
vyges physical lec — logic equivalence (combinational, sequential) and property checking

usage:
  vyges physical lec check GOLDEN.v REVISED.v --lib L.lib [--engine E] [-o OUT] [--json] [--fail-on-diff]
  vyges physical lec sec   GOLDEN.v REVISED.v --lib L.lib [-o OUT] [--json] [--fail-on-diff]
  vyges physical lec prove DESIGN.v --lib L.lib --never NET [--never NET ...] [--bound N] [...]

commands:
  check            combinational: registers cut and matched by instance name
  sec              sequential: registers kept as state, primary outputs compared on every
                   input sequence from the all-zero register state (one clock; needs --features abc)
  prove            property: each --never NET stays 0 on every input sequence from the all-zero
                   register state; --bound N checks cycles 0..N only (needs --features abc)

flags:
  --lib FILE       Liberty (pin directions + comb/seq split) — required
  --engine E       bdd (default): exact BDDs, lists every differing endpoint
                   abc: SAT-based (ABC), scales further, names the first differing endpoint
                   both: run both and fail if they disagree; reports the bdd result
                   (abc and both need a build with --features abc)
  -o FILE          write the report to FILE (default: stdout)
  --json           machine-readable JSON instead of text
  --fail-on-diff   exit 3 if the designs are not equivalent, 4 if undecided (CI gate)
  --describe            print a machine-readable JSON description of the command
  -h, --help · -V, --version
";

fn opt(args: &[String], name: &str) -> Option<String> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1).cloned())
}

fn render_text(r: &LecReport) -> String {
    let mut s = String::new();
    if r.undecided {
        s.push_str(&format!(
            "vyges-lec — UNDECIDED ?  ({} compared; the engine gave up within its limits)\n",
            r.compared
        ));
        return s;
    }
    if r.equivalent {
        s.push_str(&format!(
            "vyges-lec — EQUIVALENT ✓  ({} endpoint(s) proven)\n",
            r.compared
        ));
        return s;
    }
    s.push_str(&format!(
        "vyges-lec — NOT EQUIVALENT ✗  ({} compared, {} differ)\n",
        r.compared,
        r.mismatches.len()
    ));
    for m in r.mismatches.iter().take(100) {
        let cex: Vec<String> = m
            .counterexample
            .iter()
            .map(|(n, v)| format!("{n}={}", if *v { 1 } else { 0 }))
            .collect();
        s.push_str(&format!(
            "  differ at `{}`   when {}\n",
            m.endpoint,
            cex.join(" ")
        ));
    }
    for n in &r.only_in_golden {
        s.push_str(&format!("  only in golden:  {n}\n"));
    }
    for n in &r.only_in_revised {
        s.push_str(&format!("  only in revised: {n}\n"));
    }
    s
}

fn render_json(r: &LecReport) -> String {
    let mut s = String::from("{\n");
    s.push_str(&format!("  \"equivalent\": {},\n", r.equivalent));
    s.push_str(&format!("  \"compared\": {},\n", r.compared));
    if r.undecided {
        s.push_str("  \"undecided\": true,\n");
    }
    s.push_str("  \"mismatches\": [\n");
    for (i, m) in r.mismatches.iter().enumerate() {
        let comma = if i + 1 < r.mismatches.len() { "," } else { "" };
        let cex: Vec<String> = m
            .counterexample
            .iter()
            .map(|(n, v)| format!("\"{n}\": {v}"))
            .collect();
        s.push_str(&format!(
            "    {{\"endpoint\": \"{}\", \"counterexample\": {{{}}}}}{}\n",
            m.endpoint,
            cex.join(", "),
            comma
        ));
    }
    s.push_str("  ],\n");
    s.push_str(&format!("  \"only_in_golden\": {:?},\n", r.only_in_golden));
    s.push_str(&format!("  \"only_in_revised\": {:?}\n", r.only_in_revised));
    s.push_str("}\n");
    s
}

/// Emit the vyges-events causal trail for the LEC verdict + each differing endpoint —
/// to stderr (the report goes to stdout / -o). code=LEC-* is the clustering key; objects
/// are the endpoint / net refs used for cross-stage co-reference.
fn emit_lec_events(r: &LecReport) {
    use vyges_events::{Event, Severity};
    let e = |sev, code: &str, msg: String, objs: Vec<String>| {
        vyges_events::emit(
            &Event::new("vyges-lec", sev, msg)
                .with_code(code)
                .with_objects(objs),
        );
    };
    if r.undecided {
        e(
            Severity::Warn,
            "LEC-UNDECIDED",
            format!("LEC UNDECIDED ({} compared)", r.compared),
            vec![],
        );
        return;
    }
    if r.equivalent {
        e(
            Severity::Info,
            "LEC-EQUIVALENT",
            format!("LEC EQUIVALENT ({} endpoint(s) proven)", r.compared),
            vec![],
        );
        return;
    }
    // verdict headline
    e(
        Severity::Error,
        "LEC-DIFF",
        format!(
            "LEC NOT EQUIVALENT ({} compared, {} differ)",
            r.compared,
            r.mismatches.len()
        ),
        vec![],
    );
    // one event per differing endpoint, carrying the counter-example
    for m in &r.mismatches {
        let cex: Vec<String> = m
            .counterexample
            .iter()
            .map(|(n, v)| format!("{n}={}", if *v { 1 } else { 0 }))
            .collect();
        e(
            Severity::Error,
            "LEC-DIFF",
            format!("differ at `{}` when {}", m.endpoint, cex.join(" ")),
            vec![format!("endpoint:{}", m.endpoint)],
        );
    }
    for n in &r.only_in_golden {
        e(
            Severity::Warn,
            "LEC-DIFF",
            format!("endpoint only in golden: {n}"),
            vec![format!("endpoint:{n}")],
        );
    }
    for n in &r.only_in_revised {
        e(
            Severity::Warn,
            "LEC-DIFF",
            format!("endpoint only in revised: {n}"),
            vec![format!("endpoint:{n}")],
        );
    }
}

/// Add `"report_path"` to a `--json` payload so the result says where its report landed.
///
/// String surgery rather than a JSON round-trip because this crate is std-only. Inserting
/// after the opening brace keeps every existing field untouched; an empty object gets no
/// trailing comma.
fn with_report_path(json: &str, path: Option<&str>) -> String {
    let (Some(p), Some(rest)) = (path, json.trim_start().strip_prefix('{')) else {
        return json.to_string();
    };
    let esc = p.replace('\\', "\\\\").replace('"', "\\\"");
    let sep = if rest.trim_start().starts_with('}') {
        ""
    } else {
        ","
    };
    format!("{{\"report_path\": \"{esc}\"{sep}{rest}")
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--describe") {
        // Machine-readable description of `check` for tooling that drives it.
        const DESCRIBE: &str = r#"{
  "schema": "vyges-tool-descriptor/1.1",
  "name": "lec",
  "summary": "combinational logic equivalence check (golden vs revised)",
  "maturity": "structured",
  "provenance_limitations": [
      "input_hash covers the argument vector, not the content of the two netlists or the Liberty it names.",
      "Liberty `include` files are not enumerated."
  ],
  "invocation": {
    "args_template": ["check", "{golden}", "{revised}", "--lib", "{lib}"],
    "optional": [ { "arg": "out", "flag": "-o" } ],
    "emits_json": true
  },
  "inputs": {
    "type": "object",
    "required": ["golden", "revised", "lib"],
    "properties": {
      "golden": { "type": "string", "description": "path to the golden (reference) gate-level netlist" },
      "revised": { "type": "string", "description": "path to the revised gate-level netlist to compare" },
      "lib": { "type": "string", "description": "path to the Liberty file (pin directions + comb/seq split)" },
      "out": { "type": "string", "description": "write the report to FILE instead of stdout" }
    }
  },
  "artifacts": [ { "role": "equivalence_report", "field": "report_path" } ],
  "assertion": {
    "id": "logic-equivalent",
    "field": "equivalent",
    "pass_when": { "is_true": true }
  }
}
"#;
        print!("{DESCRIBE}");
        return;
    }
    if args.iter().any(|a| a == "-h" || a == "--help") || args.is_empty() {
        print!("{USAGE}");
        return;
    }
    if args.iter().any(|a| a == "-V" || a == "--version") {
        println!("vyges-lec {}", vyges_lec::VERSION);
        return;
    }
    if !["check", "sec", "prove"].contains(&args[0].as_str()) {
        diag!("error: unknown command {:?}\n{USAGE}", args[0]);
        exit(2);
    }
    // positionals: not a flag, not a flag's value
    let valued = ["--lib", "--engine", "-o", "--never", "--bound"];
    let pos: Vec<&String> = args[1..]
        .iter()
        .enumerate()
        .filter(|(i, a)| !a.starts_with('-') && !(*i > 0 && valued.contains(&args[*i].as_str())))
        .map(|(_, a)| a)
        .collect();
    let cmd = args[0].as_str();
    if cmd == "prove" {
        let (Some(design), None) = (pos.first(), pos.get(1)) else {
            diag!("error: `prove` needs one DESIGN netlist path\n{USAGE}");
            exit(2);
        };
        let Some(libp) = opt(&args, "--lib") else {
            diag!("error: `prove` needs --lib\n{USAGE}");
            exit(2);
        };
        let nets: Vec<String> = args.windows(2).filter(|w| w[0] == "--never").map(|w| w[1].clone()).collect();
        if nets.is_empty() {
            diag!("error: `prove` needs at least one --never NET\n{USAGE}");
            exit(2);
        }
        let bound = opt(&args, "--bound").map(|b| {
            b.parse::<usize>().unwrap_or_else(|_| {
                diag!("error: --bound wants a cycle count, got {b:?}");
                exit(2)
            })
        });
        let d = netlist::load(design).unwrap_or_else(|e| die(&format!("{design}: {e}")));
        let lib = Lib::load(&libp).unwrap_or_else(|e| die(&format!("{libp}: {e}")));
        prove(&args, &d, &lib, &nets, bound);
        return;
    }
    let (Some(gold), Some(rev)) = (pos.first(), pos.get(1)) else {
        diag!("error: `{cmd}` needs GOLDEN and REVISED netlist paths\n{USAGE}");
        exit(2);
    };
    let Some(libp) = opt(&args, "--lib") else {
        diag!("error: `{cmd}` needs --lib\n{USAGE}");
        exit(2);
    };

    let g = netlist::load(gold).unwrap_or_else(|e| die(&format!("{gold}: {e}")));
    let r = netlist::load(rev).unwrap_or_else(|e| die(&format!("{rev}: {e}")));
    let lib = Lib::load(&libp).unwrap_or_else(|e| die(&format!("{libp}: {e}")));

    if cmd == "sec" {
        sec(&args, &g, &r, &lib);
        return;
    }
    let engine = opt(&args, "--engine").unwrap_or_else(|| "bdd".into());
    let report = match engine.as_str() {
        "bdd" => lec::equivalence(&g, &r, &lib).unwrap_or_else(|e| die(&e)),
        "abc" | "both" => with_abc(&engine, &g, &r, &lib),
        other => {
            diag!("error: unknown --engine {other:?} (bdd, abc or both)\n{USAGE}");
            exit(2);
        }
    };
    emit_lec_events(&report);
    let json = args.iter().any(|a| a == "--json");
    let text = if json {
        with_report_path(&render_json(&report), opt(&args, "-o").as_deref())
    } else {
        render_text(&report)
    };
    match opt(&args, "-o") {
        Some(p) => {
            if let Err(e) = std::fs::write(&p, &text) {
                die(&format!("{p}: {e}"));
            }
            eprintln!("wrote {p}");
            // `-o` writes the report; the machine payload still goes to stdout, so asking
            // for the file does not cost the caller the parsed result.
            if json {
                print!("{text}");
            }
        }
        None => print!("{text}"),
    }
    if args.iter().any(|a| a == "--fail-on-diff") && !report.equivalent {
        exit(if report.undecided { 4 } else { 3 });
    }
}

#[cfg(feature = "abc")]
fn with_abc(engine: &str, g: &netlist::Netlist, r: &netlist::Netlist, lib: &Lib) -> LecReport {
    use vyges_lec::abc;
    let a = abc::equivalence(g, r, lib).unwrap_or_else(|e| die(&e));
    if engine == "abc" {
        return a.into();
    }
    let b = lec::equivalence(g, r, lib).unwrap_or_else(|e| die(&e));
    abc::cross_check(&b, &a).unwrap_or_else(|e| die(&e));
    b
}

#[cfg(not(feature = "abc"))]
fn with_abc(engine: &str, _: &netlist::Netlist, _: &netlist::Netlist, _: &Lib) -> LecReport {
    diag!("error: --engine {engine} needs a build with the ABC engine (cargo build --features abc)");
    exit(2);
}

/// `sec`: the sequential check, its report and its exit code (as `check`'s).
#[cfg(feature = "abc")]
fn sec(args: &[String], g: &netlist::Netlist, r: &netlist::Netlist, lib: &Lib) {
    use vyges_events::{Event, Severity};
    use vyges_lec::sec::{self, SecReport, SecVerdict};
    let rep = sec::equivalence(g, r, lib).unwrap_or_else(|e| die(&e));
    let regs = |r: &SecReport| format!("{} vs {} register(s)", r.golden_registers, r.revised_registers);
    let (code, sev, msg) = match &rep.verdict {
        SecVerdict::Undecided => ("LEC-UNDECIDED", Severity::Warn, format!("SEC UNDECIDED ({} output(s) compared)", rep.compared)),
        _ if rep.equivalent() => ("LEC-EQUIVALENT", Severity::Info, format!("SEC EQUIVALENT ({} output(s) proven, {})", rep.compared, regs(&rep))),
        SecVerdict::Differs { output, cycle, .. } => ("LEC-DIFF", Severity::Error, format!("SEC NOT EQUIVALENT: `{output}` differs in cycle {cycle}")),
        SecVerdict::Equivalent => ("LEC-DIFF", Severity::Error, "SEC NOT EQUIVALENT: the designs have different outputs".to_string()),
    };
    vyges_events::emit(&Event::new("vyges-lec", sev, msg).with_code(code));
    let bit = |v: &(String, bool)| format!("{}={}", v.0, u8::from(v.1));
    let json = args.iter().any(|a| a == "--json");
    let text = if json {
        let mut s = format!(
            "{{\n  \"equivalent\": {},\n  \"compared\": {},\n  \"golden_registers\": {},\n  \"revised_registers\": {},\n",
            rep.equivalent(),
            rep.compared,
            rep.golden_registers,
            rep.revised_registers
        );
        if let Some(c) = &rep.clock {
            s += &format!("  \"clock\": {c:?},\n");
        }
        match &rep.verdict {
            SecVerdict::Undecided => s += "  \"undecided\": true,\n",
            SecVerdict::Differs { output, cycle, trace } => {
                let cycles: Vec<String> = trace
                    .iter()
                    .map(|c| format!("{{{}}}", c.iter().map(|(n, v)| format!("{n:?}: {v}")).collect::<Vec<_>>().join(", ")))
                    .collect();
                s += &format!("  \"differs\": {{\"output\": {output:?}, \"cycle\": {cycle}, \"inputs_per_cycle\": [{}]}},\n", cycles.join(", "));
            }
            SecVerdict::Equivalent => {}
        }
        s += &format!("  \"only_in_golden\": {:?},\n  \"only_in_revised\": {:?}\n}}\n", rep.only_in_golden, rep.only_in_revised);
        with_report_path(&s, opt(args, "-o").as_deref())
    } else {
        let mut s = match &rep.verdict {
            SecVerdict::Undecided => format!("vyges-lec sec — UNDECIDED ?  ({} output(s) compared; the engine gave up within its limits)\n", rep.compared),
            _ if rep.equivalent() => format!(
                "vyges-lec sec — EQUIVALENT ✓  ({} output(s) proven on every input sequence from the all-zero register state; {})\n",
                rep.compared,
                regs(&rep)
            ),
            _ => format!("vyges-lec sec — NOT EQUIVALENT ✗  ({} output(s) compared; {})\n", rep.compared, regs(&rep)),
        };
        if let SecVerdict::Differs { output, cycle, trace } = &rep.verdict {
            s += &format!("  `{output}` differs in cycle {cycle} (cycle 0 is before the first clock edge), under:\n");
            for (k, c) in trace.iter().enumerate() {
                s += &format!("    cycle {k}: {}\n", c.iter().map(bit).collect::<Vec<_>>().join(" "));
            }
        }
        for n in &rep.only_in_golden {
            s += &format!("  only in golden:  {n}\n");
        }
        for n in &rep.only_in_revised {
            s += &format!("  only in revised: {n}\n");
        }
        s
    };
    emit(args, &text, json);
    if args.iter().any(|a| a == "--fail-on-diff") && !rep.equivalent() {
        exit(if rep.verdict == SecVerdict::Undecided { 4 } else { 3 });
    }
}

/// The `--json` / `-o` / stdout tail both ABC commands share.
#[cfg(feature = "abc")]
fn emit(args: &[String], text: &str, json: bool) {
    match opt(args, "-o") {
        Some(p) => {
            if let Err(e) = std::fs::write(&p, text) {
                die(&format!("{p}: {e}"));
            }
            eprintln!("wrote {p}");
            if json {
                print!("{text}");
            }
        }
        None => print!("{text}"),
    }
}

/// `prove`: each net stays 0. Exit codes as `check`'s: 3 a net is 1, 4 undecided (a bounded check
/// that finds nothing exits 0: it was asked for).
#[cfg(feature = "abc")]
fn prove(args: &[String], d: &netlist::Netlist, lib: &Lib, nets: &[String], bound: Option<usize>) {
    use vyges_events::{Event, Severity};
    use vyges_lec::prop::{self, PropVerdict};
    let rep = prop::never(d, lib, nets, bound).unwrap_or_else(|e| die(&e));
    let (code, sev, msg) = match &rep.verdict {
        PropVerdict::Holds => ("LEC-HOLDS", Severity::Info, format!("PROVE HOLDS ({} net(s) never 1)", nets.len())),
        PropVerdict::HoldsWithin { cycles } => ("LEC-HOLDS", Severity::Info, format!("PROVE no net is 1 in cycles 0..{cycles} (bounded)")),
        PropVerdict::Fails { net, cycle, .. } => ("LEC-FAILS", Severity::Error, format!("PROVE FAILS: `{net}` is 1 in cycle {cycle}")),
        PropVerdict::Undecided => ("LEC-UNDECIDED", Severity::Warn, "PROVE UNDECIDED".to_string()),
    };
    vyges_events::emit(&Event::new("vyges-lec", sev, msg).with_code(code));
    let json = args.iter().any(|a| a == "--json");
    let text = if json {
        let mut s = format!("{{\n  \"nets\": {:?},\n  \"registers\": {},\n", rep.nets, rep.registers);
        if let Some(c) = &rep.clock {
            s += &format!("  \"clock\": {c:?},\n");
        }
        s += &match &rep.verdict {
            PropVerdict::Holds => "  \"verdict\": \"holds\"\n".to_string(),
            PropVerdict::HoldsWithin { cycles } => format!("  \"verdict\": \"holds_within\",\n  \"cycles\": {cycles}\n"),
            PropVerdict::Undecided => "  \"verdict\": \"undecided\"\n".to_string(),
            PropVerdict::Fails { net, cycle, trace } => {
                let cycles: Vec<String> = trace
                    .iter()
                    .map(|c| format!("{{{}}}", c.iter().map(|(n, v)| format!("{n:?}: {v}")).collect::<Vec<_>>().join(", ")))
                    .collect();
                format!("  \"verdict\": \"fails\",\n  \"fails\": {{\"net\": {net:?}, \"cycle\": {cycle}, \"inputs_per_cycle\": [{}]}}\n", cycles.join(", "))
            }
        };
        with_report_path(&(s + "}\n"), opt(args, "-o").as_deref())
    } else {
        let regs = format!("{} register(s)", rep.registers);
        let mut s = match &rep.verdict {
            PropVerdict::Holds => format!(
                "vyges-lec prove — HOLDS ✓  ({} net(s) never 1 on any input sequence from the all-zero register state; {regs})\n",
                nets.len()
            ),
            PropVerdict::HoldsWithin { cycles } => format!(
                "vyges-lec prove — NO FAILURE in cycles 0..{cycles}  (a bounded check, not a proof; {regs})\n"
            ),
            PropVerdict::Undecided => "vyges-lec prove — UNDECIDED ?  (the engine gave up within its limits)\n".to_string(),
            PropVerdict::Fails { net, cycle, .. } => format!("vyges-lec prove — FAILS ✗  `{net}` is 1 in cycle {cycle} ({regs}), under:\n"),
        };
        if let PropVerdict::Fails { trace, .. } = &rep.verdict {
            for (k, c) in trace.iter().enumerate() {
                s += &format!("    cycle {k}: {}\n", c.iter().map(|(n, v)| format!("{n}={}", u8::from(*v))).collect::<Vec<_>>().join(" "));
            }
        }
        s
    };
    emit(args, &text, json);
    if args.iter().any(|a| a == "--fail-on-diff") {
        match rep.verdict {
            PropVerdict::Fails { .. } => exit(3),
            PropVerdict::Undecided => exit(4),
            _ => {}
        }
    }
}

#[cfg(not(feature = "abc"))]
fn prove(_: &[String], _: &netlist::Netlist, _: &Lib, _: &[String], _: Option<usize>) {
    diag!("error: `prove` needs a build with the ABC engine (cargo build --features abc)");
    exit(2);
}

#[cfg(not(feature = "abc"))]
fn sec(_: &[String], _: &netlist::Netlist, _: &netlist::Netlist, _: &Lib) {
    diag!("error: `sec` needs a build with the ABC engine (cargo build --features abc)");
    exit(2);
}

fn die(msg: &str) -> ! {
    diag!("error: {msg}");
    exit(1);
}
