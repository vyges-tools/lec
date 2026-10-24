//! vyges-lec CLI.
//!
//!   vyges-lec check GOLDEN.v REVISED.v --lib L.lib [--engine bdd|abc|both] [-o OUT] [--json] [--fail-on-diff]
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
vyges loom lec — combinational logic equivalence check (golden vs revised)

usage:
  vyges loom lec check GOLDEN.v REVISED.v --lib L.lib [--engine E] [-o OUT] [--json] [--fail-on-diff]

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
    if args[0] != "check" {
        diag!("error: unknown command {:?}\n{USAGE}", args[0]);
        exit(2);
    }
    let pos: Vec<&String> = args[1..].iter().filter(|a| !a.starts_with('-')).collect();
    let (Some(gold), Some(rev)) = (pos.first(), pos.get(1)) else {
        diag!("error: `check` needs GOLDEN and REVISED netlist paths\n{USAGE}");
        exit(2);
    };
    let Some(libp) = opt(&args, "--lib") else {
        diag!("error: `check` needs --lib\n{USAGE}");
        exit(2);
    };

    let g = netlist::load(gold).unwrap_or_else(|e| die(&format!("{gold}: {e}")));
    let r = netlist::load(rev).unwrap_or_else(|e| die(&format!("{rev}: {e}")));
    let lib = Lib::load(&libp).unwrap_or_else(|e| die(&format!("{libp}: {e}")));

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

fn die(msg: &str) -> ! {
    diag!("error: {msg}");
    exit(1);
}
