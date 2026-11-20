//! `prove --json`: each net is listed under `properties` with the engine that decided it and its
//! depth, added beside the keys a reader already uses (`nets`, `registers`, `clock`, `verdict`,
//! `fails`), which keep their shape.
#![cfg(feature = "abc")]

use std::process::Command;

/// `p = q AND NOT q` is 0 in every state (the BDD pre-pass decides it); `q` rises in cycle 1
/// (ABC's `pdr` finds it).
const DESIGN: &str = "module t(clk,en,p);\ninput clk,en; output p;\nwire q,d,nq;\n\
  XOR2 x(.A(en),.B(q),.Y(d));\nDFF r(.CK(clk),.D(d),.Q(q));\nINV i(.A(q),.Y(nq));\nAND2 a(.A(q),.B(nq),.Y(p));\nendmodule\n";

fn prove(dir: &std::path::Path, extra: &[&str]) -> serde_json::Value {
    let o = Command::new(env!("CARGO_BIN_EXE_vyges-lec"))
        .arg("prove")
        .arg(dir.join("d.v"))
        .args(["--lib", "tests/data/seq.lib", "--json"])
        .args(extra)
        .output()
        .expect("run vyges-lec");
    assert_eq!(o.status.code(), Some(0), "stderr: {}", String::from_utf8_lossy(&o.stderr));
    serde_json::from_slice(&o.stdout).unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&o.stdout)))
}

#[test]
fn prove_json_names_the_deciding_engine_and_depth() {
    let dir = std::env::temp_dir().join(format!("vyges-lec-prove-json-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("d.v"), DESIGN).unwrap();

    let j = prove(&dir, &["--never", "p", "--never", "q"]);
    // the keys that were there before, unchanged
    assert_eq!(j["nets"], serde_json::json!(["p", "q"]));
    assert_eq!(j["registers"], 1);
    assert_eq!(j["clock"], "clk");
    assert_eq!(j["verdict"], "fails");
    assert_eq!((j["fails"]["net"].as_str(), j["fails"]["cycle"].as_u64()), (Some("q"), Some(1)));
    // the added per-net list
    assert_eq!(
        j["properties"],
        serde_json::json!([
            {"net": "p", "result": "holds", "decided_by": "bdd-prepass", "depth": null, "depth_unit": null},
            {"net": "q", "result": "fails", "decided_by": "pdr", "depth": 1, "depth_unit": "cycle"}
        ])
    );

    let j = prove(&dir, &["--never", "q", "--bound", "0"]);
    assert_eq!((j["verdict"].as_str(), j["cycles"].as_u64()), (Some("holds_within"), Some(0)));
    assert_eq!(
        j["properties"],
        serde_json::json!([{"net": "q", "result": "holds_within", "decided_by": "bmc", "depth": 0, "depth_unit": "cycle"}])
    );
}
