//! `map --ranges`: a revised netlist that keeps the declared port numbering (`a[8]`, `a[9]` of
//! `input [9:8] a`, as plain Yosys writes it) is renumbered to the elaborated numbering (`a[0]`,
//! `a[1]`, as syn and the reference's synthesize write it) before inputs are paired by name.

use std::process::Command;

/// Elaborated (syn): bit i of [9:8] is a[|i - 8|].
const GOLDEN: &str = "module t(clk, \\a[0] , \\a[1] , y);\ninput clk, \\a[0] , \\a[1] ; output y;\nwire r0, n, r1;\n\
  DFF u1(.CK(clk), .D(\\a[0] ), .Q(r0));\nAND2 u3(.A(\\a[1] ), .B(r0), .Y(n));\nDFF u2(.CK(clk), .D(n), .Q(r1));\nBUF u4(.A(r1), .Y(y));\nendmodule\n";
/// The same design with the declared numbering kept.
const REVISED: &str = "module t(clk, \\a[8] , \\a[9] , y);\ninput clk, \\a[8] , \\a[9] ; output y;\nwire q1, m, q2;\n\
  DFF _1_(.CK(clk), .D(\\a[8] ), .Q(q1));\nAND2 _3_(.A(\\a[9] ), .B(q1), .Y(m));\nDFF _2_(.CK(clk), .D(m), .Q(q2));\nBUF _4_(.A(q2), .Y(y));\nendmodule\n";

fn map(dir: &std::path::Path, ranges: Option<&str>) -> (i32, String, String) {
    let mut c = Command::new(env!("CARGO_BIN_EXE_vyges-lec"));
    c.arg("map");
    // the flag BEFORE the netlists: its value is not read as a netlist path
    if let Some(r) = ranges {
        std::fs::write(dir.join("ranges.json"), r).unwrap();
        c.arg("--ranges").arg(dir.join("ranges.json"));
    }
    c.arg(dir.join("g.v")).arg(dir.join("r.v")).arg("--lib").arg("tests/data/seq.lib").arg("--json").arg("--fail-on-diff");
    let o = c.output().expect("run vyges-lec");
    (o.status.code().unwrap_or(-1), String::from_utf8_lossy(&o.stdout).into_owned(), String::from_utf8_lossy(&o.stderr).into_owned())
}

#[test]
fn map_pairs_inputs_by_the_declared_range() {
    let dir = std::env::temp_dir().join(format!("vyges-lec-ranges-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("g.v"), GOLDEN).unwrap();
    std::fs::write(dir.join("r.v"), REVISED).unwrap();
    // as written, a[8] pairs with nothing: the registers that read it are not proved
    let (rc, out, _) = map(&dir, None);
    assert_eq!(rc, 3, "{out}");
    assert!(out.contains("\"ports_renumbered\": null"), "{out}");
    // with the declared range, a[8] is a[0] and a[9] is a[1]: one-to-one
    let (rc, out, err) = map(&dir, Some(r#"{"schema":"vyges-syn-ranges/1.0","ranges":{"a":[9,8]},"skipped":[]}"#));
    assert_eq!(rc, 0, "{out}{err}");
    assert!(out.contains("\"u1\": \"_1_\"") && out.contains("\"u2\": \"_2_\""), "{out}");
    assert!(out.contains("{\"declared\": \"a[8]\", \"elaborated\": \"a[0]\"}"), "{out}");
    assert!(err.contains("revised: 2 port bit(s) renumbered by their declared range"), "{err}");
    // the range read the wrong way round swaps the bits: not one-to-one (the rule is the range)
    let (rc, _, _) = map(&dir, Some(r#"{"a":[8,9]}"#));
    assert_eq!(rc, 3);
    // an index outside the declared range is listed and left as written, never moved
    let (rc, out, err) = map(&dir, Some(r#"{"a":[3,0]}"#));
    assert_eq!(rc, 3, "{out}");
    assert!(out.contains("{\"bit\": \"a[8]\", \"declared\": [3, 0]}"), "{out}");
    assert!(err.contains("revised port bit a[8] lies outside its declared range [3:0]"), "{err}");
}
