// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `carcara_surface=` on the certificate line is a statement about the file
//! pair an external checker reads: the proof AND the authored problem.
//!
//! Measured at 938ec0327: `typed_vec_pins_cell64_unsat.smt2` printed
//! `carcara_surface=supported` while pinned Carcara 9a352ee stopped parsing
//! its problem at `((as mkVec Vec) ...)` (`not a valid qualified operator`).

use std::process::Command;

use tempfile::TempDir;

/// Run `ay <problem>` in its default posture, which writes the best-effort
/// `<problem>.alethe` sidecar, and return the certificate line and stderr.
fn certificate(problem: &str) -> (String, String) {
    let dir = TempDir::new().expect("tempdir");
    let input = dir.path().join("problem.smt2");
    std::fs::write(&input, problem).expect("write problem");
    let out = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg(&input)
        .current_dir(dir.path())
        .output()
        .expect("run ay");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "stdout={stdout} stderr={stderr}"
    );
    let line = stderr
        .lines()
        .find(|line| line.starts_with("c ay.proof.certificate "))
        .unwrap_or_else(|| panic!("a certificate is emitted; stderr={stderr}"))
        .to_string();
    (line, stderr)
}

#[test]
fn the_typed_vec_benchmark_discloses_its_qualified_constructor() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../benchmarks/smt/model_checker_consumer_quantified_counterexample/typed_vec_pins_cell64_unsat.smt2"
    );
    let problem = std::fs::read_to_string(path).expect("read the benchmark");
    let (line, stderr) = certificate(&problem);
    assert!(line.contains(" carcara_surface=unsupported "), "{line}");
    assert!(
        stderr.contains("carcara_surface=unsupported") && stderr.contains("(as mkVec Vec)"),
        "the warning names the construct: {stderr}"
    );
}

/// Only the source text shows these spellings: AY's command parser reads the
/// legacy datatype form like the standard one and `define-const` as a
/// `define-fun`. Pinned Carcara parses neither datatype spelling, and skips
/// `define-const`, so a use of its symbol stops the parse and an unused one
/// does not. The standard spellings stay supported.
#[test]
fn spellings_only_the_source_text_shows_are_disclosed() {
    let refutation = "(declare-const x Int)\n(assert (> x 0))\n(assert (< x 0))\n(check-sat)\n";
    for (header, fragment) in [
        ("(declare-datatypes () ((E A B)))", "legacy"),
        ("(declare-datatype E (A B))", "bare symbol"),
        ("(define-const c Int 1)\n(assert (= c 1))", "`define-const`"),
    ] {
        let (line, stderr) = certificate(&format!("(set-logic ALL)\n{header}\n{refutation}"));
        assert!(
            line.contains(" carcara_surface=unsupported "),
            "{header}: {line}"
        );
        assert!(stderr.contains(fragment), "{header}: {stderr}");
    }
    for header in [
        "(declare-datatypes ((E 0)) (((A) (B))))",
        "(define-const c Int 1)",
    ] {
        let (line, _) = certificate(&format!("(set-logic ALL)\n{header}\n{refutation}"));
        assert!(
            line.contains(" carcara_surface=supported "),
            "{header}: {line}"
        );
    }
}

/// `ay --rigor strict <problem>`'s verdict line.
fn strict_verdict(problem: &str) -> String {
    let dir = TempDir::new().expect("tempdir");
    let input = dir.path().join("problem.smt2");
    std::fs::write(&input, problem).expect("write problem");
    let out = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["--rigor", "strict"])
        .arg(&input)
        .current_dir(dir.path())
        .output()
        .expect("run ay");
    let stdout = String::from_utf8_lossy(&out.stdout);
    stdout
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| panic!("a verdict; stdout={stdout}"))
        .to_string()
}

/// Review probes b01 and a08: `--rigor strict` decides at the `check-sat` and
/// writes the certificate paired with the whole file, so a construct after the
/// query (read ahead) or in a command Carcara only lexes (`set-info`) stops
/// the external check, and the verdict is withheld. Each control publishes.
#[test]
fn strict_withholds_unsat_when_carcara_cannot_parse_the_whole_file() {
    let refutation = "(declare-const x Int)\n(assert (> x 0))\n(assert (< x 0))\n";
    let run = |head: &str, tail: &str| {
        strict_verdict(&format!(
            "(set-logic ALL)\n{head}\n{refutation}(check-sat)\n{tail}"
        ))
    };
    assert_eq!(
        run("", "(declare-const f (_ FloatingPoint 8 24))\n"),
        "unknown"
    );
    assert_eq!(run("", "(declare-const y Int)\n"), "unsat");
    assert_eq!(run("(set-info :source |C:\\ay|)", ""), "unknown");
    assert_eq!(run("(set-info :source |C:/ay|)", ""), "unsat");
}
