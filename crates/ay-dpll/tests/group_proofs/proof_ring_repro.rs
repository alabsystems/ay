// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::fs;
use std::path::Path;

fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
}

fn solve_with_proof(path: &str) -> bool {
    let path = workspace_root().join(path);
    let content = fs::read_to_string(&path).expect("read benchmark");
    let content = content
        .lines()
        .filter(|line| line.trim() != "(exit)")
        .collect::<Vec<_>>()
        .join("\n");
    let script = format!("(set-option :produce-proofs true)\n{content}\n(get-proof)\n");
    let commands = parse(&script).expect("parse benchmark");
    let mut exec = Executor::new();
    eprintln!("SOLVING {}", path.display());
    let outputs = exec.execute_all(&commands).expect("execute benchmark");
    if outputs.first().map(String::as_str) != Some("unsat") {
        eprintln!(
            "SKIP {} result={:?}",
            path.display(),
            outputs.first().map(String::as_str)
        );
        return false;
    }
    assert!(
        outputs
            .last()
            .is_some_and(|proof| proof.contains("(assume ") || proof.contains("(step ")),
        "expected proof output for {}: {outputs:?}",
        path.display()
    );
    true
}

#[test]
#[timeout(30_000)]
fn test_unsat_implied_equality_proof_generation() {
    assert!(
        solve_with_proof("benchmarks/smt/QF_UFLIA/unsat_implied_equality.smt2"),
        "expected UNSAT proof for unsat_implied_equality"
    );
}
