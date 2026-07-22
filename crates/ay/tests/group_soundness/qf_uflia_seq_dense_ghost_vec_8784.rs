// QF_UFLIA seq_dense_ghost_vec regression (#8784).
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// #8784: Soundness regression introduced by the #8764 stale-reason guard
// (commit d264e18b9 "add stale-reason guard to all LRA conflict-building
// paths"). On a Creusot-style ghost-vector benchmark that models repeated
// Seq push/len/nth operations, AY used to return SAT (matching Z3). After
// the guard was added, AY returns UNSAT in ~0.75s because a valid
// LRA "contradictory variable bounds" conflict is rejected by the guard.
// The guard's over-rejection converts a legitimate early-exit into a
// spurious empty conflict that the DPLL layer interprets as global UNSAT.
//
// Z3's expected answer: `sat`. AY must answer `sat` or `unknown`; `unsat`
// is a soundness regression.

use ntest::timeout;
use std::process::Command;

fn run_ay(smt_file: &str, timeout_ms: u64) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let benchmark_path = format!(
        "{}/../../benchmarks/smt/QF_UFLIA/{}",
        env!("CARGO_MANIFEST_DIR"),
        smt_file
    );

    let output = Command::new(ay_path)
        .arg(format!("-t:{timeout_ms}"))
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// #8784 reproducer: AY must never answer `unsat` on this Creusot-style
/// ghost-vector benchmark. Z3 answers `sat`; AY is allowed to answer `sat`
/// or `unknown`, but `unsat` is a soundness regression.
#[test]
#[timeout(120_000)]
fn seq_dense_ghost_vec_never_false_unsat_8784() {
    let result = run_ay("seq_dense_ghost_vec.smt2", 60_000);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8784): AY reported 'unsat' on a SAT QF_UFLIA \
         instance (Z3 confirms SAT). Expected 'sat' or 'unknown'. \
         Result: {result}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on seq_dense_ghost_vec.smt2: {result}"
    );
}
