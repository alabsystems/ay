// NIA bounded-enumeration negative-factor false-UNSAT regression.
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// The NIA bounded-enumeration lower-bound inference (ay-theories/nia,
// bounded_enum.rs) manufactured `var >= ceil(L / product_of_other_uppers)`
// whenever every OTHER factor merely had a positive UPPER bound -- it never
// checked the other factor could be negative. For (x*y >= 6) with y in
// [-10, 3] (positive upper bound 3, but can be negative) and x bounded only
// above, it clamped x >= ceil(6/3) = 2 and excised the negative-product cone
// (x=-4, y=-10 gives x*y = 40 >= 6), enumerated an empty box, and returned a
// spurious `unsat`. On the no-proof-check subprocess backend that UNSAT
// becomes a development verifier false proof.
//
// Fix: require every other factor to be strictly positive (lower bound > 0),
// mirroring the upper-bound inference's guard. When the sign is not pinned
// positive the inference is skipped, leaving the bound open so the procedure
// degrades to `unknown` (sound) rather than a wrong `unsat`.
//
// Z3 answers `sat`. AY must answer `sat` or `unknown`; `unsat` is a soundness
// regression (a false-PROVE).

use ntest::timeout;
use std::process::Command;

fn run_ay(smt_file: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let benchmark_path = format!(
        "{}/../../benchmarks/smt/QF_NIA/{}",
        env!("CARGO_MANIFEST_DIR"),
        smt_file
    );
    let output = Command::new(ay_path)
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout
        .trim()
        .lines()
        .find(|l| !l.starts_with("c "))
        .unwrap_or("")
        .to_string()
}

/// The negative-factor witness must never be reported `unsat`.
#[test]
#[timeout(60_000)]
fn nia_negative_factor_never_false_unsat() {
    let result = run_ay("nia_negative_factor_falseprove.smt2");
    assert_ne!(
        result, "unsat",
        "Soundness regression: AY reported 'unsat' on a SAT QF_NIA instance \
         (x=-4, y=-10 satisfies it; Z3 confirms SAT). A wrong UNSAT here is a \
         false-PROVE on the no-proof-check subprocess path. Got: {result}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on nia_negative_factor_falseprove.smt2: {result}"
    );
}
