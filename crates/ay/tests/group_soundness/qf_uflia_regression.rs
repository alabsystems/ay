// QF_UFLIA regression tests
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//
// Tests for Nelson-Oppen combination of EUF (Equality + Uninterpreted Functions)
// with LIA (Linear Integer Arithmetic). Tests verify bidirectional equality propagation
// between theories.

use ntest::timeout;
use std::process::Command;

fn run_ay(smt_file: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    // CARGO_MANIFEST_DIR is crates/ay, go up two levels to workspace root
    let benchmark_path = format!(
        "{}/../../benchmarks/smt/QF_UFLIA/{}",
        env!("CARGO_MANIFEST_DIR"),
        smt_file
    );

    let output = Command::new(ay_path)
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    assert!(
        output.status.success(),
        "ay exited with {:?} for {}\nstderr: {}",
        output.status,
        smt_file,
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// Issue #222 Example 1: f(x) = f(y) when x = y should be SAT
#[test]
#[timeout(30_000)]
fn test_sat_equal_args() {
    let result = run_ay("sat_equal_args.smt2");
    assert_eq!(
        result, "sat",
        "sat_equal_args.smt2 should be sat, got: {result}"
    );
}

/// Issue #222 Example 2: LIA constraints determine x=y=5, f(x)≠f(y) is UNSAT
///
/// This test requires Nelson-Oppen equality propagation: LIA must determine
/// that x=5 (from x>=5 ∧ x<=5) and propagate this to EUF so it can derive x=y.
/// ENABLED: Commit 8842575f implemented Nelson-Oppen tight bounds propagation.
#[test]
#[timeout(30_000)]
fn test_unsat_equality_propagation() {
    let result = run_ay("unsat_equality_propagation.smt2");
    assert_eq!(
        result, "unsat",
        "unsat_equality_propagation.smt2 should be unsat, got: {result}"
    );
}

/// Multi-argument function: g(a,0) = g(b,0) when a = b should be SAT
#[test]
#[timeout(30_000)]
fn test_sat_multiarg_congruence() {
    let result = run_ay("sat_multiarg_congruence.smt2");
    assert_eq!(
        result, "sat",
        "sat_multiarg_congruence.smt2 should be sat, got: {result}"
    );
}

/// Nested function application: h(h(c)) = h(c) should be SAT
#[test]
#[timeout(30_000)]
fn test_sat_nested_function() {
    let result = run_ay("sat_nested_function.smt2");
    assert_eq!(
        result, "sat",
        "sat_nested_function.smt2 should be sat, got: {result}"
    );
}

/// Congruence violation: x = y but f(x) ≠ f(y) should be UNSAT
#[test]
#[timeout(30_000)]
fn test_unsat_congruence_violation() {
    let result = run_ay("unsat_congruence_violation.smt2");
    assert_eq!(
        result, "unsat",
        "unsat_congruence_violation.smt2 should be unsat, got: {result}"
    );
}

/// LIA bounds + congruence: a bounded to 3, b=3, so f(a)≠f(b) is UNSAT
///
/// This test requires Nelson-Oppen equality propagation: LIA must determine
/// that a=3 (from a>=3 ∧ a<=3) and propagate this to EUF so it can derive a=b.
/// ENABLED: Commit 8842575f implemented Nelson-Oppen tight bounds propagation.
#[test]
#[timeout(30_000)]
fn test_unsat_lia_bounds_congruence() {
    let result = run_ay("unsat_lia_bounds_congruence.smt2");
    assert_eq!(
        result, "unsat",
        "unsat_lia_bounds_congruence.smt2 should be unsat, got: {result}"
    );
}

/// Implied equality from arithmetic: a+1=b+1 implies a=b, congruence applies.
///
/// Regression test for #237: ay previously returned `sat` for this `unsat`.
/// This test requires Nelson-Oppen equality propagation: LIA must determine
/// that a=b (from a+1=b+1) and propagate this to EUF.
/// ENABLED: Algebraic equality detection implemented (a+1=b+1 → a=b).
#[test]
#[timeout(30_000)]
fn test_unsat_implied_equality() {
    let result = run_ay("unsat_implied_equality.smt2");
    assert_eq!(
        result, "unsat",
        "unsat_implied_equality.smt2 should be unsat, got: {result}"
    );
}

/// Multi-constraint implied equality: a+b=c ∧ b=0 implies a=c.
///
/// Regression test for #238: ay previously returned `sat` for this `unsat`.
/// This case requires multi-constraint substitution: even though b=0 from tight bounds,
/// detecting a=c from a+b=c requires substitution across constraints.
/// ENABLED: Multi-constraint substitution implemented.
#[test]
#[timeout(30_000)]
fn test_unsat_multi_constraint_equality() {
    let result = run_ay("unsat_multi_constraint_equality.smt2");
    assert_eq!(
        result, "unsat",
        "unsat_multi_constraint_equality.smt2 should be unsat, got: {result}"
    );
}

/// EUF→LIA propagation: (f 5) = -1 must be propagated to LIA
/// so that 0 <= (f 5) becomes 0 <= -1 → contradiction.
///
/// This test requires Nelson-Oppen in the EUF→LIA direction.
/// The other tests above are LIA→EUF; this is the reverse direction.
/// ENABLED: Bidirectional Nelson-Oppen propagation implemented.
#[test]
#[timeout(30_000)]
fn test_unsat_euf_to_lia_propagation() {
    let result = run_ay("unsat_euf_to_lia_propagation.smt2");
    assert_eq!(
        result, "unsat",
        "unsat_euf_to_lia_propagation.smt2 should be unsat, got: {result}"
    );
}

/// Congruence-derived equality propagation to LIA: Issue #319 (P0 soundness bug)
///
/// From a=b, congruence closure derives f(a)=f(b). This equality must propagate
/// to LIA so it knows (f a) and (f b) represent the same integer value.
/// Otherwise, LIA sees independent constraints f(a)<0 and f(b)>=0 as satisfiable.
///
/// This tests a DIFFERENT pattern than unsat_euf_to_lia_propagation:
/// - unsat_euf_to_lia_propagation: directly asserted equality (f 5) = -1
/// - This test: congruence-DERIVED equality f(a) = f(b) from a = b
///
/// Fixed by #319: EUF now propagates congruence-derived equalities to N-O.
/// When EUF discovers f(a) = f(b) via congruence (from a = b), it adds this
/// equality to pending_propagations so LIA learns the relationship.
#[test]
#[timeout(30_000)]
fn test_unsat_congruence_to_lia() {
    let result = run_ay("unsat_congruence_to_lia.smt2");
    assert_eq!(
        result, "unsat",
        "unsat_congruence_to_lia.smt2 should be unsat, got: {result}"
    );
}
