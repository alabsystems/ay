// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The BVFP/FPLRA proof regressions and the AUFBVFP model regression.
//! These historical gaps require real proof/model authority, never a relaxed
//! publication gate.

use super::*;

// ---------------------------------------------------------------------------
// CLOSED — `BVFP`: `forall q:BV64. fp.isNaN(fromBits(q))`.
// ---------------------------------------------------------------------------

/// TRUTH, established independently: `fromBits(0)` is `+0.0`, which is not NaN,
/// so the universal is false and the assertion is unsatisfiable. Ground, no
/// quantifier.
#[test]
fn bvfp_from_bits_zero_is_not_nan() {
    assert_eq!(
        solve_one(&format!(
            r#"
            (set-logic QF_BVFP)
            (assert (fp.isNaN {}))
            (check-sat)
        "#,
            from_bits_f64("#x0000000000000000")
        )),
        "unsat",
        "the independent truth: the all-zero bit pattern is +0.0, not NaN"
    );
}

/// ay ALREADY HAS THE RIGHT ANSWER. Without a mandatory proof artifact the
/// shape decides `unsat` — MBQI finds the refuting instance `q = 0`.
///
/// This separates the reasoning from the mandatory artifact path below.
#[test]
fn bvfp_decides_unsat_when_no_proof_artifact_is_required() {
    assert_eq!(
        solve_one(&format!(
            r#"
            (set-logic BVFP)
            (assert (forall ((q (_ BitVec 64))) (fp.isNaN {})))
            (check-sat)
        "#,
            from_bits_f64("q")
        )),
        "unsat",
        "trust shape `BVFP`: refuted at q = 0 when no artifact is mandatory"
    );
}

/// The same query now has an authored `forall_inst` derivation plus a checked
/// exact FP lemma for its ground instance. The mandatory artifact gate is
/// unchanged. Native bundle replay and the unsupported Carcara surface are
/// checked separately by the consumer-facing proof-artifact tests.
#[test]
fn bvfp_under_proofs_publishes_checked_unsat() {
    assert_eq!(
        solve_one(&format!(
            r#"
            (set-logic BVFP)
            (set-option :produce-proofs true)
            (assert (forall ((q (_ BitVec 64))) (fp.isNaN {})))
            (check-sat)
        "#,
            from_bits_f64("q")
        )),
        "unsat",
        "trust shape `BVFP`: exact substitution and ground FP evaluation supply the artifact"
    );
}

/// Successful proof publication must clear the previous downgrade reason.
#[test]
fn bvfp_under_proofs_has_no_unknown_reason() {
    let commands = parse(&format!(
        r#"
        (set-logic BVFP)
        (set-option :produce-proofs true)
        (assert (forall ((q (_ BitVec 64))) (fp.isNaN {})))
        (check-sat)
    "#,
        from_bits_f64("q")
    ))
    .unwrap();
    let mut exec = Executor::new();
    let _ = exec.execute_all(&commands).unwrap();
    assert_eq!(
        exec.unknown_reason(),
        None,
        "the checked BVFP refutation no longer downgrades to QuantifierUnhandled"
    );
}

// ---------------------------------------------------------------------------
// CLOSED — `FPLRA`: independently checked arithmetic-zero instantiation.
// ---------------------------------------------------------------------------

/// TRUTH, established independently: the conjunct `(> (+ q q) q)` fails at
/// `q = 0` (ground, below), so the universal is false and the assertion is
/// unsatisfiable.
#[test]
fn fplra_conjunct_fails_at_zero() {
    assert_eq!(
        solve_one(
            r#"
            (set-logic QF_LRA)
            (assert (> (+ 0.0 0.0) 0.0))
            (check-sat)
        "#,
        ),
        "unsat",
        "the independent truth: 0 + 0 > 0 is false"
    );
}

/// The ground FP relaxation still supplies no model authority. Instead,
/// arithmetic zero is an untrusted source-side hint: exact `forall_inst`
/// substitution and the independent FP evaluator must prove a complete
/// refutation over the authored roots. No ground solve is trusted or retried.
#[test]
fn fplra_zero_instance_publishes_checked_unsat() {
    let commands = parse(
        r#"
        (set-logic FPLRA)
        (set-option :produce-proofs true)
        (assert (forall ((q Real)) (and (> (+ q q) q) (fp.isNaN (_ NaN 11 53)))))
        (check-sat)
    "#,
    )
    .unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs.last().map(String::as_str), Some("unsat"));
    assert_eq!(
        exec.unknown_reason(),
        None,
        "trust shape `FPLRA`: a checked authored zero-instance proof, \
         without loosening the FP relaxation gate"
    );
}

// ---------------------------------------------------------------------------
// CLOSED — `AUFBVFP`: complete congruence and reconstructed array/UF model.
// ---------------------------------------------------------------------------

/// TRUTH, established independently: `AUFBVFP` is SATISFIABLE, because its body
/// is satisfiable at EVERY index at once — `g` constantly true. The
/// quantifier-free instance below asserts the body at three arbitrary indices
/// and is satisfiable; nothing in the body ties different indices together, so
/// no finite set of indices can be the obstruction, and `g = true` satisfies all
/// 256.
///
/// The model must survive restoration of the original array-read application
/// IDs; merely avoiding a wrong `unsat` is not completion of this case.
#[test]
fn aufbvfp_ground_instances_are_satisfiable() {
    let verdict = solve_one(&format!(
        r#"
        (set-logic QF_AUFBVFP)
        (declare-const mem (Array (_ BitVec 8) (_ BitVec 64)))
        (declare-fun g ((_ FloatingPoint 11 53)) Bool)
        (assert (and (g {}) (g {}) (g {})))
        (check-sat)
    "#,
        from_bits_f64("(select mem #x00)"),
        from_bits_f64("(select mem #x2a)"),
        from_bits_f64("(select mem #xff)")
    ));
    assert_eq!(
        verdict, "sat",
        "the body is satisfiable at every index (g = true): the shape's truth is SAT"
    );
}

/// The BV8 binder expands to all 256 indices. Unit resolution over the actual
/// ground CNF forces every g result true, discharging all congruence pairs;
/// every FP argument is still encoded. Exact array-read rewrite provenance
/// transports existing Boolean assignments back to original applications.
/// The unchanged independent model gate must then confirm the full query.
#[test]
fn aufbvfp_full_ground_expansion_publishes_a_confirmed_model() {
    let commands = parse(&format!(
        r#"
        (set-logic AUFBVFP)
        (set-option :produce-proofs true)
        (declare-const mem (Array (_ BitVec 8) (_ BitVec 64)))
        (declare-fun g ((_ FloatingPoint 11 53)) Bool)
        (assert (forall ((q (_ BitVec 8))) (g {})))
        (check-sat)
    "#,
        from_bits_f64("(select mem q)")
    ))
    .unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs.last().map(String::as_str), Some("sat"));
    assert_eq!(exec.unknown_reason(), None);
    assert_eq!(
        exec.statistics().get_string("model_check_gate.result"),
        Some("confirmed-sat"),
        "truth-SAT is not enough: the exact reconstructed witness must pass the gate"
    );
}
