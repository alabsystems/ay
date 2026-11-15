// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_dpll::api::{Logic, Solver, SolverConfig, StrictProofVerdict};
use std::time::Duration;

#[test]
fn wide_nan_identity_exports_independently_checked_native_evidence() {
    assert_native_evidence(include_str!(
        "../../ay-proof/tests/fixtures/fp-wide-nan-identity.smt2"
    ));
}

#[test]
fn integral_rounding_and_remainder_export_independently_checked_native_evidence() {
    assert_native_evidence(include_str!(
        "../../ay-proof/tests/fixtures/fp-integral-remainder.smt2"
    ));
}

#[test]
fn wide_field_classification_exports_independently_checked_native_evidence() {
    assert_native_evidence(include_str!(
        "../../ay-proof/tests/fixtures/fp-wide-field-order.smt2"
    ));
}

fn assert_native_evidence(input: &str) {
    let config = SolverConfig::default()
        .with_timeout(Duration::from_secs(5))
        .with_memory_limit(256 * 1024 * 1024);
    let mut solver = Solver::try_new_with_config(Logic::QfFp, config).unwrap();
    solver.set_produce_proofs(true);
    solver.parse_smtlib2(input).unwrap();
    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "{result:?}; {:?}",
        solver.unknown_reason()
    );
    let artifact = solver.export_last_unsat_artifact().unwrap();
    assert!(matches!(
        artifact.strict_verdict,
        StrictProofVerdict::Verified(_)
    ));
    let bundle = solver.export_last_unsat_bundle().unwrap();
    let checked = ay_proof::re_check_bundle_strict(&bundle).unwrap();
    assert!(checked.quality.is_complete());
}

#[test]
fn precision256_exports_independently_checked_native_evidence() {
    assert_native_evidence(include_str!(
        "../../ay-proof/tests/fixtures/fp-ground-precision256.smt2"
    ));
}
