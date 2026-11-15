// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Verbatim observed failing complete scripts, not sampled or repaired models.

use crate::api::{Logic, Solver};
use ay_core::time::Instant;

use super::{enter_check_stop, Arc, Duration};

fn accepted_original(script: &str, end: Instant) {
    assert!(Instant::now() < end);
    let mut solver = Solver::try_new(Logic::All).expect("fresh native solver");
    solver.set_term_memory_limit(Some(128 * 1024 * 1024));
    assert!(Instant::now() < end);
    let assertions = solver
        .parse_smtlib2(script)
        .expect("unaltered full original query");
    assert!(!assertions.is_empty());
    drop(assertions);
    assert!(Instant::now() < end);
    assert!(solver.instance_term_bytes() <= 128 * 1024 * 1024);
    solver.set_timeout(Some(end.saturating_duration_since(Instant::now())));
    let result = solver.check_sat_interruptible_internal_query(move || {
        Instant::now() >= end || ay_core::TermStore::global_memory_exceeded()
    });
    assert!(
        result.is_sat(),
        "whole native relation: {:?}",
        solver.unknown_reason()
    );
    assert!(
        result.was_model_validated(),
        "original plus ALL complete array pins"
    );
    assert!(
        result.has_sat_emission_witness(),
        "ordinary final publication funnel"
    );
    assert!(solver.instance_term_bytes() <= 128 * 1024 * 1024);
    drop((result, solver));
    assert!(Instant::now() < end, "cleanup belongs to the original end");
}

#[test]
#[ntest::timeout(30000)]
fn original_uniform_full_pins_require_native_validation_and_emission() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    accepted_original(include_str!("uniform.smt2"), end);
}

#[test]
#[ntest::timeout(30000)]
fn original_copy_full_lambda_pins_require_native_validation_and_emission() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    accepted_original(include_str!("copy.smt2"), end);
}
