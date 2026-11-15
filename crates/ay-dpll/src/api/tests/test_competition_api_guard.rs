// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #proof-capability B3 — native-API guard against raw competition admissions.
//!
//! The competition-shedding `CompetitionRaw` UNSAT token is scope-authenticated
//! but backed by no checked refutation, so it deliberately carries ZERO
//! verification classes. `VerifiedSolveResult::certified_unsat` must never
//! mint a certified wrapper from a zero-class token — it fails closed to the
//! non-verified `Unknown` classification instead of panicking the debug build
//! on its exactly-one-class assertion.

use crate::api::{SolveResult, VerifiedSolveResult};
use crate::executor::Executor;

/// A real shed-mode `CompetitionRaw` token reaching the native
/// result boundary yields the non-verified classification — never a certified
/// UNSAT wrapper, and never a debug-build panic.
#[test]
fn competition_raw_token_never_mints_certified_wrapper_on_native_api() {
    let mut executor = Executor::new();
    executor.set_competition_mode(true);
    let proposition = executor
        .ctx
        .terms
        .mk_var("native_api_guard_p", ay_core::Sort::Bool);
    let not_proposition = executor.ctx.terms.mk_not_raw(proposition);
    executor.ctx.assertions = vec![proposition, not_proposition];
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    let proposed = executor
        .check_sat()
        .expect("contradictory Boolean units must solve");
    assert!(proposed.is_unsat());
    assert!(executor.competition_shedding_active());

    let published = executor.certify_unsat_for_publication(proposed, &[]);
    let SolveResult::Unsat(proof) = published else {
        panic!("shed-mode UNSAT must publish through the raw admission lane");
    };
    let certificate = executor
        .take_unsat_certificate()
        .expect("the raw token must be consumable while shedding is active");
    assert!(!certificate.strict_proof_verified());
    assert!(!certificate.independently_verified());
    assert!(!certificate.exact_semantic_verified());

    // The zero-class token crosses the native constructor: fail closed.
    let wrapped = VerifiedSolveResult::certified_unsat(proof, certificate);
    assert!(
        wrapped.is_unknown(),
        "a raw admission must yield the non-verified classification, got {wrapped}"
    );
    assert!(!wrapped.is_unsat());
    assert!(!wrapped.has_unsat_emission_witness());
    assert!(!wrapped.has_sat_emission_witness());
    assert!(!wrapped.was_model_validated());
    assert!(!wrapped.was_unsat_strictly_verified());
    assert!(!wrapped.was_unsat_independently_verified());
    assert!(!wrapped.was_unsat_exact_semantically_verified());
    assert!(!wrapped.was_unsat_corroborated());
    assert_eq!(wrapped.unsat_evidence_level(), None);
}
