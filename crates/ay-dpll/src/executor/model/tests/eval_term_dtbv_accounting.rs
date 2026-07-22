// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DT+BV SAT-fallback accounting tests (#6282).
//!
//! Verifies that DT+BV assertions in `validate_model` are tracked correctly:
//! - SAT-fallback increments `sat_fallback_count`, NOT `checked`
//! - No-SAT-assignment increments `skipped_dtbv`
//! - The zero-evidence and proportional guards fire when expected

use super::*;
use ay_core::DatatypeSort;

/// Helper: construct a DT+BV assertion term `bvult(f(d), y)` where
/// `d: Datatype("Foo")`. This gets both TERM_FLAG_DATATYPE (from `d`)
/// and TERM_FLAG_BV_CMP (from `bvult`), triggering the DT+BV code path
/// at validate_model line ~4478.
fn make_dtbv_assertion(executor: &mut Executor) -> TermId {
    let dt_sort = Sort::Datatype(DatatypeSort::new("Foo", vec![]));
    let d = executor.ctx.terms.mk_var("d", dt_sort);
    let f_d = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![d], Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![f_d, y], Sort::Bool)
}

#[test]
fn test_validate_model_dtbv_sat_fallback_increments_sat_fallback_count() {
    // (#6282) When a DT+BV assertion evaluates to Unknown and the SAT model
    // says true, validate_model must track this as sat_fallback_count (not
    // checked). The SAT model is validating itself — there is no independent
    // theory-level evidence.
    let mut executor = Executor::new();
    let bvult = make_dtbv_assertion(&mut executor);
    executor.ctx.assertions.push(bvult);

    // Add one independent assertion so the zero-evidence guard doesn't fire.
    let true_const = executor.ctx.terms.mk_bool(true);
    executor.ctx.assertions.push(true_const);

    let model = model_with_sat_assignments(&[(bvult, true)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let stats = executor
        .validate_model()
        .expect("DT+BV with 1 independent check should pass");

    assert_eq!(
        stats.sat_fallback_count, 1,
        "DT+BV SAT-fallback should increment sat_fallback_count, not checked (#6282)"
    );
    assert_eq!(stats.checked, 1, "Independent Bool(true) should be checked");
    assert_eq!(
        stats.skipped_dtbv, 0,
        "SAT-fallback succeeded, so skipped_dtbv should be 0"
    );
    assert_eq!(stats.total, 2);
}

#[test]
fn test_validate_model_dtbv_sat_fallback_only_triggers_zero_evidence_guard() {
    // (#6282) When ALL assertions are DT+BV SAT-fallback (no independent
    // evidence), the zero-evidence guard must reject the model. checked == 0
    // + sat_fallback > 0 triggers the guard.
    let mut executor = Executor::new();
    let bvult = make_dtbv_assertion(&mut executor);
    executor.ctx.assertions.push(bvult);

    let model = model_with_sat_assignments(&[(bvult, true)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("DT+BV SAT-fallback-only model should be rejected (#6282)");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
    assert!(
        err.contains("sat_fallback=1"),
        "Error should report sat_fallback=1: {err}"
    );
}

#[test]
fn test_validate_model_dtbv_no_sat_assignment_increments_skipped_dtbv() {
    // (#6282) When a DT+BV assertion evaluates to Unknown AND the SAT model
    // has no assignment, the assertion is counted as skipped_dtbv.
    //
    // NOTE (#dt-bv-congruence): the assertion here is `bvult(f(d), y)` — a UF
    // application over a datatype argument, NOT a datatype-reconstruction
    // (dis)equality (`=`/`distinct` over selector/constructor chains). UF results
    // are genuinely free, so this remains a benign skip that the model's other
    // independent check rescues. The DT+BV reconstruction fail-closed guard
    // (observation.rs) fires ONLY for selector/constructor (dis)equalities whose
    // truth the bit-blast cannot validate — see the m2/discharge/nested repros —
    // so it does not affect this UF case.
    let mut executor = Executor::new();
    let bvult = make_dtbv_assertion(&mut executor);
    executor.ctx.assertions.push(bvult);

    // Add one independent assertion.
    let true_const = executor.ctx.terms.mk_bool(true);
    executor.ctx.assertions.push(true_const);

    // No SAT assignment for bvult — empty model.
    let model = empty_model();
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let stats = executor
        .validate_model()
        .expect("DT+BV with 1 independent check + 1 benign UF DT+BV skip should pass");

    assert_eq!(
        stats.skipped_dtbv, 1,
        "DT+BV with no SAT assignment should increment skipped_dtbv (#6282)"
    );
    assert_eq!(
        stats.sat_fallback_count, 0,
        "No SAT assignment means no SAT-fallback"
    );
    assert_eq!(stats.checked, 1, "Independent Bool(true) should be checked");
    assert_eq!(stats.total, 2);
}
