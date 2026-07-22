// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::validation::{
    check_definitive_false, ValidationObservation, ValidationTarget, TERM_FLAG_FP,
};
use super::*;
use ay_core::{
    term::TermData, Symbol, VerificationBoundary, VerificationEvidenceKind, VerificationVerdict,
};
use ay_frontend::parse;

// ==========================================================================
// #5777: Typed verification contract regression tests
// ==========================================================================
//
// These tests prove the SAT/SMT model-validation contract is typed, not
// string-driven. They pattern-match on `ModelValidationError` variants and
// inspect `VerificationBoundary` values — if the contract reverted to strings,
// these tests would fail to compile.

/// Regression (#5777): an assertion that evaluates to `Unknown` with no model
/// must produce `ModelValidationError::Incomplete` with boundary
/// `SmtGroundAssertion`, not a stringly-typed error.
#[test]
fn test_typed_contract_incomplete_has_boundary_5777() {
    let mut executor = Executor::new();
    // UF predicate with no model → evaluator returns Unknown → Incomplete.
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let p_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    executor.ctx.assertions.push(p_x);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("UF predicate without model must fail validation");

    // Typed match — if the contract were string-based, this wouldn't compile.
    let failure = match err {
        ModelValidationError::Incomplete(ref f) => f,
        ModelValidationError::Violated(_) => {
            panic!("Expected Incomplete, got Violated: {err}");
        }
    };
    assert_eq!(
        failure.boundary,
        VerificationBoundary::SmtGroundAssertion,
        "Incomplete error must carry SmtGroundAssertion boundary"
    );
    assert!(
        !failure.detail.is_empty(),
        "Failure detail must be non-empty"
    );
}

/// Regression (#5777): a definitively false assertion must produce
/// `ModelValidationError::Violated` with boundary `SmtGroundAssertion`.
#[test]
fn test_typed_contract_violated_has_boundary_5777() {
    let mut executor = Executor::new();
    // `(assert false)` → evaluator returns Bool(false) → Violated.
    let false_term = executor.ctx.terms.mk_bool(false);
    executor.ctx.assertions.push(false_term);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("False assertion must fail validation");

    // Typed match — compile-time proof that the contract is enum-based.
    let failure = match err {
        ModelValidationError::Violated(ref f) => f,
        ModelValidationError::Incomplete(_) => {
            panic!("Expected Violated, got Incomplete: {err}");
        }
    };
    assert_eq!(
        failure.boundary,
        VerificationBoundary::SmtGroundAssertion,
        "Violated error must carry SmtGroundAssertion boundary"
    );
    assert!(
        failure.detail.contains("violated"),
        "Violated detail must mention 'violated', got: {}",
        failure.detail
    );
}

/// Regression (#5777): `finalize_sat_model_validation` routes `Incomplete` to
/// `SolveResult::Unknown` and `Violated` to `ExecutorError` — using typed
/// matching, not substring checks.
#[test]
fn test_typed_contract_finalize_routes_correctly_5777() {
    // Part 1: Incomplete → Unknown
    let mut exec_incomplete = Executor::new();
    let x = exec_incomplete.ctx.terms.mk_var("x", Sort::Int);
    let p_x = exec_incomplete
        .ctx
        .terms
        .mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    exec_incomplete.ctx.assertions.push(p_x);
    exec_incomplete.last_result = Some(SolveResult::Sat);
    exec_incomplete.last_model = Some(empty_model());

    let result = exec_incomplete
        .finalize_sat_model_validation()
        .expect("Incomplete should degrade to Ok(Unknown), not Err");
    assert_eq!(
        result,
        SolveResult::Unknown,
        "Incomplete must route to Unknown"
    );
    assert_eq!(
        exec_incomplete.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );

    // Part 2: Violated → degrade to Ok(Unknown) (#8373)
    //
    // Prior to #8373, Violated was a hard Err(ExecutorError::ModelValidation).
    // Now it degrades to Unknown like Incomplete, since model validation
    // failures indicate theory incompleteness, not a fatal error.
    let mut exec_violated = Executor::new();
    let false_term = exec_violated.ctx.terms.mk_bool(false);
    exec_violated.ctx.assertions.push(false_term);
    exec_violated.last_result = Some(SolveResult::Sat);
    exec_violated.last_model = Some(empty_model());

    let result = exec_violated
        .finalize_sat_model_validation()
        .expect("Violated should degrade to Ok(Unknown) after #8373, not Err");
    assert_eq!(
        result,
        SolveResult::Unknown,
        "Violated must degrade to Unknown (#8373)"
    );
    assert_eq!(
        exec_violated.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

/// Regression (#5777): the assumption-validation path uses the same typed
/// `Incomplete` contract, with `SmtAssumption` boundary information.
#[test]
fn test_typed_contract_assumption_incomplete_has_boundary_5777() {
    let mut executor = Executor::new();
    let hello = executor.ctx.terms.mk_string("hello".to_string());
    let uf_app =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("my_uf_predicate"), vec![hello], Sort::Bool);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_sat_assumptions(&[uf_app])
        .expect_err("UF assumption without model must fail validation");

    let failure = match err {
        ModelValidationError::Incomplete(ref f) => f,
        ModelValidationError::Violated(_) => {
            panic!("Expected Incomplete, got Violated: {err}");
        }
    };
    assert_eq!(
        failure.boundary,
        VerificationBoundary::SmtAssumption,
        "Incomplete assumption error must carry SmtAssumption boundary"
    );
    assert!(
        !failure.detail.is_empty(),
        "Assumption failure detail must be non-empty"
    );
}

/// Regression (#5777): definitively false assumptions must produce typed
/// `Violated` errors with `SmtAssumption` boundary metadata.
#[test]
fn test_typed_contract_assumption_violated_has_boundary_5777() {
    let mut executor = Executor::new();
    let false_term = executor.ctx.terms.mk_bool(false);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_sat_assumptions(&[false_term])
        .expect_err("False assumption must fail validation");

    let failure = match err {
        ModelValidationError::Violated(ref f) => f,
        ModelValidationError::Incomplete(_) => {
            panic!("Expected Violated, got Incomplete: {err}");
        }
    };
    assert_eq!(
        failure.boundary,
        VerificationBoundary::SmtAssumption,
        "Violated assumption error must carry SmtAssumption boundary"
    );
    assert!(
        failure.detail.contains("violated"),
        "Violated assumption detail must mention 'violated', got: {}",
        failure.detail
    );
}

/// Regression: `finalize_sat_assumption_validation` degrades a `Violated`
/// assumption to `Ok(SolveResult::Unknown)` instead of a hard
/// `ExecutorError::ModelValidation`.
///
/// A `Violated` assumption against a fill-completed model is a completion
/// artifact (e.g. an assumption that is false only because an unconstrained
/// term was 0-defaulted), not a soundness signal. Prior to this change the
/// hard error was mapped by `check.rs` to `Unknown(InternalError)`; now the
/// assumption path mirrors the plain `finalize_sat_model_validation` path
/// (#8373) and returns `Unknown(Incomplete)` directly. Returning `Unknown`
/// is always sound: it never converts a genuine SAT/UNSAT answer.
#[test]
fn test_typed_contract_finalize_assumption_routes_violated_5777() {
    let mut executor = Executor::new();
    let false_term = executor.ctx.terms.mk_bool(false);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor
        .finalize_sat_assumption_validation(&[false_term])
        .expect("Violated assumption must degrade to Ok(Unknown), not a hard Err");

    assert_eq!(
        result,
        SolveResult::Unknown,
        "Violated assumption must degrade to Unknown"
    );
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete),
        "degraded assumption-validation Unknown must carry Incomplete reason"
    );
}

/// Regression (#6703 Category B): pure-Boolean assertions must be accepted
/// from the SAT assignment even when the evaluator cannot reconstruct the
/// intermediate Bool variable values from theory models.
#[test]
fn test_validate_model_accepts_pure_boolean_sat_assignment_without_bool_values() {
    let mut executor = Executor::new();
    let p = executor.ctx.terms.mk_var("p", Sort::Bool);
    let q = executor.ctx.terms.mk_var("q", Sort::Bool);
    let iff = executor.ctx.terms.mk_eq(p, q);
    executor.ctx.assertions.push(iff);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(iff, true)]));

    let stats = executor
        .validate_model()
        .expect("pure-Boolean SAT assignment must count as delegated evidence");

    assert_eq!(
        stats.checked, 1,
        "delegated pure-Boolean validation should count"
    );
    assert_eq!(
        stats.sat_fallback_count, 0,
        "this is verified, not fallback"
    );
}

/// Regression (#5970 split audit): assumption validation must preserve the
/// extracted helper's delegated-SAT path instead of reporting an assertion
/// boundary or incomplete failure.
#[test]
fn test_validate_term_observation_delegates_sat_assumption_without_model_values() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    let flags = executor.precompute_term_flags();
    let model = model_with_sat_assignments(&[(a, true)]);

    let observation = executor.validate_term_observation(
        &model,
        a,
        0,
        flags[a.index()],
        false,
        ValidationTarget::Assumption,
    );

    match observation {
        ValidationObservation::Verdict {
            verdict: VerificationVerdict::Verified { boundary, evidence },
            dt_only,
        } => {
            assert_eq!(boundary, VerificationBoundary::SmtTheoryDelegation);
            assert_eq!(evidence, VerificationEvidenceKind::DelegatedSolver);
            assert!(
                !dt_only,
                "delegated SAT assumption must not be tagged as DT-only"
            );
        }
        other => panic!("Expected delegated assumption verdict, got: {other:?}"),
    }
}

/// Regression (#5970 split audit): arithmetic assertions mixed with array
/// packets must use the dedicated `ArithArrayMix` skip category when direct
/// evaluation is Unknown.
#[test]
fn test_validate_term_observation_skips_arith_array_mix_for_unknown_arith_assertion() {
    let mut executor = Executor::new();
    // Use (< (f x) 0) with an uninterpreted function f so the evaluator
    // genuinely returns Unknown (plain (< x 0) evaluates to false via
    // zero-default for x).
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let lt_zero = executor.ctx.terms.mk_lt(f_x, zero);
    let flags = executor.precompute_term_flags();

    let observation = executor.validate_term_observation(
        &empty_model(),
        lt_zero,
        0,
        flags[lt_zero.index()],
        true,
        ValidationTarget::GroundAssertion,
    );

    assert_eq!(
        observation,
        ValidationObservation::Skip(validation::ValidationSkipKind::ArithArrayMix),
        "mixed arithmetic/array validation should preserve the dedicated skip category"
    );
}

/// Regression (#7654): when arithmetic evaluation is definitively false only
/// because the extracted LRA model is off, preserve the SAT-backed fallback
/// instead of escalating to a violated assertion.
#[test]
fn test_validate_term_observation_fallbacks_false_arith_assertion_7654() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Real);
    let zero = executor.ctx.terms.mk_rational(BigRational::zero());
    let eq_zero = executor.ctx.terms.mk_eq(x, zero);
    let flags = executor.precompute_term_flags();

    let mut model = model_with_sat_assignments(&[(eq_zero, true)]);
    model.lra_model = Some(LraModel {
        values: HashMap::from_iter([(x, BigRational::one())]),
    });

    let observation = executor.validate_term_observation(
        &model,
        eq_zero,
        0,
        flags[eq_zero.index()],
        false,
        ValidationTarget::GroundAssertion,
    );

    match observation {
        ValidationObservation::Fallback(failure) => {
            assert_eq!(
                failure.boundary,
                VerificationBoundary::SmtCircularSatFallback
            );
            assert!(
                failure.detail.contains("arithmetic evaluation false"),
                "unexpected fallback detail: {}",
                failure.detail
            );
        }
        other => panic!("Expected arithmetic SAT fallback, got: {other:?}"),
    }
}

/// Regression (#4399/#8373/#919-class false-SAT): a PURE arithmetic/Boolean
/// ITE assertion (no uninterpreted functions/arrays/etc.) that evaluates
/// definitively false under a complete LRA model is a genuine violation, NOT a
/// model-extraction gap. Accepting the #8373 SAT-fallback for such assertions
/// let spurious LRA models escape as wrong SAT (gasburner-prop3-{7,8,16},
/// pursuit-safety-3). The extraction-gap classification must therefore be
/// withheld for pure-arithmetic ITE assertions.
#[test]
fn test_pure_arith_ite_definitive_false_is_not_extraction_gap_8373() {
    let mut executor = Executor::new();
    let cond = executor.ctx.terms.mk_var("cond", Sort::Bool);
    let zero = executor.ctx.terms.mk_rational(BigRational::zero());
    let one = executor.ctx.terms.mk_rational(BigRational::one());
    let y = executor.ctx.terms.mk_var("y", Sort::Real);
    let selected = executor.ctx.terms.mk_ite(cond, zero, one);
    // (= (ite cond 0 1) y) with cond=true, y=2 -> 0 = 2 -> definitively false.
    let eq_y = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![selected, y], Sort::Bool);

    let mut model = model_with_sat_assignments(&[(cond, true), (eq_y, true)]);
    model.lra_model = Some(LraModel {
        values: HashMap::from_iter([(y, BigRational::from(BigInt::from(2)))]),
    });

    assert_eq!(
        executor.evaluate_term(&model, eq_y),
        EvalValue::Bool(false),
        "test setup must produce a false arithmetic evaluation"
    );
    // Pure arithmetic ITE (no UF): NOT an extraction gap; the false is authoritative.
    assert!(
        !executor.ite_false_may_be_model_extraction_gap(&model, eq_y),
        "pure-arithmetic ITE definitive-false must NOT be treated as an extraction gap"
    );
}

/// Companion to the above: when the ITE assertion DOES contain uninterpreted
/// function applications, the extracted theory model can legitimately be
/// partial, so a false evaluation remains a possible extraction gap and the
/// SAT-backed fallback is preserved.
#[test]
fn test_uf_ite_false_remains_extraction_gap_8373() {
    let mut executor = Executor::new();
    let cond = executor.ctx.terms.mk_var("cond", Sort::Bool);
    let zero = executor.ctx.terms.mk_rational(BigRational::zero());
    let one = executor.ctx.terms.mk_rational(BigRational::one());
    let x = executor.ctx.terms.mk_var("x", Sort::Real);
    // f(x) is an uninterpreted function application over Real.
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::Real);
    let selected = executor.ctx.terms.mk_ite(cond, zero, one);
    // (= (ite cond 0 1) (f x)) — contains an uninterpreted function.
    let eq_fx = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![selected, f_x], Sort::Bool);

    let mut model = model_with_sat_assignments(&[(cond, true), (eq_fx, true)]);
    model.lra_model = Some(LraModel {
        values: HashMap::from_iter([(x, BigRational::from(BigInt::from(2)))]),
    });

    // Contains UF content -> still classified as a possible extraction gap.
    assert!(
        executor.ite_false_may_be_model_extraction_gap(&model, eq_fx),
        "ITE assertion with uninterpreted content must remain a possible extraction gap"
    );
}

/// Regression (#11920 follow-up): QF_ABV try3/try5 benchmarks wrap the whole
/// formula in a BV1 equality whose body contains many nested select terms. A
/// false evaluation of that wrapper is not a definitive array violation; it may
/// be an incomplete nested array/BV model. Direct select observations remain
/// definitive.
#[test]
fn test_array_definitive_oracle_skips_nested_bv1_wrapper_11920() {
    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let a = executor.ctx.terms.mk_var("a", arr_sort);
    let idx = executor.ctx.terms.mk_bitvec(BigInt::from(5u8), 8);
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![a, idx], Sort::bitvec(8));
    let one8 = executor.ctx.terms.mk_bitvec(BigInt::from(1u8), 8);
    let zero8 = executor.ctx.terms.mk_bitvec(BigInt::from(0u8), 8);
    let eq_select = executor.ctx.terms.mk_eq(selected, one8);
    let one1 = executor.ctx.terms.mk_bitvec(BigInt::from(1u8), 1);
    let zero1 = executor.ctx.terms.mk_bitvec(BigInt::from(0u8), 1);
    let ite_leaf = executor.ctx.terms.mk_ite(eq_select, one1, zero1);
    let wrapper_body = executor.ctx.terms.mk_app(
        Symbol::named("bvand"),
        vec![ite_leaf, one1],
        Sort::bitvec(1),
    );
    let wrapper_assertion = executor.ctx.terms.mk_eq(one1, wrapper_body);

    let mut model = bv_model(&[(selected, 0)]);
    model
        .bv_model
        .as_mut()
        .unwrap()
        .values
        .insert(zero8, BigInt::zero());

    assert_eq!(
        executor.evaluate_term(&model, eq_select),
        EvalValue::Bool(false),
        "test setup must make the direct select equality false"
    );
    assert_eq!(
        executor.evaluate_term(&model, wrapper_assertion),
        EvalValue::Bool(false),
        "test setup must make the BV1 wrapper evaluate false"
    );
    assert_eq!(
        check_definitive_false(&executor, &model, eq_select),
        Some("arrays"),
        "direct select equalities are authoritative array observations"
    );
    assert_eq!(
        check_definitive_false(&executor, &model, wrapper_assertion),
        None,
        "nested BV1 wrappers containing selects must not be hard array violations"
    );
}

#[test]
fn test_array_definitive_oracle_finalize_rejects_false_direct_select_11920() {
    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let a = executor.ctx.terms.mk_var("a", arr_sort);
    let idx = executor.ctx.terms.mk_bitvec(BigInt::from(5u8), 8);
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![a, idx], Sort::bitvec(8));
    let one8 = executor.ctx.terms.mk_bitvec(BigInt::from(1u8), 8);
    let eq_select = executor.ctx.terms.mk_eq(selected, one8);
    executor.ctx.assertions.push(eq_select);

    let model = bv_model(&[(selected, 0)]);
    assert_eq!(
        executor.evaluate_term(&model, eq_select),
        EvalValue::Bool(false),
        "test setup must make the direct select equality false"
    );
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let result = executor
        .finalize_sat_model_validation()
        .expect("strict direct-select violation should degrade cleanly");
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
    assert_eq!(
        executor.statistics().get_int("model_validation_failures"),
        Some(1)
    );
    assert_eq!(
        executor
            .statistics()
            .get_string("model_validation.strict.oracle"),
        Some("arrays")
    );
}

#[test]
fn test_array_definitive_oracle_handles_negated_equality_and_distinct_11920() {
    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let a = executor.ctx.terms.mk_var("a", arr_sort);
    let idx = executor.ctx.terms.mk_bitvec(BigInt::from(5u8), 8);
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![a, idx], Sort::bitvec(8));
    let one8 = executor.ctx.terms.mk_bitvec(BigInt::from(1u8), 8);
    let eq_select = executor.ctx.terms.mk_eq(selected, one8);
    let not_eq_select = executor.ctx.terms.mk_not(eq_select);
    let distinct_select = executor.ctx.terms.mk_distinct(vec![selected, one8]);

    let model = bv_model(&[(selected, 1)]);
    assert_eq!(
        executor.evaluate_term(&model, not_eq_select),
        EvalValue::Bool(false),
        "negated equality should be false when direct select equality is true"
    );
    assert_eq!(
        executor.evaluate_term(&model, distinct_select),
        EvalValue::Bool(false),
        "distinct should be false when direct select equals the compared value"
    );
    assert_eq!(
        check_definitive_false(&executor, &model, not_eq_select),
        Some("arrays"),
        "negated direct select equality must remain strict"
    );
    assert_eq!(
        check_definitive_false(&executor, &model, distinct_select),
        Some("arrays"),
        "direct select distinct violations must remain strict"
    );
}

/// Regression (#7654 follow-up): the Bool(false) arithmetic fallback must stay
/// narrow enough that trivially false ground arithmetic formulas still report
/// hard validation violations.
#[test]
fn test_validate_term_observation_does_not_fallback_ground_false_arith_assertion_7654() {
    let mut executor = Executor::new();
    let one = executor
        .ctx
        .terms
        .mk_rational(BigRational::from(BigInt::from(1)));
    let zero = executor.ctx.terms.mk_rational(BigRational::zero());
    let lt_false = executor.ctx.terms.mk_lt(one, zero);
    let flags = executor.precompute_term_flags();

    let mut model = model_with_sat_assignments(&[(lt_false, true)]);
    model.lra_model = Some(LraModel {
        values: HashMap::default(),
    });

    let observation = executor.validate_term_observation(
        &model,
        lt_false,
        0,
        flags[lt_false.index()],
        false,
        ValidationTarget::GroundAssertion,
    );

    match observation {
        ValidationObservation::Verdict {
            verdict: VerificationVerdict::Violated(failure),
            ..
        } => {
            assert_eq!(failure.boundary, VerificationBoundary::SmtGroundAssertion);
            assert!(
                failure.detail.contains("evaluates to false"),
                "unexpected violation detail: {}",
                failure.detail
            );
        }
        other => panic!("Expected hard validation violation, got: {other:?}"),
    }
}

/// Regression (#8456): FP-sorted terms must be tagged during precomputation so
/// they reach the dedicated FP validation path instead of the generic fallback.
#[test]
fn test_precompute_term_flags_marks_fp_terms_8456() {
    let mut executor = Executor::new();
    let fp32 = Sort::FloatingPoint(8, 24);
    let x = executor.ctx.terms.mk_var("x", fp32);
    let y = executor.ctx.terms.mk_var("y", Sort::FloatingPoint(8, 24));
    let eq_xy = executor.ctx.terms.mk_eq(x, y);
    let flags = executor.precompute_term_flags();

    assert_ne!(
        flags[x.index()] & TERM_FLAG_FP,
        0,
        "FP-sorted variable should carry TERM_FLAG_FP"
    );
    assert_ne!(
        flags[eq_xy.index()] & TERM_FLAG_FP,
        0,
        "parent assertion should inherit TERM_FLAG_FP from FP children"
    );
}

/// Regression (#8456): false FP evaluation with SAT-assigned true must use the
/// dedicated FP fallback instead of escalating to a hard violation.
#[test]
fn test_validate_term_observation_fallbacks_false_fp_assertion_8456() {
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);

    // NaN: exp=31 (all 1s), sig=1 (nonzero)
    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(31u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(1u32), 10);
    let nan = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16.clone());
    let eq_nan_nan = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.eq"), vec![nan, nan], Sort::Bool);
    let flags = executor.precompute_term_flags();
    let model = model_with_sat_assignments(&[(eq_nan_nan, true)]);

    let observation = executor.validate_term_observation(
        &model,
        eq_nan_nan,
        0,
        flags[eq_nan_nan.index()],
        false,
        ValidationTarget::GroundAssertion,
    );

    match observation {
        ValidationObservation::Fallback(failure) => {
            assert_eq!(
                failure.boundary,
                VerificationBoundary::SmtCircularSatFallback
            );
            assert!(
                failure.detail.contains("FP evaluation false"),
                "unexpected fallback detail: {}",
                failure.detail
            );
        }
        other => panic!("Expected FP SAT fallback, got: {other:?}"),
    }
}

/// Regression (#5777): assertion and assumption validation must share the same
/// private leaf helper and differ only in the boundary they report.
#[test]
fn test_typed_contract_shared_leaf_helper_boundaries_5777() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let p_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    let flags = executor.precompute_term_flags();
    let af = flags[p_x.index()];
    let model = empty_model();

    let assertion_observation = executor.validate_term_observation(
        &model,
        p_x,
        0,
        af,
        false,
        ValidationTarget::GroundAssertion,
    );
    let assumption_observation =
        executor.validate_term_observation(&model, p_x, 0, af, false, ValidationTarget::Assumption);

    match assertion_observation {
        ValidationObservation::Verdict {
            verdict: VerificationVerdict::Incomplete(ref failure),
            ..
        } => {
            assert_eq!(failure.boundary, VerificationBoundary::SmtGroundAssertion);
        }
        other => panic!("Expected assertion incomplete verdict, got: {other:?}"),
    }

    match assumption_observation {
        ValidationObservation::Verdict {
            verdict: VerificationVerdict::Incomplete(ref failure),
            ..
        } => {
            assert_eq!(failure.boundary, VerificationBoundary::SmtAssumption);
        }
        other => panic!("Expected assumption incomplete verdict, got: {other:?}"),
    }
}

/// Regression (#5777 audit): when SAT validation degrades to `Unknown`, the
/// partial validation stats must survive so `VerificationSummary` can explain
/// why validation failed instead of reporting zero evidence.
#[test]
fn test_typed_contract_finalize_preserves_incomplete_stats_5777() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::String);
    let b = executor.ctx.terms.mk_var("b", Sort::String);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    executor.ctx.assertions.push(eq_ab);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(eq_ab, true)]));

    let result = executor
        .finalize_sat_model_validation()
        .expect("fallback-only validation should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    let stats = executor
        .last_validation_stats
        .as_ref()
        .expect("incomplete validation must preserve partial stats");
    assert_eq!(stats.total, 1);
    assert_eq!(stats.checked, 0);
    assert_eq!(stats.sat_fallback_count, 1);
}

/// Regression (#5777 audit): the consumer-facing provenance counters must
/// separate independent, delegated, and incomplete categories.
#[test]
fn test_verification_evidence_counts_preserve_independent_and_delegated_split_5777() {
    let stats = ValidationStats {
        checked: 5,
        delegated_checks: 2,
        array_delegated_checks: 1,
        skipped_internal: 1,
        skipped_quantifier: 2,
        skipped_datatype: 3,
        skipped_dtbv: 4,
        skipped_arith_array_mix: 5,
        sat_fallback_count: 6,
        total: 23,
    };

    let (independent, delegated, incomplete) = stats.verification_evidence_counts();
    assert_eq!(independent, 3);
    assert_eq!(delegated, 2);
    assert_eq!(incomplete, 21);
}

#[test]
fn test_validate_model_accepts_sat_backed_negated_user_uf_over_datatype_9007() {
    let mut executor = Executor::new();
    let commands = parse(
        r#"
        (set-logic ALL)
        (declare-datatype FMap ((mk-fmap)))
        (declare-const call_43 FMap)
        (declare-fun fmap_contains (FMap Int) Bool)
        (assert (not (fmap_contains call_43 0)))
    "#,
    )
    .expect("valid #9007 repro input");
    executor
        .execute_all(&commands)
        .expect("declarations and assertion elaborate");

    let assertion = *executor
        .ctx
        .assertions
        .last()
        .expect("repro assertion is present");
    let inner = match executor.ctx.terms.get(assertion) {
        TermData::Not(inner) => *inner,
        other => panic!("expected negated predicate assertion, got {other:?}"),
    };
    let (call_43, zero) = match executor.ctx.terms.get(inner) {
        TermData::App(sym, args) if sym.name() == "fmap_contains" && args.len() == 2 => {
            (args[0], args[1])
        }
        other => panic!("expected fmap_contains application, got {other:?}"),
    };
    assert!(
        executor.contains_datatype_term(assertion),
        "the assertion must take the DT validation branch"
    );

    let mut euf_model = EufModel::default();
    euf_model
        .sort_elements
        .insert("FMap".to_string(), vec!["@FMap!0".to_string()]);
    euf_model.term_values.insert(call_43, "@FMap!0".to_string());
    euf_model.function_tables.insert(
        "fmap_contains".to_string(),
        vec![(
            vec!["@FMap!0".to_string(), executor.format_term(zero)],
            "true".to_string(),
        )],
    );

    let mut model = model_with_sat_assignments(&[(assertion, true)]);
    model.euf_model = Some(euf_model);
    assert_eq!(
        executor.evaluate_term(&model, assertion),
        EvalValue::Bool(false),
        "the extracted UF table reproduces the #9007 false DT evaluation"
    );

    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);
    let stats = executor
        .validate_model()
        .expect("SAT-backed user UF predicate over DT should use fallback");

    assert_eq!(stats.sat_fallback_count, 1);
    assert_eq!(stats.checked, 0);
}

#[test]
fn test_validate_model_preserves_hard_dt_tester_violation_9007() {
    let mut executor = Executor::new();
    // NB: a TWO-constructor datatype keeps `call_43` a genuinely free variable
    // and the tester symbolic. With a single nullary constructor, declare-const
    // binds the constant to the constructor term itself (#1745) and the
    // tester-over-constructor fold (#rec-dt-expansion) now correctly
    // constant-folds `(not (is-mk-fmap call_43))` to `false` at elaboration
    // (differentially verified vs z3: unsat), which would bypass the
    // validate_model machinery this test exercises.
    let commands = parse(
        r#"
        (set-logic QF_DT)
        (declare-datatype FMap ((mk-fmap) (other-fmap)))
        (declare-const call_43 FMap)
        (assert (not (is-mk-fmap call_43)))
    "#,
    )
    .expect("valid DT tester input");
    executor
        .execute_all(&commands)
        .expect("declarations and assertion elaborate");

    let assertion = *executor
        .ctx
        .assertions
        .last()
        .expect("tester assertion is present");
    let inner = match executor.ctx.terms.get(assertion) {
        TermData::Not(inner) => *inner,
        other => panic!("expected negated tester assertion, got {other:?}"),
    };

    let model = model_with_sat_assignments(&[(assertion, true), (inner, true)]);
    assert_eq!(
        executor.evaluate_term(&model, assertion),
        EvalValue::Bool(false),
        "the crafted model should make the negated tester evaluate false"
    );

    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);
    let err = executor
        .validate_model()
        .expect_err("real DT tester violations must not use the #9007 fallback");

    match err {
        ModelValidationError::Violated(failure) => {
            assert_eq!(failure.boundary, VerificationBoundary::SmtGroundAssertion);
            assert!(
                failure.detail.contains("datatype"),
                "expected datatype violation detail, got: {}",
                failure.detail
            );
        }
        other => panic!("expected hard DT tester violation, got {other:?}"),
    }
}

// ==========================================================================
// Pre-existing regressions
// ==========================================================================

#[test]
fn test_finalize_sat_assumption_validation_degrades_internal_assumption() {
    // Internal helper terms are not independently checkable assumptions.
    // Returning SAT here would accept a zero-evidence assumption packet.
    let mut executor = Executor::new();
    let list = Sort::Uninterpreted("List".to_string());
    let x = executor.ctx.terms.mk_var("x", list);
    let depth = executor
        .ctx
        .terms
        .mk_app(Symbol::named("__ay_dt_depth_List"), vec![x], Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let assumption = executor.ctx.terms.mk_eq(depth, zero);
    assert!(
        executor.contains_internal_symbol(assumption),
        "assumption must retain the internal helper symbol"
    );

    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor
        .finalize_sat_assumption_validation(&[assumption])
        .expect("internal assumption should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn test_finalize_sat_model_validation_returns_unknown_for_unevaluable_seq_term() {
    // (#6273, #4057) The public SAT finalizer must degrade skipped_internal-only
    // Seq packets to Unknown, not leave the caller with a false SAT result.
    let mut executor = Executor::new();
    let seq_sort = Sort::Seq(Box::new(Sort::Int));
    let s = executor.ctx.terms.mk_var("s", seq_sort);
    let seq_len = executor
        .ctx
        .terms
        .mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let assertion = executor.ctx.terms.mk_eq(seq_len, five);
    executor.ctx.assertions.push(assertion);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor
        .finalize_sat_model_validation()
        .expect("unevaluable seq term should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}
