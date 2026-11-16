// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Scoped proposal controls are not public SAT authority. The final two tests
//! execute parsed native sessions; the callback fixtures isolate policy and
//! restoration without claiming that a fabricated model proves a formula.

use super::*;
use crate::executor::model::Model;
use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;
use ay_core::Symbol;

fn candidate(executor: &mut Executor) -> Result<SolveResult> {
    assert!(executor.last_assumptions.is_none());
    let mut model = Model::empty();
    // Unmapped marker data let the test detect eager completion/replacement.
    // These bits are not evidence for any assertion or assumption.
    model.sat_model = vec![true, false, true];
    executor.last_model = Some(model);
    executor.last_model_validated = false;
    executor.last_result = Some(SolveResult::Sat);
    Ok(SolveResult::Sat)
}

fn no_candidate(executor: &mut Executor) -> Result<SolveResult> {
    executor.last_model = None;
    executor.last_result = Some(SolveResult::Sat);
    Ok(SolveResult::Sat)
}

fn unknown_with_stale_candidate(executor: &mut Executor) -> Result<SolveResult> {
    let _ = candidate(executor)?;
    executor.last_result = Some(SolveResult::Unknown);
    Ok(SolveResult::Unknown)
}

fn failed_solve(_: &mut Executor) -> Result<SolveResult> {
    Err(ExecutorError::UnsupportedLogic("scoped-test-error".into()))
}

fn stopped_candidate(executor: &mut Executor) -> Result<SolveResult> {
    let result = candidate(executor)?;
    executor.record_evaluation_stop(UnknownOrigin::SolveDeadline);
    Ok(result)
}

fn stale_validation_candidate(executor: &mut Executor) -> Result<SolveResult> {
    let result = candidate(executor)?;
    // Deliberately stale test-only evidence, never a genuine SAT authority.
    executor.plant_stale_sat_certificate_for_test();
    assert!(executor.last_sat_certificate.is_some());
    executor.last_model_validated = true;
    Ok(result)
}

fn unevaluable_assumption(executor: &mut Executor) -> TermId {
    let literal = executor.ctx.terms.mk_string("hello".to_string());
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("scoped_predicate"), vec![literal], Sort::Bool)
}

#[test]
fn scoped_publication_preserves_legacy_validation_and_defers_only_explicitly() {
    for legacy in [true, false] {
        let mut executor = Executor::new();
        let base = executor.ctx.terms.true_term();
        let assumption = unevaluable_assumption(&mut executor);
        executor.ctx.assertions = vec![base];
        executor.last_assumptions = Some(vec![assumption]);
        let result = if legacy {
            executor.solve_scoped_assumptions(&[base], &[assumption], candidate)
        } else {
            executor.solve_scoped_assumptions_with_publication(
                &[base],
                &[assumption],
                candidate,
                AssumptionSatPublication::EmitHere,
            )
        }
        .unwrap();
        assert_eq!(result, SolveResult::Unknown);
        assert_eq!(
            executor.last_unknown_reason,
            Some(UnknownReason::Incomplete)
        );
        assert_eq!(executor.ctx.assertions, [base]);
        assert_eq!(executor.last_assumptions, Some(vec![assumption]));
        assert!(executor.last_sat_certificate.is_none());
    }

    let mut executor = Executor::new();
    let base = executor.ctx.terms.true_term();
    let assumption = unevaluable_assumption(&mut executor);
    executor.ctx.assertions = vec![base];
    executor.last_assumptions = Some(vec![assumption]);
    let result = executor
        .solve_scoped_assumptions_with_publication(
            &[base],
            &[assumption],
            candidate,
            AssumptionSatPublication::DeferToPlainCheckSat,
        )
        .unwrap();
    assert_eq!(
        result,
        SolveResult::Sat,
        "an unvalidated proposal, not public SAT"
    );
    assert_eq!(
        executor.last_model.as_ref().unwrap().sat_model,
        [true, false, true]
    );
    assert!(!executor.last_model_validated);
    assert!(executor.last_sat_certificate.is_none());
    assert_eq!(executor.last_unknown_reason, None);
    assert_eq!(executor.ctx.assertions, [base]);
    assert_eq!(executor.last_assumptions, Some(vec![assumption]));
}

#[test]
fn deferred_proposal_is_validated_only_after_original_roots_are_restored() {
    let mut executor = Executor::new();
    let truth = executor.ctx.terms.true_term();
    executor.last_assumptions = Some(vec![truth]);
    let proposed = executor
        .solve_scoped_assumptions_with_publication(
            &[],
            &[truth],
            stale_validation_candidate,
            AssumptionSatPublication::DeferToPlainCheckSat,
        )
        .unwrap();
    assert_eq!(proposed, SolveResult::Sat);
    assert_eq!(executor.ctx.assertions, [] as [TermId; 0]);
    assert!(
        !executor.last_model_validated,
        "stale producer evidence is retired"
    );
    assert!(executor.last_sat_certificate.is_none());
    executor.ctx.assertions = vec![truth];
    let emitted = executor.emit_sat_verdict(proposed, &[]).unwrap();
    assert_eq!(emitted, SolveResult::Sat);
    assert!(executor.last_model_validated);
    assert!(executor.last_sat_certificate.is_some());
}

#[test]
fn deferred_false_or_missing_candidate_cannot_pass_the_outer_funnel() {
    for missing in [false, true] {
        let mut executor = Executor::new();
        let obligation = if missing {
            unevaluable_assumption(&mut executor)
        } else {
            executor.ctx.terms.false_term()
        };
        executor.last_assumptions = Some(vec![obligation]);
        let solve: fn(&mut Executor) -> Result<SolveResult> =
            if missing { no_candidate } else { candidate };
        let proposed = executor
            .solve_scoped_assumptions_with_publication(
                &[],
                &[obligation],
                solve,
                AssumptionSatPublication::DeferToPlainCheckSat,
            )
            .unwrap();
        assert_eq!(proposed, SolveResult::Sat, "still only an inner proposal");
        assert_eq!(
            executor.last_model.is_none(),
            missing,
            "no model was fabricated"
        );
        assert!(executor.last_sat_certificate.is_none());
        executor.ctx.assertions = vec![obligation];
        assert_eq!(
            executor.emit_sat_verdict(proposed, &[]).unwrap(),
            SolveResult::Unknown
        );
        assert!(!executor.last_model_validated);
        assert!(executor.last_sat_certificate.is_none());
    }
}

#[test]
fn deferred_policy_never_promotes_unknown_or_an_error() {
    let mut executor = Executor::new();
    let base = executor.ctx.terms.true_term();
    let assumption = unevaluable_assumption(&mut executor);
    executor.ctx.assertions = vec![base];
    executor.last_assumptions = Some(vec![assumption]);
    let result = executor
        .solve_scoped_assumptions_with_publication(
            &[base],
            &[assumption],
            unknown_with_stale_candidate,
            AssumptionSatPublication::DeferToPlainCheckSat,
        )
        .unwrap();
    assert_eq!(result, SolveResult::Unknown);
    assert!(
        executor.last_model.is_some(),
        "a stale candidate cannot promote Unknown"
    );
    assert!(executor.last_sat_certificate.is_none());
    assert_eq!(executor.ctx.assertions, [base]);
    assert_eq!(executor.last_assumptions, Some(vec![assumption]));
    let failed = executor.solve_scoped_assumptions_with_publication(
        &[base],
        &[assumption],
        failed_solve,
        AssumptionSatPublication::DeferToPlainCheckSat,
    );
    assert!(
        matches!(failed, Err(ExecutorError::UnsupportedLogic(ref text)) if text == "scoped-test-error")
    );
    assert_eq!(executor.ctx.assertions, [base]);
    assert_eq!(executor.last_assumptions, Some(vec![assumption]));
}

#[test]
fn scoped_publication_preserves_a_held_stop_for_both_owners() {
    for publication in [
        AssumptionSatPublication::EmitHere,
        AssumptionSatPublication::DeferToPlainCheckSat,
    ] {
        let mut executor = Executor::new();
        let truth = executor.ctx.terms.true_term();
        let _read = executor.begin_external_evaluation_read();
        let result = executor
            .solve_scoped_assumptions_with_publication(
                &[],
                &[truth],
                stopped_candidate,
                publication,
            )
            .unwrap();
        assert_eq!(result, SolveResult::Unknown);
        assert_eq!(
            executor.evaluation_stop_origin(),
            Some(UnknownOrigin::SolveDeadline)
        );
        assert_eq!(executor.last_unknown_reason, Some(UnknownReason::Timeout));
        assert!(executor.last_model.is_none());
        assert!(!executor.last_model_validated);
        assert!(executor.last_sat_certificate.is_none());
        assert_eq!(executor.ctx.assertions, [] as [TermId; 0]);
    }
}

fn panicking_solve(executor: &mut Executor) -> Result<SolveResult> {
    assert!(executor.last_assumptions.is_none());
    let generated = executor.ctx.terms.mk_var("scoped_generated", Sort::Bool);
    executor.proof_problem_assertion_provenance = Some(
        ProofProblemAssertionProvenance::passthrough(&[generated], &[generated]),
    );
    panic!("scoped publication panic");
}

#[test]
fn policy_kernel_restores_exact_scope_and_authority_on_panic() {
    for publication in [
        AssumptionSatPublication::EmitHere,
        AssumptionSatPublication::DeferToPlainCheckSat,
    ] {
        let mut executor = Executor::new();
        let base = executor.ctx.terms.mk_var("base", Sort::Bool);
        let assumption = executor.ctx.terms.mk_var("assumption", Sort::Bool);
        executor.ctx.assertions = vec![base];
        executor.last_assumptions = Some(vec![assumption]);
        executor.proof_problem_assertion_provenance = Some(
            ProofProblemAssertionProvenance::passthrough(&[base], &[base]),
        );
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            executor.solve_scoped_assumptions_with_publication(
                &[base],
                &[assumption],
                panicking_solve,
                publication,
            )
        }));
        assert!(outcome.is_err());
        assert_eq!(executor.ctx.assertions, [base]);
        assert_eq!(executor.last_assumptions, Some(vec![assumption]));
        let restored = executor
            .proof_problem_assertion_provenance
            .as_ref()
            .unwrap();
        assert_eq!(restored.original_problem_assertions, [base]);
        assert_eq!(restored.problem_assertions, [base]);
        assert_eq!(restored.assertion_sources.len(), 1);
        assert_eq!(restored.assertion_sources[&base], [vec![base]]);
    }
}

#[test]
fn actual_named_core_uflia_queries_keep_sat_and_unsat_verdicts() {
    for (tail, expected) in [
        ("(assert (! (> x 0) :named positive))", "sat"),
        (
            "(assert (! (and (> x 0) (< x 0)) :named impossible))",
            "unsat",
        ),
    ] {
        let mut executor = Executor::new();
        let source = format!(
            "(set-option :produce-unsat-cores true) (set-logic QF_UFLIA) \
             (declare-const x Int) (declare-fun f (Int) Int) \
             (assert (! (= (f x) 7) :named function_row)) {tail} (check-sat)"
        );
        assert_eq!(
            executor
                .execute_all(&ay_frontend::parse(&source).unwrap())
                .unwrap(),
            [expected]
        );
    }
}

#[test]
fn actual_named_scoped_assumptions_do_not_leak_to_the_next_public_query() {
    let mut executor = Executor::new();
    let source = "(set-option :produce-unsat-cores true) (set-logic QF_UFLIA)
        (declare-const p Bool) (declare-const x Int) (declare-fun f (Int) Int)
        (assert (! (= x 0) :named base_x))
        (assert (! (= (f x) 7) :named base_f))
        (check-sat-assuming (p))
        (assert (not p)) (check-sat)
        (check-sat-assuming (p))";
    assert_eq!(
        executor
            .execute_all(&ay_frontend::parse(source).unwrap())
            .unwrap(),
        ["sat", "sat", "unsat"],
    );
}
