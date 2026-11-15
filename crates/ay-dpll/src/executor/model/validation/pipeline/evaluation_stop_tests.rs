// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Candidate-only boundary tests unless a public check is explicitly executed.

use super::*;
use crate::executor::model::eval_fp::FpEvalPhase;
use crate::executor::model::{EvalValue, Model};
use crate::executor_types::UnknownOrigin;
use ay_core::{Sort, Symbol, TermData};
use ay_fp::{FpBuildStage, FpModelValue};
use ay_model_check::GateVerdict;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn append(executor: &mut Executor, source: &str) {
    for command in ay_frontend::parse(source).unwrap() {
        executor.ctx.process_command(&command).unwrap();
    }
}

fn candidate(truth: bool) -> Executor {
    let mut executor = Executor::new();
    append(
        &mut executor,
        if truth {
            "(assert true)"
        } else {
            "(assert false)"
        },
    );
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(Model::empty());
    executor
}

fn revoked(executor: &Executor, origin: UnknownOrigin) {
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(executor.last_unknown_reason, Some(origin.reason()));
    assert_eq!(executor.last_unknown_origin, Some(origin));
    assert!(!executor.last_model_validated);
    assert!(executor.last_model.is_none());
    assert!(executor.last_sat_certificate.is_none());
    assert!(executor.last_assumption_core.is_none());
}

fn division(executor: &mut Executor) -> TermId {
    append(
        executor,
        "(assert (fp.eq
        (fp.div RTP ((_ to_fp 5 11) #x3c00) ((_ to_fp 5 11) #x4200))
        ((_ to_fp 5 11) #x3556)))",
    );
    let root = *executor.ctx.assertions.last().unwrap();
    let TermData::App(_, args) = executor.ctx.terms.get(root) else {
        panic!("FP equality")
    };
    let term = args[0];
    assert!(
        matches!(executor.ctx.terms.get(term), TermData::App(sym, _) if sym.name() == "fp.div")
    );
    term
}

fn interrupt_division(executor: &mut Executor, term: TermId) {
    let flag = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&flag));
    let rows = Cell::new(0);
    let searched = Cell::new(false);
    let result =
        executor.evaluate_fp_term_via_bitblast_controlled(&Model::empty(), term, &|phase| {
            if let FpEvalPhase::Construction(progress) = phase {
                if progress.stage == FpBuildStage::DivideRow {
                    rows.set(rows.get() + 1);
                    if rows.get() == 4 {
                        flag.store(true, Ordering::Relaxed);
                    }
                }
            }
            if matches!(phase, FpEvalPhase::SatSearch) {
                searched.set(true);
            }
        });
    assert!(matches!(result, Err(UnknownOrigin::InterruptFlag)));
    assert_eq!(
        rows.get(),
        4,
        "actual interior restoring-divider checkpoint"
    );
    assert!(!searched.get());
    flag.store(false, Ordering::Relaxed);
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
}

#[test]
fn actual_fp_stop_cannot_be_delegated_to_lra_and_fresh_attempt_is_exact() {
    let mut executor = candidate(true);
    let term = division(&mut executor);
    let assertion = *executor.ctx.assertions.last().unwrap();
    let roots = executor.ctx.assertions.clone();
    let stamp = executor.ctx.source_context_stamp();
    let mut model = Model::empty();
    model.lra_model = Some(ay_lra::LraModel {
        values: Default::default(),
    });
    let read = executor.begin_external_evaluation_read();
    interrupt_division(&mut executor, term);
    let observation = executor.validate_term_observation(
        &model,
        assertion,
        0,
        super::super::TERM_FLAG_FP,
        false,
        ValidationTarget::GroundAssertion,
    );
    assert!(matches!(
        observation,
        ValidationObservation::Verdict {
            verdict: VerificationVerdict::Incomplete(_),
            ..
        }
    ));
    assert!(matches!(
        executor.validate_model_attempt().error,
        Some(ModelValidationError::Incomplete(_))
    ));
    assert_eq!(executor.ctx.assertions, roots);
    assert_eq!(executor.ctx.source_context_stamp(), stamp);
    drop(read);
    let _fresh = executor.begin_external_evaluation_read();
    assert!(executor.evaluation_stop_origin().is_none());
    let value = executor
        .evaluate_fp_term_via_bitblast_controlled(&model, term, &|_| {})
        .unwrap()
        .unwrap();
    // RTP(1/3), in binary16: 0x3556, not the RTZ/RNE value 0x3555.
    assert!(matches!(
        value,
        FpModelValue::Fp {
            sign: false,
            exponent: 13,
            significand: 342,
            eb: 5,
            sb: 11
        }
    ));
    assert!(matches!(
        executor.evaluate_term(&model, assertion),
        EvalValue::Bool(true)
    ));
}

#[test]
fn healthy_unknown_fp_delegation_and_real_false_observation_remain_distinct() {
    let mut executor = candidate(true);
    let x = executor
        .ctx
        .terms
        .mk_var("missing-fp", Sort::FloatingPoint(5, 11));
    let atom = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.isZero"), vec![x], Sort::Bool);
    let mut model = Model::empty();
    model.lra_model = Some(ay_lra::LraModel {
        values: Default::default(),
    });
    let _read = executor.begin_external_evaluation_read();
    // This is the existing dispatch policy, not a claim that this empty LRA
    // table is independently sufficient to certify the complete formula.
    let observation = executor.validate_term_observation(
        &model,
        atom,
        0,
        super::super::TERM_FLAG_FP,
        false,
        ValidationTarget::GroundAssertion,
    );
    assert!(matches!(
        observation,
        ValidationObservation::Verdict {
            verdict: VerificationVerdict::Verified {
                evidence: VerificationEvidenceKind::DelegatedSolver,
                ..
            },
            ..
        }
    ));
    let falsehood = executor.ctx.terms.false_term();
    let false_observation = executor.validate_term_observation(
        &model,
        falsehood,
        0,
        0,
        false,
        ValidationTarget::GroundAssertion,
    );
    assert!(matches!(
        false_observation,
        ValidationObservation::Verdict {
            verdict: VerificationVerdict::Violated(_),
            ..
        }
    ));
    assert!(executor.evaluation_stop_origin().is_none());
}

#[test]
fn strict_none_and_independent_verdicts_cannot_authorize_a_stopped_attempt() {
    for truth in [true, false] {
        let executor = candidate(truth);
        let _read = executor.begin_external_evaluation_read();
        if truth {
            assert!(executor.exact_certificate_model_passes_strict_read_only());
            assert!(matches!(
                executor.confirm_sat_with_fully_evaluated_independent_gate(),
                GateVerdict::ConfirmedSat
            ));
        } else {
            assert!(matches!(
                executor.confirm_sat_with_fully_evaluated_independent_gate(),
                GateVerdict::ModelViolates { .. }
            ));
        }
        executor.record_evaluation_stop(UnknownOrigin::DeterministicResourceBudget);
        assert!(
            executor.verify_model_strict().is_none(),
            "no false-model claim on refusal"
        );
        assert!(!executor.exact_certificate_model_passes_strict_read_only());
        assert!(matches!(
            executor.confirm_sat_with_independent_gate(),
            GateVerdict::CannotConfirm { .. }
        ));
        assert!(matches!(
            executor.confirm_sat_with_fully_evaluated_independent_gate(),
            GateVerdict::CannotConfirm { .. }
        ));
        assert!(
            executor.last_model.is_some(),
            "read-only checks do not publish"
        );
    }
}

#[test]
fn each_mutable_gate_publishes_stop_without_model_rejection_or_retry() {
    let gates: [fn(&mut Executor, SolveResult) -> SolveResult; 4] = [
        Executor::apply_strict_model_gate,
        Executor::apply_independent_model_gate,
        Executor::apply_authoritative_failclosed_gate,
        Executor::apply_quantified_model_failclosed_gate,
    ];
    for gate in gates {
        let mut executor = candidate(false);
        executor.last_model_validated = true; // Deliberately stale candidate bookkeeping.
        executor.last_assumption_core = Some(Vec::new());
        executor.bv_subst_lane = true;
        executor.uflia_congruence_lane = true;
        executor.qfax_isolated_lane = true;
        let roots = executor.ctx.assertions.clone();
        let _read = executor.begin_external_evaluation_read();
        executor.record_evaluation_stop(UnknownOrigin::MemoryBudget);
        assert_eq!(gate(&mut executor, SolveResult::Sat), SolveResult::Unknown);
        revoked(&executor, UnknownOrigin::MemoryBudget);
        assert_eq!(executor.ctx.assertions, roots);
        assert_eq!(executor.last_statistics.model_validation_failures, 0);
        assert!(!executor.bv_subst_model_rejected);
        assert!(!executor.uflia_congruence_gate_rejected);
        assert!(!executor.qfax_isolated_model_rejected);
        assert!(executor.qfax_refinement_clause.is_none());
        assert!(executor.last_rejected_array_assertion.is_none());
    }
}

#[test]
fn stopped_finalizers_do_not_accept_assumptions_or_restore_unrepaired_candidates() {
    let mut executor = candidate(true);
    let truth = executor.ctx.terms.true_term();
    executor.unrepaired_model_candidate = Some(Model::empty());
    let _read = executor.begin_external_evaluation_read();
    executor.record_evaluation_stop(UnknownOrigin::SolveDeadline);
    let rejection = (0, "arrays", truth);
    assert_eq!(
        executor.strict_verdict_after_unrepaired_fallback(rejection),
        Some(rejection)
    );
    assert!(
        executor.unrepaired_model_candidate.is_some(),
        "no repair transaction was opened"
    );
    assert!(matches!(
        executor.validate_sat_assumptions(&[truth]),
        Err(ModelValidationError::Incomplete(_))
    ));
    assert_eq!(
        executor
            .finalize_sat_assumption_validation(&[truth])
            .unwrap(),
        SolveResult::Unknown
    );
    revoked(&executor, UnknownOrigin::SolveDeadline);
    assert_eq!(
        executor.finalize_sat_model_validation().unwrap(),
        SolveResult::Unknown
    );
    revoked(&executor, UnknownOrigin::SolveDeadline);
}

#[test]
fn real_helper_stop_revokes_prior_public_sat_only_at_publication_boundary() {
    let mut executor = Executor::new();
    assert_eq!(
        executor
            .execute_all(&ay_frontend::parse("(assert true) (check-sat)").unwrap())
            .unwrap(),
        ["sat"]
    );
    assert!(executor.last_model.is_some());
    let term = division(&mut executor);
    let roots = executor.ctx.assertions.clone();
    let stamp = executor.ctx.source_context_stamp();
    let read = executor.begin_external_evaluation_read();
    interrupt_division(&mut executor, term);
    assert_eq!(
        executor.last_result,
        Some(SolveResult::Sat),
        "read refusal alone preserves the prior decision"
    );
    assert!(executor.last_model.is_some());
    assert_eq!(
        executor
            .emit_sat_verdict(SolveResult::Sat, &[executor.ctx.terms.true_term()])
            .unwrap(),
        SolveResult::Unknown
    );
    revoked(&executor, UnknownOrigin::InterruptFlag);
    assert_eq!(executor.ctx.assertions, roots);
    assert_eq!(executor.ctx.source_context_stamp(), stamp);
    assert_eq!(executor.last_statistics.model_validation_failures, 0);
    drop(read);
    assert_eq!(
        executor
            .execute_all(&ay_frontend::parse("(check-sat)").unwrap())
            .unwrap(),
        ["sat"]
    );
}
