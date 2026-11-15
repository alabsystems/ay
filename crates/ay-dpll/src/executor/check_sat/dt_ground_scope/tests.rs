// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::executor::model::Model;
use crate::executor_types::ExecutorError;
use crate::incremental_state::IncrementalSubsystem;

fn fixture() -> (Executor, Vec<TermId>, Vec<TermId>) {
    let mut exec = Executor::new();
    exec.execute_all(
        &ay_frontend::parse(
            "(declare-const a Bool) (declare-const b Bool) (declare-const generated Bool)
         (assert a) (assert (forall ((i Int)) (>= (+ i 1) i)))",
        )
        .expect("parse"),
    )
    .expect("declare");
    let b = exec
        .ctx
        .symbol_info_by_identity("b")
        .expect("b")
        .term
        .expect("constant");
    let generated = exec
        .ctx
        .symbol_info_by_identity("generated")
        .expect("generated")
        .term
        .expect("constant");
    let mut full = exec.ctx.assertions.clone();
    full.push(b);
    exec.last_assumptions = Some(vec![b, full[1]]);
    exec.self_check = true;
    exec.independent_gate_authored_assertions = Some(full.clone());
    exec.self_check_authored_assertions = Some(full.clone());
    exec.proof_problem_assertion_provenance = Some(ProofProblemAssertionProvenance::passthrough(
        &full,
        &exec.ctx.assertions,
    ));
    exec.proof_tracker.enable();
    exec.proof_tracker
        .add_assumption(full[0], None)
        .expect("outer proof");
    exec.proof_tracker.push();
    exec.last_model = Some(Model::empty());
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model_validated = true;
    let working = vec![full[0], generated];
    (exec, full, working)
}

fn assert_restored(exec: &Executor, full: &[TermId]) {
    assert_eq!(exec.ctx.assertions, full[..2]);
    assert_eq!(
        exec.last_assumptions.as_deref(),
        Some(&[full[2], full[1]][..])
    );
    assert_eq!(
        exec.independent_gate_authored_assertions.as_deref(),
        Some(full)
    );
    assert_eq!(exec.self_check_authored_assertions.as_deref(), Some(full));
    assert_eq!(
        exec.proof_problem_assertion_provenance
            .as_ref()
            .expect("authority")
            .original_problem_assertions,
        full
    );
    assert_eq!(exec.proof_tracker.scope_depth(), 1);
    assert_eq!(exec.proof_tracker.recorded_step_count(), 1);
    assert!(exec.last_model_validated);
    assert!(exec.last_model.is_some());
}

#[test]
fn ground_scope_keeps_assumptions_and_does_not_author_generated_roots() {
    let (mut exec, full, working) = fixture();
    let epoch = exec
        .last_model
        .as_mut()
        .expect("model")
        .seal_quantified_grant_model();
    let evidence = exec.with_dt_ground_candidate_scope(
        working.clone(),
        &full,
        |this| {
            assert_eq!(this.ctx.assertions, working);
            assert_eq!(
                this.independent_gate_authored_assertions.as_deref(),
                Some(&[full[0], full[2]][..])
            );
            assert_eq!(this.last_assumptions.as_deref(), Some(&[full[2]][..]));
            let provenance = this
                .proof_problem_assertion_provenance
                .as_ref()
                .expect("ground authority");
            assert!(!provenance.assertion_sources.contains_key(&working[1]));
            assert_eq!(this.proof_tracker.scope_depth(), 0);
            assert!(this.proof_tracker.is_enabled());
            this.proof_tracker.add_assumption(working[1], None);
            let _discarded = this.proof_tracker.take_proof();
            Ok(SolveResult::Unknown)
        },
        |_| panic!("non-SAT ground candidate cannot be certified"),
    );
    assert!(evidence.is_none());
    assert_restored(&exec, &full);
    assert!(exec
        .last_model
        .as_ref()
        .expect("model")
        .carries_quantified_grant_model(&epoch));
}

#[test]
fn a_ground_error_restores_absent_root_options_and_model_identity() {
    let (mut exec, full, working) = fixture();
    exec.independent_gate_authored_assertions = None;
    exec.self_check_authored_assertions = None;
    let epoch = exec
        .last_model
        .as_mut()
        .expect("model")
        .seal_quantified_grant_model();
    let evidence = exec.with_dt_ground_candidate_scope(
        working,
        &full,
        |_| {
            Err(ExecutorError::UnsupportedLogic(
                "test candidate".to_string(),
            ))
        },
        |_| panic!("error cannot grant"),
    );
    assert!(evidence.is_none());
    assert!(exec.independent_gate_authored_assertions.is_none());
    assert!(exec.self_check_authored_assertions.is_none());
    assert!(exec
        .last_model
        .as_ref()
        .expect("model")
        .carries_quantified_grant_model(&epoch));
    assert_eq!(exec.ctx.assertions, full[..2]);
}

#[test]
fn ground_unwind_restores_query_policy_and_exact_outer_tracker() {
    let (mut exec, full, working) = fixture();
    let deadline = exec.solve_deadline.get();
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        exec.with_dt_ground_candidate_scope(
            working,
            &full,
            |this| {
                this.dt_lazy_lane_suppressed_for_scoped_probe = true;
                this.defer_model_validation = true;
                let _discarded = this.proof_tracker.take_proof();
                panic!("ground candidate unwind")
            },
            |_| panic!("unwind cannot grant"),
        )
    }));
    assert!(caught.is_err());
    assert_restored(&exec, &full);
    assert_eq!(exec.solve_deadline.get(), deadline);
    assert!(!exec.dt_lazy_lane_suppressed_for_scoped_probe);
    assert!(!exec.defer_model_validation);
}

#[test]
fn full_certificate_decline_restores_predecessor_and_lane_sidecars() {
    let (mut exec, full, working) = fixture();
    exec.lane_model_pin_roots = vec![full[0]];
    exec.pending_lane_model_pin_roots = vec![full[2]];
    let epoch = exec
        .last_model
        .as_mut()
        .expect("model")
        .seal_quantified_grant_model();
    let evidence = exec.with_dt_ground_candidate_scope(
        working,
        &full,
        |this| {
            this.last_model = Some(Model::empty());
            this.lane_model_pin_roots = vec![full[2]];
            Ok(SolveResult::Sat)
        },
        |this| {
            assert_eq!(
                this.independent_gate_authored_assertions.as_deref(),
                Some(full.as_slice())
            );
            assert_eq!(
                this.last_assumptions.as_deref(),
                Some(&[full[2], full[1]][..])
            );
            assert!(!this.last_model_validated);
            assert!(!this
                .last_model
                .as_ref()
                .expect("candidate")
                .carries_quantified_grant_model(&epoch));
            None
        },
    );
    assert!(evidence.is_none());
    assert_restored(&exec, &full);
    assert_eq!(exec.lane_model_pin_roots, [full[0]]);
    assert_eq!(exec.pending_lane_model_pin_roots, [full[2]]);
    assert!(exec
        .last_model
        .as_ref()
        .expect("model")
        .carries_quantified_grant_model(&epoch));
}

#[test]
fn full_certificate_unwind_restores_predecessor_model() {
    let (mut exec, full, working) = fixture();
    let epoch = exec
        .last_model
        .as_mut()
        .expect("model")
        .seal_quantified_grant_model();
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        exec.with_dt_ground_candidate_scope(
            working,
            &full,
            |this| {
                this.last_model = Some(Model::empty());
                Ok(SolveResult::Sat)
            },
            |_| panic!("certificate unwind"),
        )
    }));
    assert!(caught.is_err());
    assert_restored(&exec, &full);
    assert!(exec
        .last_model
        .as_ref()
        .expect("model")
        .carries_quantified_grant_model(&epoch));
}

#[test]
fn ground_candidate_keeps_query_recovery_without_old_model_delegations() {
    let (mut exec, full, _) = fixture();
    exec.recorded_var_substitutions.insert(full[0], full[2]);
    exec.model_validation_delegated_assertions.insert(full[0]);
    let evidence = exec.with_dt_ground_candidate_scope(
        vec![full[0]],
        &full,
        |this| {
            assert!(this.model_validation_delegated_assertions.is_empty());
            let mut candidate = Model::empty();
            candidate.bool_overrides.insert(full[2], true);
            this.last_model = Some(candidate);
            this.last_result = Some(SolveResult::Sat);
            this.complete_model_for_validation(&[]);
            assert!(matches!(
                this.evaluate_term(this.last_model.as_ref().expect("candidate"), full[0]),
                crate::executor::model::EvalValue::Bool(true)
            ));
            Ok(SolveResult::Unknown)
        },
        |_| panic!("declining candidate cannot grant"),
    );
    assert!(evidence.is_none());
    assert_eq!(
        exec.recorded_var_substitutions.get(&full[0]),
        Some(&full[2])
    );
    assert!(exec
        .model_validation_delegated_assertions
        .contains(&full[0]));
}

#[test]
fn persistent_bv_and_fp_lanes_are_isolated_and_restored_on_unwind() {
    use crate::incremental_state::{IncrementalBvState, IncrementalFpState};
    let (mut exec, full, working) = fixture();
    exec.incr_bv_state = Some(Box::new(IncrementalBvState::new()));
    exec.incr_fp_state = Some(Box::new(IncrementalFpState::new()));
    exec.fp_persistent_armed = true;
    let bv = exec.incr_bv_state.as_deref().expect("BV") as *const _;
    let fp = exec.incr_fp_state.as_deref().expect("FP") as *const _;
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        exec.with_dt_ground_candidate_scope(
            working,
            &full,
            |this| {
                assert!(this.incr_bv_state.is_none());
                assert!(this.incr_fp_state.is_none());
                assert!(!this.fp_persistent_armed);
                this.incr_bv_state = Some(Box::new(IncrementalBvState::new()));
                this.incr_fp_state = Some(Box::new(IncrementalFpState::new()));
                panic!("private lane unwind")
            },
            |_| panic!("unwind cannot grant"),
        )
    }));
    assert!(caught.is_err());
    assert_eq!(exec.incr_bv_state.as_deref().expect("BV") as *const _, bv);
    assert_eq!(exec.incr_fp_state.as_deref().expect("FP") as *const _, fp);
    assert!(exec.fp_persistent_armed);
    assert_restored(&exec, &full);
}

#[test]
fn ground_grants_cannot_authorize_the_original_certificate() {
    let (mut exec, full, working) = fixture();
    exec.dt_cert_grant_active = true;
    exec.finite_table_cert_grant_active = true;
    exec.const_interp_cert_grant_active = true;
    exec.sat_validated_by_mod_div_or_branch = true;
    let epoch = exec
        .last_model
        .as_mut()
        .expect("model")
        .seal_quantified_grant_model();
    let evidence = exec.with_dt_ground_candidate_scope(
        working,
        &full,
        |this| {
            assert!(!this.dt_cert_grant_active && !this.finite_table_cert_grant_active);
            assert!(
                !this.const_interp_cert_grant_active && !this.sat_validated_by_mod_div_or_branch
            );
            this.last_model = Some(Model::empty());
            this.dt_cert_grant_active = true;
            this.finite_table_cert_grant_active = true;
            this.const_interp_cert_grant_active = true;
            this.sat_validated_by_mod_div_or_branch = true;
            Ok(SolveResult::Sat)
        },
        |this| {
            assert!(!this.dt_cert_grant_active && !this.finite_table_cert_grant_active);
            assert!(
                !this.const_interp_cert_grant_active && !this.sat_validated_by_mod_div_or_branch
            );
            assert!(!this
                .last_model
                .as_ref()
                .expect("candidate")
                .carries_quantified_grant_model(&epoch));
            None
        },
    );
    assert!(evidence.is_none());
    assert!(exec.dt_cert_grant_active && exec.finite_table_cert_grant_active);
    assert!(exec.const_interp_cert_grant_active && exec.sat_validated_by_mod_div_or_branch);
    assert!(exec
        .last_model
        .as_ref()
        .expect("restored")
        .carries_quantified_grant_model(&epoch));
}

#[test]
fn private_ground_rollback_does_not_refund_consumed_query_work() {
    let (mut exec, full, working) = fixture();
    exec.consequence_replay_attempts.set(2);
    exec.consequence_replay_direct_state.set(Some((1, 1)));
    let source_before = exec.proof_source_work.remaining_for_test();
    let checkpoint_before = exec.proof_checkpoint_budget.remaining();
    let evidence = exec.with_dt_ground_candidate_scope(
        working,
        &full,
        |this| {
            this.consequence_replay_attempts
                .set(this.consequence_replay_attempts.get() + 1);
            this.consequence_replay_direct_state.set(Some((2, 2)));
            assert!(this.proof_source_work.spend_canonical_scan_work(7));
            this.proof_tracker
                .add_assumption(full[0], None)
                .expect("private step");
            let _checkpoint = this
                .bounded_proof_rollback_checkpoint()
                .expect("bounded snapshot");
            Ok(SolveResult::Unknown)
        },
        |_| panic!("decline cannot grant"),
    );
    assert!(evidence.is_none());
    assert_eq!(exec.consequence_replay_attempts.get(), 3);
    assert_eq!(exec.consequence_replay_direct_state.get(), Some((2, 2)));
    assert_eq!(
        exec.proof_source_work.remaining_for_test(),
        source_before - 7
    );
    assert!(exec.proof_checkpoint_budget.remaining() < checkpoint_before);
    assert_restored(&exec, &full);
}
