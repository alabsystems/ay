// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! White-box frontend, model-validation and publication-gate tests.
//! The synthetic input model / confirmation is not a claimed SAT search.

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

mod fixtures;
use fixtures::*;

#[test]
fn ordinary_full_emission_installs_completion_without_forged_validation() {
    let (mut exec, _) = fixture();
    assert!(!exec.last_model_validated);
    assert!(exec.last_sat_certificate.is_none());
    let (verdict, completion) = capture(&exec, None);
    assert!(matches!(verdict, GateVerdict::ConfirmedSat));
    assert!(
        completion.is_some(),
        "the input model is genuinely incomplete"
    );
    drop(completion);
    assert!(!exec.last_model.as_ref().unwrap().has_residual_arrays());
    // Propose the authored candidate through the entire ordinary publication
    // pipeline. No checked-search or old model-validation authority is planted.
    assert_eq!(
        exec.emit_sat_verdict(SolveResult::Sat, &[]).unwrap(),
        SolveResult::Sat
    );
    assert!(exec.last_model_validated);
    assert!(exec.last_sat_certificate.is_some());
    assert!(exec.last_model.as_ref().unwrap().has_residual_arrays());
    assert!(matches!(full_replay(&exec), GateVerdict::ConfirmedSat));
}

#[test]
fn native_funnel_retains_a_real_completion_but_immutable_checks_do_not() {
    let (mut exec, array) = fixture();
    assert!(!exec.last_model_validated);
    assert!(matches!(
        exec.confirm_sat_with_independent_gate(),
        GateVerdict::ConfirmedSat
    ));
    assert!(!exec.last_model.as_ref().unwrap().has_residual_arrays());
    let (verdict, data) = capture(&exec, None);
    assert!(matches!(verdict, GateVerdict::ConfirmedSat));
    let data = data.expect("the actual independent view must need residual data");
    assert_eq!(data.roots, independent_gate_query_roots(&exec).unwrap());
    assert_eq!(data.assignments.len(), 1);
    assert_eq!(data.assignments[0].term(), array);
    drop(data);
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Sat
    );
    assert!(exec.last_model.as_ref().unwrap().has_residual_arrays());
    assert!(exec.last_model_validated);
    assert!(matches!(full_replay(&exec), GateVerdict::ConfirmedSat));
    let (verdict, data) = capture(&exec, None);
    assert!(matches!(verdict, GateVerdict::ConfirmedSat));
    assert!(
        data.is_none(),
        "a retained complete model needs no second extension"
    );
}

#[test]
fn full_replay_revokes_narrowed_quantified_authority_for_both_truth_values() {
    for predicate in ["(bvule i #b1)", "(= i #b0)"] {
        let (mut exec, _) = fixture();
        append(
            &mut exec,
            &format!("(assert (forall ((i (_ BitVec 1))) {predicate}))"),
        );
        forge_initial_confirmation(&mut exec);
        let (verdict, completion) = capture(&exec, exec.quantified_model_confirmation.as_ref());
        assert!(matches!(verdict, GateVerdict::ConfirmedSat));
        assert!(
            completion.is_some(),
            "the initial narrowed query needs a completion"
        );
        drop(completion);
        exec.dt_cert_grant_active = true;
        exec.finite_table_cert_grant_active = true;
        exec.const_interp_cert_grant_active = true;
        exec.mbqi_sat_cert_grant_active = true;
        exec.bv_quantifier_full_domain_proof = true;
        let result = exec.apply_independent_model_gate(SolveResult::Sat);
        assert_eq!(
            result,
            if predicate.starts_with("(bvule") {
                SolveResult::Sat
            } else {
                SolveResult::Unknown
            }
        );
        assert!(exec.quantified_model_confirmation.is_none());
        assert!(!exec.dt_cert_grant_active);
        assert!(!exec.finite_table_cert_grant_active);
        assert!(!exec.const_interp_cert_grant_active);
        assert!(!exec.mbqi_sat_cert_grant_active);
        assert!(!exec.bv_quantifier_full_domain_proof);
        if result == SolveResult::Unknown {
            assert!(exec.last_model.is_none());
        } else {
            assert!(matches!(full_replay(&exec), GateVerdict::ConfirmedSat));
        }
    }
}

#[test]
fn authored_order_and_quantified_assumptions_survive_a_mutated_context_window() {
    let (mut exec, _) = fixture();
    let authored = exec.ctx.assertions.clone();
    append(&mut exec, "(assert (forall ((i (_ BitVec 1))) (= i #b0)))");
    let assumption = *exec.ctx.assertions.last().unwrap();
    exec.independent_gate_authored_assertions = Some(authored.clone());
    exec.last_assumptions = Some(vec![assumption, assumption]);
    let yes = exec.ctx.terms.mk_bool(true);
    exec.ctx.assertions = vec![yes];
    forge_initial_confirmation(&mut exec);
    let (verdict, data) = capture(&exec, exec.quantified_model_confirmation.as_ref());
    assert!(matches!(verdict, GateVerdict::ConfirmedSat));
    let data = data.unwrap();
    assert_eq!(data.roots, [authored, vec![assumption]].concat());
    assert!(!data.roots.contains(&yes));
    assert!(matches!(
        install_and_replay(&mut exec, verdict, Some(data)),
        GateVerdict::ModelViolates { assertion } if assertion == assumption
    ));
    assert!(exec.quantified_model_confirmation.is_none());
}

#[test]
fn model_mutation_replaces_the_outer_shared_cache_instead_of_restoring_stale_data() {
    let (mut exec, array) = fixture();
    let _outer = GateViewCacheSession::new();
    let old = ACTIVE_VIEW_CACHES.with(|slot| slot.borrow().as_ref().unwrap().leaf_memo.clone());
    old.seed(array, ModelValue::Bool(false));
    let (verdict, data) = capture(&exec, None);
    assert!(matches!(verdict, GateVerdict::ConfirmedSat));
    assert!(
        data.is_some(),
        "initial evaluation must ignore the outer stale cache"
    );
    assert!(matches!(
        install_and_replay(&mut exec, verdict, data),
        GateVerdict::ConfirmedSat
    ));
    let current = ACTIVE_VIEW_CACHES.with(|slot| slot.borrow().as_ref().unwrap().leaf_memo.clone());
    assert!(!Rc::ptr_eq(&old, &current));
    assert!(
        current.is_empty(),
        "the replay restores only a fresh post-install cache"
    );
    assert!(matches!(full_replay(&exec), GateVerdict::ConfirmedSat));
}

#[test]
fn cancellation_before_capture_and_between_capture_and_install_never_keeps_sat() {
    let (mut exec, _) = fixture();
    let flag = Arc::new(AtomicBool::new(true));
    exec.set_interrupt(Arc::clone(&flag));
    let (verdict, data) = capture(&exec, None);
    assert!(matches!(verdict, GateVerdict::CannotConfirm { .. }));
    assert!(data.is_none());
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Unknown
    );
    assert!(exec.last_model.is_none());

    let (mut exec, _) = fixture();
    flag.store(false, Ordering::Relaxed);
    exec.set_interrupt(Arc::clone(&flag));
    let (verdict, data) = capture(&exec, None);
    assert!(matches!(verdict, GateVerdict::ConfirmedSat));
    assert!(data.is_some());
    flag.store(true, Ordering::Relaxed);
    assert!(matches!(
        install_and_replay(&mut exec, verdict, data),
        GateVerdict::CannotConfirm { .. }
    ));
    assert!(!exec.last_model.as_ref().unwrap().has_residual_arrays());
    assert_eq!(exec.last_result, Some(SolveResult::Unknown));
}

#[test]
fn original_deadline_and_term_memory_stop_each_side_of_extraction() {
    for stop in [Stop::Deadline, Stop::TermMemory] {
        let (mut exec, _) = fixture();
        stop.install(&mut exec);
        let (verdict, data) = capture(&exec, None);
        assert!(matches!(verdict, GateVerdict::CannotConfirm { .. }));
        assert!(data.is_none());

        let (mut exec, _) = fixture();
        let (verdict, data) = capture(&exec, None);
        assert!(matches!(verdict, GateVerdict::ConfirmedSat));
        assert!(data.is_some());
        stop.install(&mut exec);
        assert!(matches!(
            install_and_replay(&mut exec, verdict, data),
            GateVerdict::CannotConfirm { .. }
        ));
        assert!(!exec.last_model.as_ref().unwrap().has_residual_arrays());
    }
    let (mut fresh, _) = fixture();
    assert_eq!(
        fresh.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Sat
    );
}

#[test]
fn data_never_upgrades_an_initial_refutation_or_an_unsupported_full_root() {
    let (mut exec, _) = fixture();
    let (_, data) = capture(&exec, None);
    assert!(data.is_some());
    let assertion = exec.ctx.assertions[0];
    assert!(matches!(
        install_and_replay(&mut exec, GateVerdict::ModelViolates { assertion }, data),
        GateVerdict::CannotConfirm { .. }
    ));
    assert!(!exec.last_model.as_ref().unwrap().has_residual_arrays());

    let (mut exec, _) = fixture();
    append(&mut exec, "(assert (forall ((i Int)) (> i 0)))");
    forge_initial_confirmation(&mut exec);
    // A predecessor's validation flag cannot survive the model mutation when
    // the mandatory new full-root replay cannot establish its replacement.
    exec.last_model_validated = true;
    let (verdict, data) = capture(&exec, exec.quantified_model_confirmation.as_ref());
    assert!(matches!(verdict, GateVerdict::ConfirmedSat));
    assert!(data.is_some());
    assert!(matches!(
        install_and_replay(&mut exec, verdict, data),
        GateVerdict::CannotConfirm { .. }
    ));
    assert!(!exec.last_model_validated);
}

#[test]
fn literal_only_roots_cannot_publish_a_stale_retained_package() {
    let (mut exec, _) = fixture();
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Sat
    );
    assert!(exec.last_model.as_ref().unwrap().has_residual_arrays());
    append(&mut exec, "(push 1)");
    let yes = exec.ctx.terms.mk_bool(true);
    exec.ctx.assertions = vec![yes];
    assert!(!exec
        .last_model
        .as_ref()
        .unwrap()
        .residual_arrays_are_current(&exec.ctx));
    let (verdict, completion) = capture(&exec, None);
    assert!(matches!(verdict, GateVerdict::CannotConfirm { .. }));
    assert!(completion.is_none());
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Unknown
    );
    assert!(exec.last_model.is_none());
}

#[derive(Clone, Copy)]
enum Stop {
    Deadline,
    TermMemory,
}

impl Stop {
    fn install(self, exec: &mut Executor) {
        match self {
            Self::Deadline => exec.set_deadline(Some(Instant::now() - Duration::from_secs(1))),
            Self::TermMemory => exec.set_term_memory_limit(Some(0)),
        }
    }
}
