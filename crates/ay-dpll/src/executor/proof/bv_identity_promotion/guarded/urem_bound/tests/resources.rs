// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exhausted_original_work_cannot_build_or_recover() {
    let (executor, roots) = fixture(&range_source(4));
    executor.proof_source_work.set_remaining_for_test(0);
    let mut control = Control::capture(&executor, &|| false).unwrap();
    assert!(collect::occurrences(&executor, &roots, &mut control).is_none());
    executor.proof_source_work.set_remaining_for_test(1_000_000);
    assert!(control.admit(&executor.proof_source_work, 0, 0).is_none());
}

#[test]
fn transient_callback_refusal_stays_terminal_after_scope_removed() {
    let (executor, roots) = fixture(&range_source(4));
    let refusal = Arc::new(AtomicBool::new(true));
    let observed = Arc::clone(&refusal);
    let scope =
        ay_core::resource::enter_check_stop(Arc::new(move || observed.load(Ordering::SeqCst)));
    let mut control = Control::capture(&executor, &|| false).unwrap();
    drop(scope);
    assert!(collect::occurrences(&executor, &roots, &mut control).is_none());
    refusal.store(false, Ordering::SeqCst);
    assert!(control.admit(&executor.proof_source_work, 0, 0).is_none());
}

#[test]
fn original_guard_is_debited_after_ambient_scope_is_removed() {
    use ay_core::resource::{ChildSpec, Guard, NodeLabel};
    let (executor, _) = fixture(&range_source(4));
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(4)));
    let scope = guard.enter();
    let mut control = Control::capture(&executor, &|| false).unwrap();
    drop(scope);
    let replacement = Guard::new();
    let _replacement_scope = replacement.enter();
    // GuardTree stops when the charged count REACHES its allotment. Keep
    // that existing boundary; CountedAdmission's exact-fit rule is different.
    assert!(control.admit(&executor.proof_source_work, 3, 0).is_some());
    assert_eq!(guard.ticks(), 3);
    assert_eq!(replacement.ticks(), 3);
    assert!(control.admit(&executor.proof_source_work, 1, 0).is_none());
    assert_eq!(guard.ticks(), 4);
    assert_eq!(replacement.ticks(), 3);
    assert!(control.admit(&executor.proof_source_work, 0, 0).is_none());
    assert_eq!(guard.ticks(), 4);
}

#[test]
fn stopped_candidate_does_not_replace_or_retry_the_incumbent() {
    let (mut executor, roots) = fixture(&range_source(4));
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    let original = proof.steps.clone();
    let result = executor.promote_urem_bound_joint(
        &mut proof,
        &roots,
        GuardedCollapseStage::Final,
        &mut IncumbentFacts::new(false),
        &|| true,
    );
    assert_eq!(result, None);
    assert_eq!(proof.steps, original);
}

#[test]
fn incomplete_original_root_census_does_not_create_a_bound_candidate() {
    let (mut executor, roots) = fixture(&range_source(4));
    let mut proof = Proof::new();
    let result = executor.promote_urem_bound_joint(
        &mut proof,
        &roots[..1],
        GuardedCollapseStage::Final,
        &mut IncumbentFacts::new(false),
        &|| false,
    );
    assert_eq!(result, Some(false));
    assert_eq!(proof.steps, [] as [ProofStep; 0]);
}

#[test]
fn nested_one_shot_callback_latches_the_enclosing_attempt_after_helper_drop() {
    let (executor, _) = fixture(&range_source(4));
    let refusal = Arc::new(AtomicBool::new(false));
    let flag = Arc::clone(&refusal);
    let caller =
        ay_core::resource::enter_check_stop(Arc::new(move || flag.swap(false, Ordering::SeqCst)));
    let mut control = Control::capture(&executor, &|| false).unwrap();
    let scope = control.enter();
    assert!(control.admit(&executor.proof_source_work, 1, 0).is_some());
    refusal.store(true, Ordering::SeqCst);
    // Simulate an opaque presentation/strict checker observing the one shot.
    assert!(ay_core::resource::check_stop_requested());
    assert!(!refusal.load(Ordering::SeqCst));
    assert!(control.stopped());
    drop(scope);
    drop(control);
    drop(caller);
    assert!(executor.evaluation_attempt().stop_origin().is_some());
    assert!(Control::capture(&executor, &|| false).unwrap().stopped());
}

#[test]
fn callback_unwind_cannot_revive_the_same_publication_attempt() {
    let (executor, _) = fixture(&range_source(4));
    let caller = ay_core::resource::enter_check_stop(Arc::new(|| panic!("test callback")));
    let control = Control::capture(&executor, &|| false).unwrap();
    let scope = control.enter();
    assert!(std::panic::catch_unwind(ay_core::resource::check_stop_requested).is_err());
    drop(scope);
    drop(control);
    drop(caller);
    assert!(executor.evaluation_attempt().stop_origin().is_some());
    assert!(Control::capture(&executor, &|| false).unwrap().stopped());
}

#[test]
fn candidate_refusal_is_recorded_at_existing_publication_boundary() {
    let (mut executor, roots) = fixture(&range_source(4));
    executor.proof_source_work.set_remaining_for_test(0);
    let mut proof = Proof::new();
    assert_eq!(
        executor.promote_urem_bound_joint(
            &mut proof,
            &roots,
            GuardedCollapseStage::Final,
            &mut IncumbentFacts::new(false),
            &|| false
        ),
        None
    );
    assert!(executor.certification_stop().is_some());
    executor.proof_source_work.set_remaining_for_test(1_000_000);
    assert_eq!(
        executor.promote_urem_bound_joint(
            &mut proof,
            &roots,
            GuardedCollapseStage::Final,
            &mut IncumbentFacts::new(false),
            &|| false
        ),
        None
    );
    assert_eq!(proof.steps, [] as [ProofStep; 0]);
}

#[test]
fn wire_advice_never_recovers_a_spent_original_envelope() {
    let (mut executor, roots) = fixture(&range_source(4));
    let proof = candidate(&mut executor, &roots);
    let clause = proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::BvUremBound,
                clause,
                ..
            } => Some(clause),
            _ => None,
        })
        .unwrap();
    executor.proof_source_work.set_remaining_for_test(0);
    assert!(!executor.urem_bound_wire_supported(clause, None));
    assert!(executor.certification_stop().is_some());
    executor.proof_source_work.set_remaining_for_test(1_000_000);
    assert!(!executor.urem_bound_wire_supported(clause, None));
}
