// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::resource_observation::{ResourceRefusal, ScopedResourceObservation};
use crate::{CancellationToken, PdrConfig};

fn future() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

#[test]
fn additive_entry_refuses_expired_cancelled_and_zero_before_lowering() {
    let problem = high_bit_identity_problem(16, 15, 1 << 15, 1);
    let owner = ResourceGuard::new();
    let config = PdrConfig::production(false);
    assert!(try_prove_chc_loop_with_resources(&problem, Instant::now(), &config, &owner).is_none());
    assert!(try_prove_chc_loop_with_resources(
        &problem,
        future(),
        &config.clone().with_memory_budget(Some(0)),
        &owner,
    )
    .is_none());
    let cancellation = CancellationToken::new();
    cancellation.cancel();
    assert!(try_prove_chc_loop_with_resources(
        &problem,
        future(),
        &config.with_cancellation_token(Some(cancellation)),
        &owner,
    )
    .is_none());
}

#[test]
fn additive_entry_inherits_earlier_wall_cap_and_spent_original_guard() {
    let problem = high_bit_identity_problem(16, 15, 1 << 15, 1);
    let owner = ResourceGuard::new();
    let config = PdrConfig::production(false);
    {
        let _wall = crate::smt::ScopedSmtDeadline::install_until(Instant::now());
        assert!(try_prove_chc_loop_with_resources(&problem, future(), &config, &owner).is_none());
    }
    {
        let _cap = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert!(try_prove_chc_loop_with_resources(&problem, future(), &config, &owner).is_none());
    }
    let mut spent = ResourceGuard::new();
    spent.set_rlimit(Some(1));
    assert!(try_prove_chc_loop_with_resources(&problem, future(), &config, &spent).is_none());
    assert_eq!(spent.ticks(), 1);
    assert!(try_prove_chc_loop_with_resources(&problem, future(), &config, &spent).is_none());
}

#[test]
fn full_original_validator_memory_refusal_is_terminal_after_context_cleanup() {
    let problem = high_bit_identity_problem(1, 0, 0, 0);
    let model = InvariantModel::parse_smtlib(
        "(define-fun wide ((value (_ BitVec 1))) Bool (= value (_ bv0 1)))",
        &problem,
    )
    .unwrap();
    let config = PdrConfig::production(false).with_memory_budget(Some(1));
    let owner = ResourceGuard::new();
    let replay = ScopedReplayControl::install_until(future(), None);
    let resources = Arc::new(Resources::capture(&owner, &config, &replay));
    let mut live = || resources.poll();
    let parent = Control::new(replay.deadline(), &mut live);
    let observation = ScopedResourceObservation::install();
    assert_eq!(
        candidate_validates_original(&problem, &model, replay.deadline(), &parent, &resources,),
        None
    );
    assert_eq!(observation.first(), Some(ResourceRefusal::Memory));
    drop(observation);
    assert!(!resources.poll());
    assert_eq!(parent.poll(), None);
    let healthy = PdrConfig::production(false).with_memory_budget(Some(64 * 1024 * 1024));
    let fresh = Arc::new(Resources::capture(&owner, &healthy, &replay));
    let mut live = || fresh.poll();
    let parent = Control::new(replay.deadline(), &mut live);
    assert_eq!(
        candidate_validates_original(&problem, &model, replay.deadline(), &parent, &fresh,),
        Some(true)
    );
}

#[test]
fn local_original_validation_timeout_does_not_poison_reserved_parent() {
    let problem = high_bit_identity_problem(1, 0, 0, 0);
    let model = InvariantModel::new();
    let replay = ScopedReplayControl::install_until(future(), None);
    let resources = Arc::new(Resources::capture(
        &ResourceGuard::new(),
        &PdrConfig::production(false),
        &replay,
    ));
    let mut live = || resources.poll();
    let parent = Control::new(replay.deadline(), &mut live);
    assert_eq!(
        candidate_validates_original(&problem, &model, Instant::now(), &parent, &resources,),
        None
    );
    assert_eq!(parent.poll(), Some(()));
    assert!(resources.poll());
}

#[test]
fn resource_entry_still_requires_full_original_word_validation() {
    let problem = bv9_widening_validation_problem();
    let config = PdrConfig::production(false).with_memory_budget(Some(64 * 1024 * 1024));
    let owner = ResourceGuard::new();
    let model = try_prove_chc_loop_with_resources(&problem, future(), &config, &owner)
        .expect("resource-owned ladder must reach original BV9 validation");
    assert!(crate::engines::validate_external_invariant_model(&problem, &model, &config).unwrap());
    assert!(owner.ticks() > 0);
}

#[test]
fn refuted_original_candidate_is_not_evidence_and_keeps_live_parent_for_next_rung() {
    let problem = high_bit_identity_problem(1, 0, 0, 0);
    let model = InvariantModel::parse_smtlib(
        "(define-fun wide ((value (_ BitVec 1))) Bool true)",
        &problem,
    )
    .unwrap();
    let replay = ScopedReplayControl::install_until(future(), None);
    let resources = Arc::new(Resources::capture(
        &ResourceGuard::new(),
        &PdrConfig::production(false).with_memory_budget(Some(64 * 1024 * 1024)),
        &replay,
    ));
    let mut live = || resources.poll();
    let parent = Control::new(replay.deadline(), &mut live);
    assert_eq!(
        candidate_validates_original(&problem, &model, replay.deadline(), &parent, &resources,),
        Some(false)
    );
    assert_eq!(parent.poll(), Some(()));
}
