// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

fn controls() -> (CancellationToken, ScopedReplayControl, BmcConfig) {
    let caller = CancellationToken::new();
    let control = ScopedReplayControl::install_until(
        ay_core::time::Instant::now() + std::time::Duration::from_secs(60),
        Some(&caller),
    );
    let config = BmcConfig {
        base: ChcEngineConfig {
            cancellation_token: control.cancellation().cloned(),
            ..ChcEngineConfig::default()
        },
        time_budget: Some(std::time::Duration::from_secs(60)),
        prefer_exact_acyclic_first: true,
        ..BmcConfig::default()
    };
    (caller, control, config)
}

#[test]
fn exhaustive_retry_keeps_same_wall_and_only_its_remaining_allowance() {
    let (caller, control, config) = controls();
    let calls = Cell::new(0);
    assert!(run_bmc_attempts(config, &control, |config| {
        assert_eq!(
            crate::smt::deadline::effective_thread_deadline(),
            Some(control.deadline())
        );
        assert!(!config
            .base
            .cancellation_token
            .as_ref()
            .unwrap()
            .is_cancelled());
        calls.set(calls.get() + 1);
        if calls.get() == 1 {
            assert!(config.prefer_exact_acyclic_first);
            PortfolioResult::Unknown
        } else {
            assert!(!config.prefer_exact_acyclic_first);
            assert!(config.time_budget.unwrap() <= std::time::Duration::from_secs(60));
            PortfolioResult::Safe(InvariantModel::new())
        }
    }));
    assert_eq!(calls.get(), 2);
    assert!(!caller.is_cancelled());
}

#[test]
fn active_first_attempt_cancellation_latches_even_when_caller_resets() {
    let (caller, control, config) = controls();
    let calls = Cell::new(0);
    assert!(!run_bmc_attempts(config, &control, |config| {
        calls.set(calls.get() + 1);
        let active = config.base.cancellation_token.as_ref().unwrap().child();
        caller.cancel();
        assert!(active.is_cancelled());
        caller.reset();
        active.reset();
        assert!(active.is_cancelled());
        PortfolioResult::Unknown
    }));
    assert_eq!(calls.get(), 1);
    assert!(!caller.is_cancelled());
    assert!(!control.open());
}

#[test]
fn expired_wall_cannot_start_an_attempt_or_consume_a_memo() {
    let problem = acyclic_problem(false);
    let deadline = ay_core::time::Instant::now()
        .checked_sub(std::time::Duration::from_secs(1))
        .expect("fixture instant supports a one-second offset");
    let _outer = crate::smt::ScopedSmtDeadline::install_until(deadline);
    let control = ScopedReplayControl::install_until(deadline, None);
    assert!(!run_bmc_attempts(BmcConfig::default(), &control, |_| {
        panic!("expired certificate attempt")
    }));
    assert_eq!(
        run_scalar_acyclic_bmc_certificate(&problem, &PdrConfig::default()),
        Some((false, scalar_acyclic_certificate_class(&problem).unwrap().1)),
    );
    assert!(
        crate::engines::chc_safe_replay_obligations(&problem, &InvariantModel::new(),).is_err()
    );
}

fn acyclic_problem(reachable: bool) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("r1_p", vec![ChcSort::Int]);
    let q = problem.declare_predicate("r1_q", vec![ChcSort::Int]);
    let x = ChcVar::new("r1_x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::var(x.clone())])],
        Some(if reachable {
            ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0))
        } else {
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))
        }),
    )));
    problem
}

#[test]
fn healthy_original_empty_certificate_and_reachable_countercontrol_stay_checked() {
    let safe = acyclic_problem(false);
    let unsafe_problem = acyclic_problem(true);
    let budget = std::time::Duration::from_secs(20);
    let caller = CancellationToken::new();
    let _control =
        ScopedReplayControl::install_until(ay_core::time::Instant::now() + budget, Some(&caller));
    assert_eq!(
        crate::engines::chc_safe_replay_obligations(&safe, &InvariantModel::new(),).unwrap(),
        [] as [pdr::model::ChcReplayObligation; 0]
    );
    let error =
        crate::engines::chc_safe_replay_obligations(&unsafe_problem, &InvariantModel::new())
            .unwrap_err();
    assert!(error
        .to_string()
        .contains("missing invariant interpretation"));
    assert!(!caller.is_cancelled());
}

#[test]
fn definite_unsafe_never_tries_exhaustive_and_cancelled_retry_cannot_publish() {
    let (caller, control, config) = controls();
    let calls = Cell::new(0);
    assert!(!run_bmc_attempts(config.clone(), &control, |_| {
        calls.set(calls.get() + 1);
        PortfolioResult::Unsafe(Counterexample::new(Vec::new()))
    }));
    assert_eq!(calls.get(), 1);
    calls.set(0);
    assert!(!run_bmc_attempts(config, &control, |config| {
        calls.set(calls.get() + 1);
        if calls.get() == 1 {
            return PortfolioResult::Unknown;
        }
        caller.cancel();
        assert!(config
            .base
            .cancellation_token
            .as_ref()
            .unwrap()
            .is_cancelled());
        caller.reset();
        PortfolioResult::Safe(InvariantModel::new())
    }));
    assert_eq!(calls.get(), 2);
    assert!(!caller.is_cancelled());
}

#[test]
fn healthy_empty_model_safe_completes_original_strict_checked_replay() {
    let safe = acyclic_problem(false);
    let caller = CancellationToken::new();
    let budget = std::time::Duration::from_secs(20);
    assert_eq!(
        crate::engines::chc_safe_replay_obligations(&safe, &InvariantModel::new(),).unwrap(),
        [] as [pdr::model::ChcReplayObligation; 0]
    );
    let run = ChcPdrProofRun::new(
        safe,
        VerifiedChcResult::Safe(VerifiedInvariant::from_validated(InvariantModel::new())),
        "r1-original-empty-certificate",
    );
    let checked = run
        .run_checked_replay_with_cancellation(budget, &caller.child())
        .unwrap();
    assert!(checked.manifest().trust_full_verifier_admissible());
    assert!(checked
        .proof_run()
        .metadata()
        .trust_full_verifier_admissible());
    assert_ne!(
        checked.summary().obligations,
        [] as [proof_metadata::ChcCheckedReplayObligation; 0]
    );
    assert!(!caller.is_cancelled());
}

#[test]
fn independent_empty_check_respects_expired_wall_even_for_cached_or_false_formula() {
    let safe = acyclic_problem(false);
    assert!(crate::empty_acyclic_safe_check::check(
        &safe,
        std::time::Duration::from_secs(20),
        None,
    )
    .is_ok());
    let _wall = crate::smt::ScopedSmtDeadline::install_until(ay_core::time::Instant::now());
    assert_eq!(
        crate::empty_acyclic_safe_check::check(&safe, std::time::Duration::from_secs(20), None,),
        Err(crate::empty_acyclic_safe_check::NotConfirmed::Budget),
    );
}
