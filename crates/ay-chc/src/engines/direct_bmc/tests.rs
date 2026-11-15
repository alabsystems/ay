// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::VerifiedUnknownReason;

const MEMORY: usize = 64 * 1024 * 1024;
const SOURCE: &str = "(set-logic HORN)
(declare-fun P ((_ BitVec 8)) Bool)
(assert (P #x07))
(assert (forall ((x (_ BitVec 8))) (=> (and (P x) (= x #x07)) false)))
(check-sat)";

fn source() -> ChcProblem {
    ChcParser::parse(SOURCE).unwrap()
}

fn config() -> BmcConfig {
    BmcConfig::default()
        .with_max_depth(2)
        .with_acyclic_safe(true)
        .with_time_budget(Duration::from_secs(10))
        .with_per_depth_timeout(Duration::from_secs(10))
        .with_memory_budget(MEMORY)
}

fn constructor_source() -> ChcProblem {
    ChcParser::parse(
        "(set-logic HORN)
      (declare-fun P ((Array Int Int)) Bool)
      (declare-fun Q ((Array Int Int)) Bool)
      (declare-fun D (Int) Bool)
      (declare-fun E (Int) Bool)
      (assert (P ((as const (Array Int Int)) 7)))
      (assert (forall ((a (Array Int Int))) (=> (P a) (Q a))))
      (assert (forall ((a (Array Int Int))) (=> (and (Q a) (= (select a 0) 7)) false)))
      (assert (forall ((x Int)) (=> (D x) (E x))))
      (assert (forall ((x Int)) (=> (E x) (D x))))
      (check-sat)",
    )
    .unwrap()
}

#[test]
fn optional_and_ambient_deadlines_preserve_zero_and_never_extend_an_owner() {
    let mut unbounded = BmcConfig::default();
    assert_eq!(unbounded.time_budget, None);
    let unlimited = Attempt::capture(&mut unbounded);
    assert_eq!(unlimited.deadline, None);
    let mut zero = config().with_time_budget(Duration::ZERO);
    let exhausted = Attempt::capture(&mut zero);
    assert_eq!(exhausted.deadline, Some(exhausted.started_at));
    assert!(!exhausted.open());
    assert_eq!(exhausted.stopped.get(), Some(Stop::Deadline));
    let overflow = Attempt::capture(&mut config().with_time_budget(Duration::MAX));
    assert_eq!(overflow.stopped.get(), Some(Stop::DeadlineOverflow));
    assert!(!overflow.open());

    let early = Instant::now() + Duration::from_secs(2);
    let _solve = crate::smt::ScopedSolveDeadline::new(Some(early));
    let _smt = crate::smt::ScopedSmtDeadline::install_until(early + Duration::from_secs(1));
    let inherited = Attempt::capture(&mut config());
    assert_eq!(inherited.deadline, Some(early));
    let tighter = Instant::now() + Duration::from_secs(1);
    let _inner = crate::smt::ScopedSmtDeadline::install_until(tighter);
    assert_eq!(Attempt::capture(&mut config()).deadline, Some(tighter));
    assert_eq!(inherited.deadline, Some(early), "capture is immutable");
}

#[test]
fn closed_constructor_entries_refuse_before_source_clone_and_transform() {
    for (mut configured, reason) in [
        (
            config().with_time_budget(Duration::ZERO),
            VerifiedUnknownReason::BmcBudgetExhausted,
        ),
        (
            config().with_memory_budget(0),
            VerifiedUnknownReason::Inconclusive,
        ),
        (
            {
                let token = CancellationToken::new();
                token.cancel();
                config().with_cancellation(token)
            },
            VerifiedUnknownReason::Inconclusive,
        ),
    ] {
        let attempt = Attempt::capture(&mut configured);
        let mut phases = Vec::new();
        let result = attempt.solve_observed(
            || panic!("a refused attempt must not clone its source"),
            configured,
            &mut |phase| phases.push(phase),
        );
        assert_eq!(result.unknown_reason(), Some(reason));
        assert_eq!(phases, [Phase::Cleanup]);
        assert!(!attempt.open());
    }
}

#[test]
fn each_constructor_boundary_keeps_observed_cancellation_after_parent_reset() {
    let stages = [
        ConstructionStage::Start,
        ConstructionStage::DeadEndsPruned,
        ConstructionStage::ArraysScalarized,
        ConstructionStage::Profiled,
        ConstructionStage::Finished,
    ];
    for stop_at in stages {
        let parent = CancellationToken::new();
        let mut configured = config().with_cancellation(parent.clone());
        let attempt = Attempt::capture(&mut configured);
        let original = constructor_source();
        let spelling = format!("{original:?}");
        let mut phases = Vec::new();
        let result = attempt.solve_observed(|| original.clone(), configured, &mut |phase| {
            phases.push(phase);
            if phase == Phase::Construction(stop_at) {
                parent.cancel();
            }
            if phase == Phase::Cleanup {
                parent.reset();
            }
        });
        assert_eq!(
            result.unknown_reason(),
            Some(VerifiedUnknownReason::Inconclusive)
        );
        assert!(phases.contains(&Phase::Construction(stop_at)));
        assert!(!phases.contains(&Phase::Engine));
        let reached = stages.iter().position(|stage| *stage == stop_at).unwrap();
        for later in &stages[reached + 1..] {
            if *later != ConstructionStage::Finished {
                assert!(!phases.contains(&Phase::Construction(*later)));
            }
        }
        assert!(!parent.is_cancelled());
        assert!(attempt.cancellation.is_cancelled());
        assert!(!attempt.open());
        assert_eq!(format!("{original:?}"), spelling);
        assert!(Attempt::capture(&mut config().with_cancellation(parent)).open());
    }
}

#[test]
fn deadline_observed_after_pruning_refuses_later_work_and_retains_depth_zero() {
    let mut configured = config();
    let attempt = Attempt::capture(&mut configured);
    let deadline = attempt.deadline.unwrap();
    let mut phases = Vec::new();
    let result = attempt.solve_observed(constructor_source, configured, &mut |phase| {
        phases.push(phase);
        if phase == Phase::Construction(ConstructionStage::DeadEndsPruned) {
            // Deterministic clock seam: exercise the real comparison/latch at
            // its exact deadline, not a sleep or a claimed wall-time overrun.
            assert!(!attempt.open_at(deadline));
        }
    });
    assert!(!phases.contains(&Phase::Construction(ConstructionStage::ArraysScalarized)));
    assert!(!phases.contains(&Phase::Engine));
    assert_eq!(
        result.unknown_reason(),
        Some(VerifiedUnknownReason::BmcBudgetExhausted)
    );
    let marker = result.unknown_marker().unwrap();
    assert_eq!(marker.bmc_max_depth(), Some(2));
    assert_eq!(marker.bmc_depth_reached(), Some(0));
    assert!(
        !attempt.open_at(attempt.started_at),
        "earlier clock cannot revive the attempt"
    );
}

#[test]
fn real_constructor_preserves_the_absolute_handoff_and_pruning_scope() {
    for mut configured in [config(), BmcConfig::default()] {
        let attempt = Attempt::capture(&mut configured);
        let original = constructor_source();
        let before = original.clauses().len();
        let mut phases = Vec::new();
        let adaptive = AdaptivePortfolio::new_for_bmc_until(
            original.clone(),
            attempt.started_at,
            attempt.deadline,
            &attempt.cancellation,
            &mut |stage| {
                phases.push(stage);
                attempt.open()
            },
        );
        assert_eq!(
            adaptive.problem.clauses().len(),
            before - 2,
            "real dead cycle was pruned"
        );
        assert_eq!(original.clauses().len(), before);
        assert_eq!(adaptive.enclosing_subsolve_deadline(), attempt.deadline);
        assert_eq!(
            adaptive.solve_deadline(),
            attempt.deadline,
            "no fresh adaptive budget"
        );
        assert!(!adaptive.budget_exhausted(attempt.deadline));
        assert_eq!(
            phases,
            [
                ConstructionStage::Start,
                ConstructionStage::DeadEndsPruned,
                ConstructionStage::ArraysScalarized,
                ConstructionStage::Profiled,
                ConstructionStage::Finished
            ]
        );
    }
}

#[test]
fn public_checked_bmc_rearms_only_for_a_fresh_attempt_and_replays_originals() {
    let parent = CancellationToken::new();
    parent.cancel();
    let stopped = solve_bmc_proof_with_checked_replay(
        source(),
        config().with_cancellation(parent.clone()),
        Duration::from_secs(10),
    )
    .unwrap();
    assert!(stopped.result().is_unknown());
    assert!(!stopped.accepted_as_proof());
    assert!(!stopped.metadata().trust_full_verifier_admissible());
    parent.reset();
    let zero = solve_bmc_proof(source(), config().with_time_budget(Duration::ZERO)).unwrap();
    assert_eq!(
        zero.result().unknown_reason(),
        Some(VerifiedUnknownReason::BmcBudgetExhausted)
    );
    assert!(!zero.accepted_as_proof());
    let original = source();
    let run = solve_bmc_proof_with_checked_replay(
        original.clone(),
        config().with_cancellation(parent.clone()),
        Duration::from_secs(10),
    )
    .unwrap();
    let VerifiedChcResult::Unsafe(verified) = run.result() else {
        panic!(
            "fresh genuine BV8 refutation must survive replay: {:?}",
            run.result()
        );
    };
    let derivation = verified
        .counterexample()
        .ground_derivation
        .as_ref()
        .unwrap();
    crate::ground_derivation::validate_ground_derivation(&original, derivation).unwrap();
    crate::ground_derivation::validate_ground_derivation(run.problem(), derivation).unwrap();
    assert!(run.metadata().trust_full_verifier_admissible());
    let changed = ChcParser::parse(&SOURCE.replace("(= x #x07)", "(= x #x08)")).unwrap();
    assert!(crate::ground_derivation::validate_ground_derivation(&changed, derivation).is_err());
    assert!(!parent.is_cancelled());
}
