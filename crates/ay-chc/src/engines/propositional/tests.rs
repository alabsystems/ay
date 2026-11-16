// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ground_derivation::validate_ground_derivation;
use crate::{ClauseBody, ClauseHead, HornClause};

fn problem(query_live: bool) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("p", vec![]);
    let q = problem.declare_predicate("q", vec![]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(p, vec![]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![])]),
        ClauseHead::Predicate(q, vec![]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![])],
        Some(ChcExpr::Bool(query_live)),
    )));
    problem
}

fn config() -> PdrConfig {
    PdrConfig {
        strict_proofs: true,
        preserve_original_clauses: true,
        ..PdrConfig::default()
    }
}

fn phases() -> [Phase; 5] {
    [
        Phase::Search,
        Phase::Validation,
        Phase::Validated,
        Phase::Publication,
        Phase::Cleanup,
    ]
}

#[test]
fn live_prepass_keeps_original_derivation_and_body_forall_gate() {
    let source = problem(true);
    let before = format!("{source:?}");
    let mut observed = Vec::new();
    let result = run_observed(&source, &config(), None, &mut |phase| observed.push(phase))
        .expect("refutable source has a prepass result");
    assert_eq!(observed, phases());
    let cex = result
        .unsafe_counterexample()
        .expect("real original-source validation")
        .counterexample();
    let derivation = cex.ground_derivation.as_ref().unwrap();
    assert_eq!(derivation.len(), 3);
    validate_ground_derivation(&source, derivation).unwrap();
    assert!(validate_ground_derivation(&problem(false), derivation).is_err());
    assert_eq!(format!("{source:?}"), before);

    let mut approximate = source.clone();
    approximate.mark_stripped_body_forall();
    assert!(
        run(&approximate, &config(), None).is_none(),
        "the existing over-approximation gate still refuses Unsafe"
    );
    let public = solve_pdr_proof(source, config()).unwrap();
    assert!(public.result().is_unsafe());
    assert!(public.accepted_as_proof());
}

#[test]
fn every_caller_boundary_refuses_even_after_observed_parent_cancellation_resets() {
    // Establish every boundary is reached by a genuinely validated candidate.
    let source = problem(true);
    assert!(run(&source, &config(), None).unwrap().is_unsafe());
    for external in [false, true] {
        for stop_at in phases() {
            let parent = CancellationToken::new();
            let mut configured = config();
            if external {
                configured.external_cancellation_token = Some(parent.clone());
            } else {
                configured.cancellation_token = Some(parent.clone());
            }
            let mut observed = Vec::new();
            let result = run_observed(&source, &configured, None, &mut |phase| {
                observed.push(phase);
                if phase == stop_at {
                    parent.cancel();
                }
                if phase == Phase::Cleanup && stop_at != Phase::Cleanup {
                    parent.reset();
                }
            })
            .expect("a stop must terminate instead of permitting fallback");
            assert!(result.is_unknown(), "stop at {stop_at:?}");
            assert!(observed.contains(&stop_at));
            let last = phases().iter().position(|phase| *phase == stop_at).unwrap();
            for later in &phases()[last + 1..] {
                if *later != Phase::Cleanup {
                    assert!(!observed.contains(later));
                }
            }
            parent.reset();
            assert!(
                Owner::capture(&configured, None).open(),
                "a fresh attempt may resume"
            );
        }
    }
}

/// Under an effort a stop observed after validation keeps the validated
/// refutation (P4a slice 8); one during the search or the validation still
/// ends the attempt `unknown`, as without an effort.
#[test]
fn under_an_effort_a_stop_after_validation_keeps_the_refutation() {
    let source = problem(true);
    for stop_at in phases() {
        let parent = CancellationToken::new();
        let mut configured = config().with_effort(Some(1_000_000));
        configured.cancellation_token = Some(parent.clone());
        let result = run_observed(&source, &configured, None, &mut |phase| {
            if phase == stop_at {
                parent.cancel();
            }
        })
        .expect("a refutable source has a prepass result");
        let kept = matches!(
            stop_at,
            Phase::Validated | Phase::Publication | Phase::Cleanup
        );
        assert_eq!(result.is_unsafe(), kept, "stop at {stop_at:?}");
        assert_eq!(result.is_unknown(), !kept, "stop at {stop_at:?}");
    }
}

#[test]
fn validation_descendants_share_sticky_observations_without_cancelling_parents() {
    let primary = CancellationToken::new();
    let external = CancellationToken::new();
    let mut configured = config();
    configured.cancellation_token = Some(primary.clone());
    configured.external_cancellation_token = Some(external.clone());
    for parent in [&primary, &external] {
        let mut owner = Owner::capture(&configured, None);
        let descendant = owner.cancellation.as_ref().unwrap().child();
        parent.cancel();
        // Simulate a consumer of the validator's linked token. This does not
        // claim that the existing opaque ground-validator loop polls it.
        assert!(descendant.is_cancelled());
        parent.reset();
        assert!(!primary.is_cancelled());
        assert!(!external.is_cancelled());
        assert!(
            !owner.open(),
            "the outer owner must retain the inner observation"
        );
        assert!(!owner.open());
        assert!(Owner::capture(&configured, None).open());
    }
}

#[test]
fn deadline_and_memory_owners_are_inherited_without_reopening() {
    let configured = config();
    let early = Instant::now() + Duration::from_secs(30);
    let late = early + Duration::from_secs(30);
    {
        let _solve = crate::smt::ScopedSolveDeadline::new(Some(early));
        let _smt = crate::smt::ScopedSmtDeadline::install_until(late);
        let mut owner = Owner::capture(&configured, Some(late));
        assert_eq!(owner.deadline, Some(early));
        let before_early = early
            .checked_sub(Duration::from_secs(1))
            .expect("fixture instant supports a one-second offset");
        assert!(owner.open_at(before_early));
        assert!(!owner.open_at(early));
        assert!(!owner.open_at(before_early), "observed expiry is sticky");
    }
    {
        let _smt = crate::smt::ScopedSmtDeadline::install_until(Instant::now());
        assert!(run(&problem(true), &configured, Some(late))
            .unwrap()
            .is_unknown());
    }
    let mut owner = Owner::capture(&configured, None);
    {
        let _zero = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert!(!owner.open());
        assert!(run(&problem(true), &configured, None).unwrap().is_unknown());
    }
    assert!(
        !owner.open(),
        "restored memory scope cannot revive the attempt"
    );
    assert!(Owner::capture(&configured, None).open());
}

#[test]
fn missing_candidate_falls_through_but_cleanup_stop_is_terminal() {
    let source = problem(false);
    let mut observed = Vec::new();
    assert!(run_observed(&source, &config(), None, &mut |phase| observed.push(phase)).is_none());
    assert_eq!(observed, [Phase::Search, Phase::Cleanup]);
    let parent = CancellationToken::new();
    let mut configured = config();
    configured.cancellation_token = Some(parent.clone());
    let result = run_observed(&source, &configured, None, &mut |phase| {
        if phase == Phase::Cleanup {
            parent.cancel();
        }
    });
    assert!(result
        .expect("cancelled None is not fallback permission")
        .is_unknown());
}

#[test]
fn public_precancelled_and_zero_budget_entries_never_publish_proof() {
    for external in [false, true] {
        let parent = CancellationToken::new();
        parent.cancel();
        let mut configured = config();
        if external {
            configured.external_cancellation_token = Some(parent);
        } else {
            configured.cancellation_token = Some(parent);
        }
        let run = solve_pdr_proof(problem(true), configured).unwrap();
        assert!(run.result().is_unknown());
        assert!(!run.accepted_as_proof());
    }
    let mut configured = config();
    configured.solve_timeout = Some(Duration::ZERO);
    let run = solve_pdr_proof(problem(true), configured).unwrap();
    assert!(run.result().is_unknown());
    assert!(!run.accepted_as_proof());
}

/// The `solve_pdr_proof` boundary (`validate_pdr_proof_result`) wraps the
/// counterexample that passed: on a replay-decided `Valid` that is the bounded
/// replay's own witness-bearing trace, not the unchecked value-free candidate.
#[test]
fn pdr_proof_boundary_wraps_the_replays_counterexample() {
    // Cyclic two-predicate refutation: no transition-system encoding, so a
    // witness-free candidate is decided only by the bounded replay.
    const UNSAFE_MULTIPRED: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (< x 3) (= y (+ x 1))) (P y))))
(assert (forall ((x Int)) (=> (and (P x) (>= x 3)) (Q x))))
(assert (forall ((x Int)) (=> (and (Q x) (= x 3)) false)))
(check-sat)
";
    let problem = crate::ChcParser::parse(UNSAFE_MULTIPRED).expect("fixture parses");
    let candidate = Counterexample::new(
        problem
            .predicates()
            .iter()
            .map(|p| crate::pdr::CounterexampleStep::new(p.id, Default::default()))
            .collect(),
    );
    assert_eq!(
        candidate.ground_checks_unsafe(&problem).ok(),
        None,
        "setup: the value-free candidate cannot be confirmed by itself"
    );
    let result = validate_pdr_proof_result(
        &problem,
        PdrResult::Unsafe(candidate),
        &PdrConfig::default(),
        None,
    );
    let VerifiedChcResult::Unsafe(cex) = result else {
        panic!("the replay confirms this genuine refutation: {result:?}");
    };
    assert_eq!(
        cex.counterexample().ground_checks_unsafe(&problem).ok(),
        Some(true),
        "the proof-run Unsafe carries the replay's confirmable counterexample"
    );
}
