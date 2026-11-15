// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The concrete check's time accounting across a verifier run (2026-11-01,
//! hostile review of 90b40b3908). A check on an anchored domain (an Int range
//! wholly beyond ±100) used to answer `None` at once; once the anchored window
//! searched it, it cost as much as any other check and was charged to the one
//! budget every check shares, so later checks were skipped. With an invalid
//! model whose later clause carried a false UNSAT, that removed a rejection
//! the centred window made, and strict_proofs rejected valid models the
//! centred window accepted. The anchored searches now draw on an allowance of
//! their own, and (review of a074352391) the verifiers' and the cascade's
//! wall-clock budgets do not count that allowance either.

use super::*;
use crate::pdr::{InvariantModel, PdrConfig, PdrSolver, PredicateInterpretation};
use crate::smt::SmtResult;
use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
use ay_core::time::Instant;
use std::time::Duration;

pub(super) fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

pub(super) fn var(name: &str) -> ChcExpr {
    ChcExpr::var(int_var(name))
}

/// `A >= lo /\ B >= lo /\ pad conjuncts /\ A + B <= 2 lo - 1`: no model, and
/// the evaluator walks every pad conjunct before the last one refuses an
/// assignment, so a search costs in proportion to `pad`. With `lo` beyond
/// ±100 both ranges are anchored (two ranges of 201 values: the search is the
/// Monte Carlo branch's 10000 samples); with `lo = 5` both are in the window
/// (`5..=100`: the exhaustive branch's 9216 assignments).
pub(super) fn costly_unsat_body(lo: i64, pad: usize) -> ChcExpr {
    let mut conjuncts = vec![
        ChcExpr::ge(var("A"), ChcExpr::int(lo)),
        ChcExpr::ge(var("B"), ChcExpr::int(lo)),
    ];
    for i in 1..=pad {
        let i = i64::try_from(i).unwrap_or(i64::MAX);
        conjuncts.push(ChcExpr::ge(
            ChcExpr::add(var("A"), ChcExpr::mul(ChcExpr::int(i), var("B"))),
            ChcExpr::int(i64::MIN / 4),
        ));
    }
    conjuncts.push(ChcExpr::le(
        ChcExpr::add(var("A"), var("B")),
        ChcExpr::int(2 * lo - 1),
    ));
    ChcExpr::and_all(conjuncts)
}

/// The anchored search's full length on [`costly_unsat_body`] beyond ±100.
pub(super) const ANCHORED_SAMPLES: u64 = 10_000;

/// `inv := true` over `inv(A, B)`.
pub(super) fn true_model(inv: crate::PredicateId) -> InvariantModel {
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(vec![int_var("A"), int_var("B")], ChcExpr::Bool(true)),
    );
    model
}

/// `false <- inv(A, B) /\ body` for each body.
pub(super) fn query_clauses(bodies: Vec<ChcExpr>) -> (ChcProblem, InvariantModel) {
    let (mut problem, inv) = inv_problem();
    for body in bodies {
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(inv, vec![var("A"), var("B")])], Some(body)),
            ClauseHead::False,
        ));
    }
    (problem, true_model(inv))
}

fn inv_problem() -> (ChcProblem, crate::PredicateId) {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);
    (problem, inv)
}

/// The review of a074352391's clauses B: `false <- inv(A, B) /\
/// costly_unsat_body(1000, pad)` (anchored) and then `inv(A, B) <- inv(A,
/// B)`, under the valid `inv := true`.
pub(super) fn clauses_b(pad: usize) -> (ChcProblem, InvariantModel) {
    let (mut problem, model) = query_clauses(vec![costly_unsat_body(1000, pad)]);
    let inv = crate::PredicateId::new(0);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![var("A"), var("B")])], None),
        ClauseHead::Predicate(inv, vec![var("A"), var("B")]),
    ));
    (problem, model)
}

pub(super) fn config(strict_proofs: bool) -> PdrConfig {
    let mut config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    config.strict_proofs = strict_proofs;
    config
}

fn anchored_sat() -> ChcExpr {
    ChcExpr::and_all(vec![
        ChcExpr::ge(var("A"), ChcExpr::int(150)),
        ChcExpr::eq(var("A"), ChcExpr::int(150)),
    ])
}

/// An anchored check's construction is charged to the check's own budget, as
/// the centred window's construction (which found the empty range) was; its
/// search never is, and draws on the allowance.
#[test]
fn an_anchored_search_never_spends_the_checks_own_budget() {
    // With no allowance the anchored search never starts, so the witness
    // `A = 150` is not found, which is the centred window's answer there.
    let mut budget = ConcreteBudget::new(Duration::ZERO, ConcreteStop::none());
    assert_eq!(
        budget.check(&anchored_sat(), &anchored_sat()),
        ConcreteAnswer::NoWitness
    );
    assert_eq!(budget.evaluations(), 0);

    // With an allowance left the anchored search finds the witness.
    let mut budget = ConcreteBudget::new(Duration::from_secs(60), ConcreteStop::none());
    let model = budget.check(&anchored_sat(), &anchored_sat()).witness();
    assert_eq!(
        model.and_then(|m| m.get("A").cloned()),
        Some(SmtValue::Int(150))
    );
    assert!(budget.anchored_elapsed() > Duration::ZERO);

    // A costly anchored search runs its whole 200 ms allowance; the budget
    // is charged only the construction (milliseconds), so it keeps room.
    let limit = Duration::from_millis(200);
    let mut budget = ConcreteBudget::new(limit, ConcreteStop::none());
    assert_eq!(
        budget.check(
            &costly_unsat_body(1000, 2000),
            &costly_unsat_body(1000, 2000)
        ),
        ConcreteAnswer::NoWitness
    );
    assert!(budget.anchored_elapsed() >= limit);
    assert!(
        budget.elapsed() > Duration::ZERO,
        "the construction is charged to the budget"
    );
    assert!(
        budget.has_room(),
        "the search is not charged to the budget: elapsed {:?}",
        budget.elapsed()
    );

    // An in-window check is charged to the budget, search and all.
    let in_window_sat = ChcExpr::and_all(vec![
        ChcExpr::ge(var("A"), ChcExpr::int(5)),
        ChcExpr::eq(var("A"), ChcExpr::int(6)),
    ]);
    let before = budget.elapsed();
    let model = budget.check(&in_window_sat, &in_window_sat).witness();
    assert_eq!(
        model.and_then(|m| m.get("A").cloned()),
        Some(SmtValue::Int(6))
    );
    assert!(budget.elapsed() > before);
}

/// Once the allowance is spent an anchored check evaluates nothing and
/// answers `NoWitness`, and a costly anchored search stops at its allowance
/// rather than running all its samples: it counts its evaluations, so this
/// holds on any host, however fast (review of a074352391, finding 3: a
/// deadline checked only before the first evaluation passed the timing form
/// of this test).
#[test]
fn the_anchored_allowance_bounds_the_anchored_checks() {
    let costly = costly_unsat_body(1000, 1000);
    let limit = Duration::from_millis(50);
    let mut budget = ConcreteBudget::new(limit, ConcreteStop::none());
    assert_eq!(budget.check(&costly, &costly), ConcreteAnswer::NoWitness);
    assert!(
        budget.evaluations() < ANCHORED_SAMPLES,
        "the search stops at its allowance: {} of {ANCHORED_SAMPLES} evaluations",
        budget.evaluations()
    );
    assert!(budget.anchored_elapsed() >= limit);

    let spent = budget.evaluations();
    let anchored_sat = ChcExpr::and_all(vec![
        ChcExpr::le(var("A"), ChcExpr::int(-150)),
        ChcExpr::eq(var("A"), ChcExpr::int(-150)),
    ]);
    assert_eq!(
        budget.check(&anchored_sat, &anchored_sat),
        ConcreteAnswer::NoWitness
    );
    assert_eq!(
        budget.evaluations(),
        spent,
        "a spent allowance evaluates nothing"
    );
}

/// A probe whose deadline has already passed evaluates nothing; without it
/// the same search evaluates and finds its witness.
#[test]
fn a_passed_allowance_evaluates_nothing() {
    let body = anchored_sat();
    let domain = CheckDomain::new(&body, &body).expect("an anchored domain");
    assert!(domain.anchored);
    let stop = ConcreteStop::none();
    let passed = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("the clock reaches 1 ms back");
    let mut probe = Probe::new(&body, Some(passed), stop.resolve());
    assert_eq!(domain.search(&mut probe), None);
    assert_eq!(probe.evaluated(), 0);
    assert!(probe.stopped());
    assert!(
        !probe.interrupted(),
        "the allowance, not the stop, ended it"
    );

    let mut probe = Probe::new(&body, None, stop.resolve());
    assert!(domain.search(&mut probe).is_some());
    assert!(probe.evaluated() > 0);
}

/// The reviewer's P8. Clause 0 is valid, anchored and costly to evaluate;
/// clause 1 (`A = 6 /\ B = 3`) is violated by `inv := true`, and both SMT
/// answers are forced to UNSAT, so only clause 1's concrete check can reject.
/// With one shared budget clause 0's check spent it and clause 1's check was
/// skipped: verify_model accepted the invalid model under strict_proofs and
/// without it, and verify_model_fast without it. Every verifier entry still
/// rejects it now that anchored time is also kept out of their wall-clock
/// budgets.
#[test]
fn a_costly_anchored_check_leaves_the_budget_to_a_later_rejection() {
    let (problem, model) = query_clauses(vec![
        costly_unsat_body(1000, 2000),
        ChcExpr::and_all(vec![
            ChcExpr::eq(var("A"), ChcExpr::int(6)),
            ChcExpr::eq(var("B"), ChcExpr::int(3)),
        ]),
    ]);
    let forced = |strict: bool| {
        let mut solver = PdrSolver::new(problem.clone(), config(strict));
        for _ in 0..2 {
            solver
                .smt
                .push_forced_check_sat_result_for_tests(SmtResult::Unsat);
        }
        solver
    };
    for strict in [true, false] {
        assert!(
            !forced(strict).verify_model(&model),
            "verify_model (strict_proofs={strict}) must reject: A = 6, B = 3 violates clause 1"
        );
        assert!(
            !forced(strict).verify_model_with_budget(&model, Duration::from_secs(1)),
            "verify_model_with_budget (strict_proofs={strict}) must reject"
        );
        assert!(
            !forced(strict).verify_model_per_rule(&model, Duration::from_secs(1)),
            "verify_model_per_rule (strict_proofs={strict}) must reject"
        );
        assert!(
            !forced(strict).verify_model_fast(&model, Instant::now() + Duration::from_secs(60)),
            "verify_model_fast (strict_proofs={strict}) must reject"
        );
        assert!(
            !forced(strict).verify_model_fast(&model, Instant::now() + Duration::from_millis(150)),
            "verify_model_fast with 150 ms (strict_proofs={strict}) must reject"
        );
    }
}

/// The reviewer's P3: a valid model, real SMT, four anchored query clauses
/// costly to evaluate. With one shared budget the anchored checks spent
/// verify_model_fast's 200 ms, the next check was skipped for budget, and
/// strict_proofs rejected the valid model the centred window accepted.
#[test]
fn costly_anchored_checks_do_not_make_strict_proofs_reject_a_valid_model() {
    let bodies = (0..4).map(|i| costly_unsat_body(1000 + i, 600)).collect();
    let (problem, model) = query_clauses(bodies);
    let mut fast = PdrSolver::new(problem.clone(), config(true));
    assert!(fast.verify_model_fast(&model, Instant::now() + Duration::from_secs(60)));
    let mut full = PdrSolver::new(problem, config(true));
    assert!(full.verify_model(&model));
}

/// The review of a074352391, finding 1 (clauses B): a valid model, a costly
/// anchored query clause and then `inv(A, B) <- inv(A, B)` (real SMT in
/// verify_model_with_budget; the fast path's is forced, below). The
/// anchored search runs its whole allowance (1 s in verify_model_with_budget,
/// 200 ms in verify_model_fast). Counted against the verifier's own wall-clock
/// budget (1 s, a 150 ms deadline), that left nothing for the transition
/// clause, which is rejected once the budget is gone, so a model b35c9df116
/// accepted was rejected. The budget's start (and the fast path's deadline)
/// now moves forward by the anchored time.
#[test]
fn anchored_search_time_does_not_spend_the_verifiers_wall_clock_budget() {
    let (problem, model) = clauses_b(2000);

    let mut full = PdrSolver::new(problem.clone(), config(false));
    assert!(
        full.verify_model_with_budget(&model, Duration::from_secs(1)),
        "verify_model_with_budget(1 s) accepts the valid model"
    );
    assert!(
        full.telemetry.concrete_anchored_search >= Duration::from_secs(1),
        "the run records its anchored time for the cascade: {:?}",
        full.telemetry.concrete_anchored_search
    );

    // The fast path with a 150 ms deadline. Its SMT answer is forced to UNSAT,
    // the true answer (the body has no model): real SMT on the 2000-conjunct
    // body takes a load-dependent share of 150 ms, while the forced answer
    // leaves the deadline to the anchored search's 200 ms alone.
    let mut fast = PdrSolver::new(problem, config(false));
    fast.smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unsat);
    assert!(
        fast.verify_model_fast(&model, Instant::now() + Duration::from_millis(150)),
        "verify_model_fast(150 ms) accepts the valid model"
    );
    let anchored = fast.telemetry.concrete_anchored_search;
    assert!(anchored >= Duration::from_millis(200), "{anchored:?}");
}

/// The review of b645a840fe, finding B: an array-scalarized solver judges a
/// model in the original signature with a nested verifier on the original
/// problem (`model.rs`), which hands its anchored search time up to the
/// parent, whose cascade reads it. Here only the nested verifier has a clause
/// at all (the parent's working problem has none), so every nanosecond the
/// parent records came from it.
#[test]
fn a_nested_verifier_hands_its_anchored_time_to_its_parent() {
    let (original, model) = query_clauses(vec![costly_unsat_body(1000, 10)]);
    let mut scalarized = ChcProblem::new();
    scalarized.declare_predicate("inv", vec![ChcSort::Int]);
    let mut parent = PdrSolver::new(scalarized, config(false));
    parent.model_problem = original.clone();
    // A map that has no scalarized spelling for `inv`: the model is judged on
    // the original problem.
    parent.array_scalarization_maps = vec![crate::problem::ArrayScalarizationMap {
        original_predicates: original.predicates().to_vec(),
        pred_args: Default::default(),
    }];
    assert!(parent.verify_model(&model), "the valid model is accepted");
    assert!(
        parent.telemetry.concrete_anchored_search > Duration::ZERO,
        "the nested verifier's anchored search reaches the parent"
    );
}
