// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The concrete check stops when its solve does (2026-11-01). The enumeration
//! polled no cancellation and no solve deadline, so PDR workers whose solve
//! was over (their model-checker-consumer watchdog had given up on them, and nothing
//! cancelled them) sat in it for hours inside compiler_consumer: 82 such workers, one
//! alive 510 minutes, held 87% of the compiler's running samples. A check now
//! polls the solver's tokens, its solve deadline and the thread's SMT
//! deadline and lane cancellation before every evaluation (in-window and
//! anchored alike), answers `Interrupted` when one fires, never a witness,
//! and the verifiers reject rather than count it performed.

use super::budget_tests::{
    clauses_b, config, costly_unsat_body, int_var, query_clauses, var, ANCHORED_SAMPLES,
};
use super::*;
use crate::cancellation::CancellationToken;
use crate::pdr::{InvariantModel, PdrSolver, PredicateInterpretation};
use crate::smt::SmtResult;
use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
use ay_core::time::Instant;
use std::time::Duration;

/// The exhaustive branch's length on `costly_unsat_body(5, _)`: `5..=100`
/// for each of two variables.
const IN_WINDOW_ASSIGNMENTS: u64 = 96 * 96;

fn cancelled() -> CancellationToken {
    let token = CancellationToken::new();
    token.cancel();
    token
}

fn passed() -> Instant {
    Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("the clock reaches 1 ms back")
}

fn in_window_sat() -> ChcExpr {
    ChcExpr::and_all(vec![
        ChcExpr::ge(var("A"), ChcExpr::int(5)),
        ChcExpr::eq(var("A"), ChcExpr::int(6)),
    ])
}

fn anchored_sat() -> ChcExpr {
    ChcExpr::and_all(vec![
        ChcExpr::ge(var("A"), ChcExpr::int(150)),
        ChcExpr::eq(var("A"), ChcExpr::int(150)),
    ])
}

/// A cancelled token or a passed solve deadline: the check evaluates nothing
/// and answers `Interrupted` (never the witness both queries have), in the
/// window and anchored alike. The same checks with a live token find it.
#[test]
fn a_fired_stop_evaluates_nothing_and_answers_interrupted() {
    let stops = [
        (
            "cancelled token",
            ConcreteStop::new(vec![cancelled()], None),
        ),
        (
            "passed solve deadline",
            ConcreteStop::new(Vec::new(), Some(passed())),
        ),
    ];
    for (what, stop) in stops {
        for body in [in_window_sat(), anchored_sat()] {
            let mut budget = ConcreteBudget::new(Duration::from_secs(60), stop.clone());
            assert_eq!(
                budget.check(&body, &body),
                ConcreteAnswer::Interrupted,
                "{what}"
            );
            assert_eq!(budget.evaluations(), 0, "{what}");
        }
    }
    let live = ConcreteStop::new(vec![CancellationToken::new()], None);
    for body in [in_window_sat(), anchored_sat()] {
        let mut budget = ConcreteBudget::new(Duration::from_secs(60), live.clone());
        assert!(matches!(
            budget.check(&body, &body),
            ConcreteAnswer::Witness(_)
        ));
    }
}

/// The probe itself polls the stop before its first evaluation, whatever
/// starts the search (the budget also refuses to start one).
#[test]
fn a_probe_polls_the_stop_before_evaluating() {
    for (body, anchored) in [(in_window_sat(), false), (anchored_sat(), true)] {
        let domain = CheckDomain::new(&body, &body).expect("a domain");
        assert_eq!(domain.anchored, anchored);
        for stop in [
            ConcreteStop::new(vec![cancelled()], None),
            ConcreteStop::new(Vec::new(), Some(passed())),
        ] {
            let mut probe = Probe::new(&body, None, stop.resolve());
            assert_eq!(domain.search(&mut probe), None);
            assert_eq!(probe.evaluated(), 0);
            assert!(probe.interrupted());
        }
    }
}

/// Cancellation that lands while a check runs stops it at the next
/// evaluation: the exhaustive branch (in the window) and the Monte Carlo
/// branch (anchored, with a minute of allowance) each stop well short of
/// their full length.
#[test]
fn cancellation_mid_search_stops_the_enumeration() {
    for (lo, full) in [(5, IN_WINDOW_ASSIGNMENTS), (1000, ANCHORED_SAMPLES)] {
        let body = costly_unsat_body(lo, 1000);
        let token = CancellationToken::new();
        let canceller = {
            let token = token.clone();
            std::thread::spawn(move || {
                std::thread::sleep(Duration::from_millis(50));
                token.cancel();
            })
        };
        let mut budget = ConcreteBudget::new(
            Duration::from_secs(60),
            ConcreteStop::new(vec![token], None),
        );
        let answer = budget.check(&body, &body);
        canceller.join().expect("the canceller finishes");
        assert_eq!(answer, ConcreteAnswer::Interrupted, "lo = {lo}");
        assert!(
            budget.evaluations() < full,
            "lo = {lo}: stopped after {} of {full} evaluations",
            budget.evaluations()
        );
    }
}

/// A solver's verifier runs stop on its portfolio token, its embedder's
/// token, its solve deadline, and the thread's SMT deadline and lane
/// cancellation.
#[test]
fn a_solvers_stop_reads_its_tokens_deadline_and_thread() {
    let (problem, _) = query_clauses(vec![in_window_sat()]);
    let body = in_window_sat();
    let interrupted = |solver: &PdrSolver| {
        let mut budget =
            ConcreteBudget::new(Duration::from_secs(60), ConcreteStop::of_solver(solver));
        budget.check(&body, &body) == ConcreteAnswer::Interrupted
    };

    let solver = PdrSolver::new(problem.clone(), config(false));
    assert!(!interrupted(&solver), "nothing has fired");

    let mut portfolio = config(false);
    portfolio.cancellation_token = Some(cancelled());
    assert!(interrupted(&PdrSolver::new(problem.clone(), portfolio)));

    let mut embedder = config(false);
    embedder.external_cancellation_token = Some(cancelled());
    assert!(interrupted(&PdrSolver::new(problem.clone(), embedder)));

    let mut late = PdrSolver::new(problem.clone(), config(false));
    late.solve_deadline = Some(passed());
    assert!(interrupted(&late));

    {
        let _deadline = crate::smt::ScopedSmtDeadline::install_until(passed());
        assert!(interrupted(&solver), "the thread's SMT deadline has passed");
    }
    {
        let _lane = crate::smt::ScopedLaneCancellation::install(cancelled(), None);
        assert!(interrupted(&solver), "the thread's lane is cancelled");
    }
    assert!(!interrupted(&solver), "the scopes are gone");
}

/// `inv(B, A) <- inv(A, B) /\ A >= 5 /\ B >= 5 /\ pad conjuncts` under the
/// valid `inv := A >= 0`. Its query (`body /\ not (B >= 0)`) has no model, and
/// its concrete check is the exhaustive branch's 9216 assignments, each
/// walking the pad before the last conjunct refuses it.
fn transition_problem(pad: usize) -> (ChcProblem, InvariantModel, crate::PredicateId) {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);
    let mut conjuncts = vec![
        ChcExpr::ge(var("A"), ChcExpr::int(5)),
        ChcExpr::ge(var("B"), ChcExpr::int(5)),
    ];
    for i in 1..=pad {
        let i = i64::try_from(i).unwrap_or(i64::MAX);
        conjuncts.push(ChcExpr::ge(
            ChcExpr::add(var("A"), ChcExpr::mul(ChcExpr::int(i), var("B"))),
            ChcExpr::int(i64::MIN / 4),
        ));
    }
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![var("A"), var("B")])],
            Some(ChcExpr::and_all(conjuncts)),
        ),
        ClauseHead::Predicate(inv, vec![var("B"), var("A")]),
    ));
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![int_var("A"), int_var("B")],
            ChcExpr::ge(var("A"), ChcExpr::int(0)),
        ),
    );
    (problem, model, inv)
}

/// An interrupted check is no acceptance: each clause verifier rejects. The
/// clause is valid and its SMT answer is forced to UNSAT, so only the
/// interruption can reject it, and the same calls with a live stop accept.
#[test]
fn an_interrupted_check_rejects_the_clause() {
    // Query clause (`model_safety.rs`): `false <- inv(A, B) /\ A >= 5 /\ ...`.
    let (problem, model) = query_clauses(vec![costly_unsat_body(5, 10)]);
    for (stop, rejects) in [
        (ConcreteStop::new(vec![cancelled()], None), true),
        (ConcreteStop::none(), false),
    ] {
        let mut verifier = PdrSolver::new(problem.clone(), config(false));
        verifier
            .smt
            .push_forced_check_sat_result_for_tests(SmtResult::Unsat);
        let clause = verifier.problem.clauses()[0].clone();
        let body = verifier
            .clause_body_under_model(&clause.body, &model)
            .expect("body under model");
        let body = verifier.bound_int_vars(body);
        let failure = verifier.verify_query_clause(
            &clause,
            0,
            &body,
            &model,
            Duration::from_secs(10),
            None,
            None,
            &mut Vec::new(),
            &mut ConcreteBudget::new(Duration::from_secs(60), stop),
            &mut 0,
        );
        assert_eq!(
            failure.is_some(),
            rejects,
            "query clause, rejects = {rejects}"
        );
    }

    // Transition clause (`model_inductive.rs`).
    let (problem, model, inv) = transition_problem(10);
    for (stop, rejects) in [
        (ConcreteStop::new(vec![cancelled()], None), true),
        (ConcreteStop::none(), false),
    ] {
        let mut verifier = PdrSolver::new(problem.clone(), config(false));
        verifier
            .smt
            .push_forced_check_sat_result_for_tests(SmtResult::Unsat);
        let clause = verifier.problem.clauses()[0].clone();
        let body = verifier
            .clause_body_under_model(&clause.body, &model)
            .expect("body under model");
        let body = verifier.bound_int_vars(body);
        let failure = verifier.verify_transition_clause(
            &clause,
            0,
            &body,
            &inv,
            &[var("B"), var("A")],
            &model,
            Duration::from_secs(10),
            None,
            None,
            &mut false,
            &mut ConcreteBudget::new(Duration::from_secs(60), stop),
            &mut 0,
            &mut crate::ground_derivation::compact::Owner::capture()
                .expect("original verifier owner"),
        );
        assert_eq!(
            failure.is_some(),
            rejects,
            "transition clause, rejects = {rejects}"
        );
    }
}

/// `verify_model_fast` on `problem` with SMT forced UNSAT, its solver's token
/// cancelled after `cancel_after` when given: whether it accepts, and how long
/// it took.
fn fast_run(
    problem: &ChcProblem,
    model: &InvariantModel,
    cancel_after: Option<Duration>,
) -> (bool, Duration) {
    let token = CancellationToken::new();
    let mut solver_config = config(false);
    solver_config.cancellation_token = Some(token.clone());
    let mut fast = PdrSolver::new(problem.clone(), solver_config);
    fast.smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unsat);
    let canceller = cancel_after.map(|after| {
        std::thread::spawn(move || {
            std::thread::sleep(after);
            token.cancel();
        })
    });
    let start = Instant::now();
    let accepted = fast.verify_model_fast(model, Instant::now() + Duration::from_secs(600));
    let took = start.elapsed();
    if let Some(canceller) = canceller {
        canceller.join().expect("the canceller finishes");
    }
    (accepted, took)
}

/// The fast verifier rejects when its solver is cancelled while the last
/// clause's concrete check runs, instead of accepting on the unfinished
/// check, and it stops promptly rather than finishing the search: a query
/// clause and a transition clause, each valid, each with about two seconds
/// of exhaustive search (9216 assignments of a 1000-conjunct body).
#[test]
fn verify_model_fast_rejects_when_cancelled_during_the_last_check() {
    let (query_problem, query_model) = query_clauses(vec![costly_unsat_body(5, 1000)]);
    let (transition_problem, transition_model, _) = transition_problem(1000);
    for (what, problem, model) in [
        ("query clause", &query_problem, &query_model),
        ("transition clause", &transition_problem, &transition_model),
    ] {
        let (accepted, took) = fast_run(problem, model, Some(Duration::from_millis(200)));
        assert!(
            !accepted,
            "{what}: a cancelled run never accepts (took {took:?})"
        );
        // Control: never cancelled, the run searches to the end and accepts;
        // the cancelled run stopped well before that.
        let (accepted, full) = fast_run(problem, model, None);
        assert!(accepted, "{what}: the valid model is accepted");
        assert!(
            took < full,
            "{what}: the cancelled run stopped early: {took:?} against {full:?}"
        );
    }
}

/// The review of b645a840fe, finding A: under a deadline an anchored search
/// takes at most half the time to it, less the anchored time its run has
/// already spent, answers `NoWitness` when that runs out (the centred
/// window's answer), and leaves the rest to the verifier. It used to search
/// into the deadline, answer `Interrupted` and leave nothing. Through the
/// solve deadline and through the thread's SMT deadline (a solver's stop):
/// the first search is cut short of its 10000 samples (seconds of a
/// 3000-conjunct body) and the deadline has not passed; the run's second
/// search finds no time left and evaluates nothing.
#[test]
fn an_anchored_search_takes_at_most_half_the_time_its_deadline_leaves() {
    let costly = costly_unsat_body(1000, 3000);
    let (problem, _) = query_clauses(Vec::new());
    let solver = PdrSolver::new(problem, config(false));
    for (what, through_thread) in [("solve deadline", false), ("thread SMT deadline", true)] {
        let end = Instant::now() + Duration::from_millis(400);
        let _thread = through_thread.then(|| crate::smt::ScopedSmtDeadline::install_until(end));
        let stop = if through_thread {
            ConcreteStop::of_solver(&solver)
        } else {
            ConcreteStop::new(Vec::new(), Some(end))
        };
        let mut budget = ConcreteBudget::new(Duration::from_secs(60), stop);
        assert_eq!(
            budget.check(&costly, &costly),
            ConcreteAnswer::NoWitness,
            "{what}"
        );
        assert!(
            Instant::now() < end,
            "{what}: the search left time before the deadline"
        );
        let spent = budget.evaluations();
        assert!(
            spent > 0 && spent < ANCHORED_SAMPLES,
            "{what}: cut at {spent} of {ANCHORED_SAMPLES} evaluations"
        );
        assert_eq!(
            budget.check(&costly, &costly),
            ConcreteAnswer::NoWitness,
            "{what}"
        );
        assert_eq!(
            budget.evaluations(),
            spent,
            "{what}: the run's anchored time used up its share of the deadline"
        );
    }
}

/// Finding A through the verifiers (the reviewer's D1): clauses B with the
/// SMT answers forced to the true UNSAT and a solve deadline 400 ms away.
/// b35c9df116 accepted in about 7 ms, and b645a840fe rejected at the
/// deadline, its anchored search having spent all of it. Each verifier now
/// accepts, and its anchored search did run.
#[test]
fn a_solve_deadline_inside_an_anchored_search_leaves_the_clauses_their_time() {
    let (problem, model) = clauses_b(2000);
    let solver = || {
        let mut solver = PdrSolver::new(problem.clone(), config(false));
        for _ in 0..4 {
            solver
                .smt
                .push_forced_check_sat_result_for_tests(SmtResult::Unsat);
        }
        solver.solve_deadline = Some(Instant::now() + Duration::from_millis(400));
        solver
    };
    let mut full = solver();
    assert!(
        full.verify_model_with_budget(&model, Duration::from_millis(1500)),
        "verify_model_with_budget accepts the valid model"
    );
    assert!(full.telemetry.concrete_anchored_search > Duration::ZERO);
    let mut fast = solver();
    assert!(
        fast.verify_model_fast(&model, Instant::now() + Duration::from_millis(800)),
        "verify_model_fast accepts the valid model"
    );
    assert!(fast.telemetry.concrete_anchored_search > Duration::ZERO);
}
