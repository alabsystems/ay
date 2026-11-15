// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Int window `transition_check` enumerates (2026-11-01): a range that
//! meets [-100, 100] keeps that intersection, a range wholly outside it is
//! checked on its own 201 values nearest the window, and only crossed bounds
//! leave a range empty. Before, a variable bounded beyond ±100 got an empty
//! range, so the check evaluated nothing, and an SMT false-UNSAT whose witness
//! lay there passed both model verifiers.

use super::*;
use crate::pdr::{InvariantModel, PdrConfig, PdrSolver, PredicateInterpretation};
use crate::smt::SmtResult;
use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
use ay_core::time::Instant;
use std::sync::mpsc;
use std::time::Duration;

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(int_var(name))
}

/// `A >= lower /\ A = value /\ B = 3` (the reviewer's probe shape).
fn above_probe(lower: i64, value: i64) -> ChcExpr {
    ChcExpr::and_all(vec![
        ChcExpr::ge(var("A"), ChcExpr::int(lower)),
        ChcExpr::eq(var("A"), ChcExpr::int(value)),
        ChcExpr::eq(var("B"), ChcExpr::int(3)),
    ])
}

/// `A <= upper /\ A = value /\ B = 3`, the probe's mirror.
fn below_probe(upper: i64, value: i64) -> ChcExpr {
    ChcExpr::and_all(vec![
        ChcExpr::le(var("A"), ChcExpr::int(upper)),
        ChcExpr::eq(var("A"), ChcExpr::int(value)),
        ChcExpr::eq(var("B"), ChcExpr::int(3)),
    ])
}

/// `A >= 150 /\ A <= 120 /\ A = 150 /\ B = 3`: crossed bounds, no model.
fn crossed_probe() -> ChcExpr {
    ChcExpr::and_all(vec![
        ChcExpr::ge(var("A"), ChcExpr::int(150)),
        ChcExpr::le(var("A"), ChcExpr::int(120)),
        ChcExpr::eq(var("A"), ChcExpr::int(150)),
        ChcExpr::eq(var("B"), ChcExpr::int(3)),
    ])
}

/// The query-clause self-check every production caller runs on a query
/// clause: `transition_check(body, true, body)`.
fn self_check(body: &ChcExpr) -> Option<FxHashMap<String, SmtValue>> {
    transition_check(body, &ChcExpr::Bool(true), body)
}

/// The self-check's witness, which must hold under the exact evaluator.
fn witness(body: &ChcExpr) -> FxHashMap<String, SmtValue> {
    let model = self_check(body).unwrap_or_else(|| panic!("a witness for {body}"));
    assert_eq!(
        evaluate_expr(body, &model),
        Some(SmtValue::Bool(true)),
        "the witness {model:?} must satisfy {body}"
    );
    model
}

/// `false <- inv(A, B) /\ body` with `inv := true`, the SMT answer forced to
/// UNSAT (as in `test_verify_model_query_clause_concrete_cross_check_rejects_
/// forced_false_unsat_5803`): what `verify_model` and `verify_model_fast`
/// return.
fn verdicts_under_forced_unsat(body: ChcExpr) -> (bool, bool) {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![var("A"), var("B")])], Some(body)),
        ClauseHead::False,
    ));
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(vec![int_var("A"), int_var("B")], ChcExpr::Bool(true)),
    );
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };

    let mut verifier = PdrSolver::new(problem.clone(), config.clone());
    verifier
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unsat);
    let full = verifier.verify_model(&model);

    let mut fast_verifier = PdrSolver::new(problem, config);
    fast_verifier
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unsat);
    let fast = fast_verifier.verify_model_fast(&model, Instant::now() + Duration::from_secs(2));
    (full, fast)
}

#[test]
fn a_range_meeting_the_centred_window_keeps_its_intersection() {
    // Today's clamp, value for value.
    assert_eq!(int_check_window(-50, 50), (-50, 50));
    assert_eq!(int_check_window(i64::MIN, i64::MAX), (-100, 100));
    assert_eq!(int_check_window(5, 7), (5, 7));
    assert_eq!(int_check_window(50, 500), (50, 100));
    assert_eq!(int_check_window(-500, -50), (-100, -50));
    assert_eq!(int_check_window(100, i64::MAX), (100, 100));
    assert_eq!(int_check_window(i64::MIN, -100), (-100, -100));
    // Crossed bounds inside the window stay empty.
    assert_eq!(int_check_window(50, 20), (50, 20));
}

#[test]
fn a_range_wholly_outside_is_checked_on_its_values_nearest_the_window() {
    assert_eq!(int_check_window(101, i64::MAX), (101, 301));
    assert_eq!(int_check_window(150, 160), (150, 160));
    assert_eq!(int_check_window(150, 350), (150, 350));
    assert_eq!(int_check_window(150, 351), (150, 350));
    assert_eq!(int_check_window(i64::MIN, -101), (-301, -101));
    assert_eq!(int_check_window(-160, -150), (-160, -150));
    assert_eq!(int_check_window(-351, -150), (-350, -150));
}

#[test]
fn crossed_bounds_outside_the_window_stay_empty() {
    for (lo, hi) in [
        (150, 120),
        (150, 100),
        (150, -150),
        (-120, -150),
        (i64::MAX, i64::MAX - 1),
        (i64::MIN + 1, i64::MIN),
    ] {
        let (wlo, whi) = int_check_window(lo, hi);
        assert!(
            wlo > whi,
            "{lo}..={hi} holds no value, so its window must not"
        );
    }
}

#[test]
fn a_window_at_the_ends_of_i64_neither_overflows_nor_leaves_its_range() {
    assert_eq!(int_check_window(i64::MAX, i64::MAX), (i64::MAX, i64::MAX));
    assert_eq!(
        int_check_window(i64::MAX - 5, i64::MAX),
        (i64::MAX - 5, i64::MAX)
    );
    assert_eq!(
        int_check_window(i64::MAX - 500, i64::MAX),
        (i64::MAX - 500, i64::MAX - 300)
    );
    assert_eq!(int_check_window(i64::MIN, i64::MIN), (i64::MIN, i64::MIN));
    assert_eq!(
        int_check_window(i64::MIN, i64::MIN + 5),
        (i64::MIN, i64::MIN + 5)
    );
    assert_eq!(
        int_check_window(i64::MIN, i64::MIN + 500),
        (i64::MIN + 300, i64::MIN + 500)
    );
}

/// The reviewer's probe of 40eb461a07 and its mirror: the witness lies beyond
/// ±100, inside the variable's bounds.
#[test]
fn the_self_check_finds_a_witness_beyond_the_centred_window() {
    let model = witness(&above_probe(150, 150));
    assert_eq!(model.get("A"), Some(&SmtValue::Int(150)));
    assert_eq!(model.get("B"), Some(&SmtValue::Int(3)));

    let model = witness(&below_probe(-150, -150));
    assert_eq!(model.get("A"), Some(&SmtValue::Int(-150)));
    assert_eq!(model.get("B"), Some(&SmtValue::Int(3)));
}

#[test]
fn the_self_check_finds_a_witness_at_the_ends_of_i64() {
    let model = witness(&above_probe(i64::MAX - 5, i64::MAX));
    assert_eq!(model.get("A"), Some(&SmtValue::Int(i128::from(i64::MAX))));
    let model = witness(&below_probe(i64::MIN + 5, i64::MIN));
    assert_eq!(model.get("A"), Some(&SmtValue::Int(i128::from(i64::MIN))));
}

/// The reviewer's in-window twin, and a range reaching far below the window
/// whose witness sits at its top edge: a range that meets [-100, 100] is still
/// searched there, not at its own lower end.
#[test]
fn the_self_check_still_finds_the_in_window_witness() {
    let model = witness(&above_probe(5, 6));
    assert_eq!(model.get("A"), Some(&SmtValue::Int(6)));
    assert_eq!(model.get("B"), Some(&SmtValue::Int(3)));

    let model = witness(&above_probe(-500, 100));
    assert_eq!(model.get("A"), Some(&SmtValue::Int(100)));
}

/// Crossed bounds leave the range empty. In the self-check the query repeats
/// the bounds, so no window could find a witness there; with the bounds in the
/// body alone (as the empty-domain tests split them) only the empty range
/// keeps `A = 150` from being tried.
#[test]
fn crossed_bounds_still_answer_none() {
    assert_eq!(self_check(&crossed_probe()), None);

    let body = ChcExpr::and_all(vec![
        ChcExpr::ge(var("A"), ChcExpr::int(150)),
        ChcExpr::le(var("A"), ChcExpr::int(120)),
    ]);
    let query = ChcExpr::and_all(vec![
        ChcExpr::eq(var("A"), ChcExpr::int(150)),
        ChcExpr::eq(var("B"), ChcExpr::int(3)),
    ]);
    assert_eq!(transition_check(&body, &ChcExpr::Bool(true), &query), None);
}

/// A variable whose name a query variable of another sort shares keeps the
/// centred clamp: the evaluator's sort-aware lookup falls back to the plain
/// entry, so `J:Bool` reads `J:Int`'s value, and an anchored `J:Int = 150`
/// would make `J:Bool` neither `true` nor `false`, a witness no Bool value
/// gives. The query below has no model.
#[test]
fn a_name_shared_across_sorts_keeps_the_centred_clamp() {
    let j_bool = ChcExpr::var(ChcVar::new("J", ChcSort::Bool));
    let query = ChcExpr::and_all(vec![
        ChcExpr::ge(var("J"), ChcExpr::int(150)),
        ChcExpr::not(ChcExpr::eq(j_bool.clone(), ChcExpr::Bool(true))),
        ChcExpr::not(ChcExpr::eq(j_bool, ChcExpr::Bool(false))),
    ]);
    assert_eq!(self_check(&query), None);
}

/// Nine variables, one bounded beyond ±100 at every position, on both sides,
/// the other eight in `0..=1`: the anchored range is no longer empty, the
/// domain (2^8 * 201 assignments) goes to sampling, and its boundary phase
/// finds the pinned witness within the limit (the empty range of 2026-10-31
/// answered `None` here; the hang it fixed must not come back).
#[test]
fn an_anchored_range_in_a_sampled_domain_finds_its_witness_within_the_limit() {
    for at in 0..9 {
        for (bound, pinned) in [
            (ChcExpr::ge(var(&format!("v{at}")), ChcExpr::int(150)), 150),
            (
                ChcExpr::le(var(&format!("v{at}")), ChcExpr::int(-150)),
                -150,
            ),
        ] {
            let mut conjuncts = vec![bound];
            for i in (0..9).filter(|i| *i != at) {
                conjuncts.push(ChcExpr::ge(var(&format!("v{i}")), ChcExpr::int(0)));
                conjuncts.push(ChcExpr::le(var(&format!("v{i}")), ChcExpr::int(1)));
            }
            let body = ChcExpr::and_all(conjuncts);
            let query = ChcExpr::and_all(
                (0..9)
                    .map(|i| {
                        let value = if i == at { pinned } else { 0 };
                        ChcExpr::eq(var(&format!("v{i}")), ChcExpr::int(value))
                    })
                    .collect::<Vec<_>>(),
            );
            let (tx, rx) = mpsc::channel();
            let (b, q) = (body.clone(), query.clone());
            std::thread::spawn(move || {
                let _ = tx.send(transition_check(&b, &ChcExpr::Bool(true), &q));
            });
            let answer = rx
                .recv_timeout(Duration::from_secs(60))
                .unwrap_or_else(|_| panic!("position {at} must answer within the limit"));
            let model = answer
                .unwrap_or_else(|| panic!("position {at}: v{at} = {pinned} lies in its window"));
            assert_eq!(evaluate_expr(&query, &model), Some(SmtValue::Bool(true)));
            assert_eq!(
                model.get(&format!("v{at}")),
                Some(&SmtValue::Int(i128::from(pinned)))
            );
        }
    }
}

/// The probe end to end: `verify_model` and `verify_model_fast` reject the
/// model a forced false-UNSAT would otherwise certify.
#[test]
fn both_verifiers_reject_a_forced_false_unsat_beyond_the_centred_window() {
    assert_eq!(
        verdicts_under_forced_unsat(above_probe(150, 150)),
        (false, false),
        "A >= 150 /\\ A = 150 /\\ B = 3 is satisfiable"
    );
    assert_eq!(
        verdicts_under_forced_unsat(below_probe(-150, -150)),
        (false, false),
        "A <= -150 /\\ A = -150 /\\ B = 3 is satisfiable"
    );
}

#[test]
fn both_verifiers_still_reject_the_in_window_twin() {
    assert_eq!(
        verdicts_under_forced_unsat(above_probe(5, 6)),
        (false, false)
    );
    assert_eq!(
        verdicts_under_forced_unsat(above_probe(-500, 100)),
        (false, false)
    );
}

/// Crossed bounds: the clause body has no model, the forced UNSAT is right,
/// and both verifiers accept, as before. The body repeats the bounds, so the
/// exact evaluator refuses every assignment whatever the window.
#[test]
fn both_verifiers_still_accept_crossed_bounds() {
    assert_eq!(verdicts_under_forced_unsat(crossed_probe()), (true, true));
}

/// An Int variable literally named `J!Bool` is read by a Bool variable `J`:
/// with no plain `J` entry, `lookup_model_value` takes the sort-qualified
/// `J!Bool` entry, so `J:Bool` reads the Int value. The query below has no
/// model (`J` equals one of the two complementary comparisons), yet an
/// anchored `J!Bool = 150` makes `J:Bool` neither, which the evaluator
/// accepts. Such a variable keeps the centred clamp (review of 90b40b3908,
/// P1b); its in-window form (`>= 5`) predates the anchored window.
#[test]
fn an_int_named_like_a_sort_qualified_key_keeps_the_centred_clamp() {
    let j_bool = ChcExpr::var(ChcVar::new("J", ChcSort::Bool));
    let query = ChcExpr::and_all(vec![
        ChcExpr::ge(var("J!Bool"), ChcExpr::int(150)),
        ChcExpr::not(ChcExpr::eq(
            j_bool.clone(),
            ChcExpr::ge(var("A"), ChcExpr::int(0)),
        )),
        ChcExpr::not(ChcExpr::eq(j_bool, ChcExpr::lt(var("A"), ChcExpr::int(0)))),
    ]);
    assert_eq!(self_check(&query), None);
}

/// A valid model whose clause body has no model only by parity, its range
/// anchored on a non-empty window: the window's 201 values are evaluated and
/// none holds, and both verifiers accept with the real SMT answer (review of
/// 90b40b3908, P7; the crossed-bounds case never reaches evaluation).
#[test]
fn a_valid_model_is_accepted_through_a_non_empty_anchored_window() {
    let parity = |bound: ChcExpr, odd: i64| {
        ChcExpr::and_all(vec![
            bound,
            ChcExpr::eq(ChcExpr::add(var("A"), var("A")), ChcExpr::int(odd)),
        ])
    };
    for body in [
        parity(ChcExpr::ge(var("A"), ChcExpr::int(150)), 301),
        parity(ChcExpr::le(var("A"), ChcExpr::int(-150)), -301),
        parity(ChcExpr::ge(var("A"), ChcExpr::int(5)), 11),
    ] {
        assert_eq!(self_check(&body), None, "{body}");

        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(inv, vec![var("A"), var("B")])], Some(body.clone())),
            ClauseHead::False,
        ));
        let mut model = InvariantModel::new();
        model.set(
            inv,
            PredicateInterpretation::new(vec![int_var("A"), int_var("B")], ChcExpr::Bool(true)),
        );
        let config = PdrConfig {
            verbose: false,
            ..PdrConfig::default()
        };
        let mut full = PdrSolver::new(problem.clone(), config.clone());
        assert!(full.verify_model(&model), "verify_model, {body}");
        let mut fast = PdrSolver::new(problem, config);
        assert!(
            fast.verify_model_fast(&model, Instant::now() + Duration::from_secs(60)),
            "verify_model_fast, {body}"
        );
    }
}

/// `not (A >= i64::MIN)` holds for no i64 value; bound extraction saturates
/// its upper bound to `i64::MIN`, so the range is `MIN..=MIN`, one value
/// outside the conjunct. The query still carries the conjunct, so that value
/// is refused and the check finds nothing (review of 90b40b3908, finding 4).
#[test]
fn a_saturated_bound_admits_a_value_the_query_still_refuses() {
    let body = ChcExpr::not(ChcExpr::ge(var("A"), ChcExpr::int(i64::MIN)));
    assert_eq!(self_check(&body), None);
}
