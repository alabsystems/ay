// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]

use std::sync::Arc;
use std::time::Duration;

use crate::clause::{ClauseBody, ClauseHead, HornClause};
use crate::ic3::solver::{Ic3Result, Ic3Solver};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar};

use super::*;
use crate::ic3_lane::build_latch_layout;

fn op(operator: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operator, args.into_iter().map(Arc::new).collect())
}

fn high_bit_identity_problem(
    width: u32,
    observed_bit: u32,
    init: u128,
    expected_bit: u128,
) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let sort = ChcSort::BitVec(width);
    let pred = problem.declare_predicate("wide", vec![sort.clone()]);
    let value = ChcVar::new("value", sort);
    let value_expr = ChcExpr::var(value);

    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![ChcExpr::BitVec(init, width)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(pred, vec![value_expr.clone()])]),
        ClauseHead::Predicate(pred, vec![value_expr.clone()]),
    ));
    let observed = op(
        ChcOp::BvExtract(observed_bit, observed_bit),
        vec![value_expr.clone()],
    );
    let bad = ChcExpr::ne(observed, ChcExpr::BitVec(expected_bit, 1));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(pred, vec![value_expr])], Some(bad)),
        ClauseHead::False,
    ));
    problem
}

fn bv9_widening_validation_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let sort = ChcSort::BitVec(9);
    let pred = problem.declare_predicate("bounded", vec![sort.clone()]);
    let value = ChcVar::new("value", sort);
    let value_expr = ChcExpr::var(value);
    let limit = ChcExpr::BitVec(256, 9);

    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![ChcExpr::BitVec(0, 9)]),
    ));
    let guard = op(ChcOp::BvULt, vec![value_expr.clone(), limit.clone()]);
    let next = op(
        ChcOp::BvAdd,
        vec![value_expr.clone(), ChcExpr::BitVec(128, 9)],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(pred, vec![value_expr.clone()])], Some(guard)),
        ClauseHead::Predicate(pred, vec![next]),
    ));
    let bad = op(ChcOp::BvUGt, vec![value_expr.clone(), limit]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(pred, vec![value_expr])], Some(bad)),
        ClauseHead::False,
    ));
    problem
}

#[test]
fn widening_sequence_reaches_resource_capped_original_width() {
    let mut bv96 = ChcProblem::new();
    bv96.declare_predicate("p", vec![ChcSort::BitVec(96)]);
    assert_eq!(widening_widths(&bv96), vec![8, 16, 32, 64, 96]);

    let mut mixed = ChcProblem::new();
    mixed.declare_predicate("p", vec![ChcSort::Int, ChcSort::BitVec(12)]);
    assert_eq!(widening_widths(&mixed), vec![8, 16, 32, 64]);

    let mut beyond_kani = ChcProblem::new();
    beyond_kani.declare_predicate("p", vec![ChcSort::BitVec(256)]);
    assert_eq!(
        widening_widths(&beyond_kani),
        vec![8, 16, 32, 64, MAX_EXACT_BV_BLAST_WIDTH]
    );
}

#[test]
fn allocation_reserves_search_validation_and_original_width_time() {
    let total = Duration::from_secs(5);
    for rung_count in 1..=5 {
        let budgets = allocate_rung_budgets(total, rung_count)
            .expect("a five-second caller budget must allocate every supported ladder");
        assert_eq!(budgets.len(), rung_count);
        assert!(
            budgets
                .iter()
                .all(|budget| !budget.search.is_zero() && !budget.validation.is_zero()),
            "every attempted rung needs both search and validation time"
        );
        let allocated = budgets
            .iter()
            .fold(Duration::ZERO, |sum, budget| sum + budget.total());
        assert!(allocated <= total, "the plan must stay under one deadline");
        assert!(
            !budgets.last().unwrap().total().is_zero(),
            "the final/original-width rung needs a fixed nonzero reserve"
        );
    }

    let four_rungs = allocate_rung_budgets(total, 4).unwrap();
    assert!(
        four_rungs[0].total() >= Duration::from_secs(3),
        "the established 8-bit lane must retain most of a short budget"
    );
    assert!(
        four_rungs[3].total() >= Duration::from_millis(250),
        "a true narrow timeout must leave a bounded original-width reserve"
    );
}

#[test]
fn oversized_state_layout_declines_before_cnf_allocation() {
    let at_cap = vec![ChcSort::BitVec(128); MAX_IC3_STATE_LATCHES / 128];
    assert!(
        build_latch_layout(&at_cap, BlastWidth::new(128), false).is_some(),
        "a layout exactly at the deterministic latch cap remains admissible"
    );

    let over_cap = vec![ChcSort::BitVec(128); MAX_IC3_STATE_LATCHES / 128 + 1];
    assert!(
        build_latch_layout(&over_cap, BlastWidth::new(128), false).is_none(),
        "one authored word beyond the latch cap must decline fail-closed"
    );
}

#[test]
fn wider_rung_admits_high_bit_loop_and_validates_original_word() {
    let problem = high_bit_identity_problem(16, 15, 1 << 15, 1);
    assert!(
        lower_loop(&problem, BlastWidth::new(8)).is_none(),
        "the 8-bit abstraction cannot encode an authored bit-15 property"
    );
    assert!(
        lower_loop(&problem, BlastWidth::new(16)).is_some(),
        "the original-width rung must encode bit 15"
    );

    let model = try_prove_chc_loop(&problem, Duration::from_secs(30))
        .expect("the 8->16 ladder should find the original-width invariant");
    let accepted = crate::engines::validate_external_invariant_model(
        &problem,
        &model,
        &crate::PdrConfig::production(false),
    )
    .expect("original-word validation should not error");
    assert!(
        accepted,
        "the returned rung must validate on the BV16 clauses"
    );
}

#[test]
fn rejected_eight_bit_candidate_continues_to_original_width() {
    let problem = bv9_widening_validation_problem();
    let Lowering {
        ts,
        pred,
        params,
        latches,
        orig_header,
    } = lower_loop(&problem, BlastWidth::new(8))
        .expect("the deliberately narrow abstraction should still encode");
    assert!(orig_header.is_none());
    let mut solver = Ic3Solver::new(ts, false);
    let invariant_level = match solver.solve() {
        Ic3Result::Safe { invariant_level } => invariant_level,
        other => panic!("the narrow singleton abstraction should be Safe, got {other:?}"),
    };
    let clauses = solver.invariant_clauses(invariant_level);
    let narrow = back_translate(pred, &params, &latches, &clauses)
        .expect("the narrow invariant should back-translate");
    let narrow_accepted = crate::engines::validate_external_invariant_model(
        &problem,
        &narrow,
        &crate::PdrConfig::production(false),
    )
    .expect("narrow original-word validation should not error");
    assert!(
        !narrow_accepted,
        "the BV8 singleton invariant must be rejected on the original BV9 loop"
    );

    let widened = try_prove_chc_loop(&problem, Duration::from_secs(30))
        .expect("the ladder must continue from rejected BV8 to original-width BV9");
    let widened_accepted = crate::engines::validate_external_invariant_model(
        &problem,
        &widened,
        &crate::PdrConfig::production(false),
    )
    .expect("widened original-word validation should not error");
    assert!(
        widened_accepted,
        "the returned BV9 candidate must pass the original-word gate"
    );
}

#[test]
fn property_above_resource_cap_declines_fail_closed() {
    let problem = high_bit_identity_problem(256, 200, 0, 0);
    assert!(
        try_prove_chc_loop(&problem, Duration::from_secs(2)).is_none(),
        "a property above the capped original width must decline, never prove"
    );
}
