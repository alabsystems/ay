// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::sync::atomic::{AtomicBool, Ordering};

use crate::ClauseHead;
use ay_core::resource::{enter_check_stop, ChildSpec, Guard, NodeLabel};

use super::*;

#[test]
fn symbolic_and_ill_typed_arrays_do_not_supply_constants() {
    let index = ChcExpr::var(ChcVar::new("i", ChcSort::BitVec(32)));
    let value = ChcExpr::var(ChcVar::new("b", ChcSort::Bool));
    let cases = [
        store(array(32, false), index, ChcExpr::Bool(true)),
        store(array(32, false), ChcExpr::BitVec(0, 32), value),
        store(array(32, false), ChcExpr::BitVec(0, 8), ChcExpr::Bool(true)),
        store(array(32, false), ChcExpr::BitVec(0, 32), ChcExpr::Int(1)),
        ChcExpr::ConstArray(ChcSort::BitVec(32), Arc::new(ChcExpr::Int(0))),
        ChcExpr::ConstArray(ChcSort::BitVec(32), Arc::new(array(1, false))),
        array(0, false),
        array(129, false),
    ];
    for expr in cases {
        assert_eq!(
            evaluate(&expr, &Pins::default(), &mut Budget::new(), 0).expect("bounded decline"),
            None
        );
    }
}

#[test]
fn malformed_array_pin_cannot_establish_vacuity() {
    let mut problem = ChcProblem::new();
    let sort = ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool));
    let pid = problem.declare_predicate("P", vec![sort.clone()]);
    let var = ChcExpr::var(ChcVar::new("a", sort));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], Some(ChcExpr::eq(var.clone(), array(8, true)))),
        ClauseHead::Predicate(pid, vec![var.clone()]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(pid, vec![var])], None),
        ClauseHead::False,
    ));
    let original = format!("{:?}", problem.clauses());
    let result = Box::new(ConstantPropagator::new()).transform(problem);
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
    assert_eq!(format!("{:?}", result.problem.clauses()), original);
}

#[test]
fn depth_refusal_returns_the_unchanged_original_problem() {
    let mut expr = array(32, false);
    for index in 0..=ground::MAX_DEPTH {
        expr = store(
            expr,
            ChcExpr::BitVec(index as u128, 32),
            ChcExpr::Bool(true),
        );
    }
    let mut problem = ChcProblem::new();
    let pid = problem.declare_predicate(
        "P",
        vec![ChcSort::Array(
            Box::new(ChcSort::BitVec(32)),
            Box::new(ChcSort::Bool),
        )],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(pid, vec![expr]),
    ));
    let original = format!("{:?}", problem.clauses());
    let result = Box::new(ConstantPropagator::new()).transform(problem);
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
    assert_eq!(format!("{:?}", result.problem.clauses()), original);
}

#[test]
fn array_map_storage_refusal_is_sticky() {
    let mut array = Arc::new(BoolArray::constant(32, false).expect("width"));
    let mut budget = Budget::new();
    for index in 0..ground::MAX_ARRAY_ENTRIES {
        array = array
            .store(index as u128, true, &mut budget)
            .expect("within entry cap");
    }
    assert!(array
        .store(ground::MAX_ARRAY_ENTRIES as u128, true, &mut budget)
        .is_err());
    assert!(
        budget.charge(0).is_err(),
        "a refused operation cannot resume"
    );
}

#[test]
fn work_and_output_allowances_are_cumulative_and_never_renewed() {
    let mut work = Budget::new();
    work.charge(work.remaining())
        .expect("exact last work units");
    assert!(work.charge(1).is_err());
    assert!(work.charge(0).is_err());
    let mut output = Budget::new();
    output
        .reserve_output(600_000)
        .expect("first output allocation");
    output
        .reserve_output(400_000)
        .expect("second output allocation");
    assert!(output.reserve_output(1).is_err());
    assert!(output.reserve_output(0).is_err());
}

#[test]
fn transient_original_callback_refusal_survives_callback_reset_and_scope_change() {
    let flag = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&flag);
    let outer = enter_check_stop(Arc::new(move || observed.load(Ordering::SeqCst)));
    let mut budget = Budget::new();
    budget.charge(1).expect("open owner");
    drop(outer);
    let _replacement = enter_check_stop(Arc::new(|| false));
    flag.store(true, Ordering::SeqCst);
    assert!(
        budget.charge(1).is_err(),
        "original callback cannot be hidden by TLS replacement"
    );
    flag.store(false, Ordering::SeqCst);
    assert!(budget.charge(0).is_err(), "observed refusal stays terminal");
}

#[test]
fn a_caught_owner_callback_panic_cannot_reopen_the_allowance() {
    let once = Arc::new(AtomicBool::new(true));
    let observed = Arc::clone(&once);
    let _owner = enter_check_stop(Arc::new(move || {
        assert!(
            !observed.swap(false, Ordering::SeqCst),
            "test callback panic"
        );
        false
    }));
    let mut budget = Budget::new();
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| budget.charge(1))).is_err());
    assert!(budget.charge(0).is_err());
}

#[test]
fn original_guard_cancellation_is_retained_after_tls_scope_changes() {
    let flag = Arc::new(AtomicBool::new(false));
    let owner =
        Guard::root_child(ChildSpec::new(NodeLabel::Check).with_external(Arc::clone(&flag)));
    let entered = owner.enter();
    let mut budget = Budget::new();
    budget.charge(1).expect("open tree");
    drop(entered);
    let other = Guard::new();
    let _replacement = other.enter();
    flag.store(true, Ordering::SeqCst);
    assert!(
        budget.charge(0).is_err(),
        "the original tree remains authoritative"
    );
    flag.store(false, Ordering::SeqCst);
    assert!(budget.charge(0).is_err());
}

#[test]
fn cancelled_transform_returns_original_and_no_strengthened_certificate() {
    let problem = multi_block("#x00000043");
    let original = format!("{:?}", problem.clauses());
    let _stopped = enter_check_stop(Arc::new(|| true));
    let result = Box::new(ConstantPropagator::new()).transform(problem);
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
    assert_eq!(format!("{:?}", result.problem.clauses()), original);
}

#[test]
fn long_names_are_charged_before_even_an_existing_pin_lookup() {
    let var = ChcVar::new("v".repeat(128), ChcSort::Bool);
    let mut pins = Pins::default();
    pins.insert(var.clone(), Value::Scalar(ChcExpr::Bool(true)));
    let mut budget = Budget::new();
    budget
        .charge(budget.remaining() - 64)
        .expect("leave less than the name cost");
    assert!(evaluate(&ChcExpr::var(var), &pins, &mut budget, 0).is_err());
    assert!(budget.charge(0).is_err());
}

#[test]
fn rewrite_depth_is_not_a_silently_accepted_partial_node_count() {
    let var = ChcVar::new("x", ChcSort::Bool);
    let mut constraint = ChcExpr::var(var.clone());
    for _ in 0..ground::MAX_DEPTH {
        constraint = ChcExpr::Op(ChcOp::Not, vec![Arc::new(constraint)]);
    }
    let clause = HornClause::new(ClauseBody::new(vec![], Some(constraint)), ClauseHead::False);
    let mut budget = Budget::new();
    assert!(rewrite_budget::reserve(&clause, &[(var, ChcExpr::Bool(true))], &mut budget).is_err());
    assert!(budget.charge(0).is_err());
}

#[test]
fn original_guard_work_is_debited_after_tls_replacement_and_refusal_is_terminal() {
    let original = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(10)));
    let entered = original.enter();
    let mut budget = Budget::new();
    budget.charge(3).expect("first original debit");
    drop(entered);
    let replacement = Guard::new();
    let _entered = replacement.enter();
    budget.reserve_output(6).expect("same original allowance");
    assert_eq!(original.ticks(), 9);
    assert_eq!(replacement.ticks(), 0);
    assert!(
        budget.charge(1).is_err(),
        "reaching the original limit stops"
    );
    let stopped_at = original.ticks();
    assert_eq!(stopped_at, 10);
    assert!(budget.charge(0).is_err());
    assert!(budget.charge(1).is_err());
    assert_eq!(original.ticks(), stopped_at, "no work after refusal");
}

#[test]
fn discovery_justification_serialization_and_rewrite_share_original_work() {
    let problem = multi_block("#x00000043");
    let original = Guard::new();
    let _entered = original.enter();
    let mut budget = Budget::new();
    let initial = budget.remaining();
    let constants = analysis::constants(&problem, &mut budget).expect("complete analysis");
    assert!(!constants.is_empty());
    let after_analysis = original.ticks();
    assert_eq!(after_analysis, (initial - budget.remaining()) as u64);
    let mut rewrites = 0;
    for clause in problem.clauses() {
        let subst = rewrite_budget::substitutions(clause, &constants, &mut budget)
            .expect("substitution admission");
        if !subst.is_empty() {
            rewrite_budget::reserve(clause, &subst, &mut budget).expect("rewrite admission");
            rewrites += 1;
        }
    }
    assert!(rewrites > 0);
    assert!(original.ticks() > after_analysis);
    assert_eq!(original.ticks(), (initial - budget.remaining()) as u64);
}

#[test]
fn full_transform_respects_exact_and_short_original_count_boundaries() {
    let problem = multi_block("#x00000043");
    let run = |limit| {
        let owner = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(limit));
        let _entered = owner.enter();
        let result = Box::new(ConstantPropagator::new()).transform(problem.clone());
        (result, owner.ticks())
    };
    let (healthy, work) = run(None);
    assert!(!healthy
        .back_translator
        .transform_memory()
        .is_identity_grade());
    assert!(work > 1);
    let (enough, same_work) = run(Some(work + 1));
    assert!(!enough
        .back_translator
        .transform_memory()
        .is_identity_grade());
    assert_eq!(same_work, work);
    for limit in [1, work / 2, work] {
        let (refused, _) = run(Some(limit));
        assert!(refused
            .back_translator
            .transform_memory()
            .is_identity_grade());
        assert_eq!(
            refused.problem.normalized_input(),
            problem.normalized_input()
        );
    }
}
