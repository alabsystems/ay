// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::time::{Duration, Instant};

use ay_bindings::{ExprValue, RoundingMode};
use ay_chc::{ChcExpr, ChcOp, ChcSort, ClauseHead, HornClause};
use ay_core::original_query::{QueryError, StopReason};

use super::*;

mod admission;
mod guards;
mod numeric;
mod raw_results;
mod raw_words;
mod rounded;
mod semantics;
mod source_controls;
mod truncating;
mod units;

const WORK: u64 = 200_000_000_000;
const BYTES: u64 = 800_000_000_000;

fn with_owner<T>(run: impl FnOnce(&mut WorkBudget<'_>) -> T) -> T {
    with_owner_until(|budget, _end| run(budget))
}

fn with_owner_until<T>(run: impl FnOnce(&mut WorkBudget<'_>, Instant) -> T) -> T {
    let end = Instant::now() + Duration::from_secs(20);
    let mut work = WORK;
    let mut bytes = BYTES;
    let mut admission = |w: usize, b: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        work = work.checked_sub(w as u64).ok_or(QueryError::Exhausted)?;
        bytes = bytes.checked_sub(b as u64).ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut admission);
    let result = run(&mut budget, end);
    budget.charge(0).unwrap();
    result
}

fn input(width: u32) -> (Expr, ChcVar) {
    let (e, s) = if width == 32 { (8, 24) } else { (11, 53) };
    (
        Expr::var("original_x", crate::Sort::fp(e, s)),
        ChcVar::new("original_x", ChcSort::BitVec(width)),
    )
}

fn relation<'a, 'budget, 'owner>(
    roots: &'a [Expr],
    bindings: &'a [FpExprInputBinding<'a>],
    problem: &'a ChcProblem,
    budget: &'budget mut WorkBudget<'owner>,
) -> FpExprClauseBody<'a, 'budget, 'owner> {
    lower_fp_expr_clause(roots, bindings, problem, budget)
        .unwrap()
        .into_body(ClauseBody::empty())
        .unwrap()
}

#[test]
fn complete_data_moves_into_a_genuine_body_without_changing_predicate_arguments() {
    let (x, target) = input(32);
    let roots = [x.clone().fp_is_normal(), x.clone().fp_is_positive()];
    let bindings = [FpExprInputBinding {
        source: &x,
        target: &target,
    }];
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("original_p", vec![ChcSort::BitVec(32)]);
    let old = ClauseBody::new(
        vec![(p, vec![ChcExpr::Var(target.clone())])],
        Some(ChcExpr::Bool(true)),
    );
    with_owner(|budget| {
        let output = lower_fp_expr_clause(&roots, &bindings, &problem, budget).unwrap();
        assert!(std::ptr::eq(output.source().roots(), roots.as_slice()));
        let attached = output.into_body(old).unwrap();
        assert_eq!(attached.body().predicates.len(), 1);
        assert_eq!(
            attached.body().predicates[0].1,
            [ChcExpr::Var(target.clone())]
        );
        let (body, source) = attached.into_parts().unwrap();
        assert!(std::ptr::eq(source.namespace(), &raw const problem));
        assert!(std::ptr::eq(source.bindings()[0].source, &raw const x));
        let clause = HornClause::new(
            body,
            ClauseHead::Predicate(p, vec![ChcExpr::Var(target.clone())]),
        );
        assert!(matches!(clause.head,ClauseHead::Predicate(_,ref args) if args.len()==1));
        assert!(clause.body.constraint.is_some());
        assert!(!clause.body.predicates[0]
            .1
            .iter()
            .any(|a| matches!(a,ChcExpr::Var(v) if v.name.starts_with("__ay_fp_bits_"))));
        drop(clause);
        budget.charge(0).unwrap();
    });
}

#[test]
fn repeated_ordered_roots_and_stable_expr_inputs_survive_temporary_arena_cleanup() {
    let (x, target) = input(64);
    let first = x.clone().fp_is_zero();
    let second = x.clone().fp_is_nan();
    let roots = [first.clone(), second.clone(), first];
    let bindings = [FpExprInputBinding {
        source: &x,
        target: &target,
    }];
    let problem = ChcProblem::new();
    with_owner(|budget| {
        let output = relation(&roots, &bindings, &problem, budget);
        assert_eq!(output.source().roots().len(), 3);
        assert!(std::ptr::eq(
            output.source().roots()[0].value(),
            roots[2].value()
        ));
        assert!(
            matches!(output.source().bindings()[0].source.value(),ExprValue::Var { name } if name=="original_x")
        );
        let ChcExpr::Op(ChcOp::And, whole) = output.body().constraint.as_ref().unwrap() else {
            panic!()
        };
        let ChcExpr::Op(ChcOp::And, entries) = whole[0].as_ref() else {
            panic!()
        };
        assert!(entries.len() >= 64 + 3);
    });
}

#[test]
fn raw_fp_words_are_linked_in_exact_lsb_order_after_the_complete_move() {
    for width in [32, 64] {
        let (x, target) = input(width);
        let roots = [x.clone().fp_is_normal()];
        let bindings = [FpExprInputBinding {
            source: &x,
            target: &target,
        }];
        let problem = ChcProblem::new();
        with_owner(|budget| {
            let _bits = {
                let attached = relation(&roots, &bindings, &problem, budget);
                let (body, _source) = attached.into_parts().unwrap();
                let ChcExpr::Op(ChcOp::And, outer) = body.constraint.as_ref().unwrap() else {
                    panic!()
                };
                let ChcExpr::Op(ChcOp::And, entries) = outer[0].as_ref() else {
                    panic!()
                };
                budget.admit(4096, 4096).unwrap();
                let mut bits = Vec::new();
                for entry in entries.iter().rev().take(width as usize).rev() {
                    budget.charge(256).unwrap();
                    let ChcExpr::Op(ChcOp::Eq, pair) = entry.as_ref() else {
                        panic!()
                    };
                    let ChcExpr::Op(ChcOp::Eq, value) = pair[1].as_ref() else {
                        panic!()
                    };
                    let ChcExpr::Op(ChcOp::BvExtract(hi, lo), word) = value[0].as_ref() else {
                        panic!()
                    };
                    assert_eq!(hi, lo);
                    assert_eq!(word[0].as_ref(), &ChcExpr::Var(target.clone()));
                    bits.push(*lo);
                }
                assert_eq!(bits, (0..width).collect::<Vec<_>>());
                drop(body);
                bits
            };
            budget.charge(0).unwrap();
        });
    }
}

#[test]
fn separate_complete_encodings_cannot_alias_auxiliaries_in_one_body() {
    let (x, target) = input(32);
    let roots = [x.clone().fp_is_normal()];
    let bindings = [FpExprInputBinding {
        source: &x,
        target: &target,
    }];
    let problem = ChcProblem::new();
    with_owner(|budget| {
        let first = relation(&roots, &bindings, &problem, budget);
        let (body, _) = first.into_parts().unwrap();
        let second = lower_fp_expr_clause(&roots, &bindings, &problem, budget).unwrap();
        assert!(matches!(
            second.into_body(body),
            Err(FpAdapterError::Invalid(_))
        ));
    });
}
