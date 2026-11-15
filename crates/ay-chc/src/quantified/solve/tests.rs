// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ntest::timeout;

use super::*;
use crate::quantified::{QuantifiedHornClause, UniversalPremise};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

const SOLVE_BUDGET: Duration = Duration::from_secs(60);
const TERM_BUDGET: usize = 128 * 1024 * 1024;

#[derive(Clone, Copy)]
enum FillPremise {
    Present,
    Missing,
}

#[derive(Clone, Copy)]
enum Query {
    FilledSuffix,
    ShiftedFill,
    OutsideSuffix,
}

fn op(operator: ChcOp, left: ChcExpr, right: ChcExpr) -> ChcExpr {
    ChcExpr::Op(operator, vec![Arc::new(left), Arc::new(right)])
}

/// Growth specialization of MODEL_CHECKER_CONSUMER 22278991c4d8e731's Vec resize encoding
/// (codegen_call_vec_ops/resize.rs:269–300). The 32 ground hints are entailed
/// by the retained forall; j>=32 deliberately excludes all of them.
fn resize(premise: FillPremise, query: Query) -> QuantifiedChcProblem {
    let key = ChcSort::BitVec(64);
    let value = ChcSort::BitVec(8);
    let array = ChcSort::Array(Box::new(key.clone()), Box::new(value.clone()));
    let mut declarations = ChcProblem::new();
    let relation = declarations.declare_predicate(
        "R",
        vec![array.clone(), key.clone(), key.clone(), value.clone()],
    );
    let a = ChcExpr::var(ChcVar::new("a", array.clone()));
    let b = ChcExpr::var(ChcVar::new("b", array));
    let old = ChcExpr::var(ChcVar::new("old", key.clone()));
    let new = ChcExpr::var(ChcVar::new("new", key.clone()));
    let fill = ChcExpr::var(ChcVar::new("fill", value));
    let binder = ChcVar::new("i", key.clone());
    let i = ChcExpr::var(binder.clone());
    let j = ChcExpr::var(ChcVar::new("j", key));
    let arguments = vec![b.clone(), old.clone(), new.clone(), fill.clone()];

    let prefix = ChcExpr::implies(
        op(ChcOp::BvULt, i.clone(), old.clone()),
        ChcExpr::eq(
            ChcExpr::select(b.clone(), i.clone()),
            ChcExpr::select(a, i.clone()),
        ),
    );
    let suffix = ChcExpr::implies(
        ChcExpr::and(
            op(ChcOp::BvUGe, i.clone(), old.clone()),
            op(ChcOp::BvULt, i.clone(), new.clone()),
        ),
        ChcExpr::eq(ChcExpr::select(b.clone(), i), fill.clone()),
    );
    let matrix = match premise {
        FillPremise::Present => ChcExpr::and(prefix, suffix),
        FillPremise::Missing => prefix,
    };
    let initiation = QuantifiedHornClause::new(
        HornClause::new(
            ClauseBody::constraint(op(ChcOp::BvULt, old.clone(), new.clone())),
            ClauseHead::Predicate(relation, arguments.clone()),
        ),
        vec![UniversalPremise::new(binder, matrix)],
    );
    let range = match query {
        Query::OutsideSuffix => op(ChcOp::BvUGe, j.clone(), new),
        Query::FilledSuffix | Query::ShiftedFill => ChcExpr::and(
            op(ChcOp::BvUGe, j.clone(), old),
            op(ChcOp::BvULt, j.clone(), new),
        ),
    };
    let expected = match query {
        Query::ShiftedFill => op(ChcOp::BvAdd, fill, ChcExpr::BitVec(1, 8)),
        Query::FilledSuffix | Query::OutsideSuffix => fill,
    };
    let query = QuantifiedHornClause::new(
        HornClause::query(ClauseBody::new(
            vec![(relation, arguments)],
            Some(ChcExpr::and_all([
                range,
                op(ChcOp::BvUGe, j.clone(), ChcExpr::BitVec(32, 64)),
                ChcExpr::ne(ChcExpr::select(b, j), expected),
            ])),
        )),
        Vec::new(),
    );
    QuantifiedChcProblem::new(declarations, vec![initiation, query]).expect("typed resize source")
}

#[test]
fn resize_source_retains_symbolic_lengths_and_local_bv64_index() {
    let problem = resize(FillPremise::Present, Query::FilledSuffix);
    let source = problem.source_smtlib();
    assert!(source.contains("(forall ((i (_ BitVec 64)))"));
    assert!(source.contains("(bvult i old)"));
    assert!(source.contains("(bvuge i old)"));
    assert!(source.contains("(bvult i new)"));
    assert!(source.contains("(select a i)"));
    assert!(source.contains("(bvuge j (_ bv32 64))"));
    assert_eq!(problem.source_problem().predicates()[0].arg_sorts.len(), 4);
    assert_eq!(problem.source_problem().clauses().len(), 2);
    assert_eq!(problem.premises()[0].len(), 1);
    assert!(problem.premises()[1].is_empty());
}

#[test]
#[timeout(180000)]
fn symbolic_resize_beyond_ground_hints_seals_original_source() {
    let problem = resize(FillPremise::Present, Query::FilledSuffix);
    let cancellation = CancellationToken::new();
    let QuantifiedChcResult::Safe(evidence) =
        problem.solve(SOLVE_BUDGET, Some(TERM_BUDGET), &cancellation)
    else {
        panic!("query-local BV64 probe must establish symbolic suffix fill");
    };
    assert_eq!(evidence.source_smtlib(), problem.source_smtlib());
    let obligations = evidence.replay_obligations();
    assert_eq!(obligations.len(), 2);
    assert_eq!(obligations[0].clause_index, 0);
    assert_eq!(obligations[1].clause_index, 1);
    assert!(obligations[0]
        .smtlib
        .contains("(forall ((i (_ BitVec 64)))"));
    assert!(obligations[0].smtlib.contains("(select a i)"));
    assert!(obligations[0].smtlib.contains("(bvult i new)"));
    assert!(evidence.recheck(&problem, SOLVE_BUDGET, &cancellation));

    let missing_fill = resize(FillPremise::Missing, Query::FilledSuffix);
    let different_query = resize(FillPremise::Present, Query::ShiftedFill);
    assert!(!evidence.recheck(&missing_fill, SOLVE_BUDGET, &cancellation));
    assert!(!evidence.recheck(&different_query, SOLVE_BUDGET, &cancellation));
    cancellation.cancel();
    assert!(!evidence.recheck(&problem, SOLVE_BUDGET, &cancellation));
}

#[test]
#[timeout(180000)]
fn reachable_resize_errors_never_become_safe_or_unvalidated_unsafe() {
    // Concrete countermodels exist: old=32,new=33,j=32,fill=0, both arrays
    // constantly zero for ShiftedFill; missing fill permits b[32]=1. For
    // OutsideSuffix use j=33,b[33]=1. Only complete original-path SAT may now
    // return sealed Unsafe; finite-instance SAT still cannot justify it.
    for (premise, query) in [
        (FillPremise::Present, Query::ShiftedFill),
        (FillPremise::Missing, Query::FilledSuffix),
        (FillPremise::Present, Query::OutsideSuffix),
    ] {
        assert!(!matches!(
            resize(premise, query).solve(
                Duration::from_secs(30),
                Some(TERM_BUDGET),
                &CancellationToken::new(),
            ),
            QuantifiedChcResult::Safe(_)
        ));
    }
}

#[test]
fn cancelled_zero_overflow_and_expired_parent_decline_before_search() {
    let problem = resize(FillPremise::Present, Query::FilledSuffix);
    let cancellation = CancellationToken::new();
    for budget in [Duration::ZERO, Duration::MAX] {
        assert!(matches!(
            problem.solve(budget, None, &cancellation),
            QuantifiedChcResult::Unknown
        ));
    }
    cancellation.cancel();
    assert!(matches!(
        problem.solve(SOLVE_BUDGET, None, &cancellation),
        QuantifiedChcResult::Unknown
    ));
    let _parent = ScopedSmtDeadline::install_until(Instant::now());
    assert!(matches!(
        problem.solve(SOLVE_BUDGET, None, &CancellationToken::new()),
        QuantifiedChcResult::Unknown
    ));
}

#[test]
fn term_budget_cannot_admit_context_or_widen_parent() {
    assert_eq!(tighter_budget(None, None), None);
    assert_eq!(tighter_budget(Some(10), None), Some(10));
    assert_eq!(tighter_budget(None, Some(20)), Some(20));
    assert_eq!(tighter_budget(Some(10), Some(20)), Some(10));
    assert_eq!(tighter_budget(Some(20), Some(10)), Some(10));
    let problem = resize(FillPremise::Present, Query::FilledSuffix);
    let _parent = SmtContext::scoped_thread_term_memory_budget(Some(0));
    assert!(matches!(
        problem.solve(SOLVE_BUDGET, Some(TERM_BUDGET), &CancellationToken::new()),
        QuantifiedChcResult::Unknown
    ));
}
