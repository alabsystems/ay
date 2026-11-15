// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::*;
use crate::quantified::{QuantifiedHornClause, UniversalPremise};
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ntest::timeout;

const TERM_BUDGET: usize = 128 * 1024 * 1024;

#[derive(Clone, Copy)]
enum IndexRelation {
    Independent,
    ReversedBinderOrder,
    Diagonal,
}

fn op(operation: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operation, args.into_iter().map(Arc::new).collect())
}

fn source(relation: IndexRelation) -> QuantifiedChcProblem {
    // Synthetic prerequisite for nested collection probes, not an exported MC
    // harness: rank-one arrays isolate independent binder instantiation from
    // the separate nested-cell observation transport.
    let key = ChcSort::BitVec(64);
    let value = ChcSort::BitVec(8);
    let array = ChcSort::Array(Box::new(key.clone()), Box::new(value.clone()));
    let a = ChcExpr::Var(ChcVar::new("a", array.clone()));
    let b = ChcExpr::Var(ChcVar::new("b", array.clone()));
    let fill = ChcExpr::Var(ChcVar::new("fill", value.clone()));
    let i = ChcVar::new("i", key.clone());
    let j = ChcVar::new("j", key.clone());
    let k = ChcExpr::Var(ChcVar::new("k", key));
    let right_index = match relation {
        IndexRelation::Diagonal => i.clone(),
        _ => j.clone(),
    };
    let matrix = op(
        ChcOp::Eq,
        vec![
            ChcExpr::select(a.clone(), ChcExpr::Var(i.clone())),
            ChcExpr::select(b.clone(), ChcExpr::Var(right_index)),
        ],
    );
    let premise = match relation {
        IndexRelation::Independent => UniversalPremise::with_binders(vec![i, j], matrix).unwrap(),
        IndexRelation::ReversedBinderOrder => {
            UniversalPremise::with_binders(vec![j, i], matrix).unwrap()
        }
        IndexRelation::Diagonal => UniversalPremise::new(i, matrix),
    };
    let arguments = vec![a.clone(), b.clone(), fill.clone()];
    let mut declarations = ChcProblem::new();
    let predicate = declarations.declare_predicate("P", vec![array.clone(), array, value]);
    let initiation = HornClause::new(
        ClauseBody::constraint(op(
            ChcOp::Eq,
            vec![ChcExpr::select(b, ChcExpr::BitVec(0, 64)), fill.clone()],
        )),
        ClauseHead::Predicate(predicate, arguments.clone()),
    );
    let query = HornClause::query(ClauseBody::new(
        vec![(predicate, arguments)],
        Some(op(
            ChcOp::And,
            vec![
                op(ChcOp::BvUGe, vec![k.clone(), ChcExpr::BitVec(32, 64)]),
                op(ChcOp::Ne, vec![ChcExpr::select(a, k), fill]),
            ],
        )),
    ));
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(initiation, vec![premise]),
            QuantifiedHornClause::new(query, vec![]),
        ],
    )
    .unwrap()
}

#[test]
#[timeout(180000)]
fn independent_bv64_indices_reach_public_safety_and_fresh_original_replay() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(60);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let source = source(IndexRelation::Independent);
    let token = CancellationToken::new();
    let group = "(forall ((i (_ BitVec 64)) (j (_ BitVec 64)))";
    assert!(source.source_smtlib().contains(group));
    assert!(source
        .source_smtlib()
        .contains("(= (select a i) (select b j))"));
    assert!(source.source_smtlib().contains("(bvuge k (_ bv32 64))"));
    assert_eq!(source.source_problem().predicates()[0].arg_sorts.len(), 3);
    let QuantifiedChcResult::Safe(evidence) =
        source.solve(Duration::from_secs(30), Some(TERM_BUDGET), &token)
    else {
        panic!("independent (i,j) instances must connect a[k] to b[0]=fill");
    };
    assert_eq!(evidence.source_smtlib(), source.source_smtlib());
    let obligations = evidence.replay_obligations();
    assert_eq!(obligations.len(), 2);
    assert_eq!(obligations[0].clause_index, 0);
    assert_eq!(obligations[1].clause_index, 1);
    assert!(obligations[0].smtlib.contains(group));
    assert!(obligations[0]
        .smtlib
        .contains("(= (select a i) (select b j))"));
    assert!(evidence.recheck(
        &source,
        deadline.saturating_duration_since(Instant::now()),
        &token
    ));
    for changed in [IndexRelation::Diagonal, IndexRelation::ReversedBinderOrder] {
        let changed = self::source(changed);
        assert_ne!(source.source_smtlib(), changed.source_smtlib());
        assert!(!evidence.recheck(
            &changed,
            deadline.saturating_duration_since(Instant::now()),
            &token
        ));
    }
    assert!(
        Instant::now() < deadline,
        "all positive work shares one original budget"
    );
}

fn assert_diagonal_countermodel(source: &QuantifiedChcProblem) {
    // Identical arrays establish forall i. a[i]=b[i] over the entire BV64
    // domain, but not the off-diagonal a[32]=b[0] needed by the positive case.
    let array = SmtValue::ArrayMap {
        default: Box::new(SmtValue::BitVec(7, 8)),
        entries: vec![(SmtValue::BitVec(32, 64), SmtValue::BitVec(9, 8))],
    };
    let mut env: ay_core::kani_compat::DetHashMap<String, SmtValue> = [
        ("a".to_owned(), array.clone()),
        ("b".to_owned(), array),
        ("fill".to_owned(), SmtValue::BitVec(7, 8)),
        ("k".to_owned(), SmtValue::BitVec(32, 64)),
    ]
    .into_iter()
    .collect();
    let evaluate = crate::expr::evaluate::evaluate_expr;
    assert_eq!(env.get("a"), env.get("b"));
    for index in [0, 1, 31, 32, 33, u64::MAX as u128] {
        env.insert("i".to_owned(), SmtValue::BitVec(index, 64));
        assert_eq!(
            evaluate(source.premises()[0][0].matrix(), &env),
            Some(SmtValue::Bool(true))
        );
    }
    for clause in source.source_problem().clauses() {
        assert_eq!(
            evaluate(clause.body.constraint.as_ref().unwrap(), &env),
            Some(SmtValue::Bool(true))
        );
    }
    let independent = self::source(IndexRelation::Independent);
    env.insert("i".to_owned(), SmtValue::BitVec(32, 64));
    env.insert("j".to_owned(), SmtValue::BitVec(0, 64));
    assert_eq!(
        evaluate(independent.premises()[0][0].matrix(), &env),
        Some(SmtValue::Bool(false))
    );
}

#[test]
#[timeout(180000)]
fn diagonal_only_premise_cannot_certify_an_off_diagonal_query() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(30);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let source = source(IndexRelation::Diagonal);
    assert_eq!(source.premises()[0][0].binder_count(), 1);
    assert_diagonal_countermodel(&source);
    assert!(!matches!(
        source.solve(
            deadline.saturating_duration_since(Instant::now()),
            Some(TERM_BUDGET),
            &CancellationToken::new(),
        ),
        QuantifiedChcResult::Safe(_)
    ));
}
