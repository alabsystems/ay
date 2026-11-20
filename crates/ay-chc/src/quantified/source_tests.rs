// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::{ChcOp, ChcSort, ClauseBody, PredicateId};
use std::sync::Arc;

mod arrays;
mod functions;
mod grouped;
mod wide;

fn bv(width: u32) -> ChcSort {
    ChcSort::BitVec(width)
}

fn array() -> ChcSort {
    ChcSort::Array(Box::new(bv(64)), Box::new(bv(8)))
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

fn op(operation: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operation, args.into_iter().map(Arc::new).collect())
}

fn premise(name: &str, width: u32, matrix: ChcExpr) -> UniversalPremise {
    UniversalPremise::new(ChcVar::new(name, bv(width)), matrix)
}

fn query(constraint: ChcExpr, premises: Vec<UniversalPremise>) -> QuantifiedHornClause {
    QuantifiedHornClause::new(
        HornClause::query(ClauseBody::constraint(constraint)),
        premises,
    )
}

fn standalone(premises: Vec<UniversalPremise>) -> ChcResult<QuantifiedChcProblem> {
    QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![query(ChcExpr::Bool(true), premises)],
    )
}

#[test]
fn raw_false_clauses_queries_duplicates_and_literal_guards_are_retained() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let guard = op(ChcOp::And, vec![ChcExpr::Bool(true), ChcExpr::Bool(false)]);
    let fact = QuantifiedHornClause::new(HornClause::fact(ChcExpr::Bool(false), p, vec![]), vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            fact,
            query(guard.clone(), vec![premise("i", 64, ChcExpr::Bool(false))]),
            query(ChcExpr::Bool(false), vec![]),
            query(ChcExpr::Bool(false), vec![]),
        ],
    )
    .unwrap();
    let raw = source.source_problem();
    assert_eq!(raw.clauses().len(), 4);
    assert_eq!(raw.pruned_false_query_count(), 0);
    assert!(!raw.has_stripped_body_forall());
    assert_eq!(raw.clauses()[1].body.constraint.as_ref(), Some(&guard));
    assert_eq!(
        raw.clauses()
            .iter()
            .map(|c| c.source_query_ordinal)
            .collect::<Vec<_>>(),
        vec![None, Some(0), Some(1), Some(2)]
    );
    assert_eq!(
        source.premises().iter().map(Vec::len).collect::<Vec<_>>(),
        vec![0, 1, 0, 0]
    );
    assert!(source.source_smtlib().contains("(=> false P)"));
    assert!(source.source_smtlib().contains("(and true false)"));
    assert_eq!(
        source
            .source_smtlib()
            .matches("(assert (=> false false))")
            .count(),
        2
    );
}

#[test]
fn matrix_only_variables_are_outer_bound_and_symbolic_guard_is_not_enumerated() {
    let index = var("i", bv(64));
    let guard = op(ChcOp::BvULt, vec![index.clone(), var("length", bv(64))]);
    let read = op(ChcOp::Select, vec![var("data", array()), index]);
    let matrix = op(
        ChcOp::Implies,
        vec![guard, op(ChcOp::Eq, vec![read, var("fill", bv(8))])],
    );
    let source = standalone(vec![premise("i", 64, matrix.clone())]).unwrap();
    assert_eq!(source.premises()[0][0].matrix(), &matrix);
    assert_eq!(source.premises()[0][0].binder(), &ChcVar::new("i", bv(64)));
    let text = source.source_smtlib();
    assert!(text.contains("(forall ((data (Array (_ BitVec 64) (_ BitVec 8))) (fill (_ BitVec 8)) (length (_ BitVec 64)))"));
    assert!(text
        .contains("(forall ((i (_ BitVec 64))) (=> (bvult i length) (= (select data i) fill)))"));
    assert_eq!(text.matches("(i (_ BitVec 64))").count(), 1);
}

#[test]
fn sibling_binders_and_differently_sorted_outer_shadowing_remain_lexical() {
    let first = premise(
        "x",
        8,
        op(ChcOp::Eq, vec![var("x", bv(8)), ChcExpr::BitVec(0, 8)]),
    );
    let second = premise(
        "x",
        1,
        op(ChcOp::Eq, vec![var("x", bv(1)), ChcExpr::BitVec(1, 1)]),
    );
    let source = QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![query(var("x", ChcSort::Bool), vec![first, second])],
    )
    .unwrap();
    assert!(source.source_smtlib().contains("(forall ((x Bool))"));
    assert!(source
        .source_smtlib()
        .contains("(forall ((x (_ BitVec 8)))"));
    assert!(source
        .source_smtlib()
        .contains("(forall ((x (_ BitVec 1)))"));
    let unused = standalone(vec![premise("unused", 64, ChcExpr::Bool(true))]).unwrap();
    assert!(unused
        .source_smtlib()
        .contains("(forall ((unused (_ BitVec 64))) true)"));
}

#[test]
fn free_name_conflicts_and_wrong_bound_reference_sorts_are_refused() {
    let make = |name, sort| op(ChcOp::Eq, vec![var(name, sort), var(name, bv(8))]);
    assert!(standalone(vec![premise("i", 8, make("i", ChcSort::Bool))]).is_err());
    let first = premise(
        "i",
        8,
        op(ChcOp::Eq, vec![var("free", bv(8)), ChcExpr::BitVec(0, 8)]),
    );
    let second = premise("j", 8, var("free", ChcSort::Bool));
    assert!(standalone(vec![first.clone(), second]).is_err());
    assert!(QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![query(var("free", ChcSort::Bool), vec![first]),]
    )
    .is_err());
    // The first binder does not bind a free occurrence in its sibling.
    let bound = premise("shared", 8, ChcExpr::Bool(true));
    let free = premise("j", 1, var("shared", ChcSort::Bool));
    let admitted = standalone(vec![bound, free]).unwrap();
    assert!(admitted.source_smtlib().contains("(forall ((shared Bool))"));
}

#[test]
fn malformed_operator_literal_and_intermediate_sorts_are_rejected() {
    let invalid = vec![
        ChcExpr::BitVec(0, 0),
        ChcExpr::BitVec(0, crate::MAX_BITVECTOR_WIDTH + 1),
        ChcExpr::BitVec(256, 8),
        op(ChcOp::Not, vec![]),
        op(ChcOp::Not, vec![ChcExpr::BitVec(0, 8)]),
        op(
            ChcOp::Eq,
            vec![ChcExpr::BitVec(0, 8), ChcExpr::BitVec(0, 9)],
        ),
        op(
            ChcOp::Select,
            vec![var("a", array()), ChcExpr::BitVec(0, 8)],
        ),
        op(ChcOp::BvExtract(8, 0), vec![ChcExpr::BitVec(0, 8)]),
        op(ChcOp::BvRepeat(u32::MAX), vec![ChcExpr::BitVec(0, 8)]),
        op(ChcOp::BvZeroExtend(64), vec![ChcExpr::BitVec(0, 8)]),
        op(
            ChcOp::Eq,
            vec![
                op(ChcOp::Bv2Nat, vec![ChcExpr::BitVec(0, 8)]),
                op(ChcOp::Bv2Nat, vec![ChcExpr::BitVec(0, 8)]),
            ],
        ),
    ];
    for matrix in invalid {
        assert!(standalone(vec![premise("i", 64, matrix)]).is_err());
    }
    for width in [0, 65, u32::MAX] {
        assert!(standalone(vec![premise("i", width, ChcExpr::Bool(true))]).is_err());
    }
}

#[test]
fn unsupported_families_cannot_hide_below_false_or_unused_premises() {
    let invalid = vec![
        ChcExpr::Int(0),
        ChcExpr::Real(0, 1),
        ChcExpr::FuncApp("global".into(), ChcSort::Bool, vec![]),
        ChcExpr::PredicateApp("P".into(), PredicateId::new(0), vec![]),
        ChcExpr::ConstArrayMarker(bv(8)),
        var(
            "rank_three",
            ChcSort::Array(
                Box::new(bv(8)),
                Box::new(ChcSort::Array(Box::new(bv(8)), Box::new(array()))),
            ),
        ),
        var("dt", ChcSort::Uninterpreted("D".into())),
    ];
    for expression in invalid {
        let matrix = op(ChcOp::And, vec![ChcExpr::Bool(false), expression]);
        assert!(standalone(vec![premise("unused", 64, matrix)]).is_err());
    }
    let constant = ChcExpr::ConstArray(bv(64), Arc::new(ChcExpr::Bool(true)));
    let read = op(ChcOp::Select, vec![constant, var("i", bv(64))]);
    assert!(standalone(vec![premise("i", 64, read)]).is_ok());
}

#[test]
fn declaration_only_contract_rejects_live_pruned_and_stripped_sources() {
    let mut live = ChcProblem::new();
    live.add_clause(HornClause::query(ClauseBody::empty()));
    let mut pruned = ChcProblem::new();
    pruned.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        false,
    ))));
    assert_eq!(pruned.pruned_false_query_count(), 1);
    let mut stripped = ChcProblem::new();
    stripped.mark_stripped_body_forall();
    for declarations in [live, pruned, stripped] {
        assert!(
            QuantifiedChcProblem::new(declarations, vec![query(ChcExpr::Bool(false), vec![])])
                .is_err()
        );
    }
    let source = standalone(vec![]).unwrap();
    assert!(QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![QuantifiedHornClause::new(
            source.source_problem().clauses()[0].clone(),
            vec![]
        ),]
    )
    .is_err());
}

#[test]
fn predicate_registry_arity_and_argument_sorts_are_authenticated() {
    for args in [
        vec![],
        vec![ChcExpr::Bool(true)],
        vec![ChcExpr::BitVec(0, 8), ChcExpr::BitVec(1, 8)],
    ] {
        let mut declarations = ChcProblem::new();
        let p = declarations.declare_predicate("P", vec![bv(8)]);
        let query = HornClause::query(ClauseBody::predicates_only(vec![(p, args)]));
        assert!(QuantifiedChcProblem::new(
            declarations,
            vec![QuantifiedHornClause::new(query, vec![])]
        )
        .is_err());
    }
    let unknown = HornClause::query(ClauseBody::predicates_only(vec![(
        PredicateId::new(2),
        vec![],
    )]));
    assert!(QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![QuantifiedHornClause::new(unknown, vec![])]
    )
    .is_err());
    let mut duplicate = ChcProblem::new();
    duplicate.declare_predicate("P", vec![]);
    duplicate.declare_predicate("P", vec![bv(8)]);
    assert!(
        QuantifiedChcProblem::new(duplicate, vec![query(ChcExpr::Bool(false), vec![])]).is_err()
    );
}

#[test]
fn theory_shadowing_bad_symbols_and_predicate_capture_are_refused() {
    for name in [
        "",
        "bad\0name",
        "bad|name",
        "bad\\name",
        "bvadd",
        "select",
        "true",
        "=",
    ] {
        assert!(standalone(vec![premise(name, 8, ChcExpr::Bool(true))]).is_err());
        assert!(standalone(vec![premise("i", 8, var(name, ChcSort::Bool))]).is_err());
    }
    let mut declarations = ChcProblem::new();
    declarations.declare_predicate("select", vec![]);
    assert!(
        QuantifiedChcProblem::new(declarations, vec![query(ChcExpr::Bool(false), vec![])]).is_err()
    );
    let mut declarations = ChcProblem::new();
    declarations.declare_predicate("P", vec![]);
    assert!(
        QuantifiedChcProblem::new(declarations, vec![query(var("P", ChcSort::Bool), vec![])])
            .is_err()
    );
    let source = standalone(vec![premise(
        "bound index",
        8,
        var("source value", ChcSort::Bool),
    )])
    .unwrap();
    assert!(source.source_smtlib().contains("(|source value| Bool)"));
    assert!(source
        .source_smtlib()
        .contains("(|bound index| (_ BitVec 8))"));
}

/// AY-SMT-10: the SMT-LIB 2.7 names of the BV/Int conversions are theory
/// symbols the CHC parser reads, so a source binder or free name spelled like
/// one must be refused exactly as `bv2nat` / `int2bv` are.
#[test]
fn smtlib_2_7_bv_conversion_names_cannot_be_shadowed() {
    for name in [
        "bv2nat",
        "int2bv",
        "bv2int",
        "ubv_to_int",
        "sbv_to_int",
        "int_to_bv",
    ] {
        assert!(standalone(vec![premise(name, 8, ChcExpr::Bool(true))]).is_err());
        assert!(standalone(vec![premise("i", 8, var(name, ChcSort::Bool))]).is_err());
    }
    assert!(standalone(vec![premise("i", 8, var("ubv_to_int_x", ChcSort::Bool))]).is_ok());
}

#[test]
fn raw_argument_structure_is_retained_without_relational_normalization() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![bv(8)]);
    let argument = op(ChcOp::BvAdd, vec![var("x", bv(8)), ChcExpr::BitVec(0, 8)]);
    let clause = HornClause::query(ClauseBody::predicates_only(vec![
        (p, vec![argument.clone()]),
        (p, vec![argument.clone()]),
    ]));
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![QuantifiedHornClause::new(clause, vec![])],
    )
    .unwrap();
    let body = &source.source_problem().clauses()[0].body;
    assert_eq!(body.predicates.len(), 2);
    assert_eq!(body.predicates[0].1, vec![argument]);
    assert!(body.constraint.is_none());
    assert_eq!(
        source
            .source_smtlib()
            .matches("(P (bvadd x (_ bv0 8)))")
            .count(),
        2
    );
}

#[test]
fn declaration_matrix_query_order_and_source_mode_change_identity() {
    let make = |width, matrix, reverse, fixedpoint| {
        let mut declarations = ChcProblem::new();
        declarations.declare_predicate("unused", vec![bv(width)]);
        if fixedpoint {
            declarations.set_fixedpoint_format();
        }
        let mut clauses = vec![
            query(
                ChcExpr::Bool(true),
                vec![premise("i", 64, ChcExpr::Bool(matrix))],
            ),
            query(ChcExpr::Bool(false), vec![]),
        ];
        if reverse {
            clauses.reverse();
        }
        QuantifiedChcProblem::new(declarations, clauses).unwrap()
    };
    let base = make(8, true, false, false);
    assert_eq!(
        base.source_smtlib(),
        make(8, true, false, false).source_smtlib()
    );
    for changed in [
        make(9, true, false, false),
        make(8, false, false, false),
        make(8, true, true, false),
        make(8, true, false, true),
    ] {
        assert_ne!(base.source_smtlib(), changed.source_smtlib());
    }
}

#[test]
fn bounded_occurrences_depth_names_and_collection_counts_refuse_then_retry() {
    let mut deep = ChcExpr::Bool(true);
    for _ in 0..65 {
        deep = op(ChcOp::Not, vec![deep]);
    }
    assert!(standalone(vec![premise("i", 8, deep)]).is_err());
    #[expect(
        clippy::rc_clone_in_vec_init,
        reason = "the quantified cap fixture intentionally shares one immutable boolean node to isolate occurrence accounting"
    )]
    let wide = ChcExpr::Op(ChcOp::And, vec![Arc::new(ChcExpr::Bool(true)); 65_536]);
    assert!(standalone(vec![premise("i", 8, wide)]).is_err());
    assert!(standalone(vec![premise(&"x".repeat(16_385), 8, ChcExpr::Bool(true))]).is_err());
    assert!(standalone(vec![premise("i", 8, ChcExpr::Bool(true)); 4_097]).is_err());
    assert!(QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![query(ChcExpr::Bool(false), vec![]); 2_049]
    )
    .is_err());
    let mut declarations = ChcProblem::new();
    for index in 0..1_025 {
        declarations.declare_predicate(format!("P{index}"), vec![]);
    }
    assert!(
        QuantifiedChcProblem::new(declarations, vec![query(ChcExpr::Bool(false), vec![])]).is_err()
    );
    assert!(standalone(vec![premise("i", 8, ChcExpr::Bool(true))]).is_ok());
}
