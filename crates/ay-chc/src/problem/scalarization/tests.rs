// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn build_problem(pred_sorts: Vec<ChcSort>, clauses: Vec<HornClause>) -> ChcProblem {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("inv", pred_sorts);
    for clause in clauses {
        problem.add_clause(clause);
    }
    problem
}

fn clause_eq_rhs_var_name(clause: &ChcExpr) -> String {
    let ChcExpr::Op(ChcOp::Or, args) = clause else {
        panic!("expected Or, got: {clause}");
    };
    let ChcExpr::Op(ChcOp::Eq, eq_args) = args[1].as_ref() else {
        panic!("expected Eq in second disjunct, got: {}", args[1]);
    };
    match eq_args[1].as_ref() {
        ChcExpr::Var(v) => v.name.clone(),
        other => format!("{other}"),
    }
}

#[test]
fn store_semantics_overwrite_at_target_index() {
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let next_a = ChcVar::new("next_A", arr_sort.clone());
    let base_b = ChcVar::new("base_B", arr_sort);
    let idx_var = ChcVar::new("idx", ChcSort::Int);
    let val_var = ChcVar::new("val", ChcSort::Int);
    let store_expr = ChcExpr::store(
        ChcExpr::var(base_b),
        ChcExpr::var(idx_var),
        ChcExpr::var(val_var),
    );
    let eq_conjunct = ChcExpr::eq(ChcExpr::var(next_a), store_expr);

    let mut index_map: FxHashMap<ChcSort, Vec<ConstIndex>> = FxHashMap::default();
    index_map.insert(ChcSort::Int, vec![ConstIndex::Int(0), ConstIndex::Int(1)]);

    let clauses = ChcProblem::scalarize_store_equality(&eq_conjunct, &index_map)
        .expect("should scalarize store equality");
    assert_eq!(clauses.len(), 4);
    assert_eq!(clause_eq_rhs_var_name(&clauses[0]), "val");
    assert_eq!(clause_eq_rhs_var_name(&clauses[1]), "base_B__sel_0");
    assert_eq!(clause_eq_rhs_var_name(&clauses[2]), "val");
    assert_eq!(clause_eq_rhs_var_name(&clauses[3]), "base_B__sel_1");
}

#[test]
fn property_directed_blocked_by_symbolic_select() {
    let bv32 = ChcSort::BitVec(32);
    let arr_sort = ChcSort::Array(Box::new(bv32.clone()), Box::new(ChcSort::Bool));
    let ov = ChcVar::new("ov", arr_sort.clone());
    let cnt = ChcVar::new("cnt", bv32.clone());
    let pred_id = PredicateId::new(0);

    let init_clause = HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(
            pred_id,
            vec![ChcExpr::var(ov.clone()), ChcExpr::var(cnt.clone())],
        ),
    );
    let trans_clause = HornClause::new(
        ClauseBody::new(
            vec![(
                pred_id,
                vec![ChcExpr::var(ov.clone()), ChcExpr::var(cnt.clone())],
            )],
            Some(ChcExpr::select(
                ChcExpr::var(ov.clone()),
                ChcExpr::var(cnt.clone()),
            )),
        ),
        ClauseHead::Predicate(
            pred_id,
            vec![ChcExpr::var(ov.clone()), ChcExpr::var(cnt.clone())],
        ),
    );
    let query_clause = HornClause::new(
        ClauseBody::new(
            vec![(pred_id, vec![ChcExpr::var(ov), ChcExpr::var(cnt)])],
            Some(ChcExpr::Bool(true)),
        ),
        ClauseHead::False,
    );
    let mut problem = build_problem(
        vec![arr_sort.clone(), bv32],
        vec![init_clause, trans_clause, query_clause],
    );

    let orig_arity = problem.predicates()[0].arity();
    problem.try_scalarize_property_directed();
    assert_eq!(problem.predicates()[0].arity(), orig_arity);
    assert_eq!(problem.predicates()[0].arg_sorts[0], arr_sort);
}

#[test]
fn scalarize_bvconcat_const_index() {
    let bv32 = ChcSort::BitVec(32);
    let arr_sort = ChcSort::Array(Box::new(bv32), Box::new(ChcSort::Bool));
    let ov = ChcVar::new("ov", arr_sort.clone());
    let pred_id = PredicateId::new(0);

    let concat_idx = ChcExpr::Op(
        ChcOp::BvConcat,
        vec![
            Arc::new(ChcExpr::BitVec(0, 16)),
            Arc::new(ChcExpr::BitVec(1, 16)),
        ],
    );
    let clause = HornClause::new(
        ClauseBody::new(
            vec![(pred_id, vec![ChcExpr::var(ov.clone())])],
            Some(ChcExpr::select(ChcExpr::var(ov), concat_idx)),
        ),
        ClauseHead::Predicate(pred_id, vec![ChcExpr::var(ChcVar::new("ov2", arr_sort))]),
    );

    let mut problem = build_problem(
        vec![ChcSort::Array(
            Box::new(ChcSort::BitVec(32)),
            Box::new(ChcSort::Bool),
        )],
        vec![clause],
    );
    let map = problem
        .try_scalarize_const_array_selects_with_map()
        .expect("BV const index should scalarize");
    assert_eq!(problem.predicates()[0].arity(), 1);
    assert_eq!(problem.predicates()[0].arg_sorts[0], ChcSort::Bool);
    assert!(matches!(
        &map.pred_args[&pred_id][0],
        ArrayScalarizedArg::Select { index, .. }
            if *index == ChcExpr::BitVec(1, 32)
    ));
}

#[test]
fn scalarize_observed_extra_const_index_without_source_select() {
    let key_sort = ChcSort::BitVec(160);
    let arr_sort = ChcSort::Array(Box::new(key_sort.clone()), Box::new(ChcSort::Bool));
    let ov = ChcVar::new("ov", arr_sort.clone());
    let pred_id = PredicateId::new(0);
    let clause = HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(pred_id, vec![ChcExpr::var(ov)]),
    );

    let mut problem = build_problem(vec![arr_sort], vec![clause]);
    let map = problem
        .try_scalarize_const_array_selects_with_extra_indices_with_map(&[(
            key_sort,
            ChcExpr::BitVec(4, 160),
        )])
        .expect("observed constant refinement key should scalarize");

    assert_eq!(problem.predicates()[0].arity(), 1);
    assert_eq!(problem.predicates()[0].arg_sorts[0], ChcSort::Bool);
    assert!(matches!(
        &map.pred_args[&pred_id][0],
        ArrayScalarizedArg::Select { index, .. }
            if *index == ChcExpr::BitVec(4, 160)
    ));
}

#[test]
fn const_key_cegar_scalarization_keeps_literal_keys_with_symbolic_accesses() {
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let arr = ChcVar::new("a", arr_sort.clone());
    let idx = ChcVar::new("i", ChcSort::Int);
    let pred_id = PredicateId::new(0);
    let constraint = ChcExpr::and_all(vec![
        ChcExpr::eq(
            ChcExpr::select(ChcExpr::var(arr.clone()), ChcExpr::Int(3)),
            ChcExpr::Int(42),
        ),
        ChcExpr::eq(
            ChcExpr::select(ChcExpr::var(arr.clone()), ChcExpr::var(idx)),
            ChcExpr::Int(7),
        ),
    ]);
    let clause = HornClause::new(
        ClauseBody::new(vec![(pred_id, vec![ChcExpr::var(arr)])], Some(constraint)),
        ClauseHead::False,
    );

    let mut conservative = build_problem(vec![arr_sort.clone()], vec![clause.clone()]);
    assert!(
        conservative
            .try_scalarize_const_array_selects_with_map()
            .is_none(),
        "default scalarization should still avoid mixed symbolic key sorts"
    );

    let mut cegar = build_problem(vec![arr_sort], vec![clause]);
    let map = cegar
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .expect("CEGAR profile keeps the finite literal key");
    assert_eq!(cegar.predicates()[0].arity(), 1);
    assert_eq!(cegar.predicates()[0].arg_sorts[0], ChcSort::Int);
    assert!(matches!(
        &map.pred_args[&pred_id][0],
        ArrayScalarizedArg::Select { index, .. } if *index == ChcExpr::Int(3)
    ));
}

#[test]
fn clause_local_constant_aliases_expose_array_keys_for_cegar_scalarization() {
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let arr = ChcVar::new("a", arr_sort.clone());
    let idx = ChcVar::new("i", ChcSort::Int);
    let pred_id = PredicateId::new(0);
    let constraint = ChcExpr::and_all(vec![
        ChcExpr::eq(ChcExpr::var(idx.clone()), ChcExpr::Int(0)),
        ChcExpr::eq(
            ChcExpr::select(ChcExpr::var(arr.clone()), ChcExpr::var(idx)),
            ChcExpr::Int(7),
        ),
    ]);
    let clause = HornClause::new(
        ClauseBody::new(vec![(pred_id, vec![ChcExpr::var(arr)])], Some(constraint)),
        ClauseHead::False,
    );
    let mut problem = build_problem(vec![arr_sort], vec![clause]);

    assert_eq!(
        problem.rewrite_clause_local_constant_aliases_for_array_scalarization(),
        1
    );
    let map = problem
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .expect("constant alias should expose the finite array key");

    assert_eq!(problem.predicates()[0].arity(), 1);
    assert_eq!(problem.predicates()[0].arg_sorts[0], ChcSort::Int);
    assert!(matches!(
        &map.pred_args[&pred_id][0],
        ArrayScalarizedArg::Select { index, .. } if *index == ChcExpr::Int(0)
    ));
}

#[test]
fn scalarization_validates_pruned_queries_against_the_source_registry() {
    let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let array = ChcVar::new("a", array_sort.clone());
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("p", vec![array_sort]);
    let action = problem.declare_action("step");

    problem.add_clause_with_action(
        HornClause::new(
            ClauseBody::constraint(ChcExpr::and_all(vec![
                ChcExpr::eq(
                    ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::Int(0)),
                    ChcExpr::Int(1),
                ),
                ChcExpr::eq(
                    ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::Int(1)),
                    ChcExpr::Int(2),
                ),
            ])),
            ClauseHead::Predicate(predicate, vec![ChcExpr::var(array.clone())]),
        ),
        action,
    );
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(predicate, vec![ChcExpr::var(array.clone())])],
        Some(ChcExpr::Bool(false)),
    )));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        predicate,
        vec![ChcExpr::var(array)],
    )])));

    problem.validate().expect("source problem should validate");
    let mut malformed = problem.clone();
    malformed.pruned_false_queries[0].body.predicates[0]
        .1
        .clear();
    malformed
        .try_scalarize_const_array_selects_with_map()
        .expect("malformed source still has a scalarizable live clause");
    assert!(matches!(
        malformed.validate(),
        Err(crate::ChcError::ArityMismatch { .. })
    ));

    let source_pruned_ids = problem.pruned_false_query_ids();
    problem
        .try_scalarize_const_array_selects_with_map()
        .expect("constant array index should scalarize the predicate");

    assert_eq!(
        problem.predicates()[0].arg_sorts,
        vec![ChcSort::Int, ChcSort::Int]
    );
    assert_eq!(problem.clause_action(0), Some(action));
    assert!(problem.pruned_query_source.is_some());
    problem
        .validate()
        .expect("derived clauses and retained source provenance validate in their own registries");
    assert_eq!(problem.pruned_false_query_ids(), source_pruned_ids);
    let obligations = problem
        .query_obligations()
        .expect("derived active query should remain independently solvable");
    assert_eq!(obligations.len(), 1);
    assert_eq!(source_pruned_ids[0].ordinal(), 0);
    assert_eq!(obligations[0].id().source_query_ordinal(), 1);
}
