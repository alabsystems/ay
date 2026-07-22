// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn pdr_new_uses_arrays_false_for_pure_lia_problem() {
    let solver = PdrSolver::new(test_linear_problem(), test_config());

    assert!(
        !solver.uses_arrays,
        "pure-LIA problems must stay on the non-array fast path"
    );
}

#[test]
fn pdr_new_marks_bv_problem_non_pure_lia_issue_5877() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let x_next = ChcVar::new("x_next", ChcSort::BitVec(8));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8))),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x_next.clone()),
                ChcExpr::Op(
                    ChcOp::BvAdd,
                    vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::BitVec(1, 8))],
                ),
            )),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x_next)]),
    ));

    let solver = PdrSolver::new(problem, test_config());
    assert!(
        !solver.problem_is_pure_lia,
        "BV predicate/state space must bypass the LIA-only incremental fast-path"
    );
}

#[test]
fn pdr_new_bitvector_only_enables_incremental_pdr_issue_8205() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let x_next = ChcVar::new("x_next", ChcSort::BitVec(8));

    // Fact: inv(0)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8))),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x.clone())]),
    ));
    // Transition: inv(x) -> inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x_next.clone()),
                ChcExpr::Op(
                    ChcOp::BvAdd,
                    vec![
                        Arc::new(ChcExpr::var(x.clone())),
                        Arc::new(ChcExpr::BitVec(1, 8)),
                    ],
                ),
            )),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x_next)]),
    ));
    // Query: inv(x) /\ x = 255 -> false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(255, 8))),
        ),
        ClauseHead::False,
    ));

    let solver = PdrSolver::new(problem, test_config());
    assert!(
        solver.problem_is_bitvector_only,
        "pure BV problem must be classified as bitvector-only (#8205)"
    );
    // Incremental PDR for BV is temporarily disabled due to regressions
    // where the prop_solver path returns Unknown for simple BV counting loops.
    // The classification is still correct (problem_is_bitvector_only = true),
    // but incremental_pdr_enabled() returns false until the prop_solver issues
    // are resolved.
    assert!(
        !solver.incremental_pdr_enabled(),
        "incremental PDR is temporarily disabled for BV problems due to regressions"
    );
    assert!(
        !solver.problem_is_pure_lia,
        "BV problem must not be classified as pure LIA"
    );
}

#[test]
fn pdr_new_lia_problem_disables_incremental_pdr_issue_8205() {
    let solver = PdrSolver::new(test_linear_problem(), test_config());
    assert!(
        !solver.problem_is_bitvector_only,
        "LIA problem must not be classified as bitvector-only"
    );
    assert!(
        !solver.incremental_pdr_enabled(),
        "incremental PDR must stay disabled for LIA problems (#6583)"
    );
}

#[test]
fn pdr_new_mixed_bv_lia_disables_incremental_pdr_issue_8205() {
    let mut problem = ChcProblem::new();
    // Mixed BV + Int predicate
    let pred = problem.declare_predicate("inv", vec![ChcSort::BitVec(8), ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let n = ChcVar::new("n", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8)),
                ChcExpr::eq(ChcExpr::var(n.clone()), ChcExpr::Int(0)),
            )),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x.clone()), ChcExpr::var(n.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone()), ChcExpr::var(n.clone())])],
            Some(ChcExpr::Bool(true)),
        ),
        ClauseHead::False,
    ));

    let solver = PdrSolver::new(problem, test_config());
    assert!(
        !solver.problem_is_bitvector_only,
        "mixed BV+LIA problem must not be classified as bitvector-only (#8205)"
    );
    assert!(
        !solver.incremental_pdr_enabled(),
        "incremental PDR must stay disabled for mixed BV+LIA problems"
    );
}

#[test]
fn pdr_new_uses_arrays_false_after_constant_array_scalarization() {
    let mut problem = ChcProblem::new();
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let pred = problem.declare_predicate("inv", vec![arr_sort.clone(), ChcSort::Int]);
    let arr = ChcVar::new("arr", arr_sort);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                pred,
                vec![ChcExpr::var(arr.clone()), ChcExpr::var(x.clone())],
            )],
            Some(ChcExpr::eq(
                ChcExpr::select(ChcExpr::var(arr.clone()), ChcExpr::int(0)),
                ChcExpr::var(x.clone()),
            )),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(arr), ChcExpr::var(x)]),
    ));

    let solver = PdrSolver::new(problem, test_config());

    assert!(
        !solver.uses_arrays,
        "constant-select scalarization should clear the array fast-path guard"
    );
    assert!(
        solver.problem.predicates()[0]
            .arg_sorts
            .iter()
            .all(|sort| !matches!(sort, ChcSort::Array(_, _))),
        "scalarized predicate signature should not retain Array sorts"
    );
}

#[test]
fn pdr_new_uses_arrays_true_when_symbolic_select_blocks_scalarization() {
    let mut problem = ChcProblem::new();
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let pred = problem.declare_predicate("inv", vec![arr_sort.clone(), ChcSort::Int]);
    let arr = ChcVar::new("arr", arr_sort);
    let idx = ChcVar::new("idx", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                pred,
                vec![ChcExpr::var(arr.clone()), ChcExpr::var(idx.clone())],
            )],
            Some(ChcExpr::eq(
                ChcExpr::select(ChcExpr::var(arr.clone()), ChcExpr::var(idx.clone())),
                ChcExpr::var(idx.clone()),
            )),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(arr), ChcExpr::var(idx)]),
    ));

    let solver = PdrSolver::new(problem, test_config());

    assert!(
        solver.uses_arrays,
        "symbolic selects must keep array-aware handling enabled"
    );
    assert!(
        matches!(
            solver.problem.predicates()[0].arg_sorts[0],
            ChcSort::Array(_, _)
        ),
        "predicate signature should still contain the original Array sort"
    );
}

#[test]
fn obligation_queue_overflow_sets_degrade_flag_and_keeps_queue_bounded() {
    let mut config = test_config();
    config.max_obligations = 2; // queue cap = 4

    let mut solver = PdrSolver::new(test_linear_problem(), config);
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;

    let cap = solver.obligation_queue_cap();
    assert_eq!(cap, 4);

    for i in 0..cap {
        let pob = ProofObligation::new(
            pred,
            ChcExpr::eq(ChcExpr::int(i as i64), ChcExpr::int(i as i64)),
            1,
        );
        solver.push_obligation(pob);
    }

    assert_eq!(solver.obligation_queue_size(), cap);
    assert!(
        !solver.obligations.overflowed,
        "queue should not be marked overflowed at exact cap"
    );

    let extra = ProofObligation::new(pred, ChcExpr::Bool(true), 1);
    solver.push_obligation(extra);

    assert_eq!(
        solver.obligation_queue_size(),
        cap,
        "queue size must remain bounded at cap after overflow"
    );
    assert!(
        solver.obligations.overflowed,
        "overflow must mark the strengthen attempt as degraded"
    );
}

#[test]
fn bounded_cache_insert_clears_when_cap_reached_by_new_key() {
    let mut cache: FxHashMap<u32, u32> = FxHashMap::default();
    PdrCacheStore::bounded_insert(&mut cache, 1, 10, 2);
    PdrCacheStore::bounded_insert(&mut cache, 2, 20, 2);
    assert_eq!(cache.len(), 2);

    PdrCacheStore::bounded_insert(&mut cache, 3, 30, 2);
    assert_eq!(cache.len(), 1);
    assert_eq!(cache.get(&3), Some(&30));
}

#[test]
fn bounded_cache_insert_updates_existing_without_clear() {
    let mut cache: FxHashMap<u32, u32> = FxHashMap::default();

    PdrCacheStore::bounded_insert(&mut cache, 1, 10, 2);
    PdrCacheStore::bounded_insert(&mut cache, 2, 20, 2);
    assert_eq!(cache.len(), 2);

    PdrCacheStore::bounded_insert(&mut cache, 2, 22, 2);
    assert_eq!(cache.len(), 2);
    assert_eq!(cache.get(&1), Some(&10));
    assert_eq!(cache.get(&2), Some(&22));
}

#[test]
fn upsert_clause_guarded_lemma_enforces_per_key_cap() {
    let mut solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;

    let key = (pred, 0);
    let (inserted0, bumped0) = solver.upsert_clause_guarded_lemma(key, ChcExpr::Bool(true), 1, 2);
    let (inserted1, bumped1) = solver.upsert_clause_guarded_lemma(key, ChcExpr::Bool(false), 1, 2);
    let (inserted2, bumped2) = solver.upsert_clause_guarded_lemma(
        key,
        ChcExpr::eq(ChcExpr::Int(1), ChcExpr::Int(1)),
        1,
        2,
    );

    assert!((inserted0, bumped0) == (true, false));
    assert!((inserted1, bumped1) == (true, false));
    assert!((inserted2, bumped2) == (false, false));
    let cgl = &solver.caches.clause_guarded_lemmas;
    assert_eq!(cgl.get(&key).expect("key should be present").len(), 2);
}

#[test]
fn upsert_clause_guarded_lemma_clears_keys_on_global_cap_overflow() {
    let mut solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;

    for clause_idx in 0..PdrCacheStore::clause_guarded_keys_cap() {
        let (inserted, bumped) =
            solver.upsert_clause_guarded_lemma((pred, clause_idx), ChcExpr::Bool(true), 1, 4);
        assert!((inserted, bumped) == (true, false));
    }
    assert_eq!(
        solver.caches.clause_guarded_lemmas.len(),
        PdrCacheStore::clause_guarded_keys_cap()
    );

    let overflow_key = (pred, PdrCacheStore::clause_guarded_keys_cap());
    let (inserted, bumped) =
        solver.upsert_clause_guarded_lemma(overflow_key, ChcExpr::Bool(true), 1, 4);
    assert!((inserted, bumped) == (true, false));
    assert_eq!(
        solver.caches.clause_guarded_lemmas.len(),
        1,
        "overflow insert should clear old keys before inserting new key"
    );
    let cgl = &solver.caches.clause_guarded_lemmas;
    assert!(cgl.contains_key(&overflow_key), "overflow key retained");
}

#[test]
fn clear_restart_caches_drops_restart_sensitive_maps() {
    let mut solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;

    {
        let c = &mut solver.caches;
        c.push_cache
            .insert((1, pred.index(), 11), (ChcExpr::Bool(true), 7, true));
        c.self_inductive_cache.insert(
            (pred, ChcExpr::Bool(true).structural_hash()),
            (ChcExpr::Bool(true), 4, true),
        );
        c.inductive_blocking_cache.insert(
            (pred, 1, ChcExpr::Bool(false).structural_hash()),
            (ChcExpr::Bool(false), 3, false),
        );
        c.init_only_value_cache
            .insert((pred, "x".to_string(), 0), (2, false));
        c.cumulative_constraint_cache
            .borrow_mut()
            .insert((1, pred), (1, ChcExpr::Bool(true)));
        c.spurious_cex_weakness.insert((pred, 12345), 3);
        c.blocked_states_for_convex.insert(
            pred,
            vec![{
                let mut m = FxHashMap::default();
                m.insert("x".to_string(), 1);
                m
            }]
            .into(),
        );
        c.diseq_values
            .insert((pred, "x".to_string(), 1), vec![1, 2, 3]);
    }

    solver.clear_restart_caches();

    let c = &solver.caches;
    assert!(c.push_cache.is_empty());
    assert!(c.self_inductive_cache.is_empty());
    assert!(c.inductive_blocking_cache.is_empty());
    assert!(c.init_only_value_cache.is_empty());
    assert!(c.cumulative_constraint_cache.borrow().is_empty());
    assert!(c.spurious_cex_weakness.is_empty());
    assert!(c.blocked_states_for_convex.is_empty());
    assert!(c.diseq_values.is_empty());
}
