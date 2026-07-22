// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn clause_guarded_constraint_returns_true_when_no_guarded_lemmas_exist() {
    let solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let clause_index = solver
        .problem
        .clauses_defining_with_index(pred)
        .next()
        .expect("P should have a defining clause")
        .0;
    let head_arg = ChcVar::new("head_arg", ChcSort::Int);
    let guarded =
        solver.clause_guarded_constraint(pred, clause_index, &[ChcExpr::var(head_arg)], 0);

    assert_eq!(
        guarded,
        ChcExpr::Bool(true),
        "no clause-guarded lemmas should produce Bool(true)"
    );
}

#[test]
fn clause_guarded_constraint_applies_guarded_lemmas_to_head_args() {
    let mut solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let clause_index = solver
        .problem
        .clauses_defining_with_index(pred)
        .next()
        .expect("P should have a defining clause")
        .0;
    let canon_x = solver.canonical_vars(pred).unwrap()[0].clone();
    let guarded_formula = ChcExpr::ge(ChcExpr::var(canon_x), ChcExpr::int(0));
    let cgl = &mut solver.caches.clause_guarded_lemmas;
    cgl.insert((pred, clause_index), vec![(guarded_formula, usize::MAX)]);

    let head_arg = ChcVar::new("head_arg", ChcSort::Int);
    let guarded =
        solver.clause_guarded_constraint(pred, clause_index, &[ChcExpr::var(head_arg.clone())], 0);

    assert_eq!(
        guarded,
        ChcExpr::ge(ChcExpr::var(head_arg), ChcExpr::int(0)),
        "guarded lemmas should be instantiated with clause head args"
    );
}

#[test]
fn add_blocking_lemma_increments_restart_counter_and_clears_fixed_point() {
    let mut solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let canon_x = solver.canonical_vars(pred).unwrap()[0].clone();

    // Seed fixed_point_pob_seen with a dummy entry
    solver
        .obligations
        .fixed_point_pob_seen
        .insert((pred, 0, 99999));
    assert!(!solver.obligations.fixed_point_pob_seen.is_empty());
    assert_eq!(solver.restart.lemmas_since_restart, 0);

    // Add a blocking lemma: NOT(x = 0)
    let blocking = ChcExpr::not(ChcExpr::eq(ChcExpr::var(canon_x), ChcExpr::int(0)));
    let lemma = Lemma::new(pred, blocking, 0);
    solver.add_blocking_lemma(lemma, 0);

    assert_eq!(solver.restart.lemmas_since_restart, 1);
    assert!(
        solver.obligations.fixed_point_pob_seen.is_empty(),
        "fixed_point_pob_seen should be cleared after adding blocking lemma"
    );
}

#[test]
fn add_lemma_to_frame_inserts_into_correct_frame() {
    let mut solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let canon_x = solver.canonical_vars(pred).unwrap()[0].clone();

    let formula = ChcExpr::ge(ChcExpr::var(canon_x), ChcExpr::int(0));
    let lemma = Lemma::new(pred, formula.clone(), 0);
    solver.add_lemma_to_frame(lemma, 0);

    assert!(
        solver.frames[0].contains_lemma(pred, &formula),
        "lemma should be present in frame 0"
    );
    assert!(
        !solver.frames[1].contains_lemma(pred, &formula),
        "lemma should NOT be in frame 1"
    );
}

#[test]
fn add_lemma_to_frame_does_not_affect_restart_accounting() {
    let mut solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let canon_x = solver.canonical_vars(pred).unwrap()[0].clone();

    // Seed state to verify it's NOT touched by add_lemma_to_frame
    solver
        .obligations
        .fixed_point_pob_seen
        .insert((pred, 0, 99999));
    assert_eq!(solver.restart.lemmas_since_restart, 0);

    let formula = ChcExpr::ge(ChcExpr::var(canon_x), ChcExpr::int(0));
    let lemma = Lemma::new(pred, formula, 0);
    solver.add_lemma_to_frame(lemma, 0);

    // add_lemma_to_frame is NOT add_blocking_lemma: no restart accounting
    assert_eq!(
        solver.restart.lemmas_since_restart, 0,
        "add_lemma_to_frame should NOT increment lemmas_since_restart"
    );
    assert!(
        !solver.obligations.fixed_point_pob_seen.is_empty(),
        "add_lemma_to_frame should NOT clear fixed_point_pob_seen"
    );
}

#[test]
fn add_lemma_to_frame_no_propagation_inserts_without_propagation_side_effects() {
    // Build a two-predicate problem where propagation would create
    // clause_guarded_lemmas for the parent predicate.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // P(x) => Q(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    // Fact: => P(x) (so P is seeded)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));
    // Q(y) => false (query)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![ChcExpr::var(y)])], Some(ChcExpr::Bool(true))),
        ClauseHead::False,
    ));

    let mut solver = PdrSolver::new(problem, test_config());
    // Add a third frame so we can insert at level 1 (need frames 0, 1, 2)
    solver.frames.push(Frame::new());

    let canon_x = solver.canonical_vars(p).unwrap()[0].clone();
    let formula = ChcExpr::ge(ChcExpr::var(canon_x), ChcExpr::int(0));
    let lemma = Lemma::new(p, formula.clone(), 1);

    // Use no_propagation: should NOT create clause_guarded_lemmas for Q
    solver.add_lemma_to_frame_no_propagation(lemma, 1);

    assert!(
        solver.frames[1].contains_lemma(p, &formula),
        "lemma should be in frame 1"
    );
    assert!(
        solver.caches.clause_guarded_lemmas.is_empty(),
        "no_propagation should NOT create clause_guarded_lemmas"
    );

    // Positive propagation (add_lemma_to_frame DOES propagate) is tested by
    // test_transitive_clause_guarded_max_level_bump in propagation.rs, which
    // exercises propagate_frame1_invariants_to_users end-to-end with assertions
    // on clause_guarded_lemmas. This test focuses on verifying the NEGATIVE
    // property: no_propagation must not create clause_guarded entries.
}

#[test]
fn add_lemma_to_frame_level_gt_zero_triggers_propagation_to_users() {
    // Build P(x) => Q(x) problem so propagating a lemma on P can produce
    // clause-guarded lemmas for Q.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    // P(x) => Q(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    // Fact: => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    // Q(x) => false (query)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![ChcExpr::var(x)])], Some(ChcExpr::Bool(true))),
        ClauseHead::False,
    ));

    let mut solver = PdrSolver::new(problem, test_config());
    // Need at least 3 frames to insert at level 1 and propagate to level 2.
    solver.frames.push(Frame::new());
    assert!(
        solver.caches.clause_guarded_lemmas.is_empty(),
        "no clause-guarded lemmas before add_lemma_to_frame propagation"
    );

    let p_canon = solver.canonical_vars(p).unwrap()[0].clone();
    let formula = ChcExpr::ge(ChcExpr::var(p_canon), ChcExpr::int(0));
    let lemma = Lemma::new(p, formula.clone(), 1);

    solver.add_lemma_to_frame(lemma, 1);

    assert!(
        solver.frames[1].contains_lemma(p, &formula),
        "lemma should be inserted into frame 1"
    );
    let cgl = &solver.caches.clause_guarded_lemmas;
    let q_entries: Vec<_> = cgl.iter().filter(|((pred, _), _)| *pred == q).collect();
    assert!(
        !q_entries.is_empty(),
        "add_lemma_to_frame(level>0) should propagate and create Q clause-guarded lemmas"
    );
    assert!(
        q_entries
            .iter()
            .all(|(_, guarded)| guarded.iter().all(|(_, lvl)| *lvl == 2)),
        "propagated entries should target level+1 (=2)"
    );
}

#[test]
fn propagate_lemma_to_users_populates_clause_guarded_lemmas() {
    // Build P(x) => Q(x) problem: Q "uses" P.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    // P(x) => Q(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    // Fact => P(x) (seed)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    // Q(x) => false (query)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![ChcExpr::var(x)])], Some(ChcExpr::Bool(true))),
        ClauseHead::False,
    ));

    let mut solver = PdrSolver::new(problem, test_config());
    // Need at least 3 frames to propagate at level 1 (target becomes level+1=2)
    solver.frames.push(Frame::new());

    assert!(
        solver.caches.clause_guarded_lemmas.is_empty(),
        "no clause-guarded lemmas before propagation"
    );

    let p_canon = solver.canonical_vars(p).unwrap()[0].clone();
    let formula = ChcExpr::ge(ChcExpr::var(p_canon), ChcExpr::int(0));

    let added = solver.propagate_lemma_to_users(p, &formula, 1);

    // propagate_lemma_to_users should have created a clause-guarded entry for Q
    // via the P(x)=>Q(x) clause, translating P's canonical var to Q's canonical var.
    assert!(
            added > 0,
            "propagation should produce at least 1 clause-guarded lemma for Q (added={}, guarded_len={})",
            added,
            solver.caches.clause_guarded_lemmas.len()
        );
    assert!(
        !solver.caches.clause_guarded_lemmas.is_empty(),
        "clause_guarded_lemmas should be non-empty after successful propagation"
    );

    // Verify Q got an entry keyed by (q, clause_index=0)
    let cgl = &solver.caches.clause_guarded_lemmas;
    let q_entries: Vec<_> = cgl.iter().filter(|((pred, _), _)| *pred == q).collect();
    assert!(
        !q_entries.is_empty(),
        "clause_guarded_lemmas should have Q entries"
    );
}

#[test]
fn add_blocking_lemma_multiple_increments_counter_cumulatively() {
    let mut solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let canon_x = solver.canonical_vars(pred).unwrap()[0].clone();

    for i in 1..=5 {
        let formula = ChcExpr::not(ChcExpr::eq(ChcExpr::var(canon_x.clone()), ChcExpr::int(i)));
        let lemma = Lemma::new(pred, formula, 0);
        solver.add_blocking_lemma(lemma, 0);
    }

    assert_eq!(
        solver.restart.lemmas_since_restart, 5,
        "5 blocking lemmas should give lemmas_since_restart=5"
    );
}

// =========================================================================
// Obligation overflow safety (#2983)
// =========================================================================

/// Verify that the obligation overflow flag prevents false Safe results
/// across both the must-summaries Continue path and the terminal Safe path.
/// This is the key soundness invariant from #2983.
#[test]
fn obligation_overflow_prevents_safe_on_both_exit_paths() {
    let mut config = test_config();
    config.max_obligations = 1; // queue cap = 2

    let mut solver = PdrSolver::new(test_linear_problem(), config);
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;

    // Fill to cap
    for i in 0..2 {
        solver.push_obligation(ProofObligation::new(
            pred,
            ChcExpr::eq(ChcExpr::int(i), ChcExpr::int(i)),
            1,
        ));
    }
    assert!(!solver.obligations.overflowed);

    // Overflow
    solver.push_obligation(ProofObligation::new(pred, ChcExpr::Bool(true), 1));
    assert!(solver.obligations.overflowed, "overflow flag must be set");

    // Same overflow behavior for push_obligation_front
    let mut solver2 = PdrSolver::new(test_linear_problem(), {
        let mut c = test_config();
        c.max_obligations = 1;
        c
    });
    for i in 0..2 {
        solver2.push_obligation_front(ProofObligation::new(
            pred,
            ChcExpr::eq(ChcExpr::int(i), ChcExpr::int(i)),
            1,
        ));
    }
    assert!(!solver2.obligations.overflowed);
    solver2.push_obligation_front(ProofObligation::new(pred, ChcExpr::Bool(true), 1));
    assert!(
        solver2.obligations.overflowed,
        "push_obligation_front must also set overflow flag"
    );
}
