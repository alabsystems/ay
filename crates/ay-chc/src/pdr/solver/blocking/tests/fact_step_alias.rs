// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-clause variable aliasing (`rename_clause_apart`).
//!
//! Clause variables are scoped per clause, but the parser keeps the user's
//! names. VMT/lustre encodings bind the same letters in every clause at
//! different roles: the fact below uses `D` as an init-state local while the
//! step clause uses `D` as its post-state counter. A query that conjoins two
//! clauses' formulas without renaming one apart equates the two `D`s — it is
//! over-constrained and its UNSAT answers can be spurious.
//!
//! The level-1 predecessor query was fixed on main while this change was in
//! flight (`blocking/tests/prev_level_zero.rs`); the two lustre-shaped
//! level-1 rows below are kept as regressions. The rows that FAIL on main
//! (`1c0295fa0`… `b9df884ba`) cover the sites upstream did not fix: the
//! fact-vs-query joins — init-safe, the root query POB at level 0, acyclic
//! safety (and backward-chain safety, `invariant_check/alias_tests.rs`) —
//! the level-0 must-summary's locals, and fact-local init inequalities
//! admitted as lemmas. The IUC level-1 frame row is a guard (its outcome on
//! main depends on which core the solver returns).

use super::*;

/// `state(A, B, C)`: init `A ∧ B = 0 ∧ C = D ∧ D = 5` (local `D`); step
/// `B' = B + 1, C' = C, A' = A` written with `D` as the post-state `B'`;
/// bad `B ≥ 2 ∧ C = 5` — reachable in two steps: (T,0,5) → (T,1,5) → (T,2,5).
const LUSTRE_SHAPED_UNSAFE: &str = r#"
(set-logic HORN)
(declare-fun |state| (Bool Int Int) Bool)
(assert (forall ((A Bool) (B Int) (C Int) (D Int))
  (=> (and (= B 0) (= C D) (= D 5) A) (state A B C))))
(assert (forall ((A Bool) (B Int) (C Int) (D Int) (E Int) (F Bool))
  (=> (and (state A B C) (= D (+ B 1)) (= E C) (= F A)) (state F D E))))
(assert (forall ((A Bool) (B Int) (C Int))
  (=> (and (state A B C) (>= B 2) (= C 5)) false)))
(check-sat)
"#;

/// The same system with the safe query `C ≠ 5` (C is invariant at 5).
const LUSTRE_SHAPED_SAFE: &str = r#"
(set-logic HORN)
(declare-fun |state| (Bool Int Int) Bool)
(assert (forall ((A Bool) (B Int) (C Int) (D Int))
  (=> (and (= B 0) (= C D) (= D 5) A) (state A B C))))
(assert (forall ((A Bool) (B Int) (C Int) (D Int) (E Int) (F Bool))
  (=> (and (state A B C) (= D (+ B 1)) (= E C) (= F A)) (state F D E))))
(assert (forall ((A Bool) (B Int) (C Int))
  (=> (and (state A B C) (not (= C 5))) false)))
(check-sat)
"#;

/// Acyclic (no transition): the fact binds a local `B`, the query binds an
/// unrelated local `B`. `state(0)` is initial and the query only needs
/// `A = 0` and some `B = 7`, so the system is UNSAFE; unifying the two `B`s
/// makes the fact/query check spuriously UNSAT.
const ACYCLIC_SHARED_LOCAL_UNSAFE: &str = r#"
(set-logic HORN)
(declare-fun |state| (Int) Bool)
(assert (forall ((A Int) (B Int))
  (=> (and (= A B) (= B 0)) (state A))))
(assert (forall ((A Int) (B Int))
  (=> (and (state A) (= A 0) (= B 7)) false)))
(check-sat)
"#;

/// Depth-0 counterexample with a transition present (so the acyclic path is
/// not taken): the fact binds a local `C = 3`, the query binds an unrelated
/// local `C = 7`. The initial state `(0, 5)` satisfies the query
/// (`A = 0 ∧ B = 5 ∧ ∃C. C = 7`), so the system is UNSAFE at depth 0. With the
/// two `C`s unified the init-safe check, the root query POB's level-0 check
/// and the fact-predecessor query are all spuriously UNSAT.
const DEPTH0_SHARED_LOCAL_UNSAFE: &str = r#"
(set-logic HORN)
(declare-fun |state| (Int Int) Bool)
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (= A 0) (= B 5) (= C 3)) (state A B))))
(assert (forall ((A Int) (B Int) (D Int) (E Int))
  (=> (and (state A B) (= D (+ A 1)) (= E B)) (state D E))))
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (state A B) (= A 0) (= B 5) (= C 7)) false)))
(check-sat)
"#;

fn alias_config() -> PdrConfig {
    PdrConfig {
        verbose: false,
        use_negated_equality_splits: false,
        solve_timeout: Some(std::time::Duration::from_secs(20)),
        ..PdrConfig::default()
    }
}

fn state_pred(solver: &PdrSolver) -> PredicateId {
    solver.problem.get_predicate_by_name("state").unwrap().id
}

/// The level-1 predecessor query of a state one step from init must find the
/// init predecessor. With the fact's `D` captured by the step's `D`
/// (`D = B + 1 = 1` and `D = 5`) the unrenamed query is UNSAT and the POB is
/// wrongly blocked.
#[test]
fn level_one_predecessor_query_renames_the_fact_apart() {
    let problem = ChcParser::parse(LUSTRE_SHAPED_UNSAFE).unwrap();
    let mut solver = PdrSolver::new(problem, alias_config());
    while solver.frames.len() < 3 {
        solver.frames.push(crate::pdr::frame::Frame::new());
    }
    let p = state_pred(&solver);
    let c: Vec<ChcExpr> = solver
        .canonical_vars(p)
        .unwrap()
        .iter()
        .cloned()
        .map(ChcExpr::var)
        .collect();
    // (A, B, C) = (true, 1, 5): one step from the initial (true, 0, 5).
    let state = ChcExpr::and_all([
        c[0].clone(),
        ChcExpr::eq(c[1].clone(), ChcExpr::int(1)),
        ChcExpr::eq(c[2].clone(), ChcExpr::int(5)),
    ]);
    let mut pob = ProofObligation::new(p, state, 1);
    match solver.check_predecessor_reachability(&mut pob, &[]) {
        Err(BlockResult::Reachable(pred)) => {
            assert_eq!(pred.predicate, p);
            assert_eq!(
                pred.clause_index, 1,
                "the predecessor is via the step clause"
            );
        }
        Err(BlockResult::Unknown) => panic!("level-1 predecessor query answered Unknown"),
        Err(
            BlockResult::Blocked(_) | BlockResult::AlreadyBlocked | BlockResult::MustReachable(_),
        ) => panic!("unexpected result from the level-1 predecessor query"),
        Ok(_) => panic!(
            "a state one step from init was blocked at level 1: the fact's local `D` \
             was captured by the step clause's `D`"
        ),
    }
}

/// The level-0 must-summary built from the fact is applied to other clauses'
/// body arguments: its non-canonical (local) variables must be renamed apart.
#[test]
fn init_must_summary_locals_are_renamed_apart() {
    let problem = ChcParser::parse(LUSTRE_SHAPED_UNSAFE).unwrap();
    let mut solver = PdrSolver::new(problem, alias_config());
    assert!(solver.init_must_summaries_from_facts());
    let p = state_pred(&solver);
    let summary = solver
        .reachability
        .must_summaries
        .get(0, p)
        .expect("init must-summary");
    let canon: Vec<String> = solver
        .canonical_vars(p)
        .unwrap()
        .iter()
        .map(|v| v.name.clone())
        .collect();
    let locals: Vec<String> = summary
        .vars()
        .into_iter()
        .map(|v| v.name)
        .filter(|n| !canon.contains(n))
        .collect();
    assert!(
        !locals.is_empty(),
        "the fact's local D survives in the summary: {summary}"
    );
    for name in &locals {
        assert!(
            name.starts_with("__fact0_"),
            "summary local `{name}` is not renamed apart: {summary}"
        );
    }
}

/// Depth-0 counterexample whose query and fact share a local name: must be
/// refuted (fails on main: the init-safe and level-0 checks unify the `C`s).
#[test]
fn depth_zero_counterexample_with_shared_query_fact_local_is_found() {
    let problem = ChcParser::parse(DEPTH0_SHARED_LOCAL_UNSAFE).unwrap();
    let mut solver = PdrSolver::new(problem, alias_config());
    let result = solver.solve();
    assert!(
        matches!(result, PdrResult::Unsafe(_)),
        "the initial state (0, 5) violates the query; got {result:?}"
    );
}

/// The root query POB keeps no source-named local: its locals are renamed
/// apart before the canonical mapping (they meet fact clauses at level 0).
#[test]
fn init_safe_sees_the_depth_zero_violation() {
    let problem = ChcParser::parse(DEPTH0_SHARED_LOCAL_UNSAFE).unwrap();
    let mut solver = PdrSolver::new(problem, alias_config());
    assert!(
        matches!(solver.init_safe(), crate::pdr::types::InitResult::Unsafe),
        "init ∧ bad is satisfiable once the query's `C` and the fact's `C` are apart"
    );
}

/// A counterexample that runs through level 1: PDR must refute the system.
/// With the fact's `D` captured by the step, every step out of init looked
/// impossible to the level-1 query and the depth-2 counterexample was blocked.
#[test]
fn counterexample_through_level_one_is_found() {
    let problem = ChcParser::parse(LUSTRE_SHAPED_UNSAFE).unwrap();
    let mut solver = PdrSolver::new(problem, alias_config());
    let result = solver.solve();
    assert!(
        matches!(result, PdrResult::Unsafe(_)),
        "(T,0,5) → (T,1,5) → (T,2,5) violates B ≥ 2 ∧ C = 5; got {result:?}"
    );
}

/// The safe twin stays safe (the rename never loosens a correct UNSAT).
#[test]
fn safe_twin_is_still_proved_safe() {
    let problem = ChcParser::parse(LUSTRE_SHAPED_SAFE).unwrap();
    let mut solver = PdrSolver::new(problem, alias_config());
    let result = solver.solve();
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "C stays 5; got {result:?}"
    );
}

/// Acyclic fact/query with a shared local name: the system is unsafe and must
/// not be "proved" safe by unifying the fact's `B` with the query's `B`.
#[test]
fn acyclic_fact_query_shared_local_is_unsafe() {
    let problem = ChcParser::parse(ACYCLIC_SHARED_LOCAL_UNSAFE).unwrap();
    let mut solver = PdrSolver::new(problem, alias_config());
    let result = solver.solve();
    assert!(
        !matches!(result, PdrResult::Safe(_)),
        "state(0) is initial and the query needs only A = 0 ∧ ∃B. B = 7; got {result:?}"
    );
    assert!(
        matches!(result, PdrResult::Unsafe(_)),
        "expected Unsafe, got {result:?}"
    );
}

/// The IUC shrink's level-1 frame is the fact joined to the step clause's
/// body. With the fact's `D` captured by the step's `D` (`D = 5` and
/// `D = B + 1`) the frame and the step are jointly UNSAT, so any core — even
/// `{B' = 1}` alone, a state one step from init — "blocks". Renamed apart, the
/// only reason `(B', C') = (1, 6)` is unreachable at level 1 is `C' = 6`.
#[test]
fn iuc_level_one_frame_renames_the_fact_apart() {
    let problem = ChcParser::parse(LUSTRE_SHAPED_UNSAFE).unwrap();
    let mut solver = PdrSolver::new(problem, alias_config());
    let p = state_pred(&solver);
    let c: Vec<ChcExpr> = solver
        .canonical_vars(p)
        .unwrap()
        .iter()
        .cloned()
        .map(ChcExpr::var)
        .collect();
    let b_is_1 = ChcExpr::eq(c[1].clone(), ChcExpr::int(1));
    let c_is_6 = ChcExpr::eq(c[2].clone(), ChcExpr::int(6));
    let shrunk = solver.try_shrink_blocking_conjuncts_with_iuc(&[b_is_1, c_is_6.clone()], p, 1);
    if let Some(shrunk) = shrunk {
        assert!(
            shrunk.contains(&c_is_6),
            "the level-1 core must keep C' = 6 (B' = 1 is reachable at level 1); got {shrunk:?}"
        );
    }
}

/// Init inequalities become lemmas over the predicate's canonical variables:
/// one that mentions a fact local (`D`) is not a predicate invariant, and its
/// free `D` would be captured by the step clause's `D` wherever the lemma is
/// applied. Only canonical-only inequalities survive.
#[test]
fn init_inequalities_keep_only_canonical_variables() {
    const FACT_LOCAL_INEQUALITY: &str = r#"
(set-logic HORN)
(declare-fun |state| (Int Int) Bool)
(assert (forall ((A Int) (B Int) (D Int))
  (=> (and (= A 0) (<= A B) (>= D A) (= D 5) (<= B D)) (state A B))))
(assert (forall ((A Int) (B Int) (D Int) (E Int))
  (=> (and (state A B) (= D (+ A 1)) (= E B)) (state D E))))
(assert (forall ((A Int) (B Int)) (=> (and (state A B) (< A 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(FACT_LOCAL_INEQUALITY).unwrap();
    let solver = PdrSolver::new(problem, alias_config());
    let p = state_pred(&solver);
    let canon: Vec<String> = solver
        .canonical_vars(p)
        .unwrap()
        .iter()
        .map(|v| v.name.clone())
        .collect();
    let inequalities = solver.extract_init_inequalities(p);
    for ineq in &inequalities {
        assert!(
            ineq.vars().iter().all(|v| canon.contains(&v.name)),
            "init inequality `{ineq}` leaks a fact-local variable"
        );
    }
    assert!(
        !inequalities.is_empty(),
        "the canonical-only `A <= B` is kept: {inequalities:?}"
    );
}
