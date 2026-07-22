// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{ChcExpr, ChcSort, ChcVar, Lemma, PdrConfig, PdrSolver};
use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};

fn test_config() -> PdrConfig {
    PdrConfig {
        verbose: false,
        use_negated_equality_splits: false,
        ..PdrConfig::default()
    }
}

fn increment_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x1 = ChcVar::new("x1", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x1.clone()),
                ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x1)]),
    ));
    problem
}

/// #5653 Phase 1A: All discovered invariants now get full SMT checks during
/// push (no spot-check sampling). Verify that non-inductive discovered
/// invariants are always rejected.
#[test]
fn can_push_lemma_rejects_non_inductive_discovered_parity_invariant() {
    let mut solver = PdrSolver::new(increment_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let x = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")[0]
        .clone();

    // x % 2 == 0 is a discovered-invariant shape, but it's not inductive
    // for x' = x + 1.
    let non_inductive_parity = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(2)),
        ChcExpr::int(0),
    );
    assert!(
        PdrSolver::is_discovered_invariant(&non_inductive_parity),
        "parity constraint should be classified as discovered-invariant shape",
    );

    // No counter manipulation needed: all lemma pushes now get full SMT
    // checks in both debug and release builds (#5653 Phase 1A removed
    // the spot-check sampling).
    let lemma = Lemma::new(pred, non_inductive_parity, 1);
    assert!(
        !solver.can_push_lemma(&lemma, 1),
        "non-inductive discovered invariant must fail can_push_lemma",
    );
}
