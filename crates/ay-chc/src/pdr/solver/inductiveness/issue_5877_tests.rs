// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::parser::ChcParser;
use crate::pdr::config::PdrConfig;
use crate::pdr::solver::PdrSolver;
use crate::ChcExpr;

#[test]
fn test_add_discovered_invariant_same_level_duplicate_is_noop() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x_next Int))
  (=> (and (inv x) (= x_next (+ x 1))) (inv x_next))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();
    let non_negative = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));

    assert!(
        solver.add_discovered_invariant(inv, non_negative.clone(), 1),
        "first discovered invariant insertion should succeed"
    );
    let frame_lemma_count = solver.frames[1].lemmas.len();

    assert!(
        solver.add_discovered_invariant(inv, non_negative.clone(), 1),
        "re-adding the same discovered invariant at the same level should succeed"
    );
    assert_eq!(
        solver.frames[1].lemmas.len(),
        frame_lemma_count,
        "same-level duplicate insertion should not grow frame[1]"
    );
    assert!(
        solver.frames[1].contains_lemma(inv, &non_negative),
        "frame[1] should still contain the original invariant"
    );
}

#[test]
fn test_add_discovered_invariant_duplicate_upgrades_algebraic_flag() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x_next Int))
  (=> (and (inv x) (= x_next (+ x 1))) (inv x_next))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();
    let non_negative = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));

    assert!(
        solver.add_discovered_invariant(inv, non_negative.clone(), 1),
        "first insertion should succeed"
    );
    let frame_lemma_count = solver.frames[1].lemmas.len();
    let lemma_before = solver.frames[1]
        .lemmas
        .iter()
        .find(|lemma| lemma.predicate == inv && lemma.formula == non_negative)
        .expect("lemma should exist after first insertion");
    assert!(
        !lemma_before.algebraically_verified,
        "initial non-algebraic insertion should keep algebraic flag cleared"
    );

    assert!(
        solver.add_discovered_invariant_algebraic(inv, non_negative.clone(), 1),
        "algebraic duplicate insertion should succeed"
    );
    assert_eq!(
        solver.frames[1].lemmas.len(),
        frame_lemma_count,
        "algebraic duplicate insertion should not grow frame[1]"
    );
    let lemma_after = solver.frames[1]
        .lemmas
        .iter()
        .find(|lemma| lemma.predicate == inv && lemma.formula == non_negative)
        .expect("lemma should still exist after algebraic upgrade");
    assert!(
        lemma_after.algebraically_verified,
        "duplicate algebraic insertion should upgrade the stored lemma"
    );
}
