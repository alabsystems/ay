// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Error-guided discovery may only push lemmas closed over the query
//! predicate's canonical variables (#5805's shape, second site).

#![allow(clippy::unwrap_used)]
use super::*;
use crate::pdr::PdrConfig;
use crate::{ChcParser, ClauseHead};

/// `src` feeds `loop` (no facts of its own); `loop`'s step carries a Bool
/// variable `C`, and the query compares with an Int local `C`. Error-guided
/// discovery negates each comparison conjunct of the query: the closed
/// `(< A B)` gives `loop`'s real invariant `__p0 >= __p1`, and `(< (+ A C) C)`
/// gives `(+ __p0 C) >= C`. That candidate is valid for every `C`, so every
/// check passes with `C` free, and it would reach frame[1] with the query's
/// `C:Int` unbound, to be captured by the step's `C:Bool`.
const PROBLEM: &str = r#"
(set-logic HORN)
(declare-fun src (Int) Bool)
(declare-fun loop (Int Int) Bool)
(assert (forall ((A Int)) (=> (= A 0) (src A))))
(assert (forall ((A Int) (J Int) (K Int))
  (=> (and (src A) (= J A) (= K A)) (loop J K))))
(assert (forall ((A Int) (B Int) (C Bool) (J Int) (K Int))
  (=> (and (loop A B) C (>= J (+ A 1)) (<= J (+ A 1)) (= K (+ B 1))) (loop J K))))
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (loop A B) (< A B) (< (+ A C) C)) false)))
(check-sat)
"#;

fn discover() -> (PdrSolver, PredicateId) {
    let problem = ChcParser::parse(PROBLEM).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let src = solver.problem.get_predicate_by_name("src").unwrap().id;
    let lp = solver.problem.get_predicate_by_name("loop").unwrap().id;
    let x = solver.canonical_vars(src).unwrap()[0].clone();
    solver.frames[1].add_lemma(Lemma::new(
        src,
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0)),
        1,
    ));
    let queries: Vec<HornClause> = solver
        .problem
        .clauses()
        .iter()
        .filter(|clause| matches!(clause.head, ClauseHead::False))
        .cloned()
        .collect();
    let _ = solver.try_error_guided_discovery(&queries, &[]);
    (solver, lp)
}

#[test]
fn error_guided_discovery_never_pushes_a_lemma_over_a_query_local() {
    let (solver, _) = discover();
    for lemma in &solver.frames[1].lemmas {
        let canonical = solver.canonical_vars(lemma.predicate).unwrap();
        let free: Vec<_> = lemma
            .formula
            .vars()
            .into_iter()
            .filter(|v| !canonical.contains(v))
            .collect();
        assert!(free.is_empty(), "free {free:?} in {}", lemma.formula);
    }
}

/// The capability the filter must keep: the closed conjunct still yields its
/// lemma.
#[test]
fn error_guided_discovery_still_pushes_the_closed_conjunct() {
    let (solver, lp) = discover();
    let canon = solver.canonical_vars(lp).unwrap().to_vec();
    let expected = ChcExpr::ge(
        ChcExpr::var(canon[0].clone()),
        ChcExpr::var(canon[1].clone()),
    );
    let lemmas: Vec<String> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|lemma| lemma.predicate == lp)
        .map(|lemma| lemma.formula.to_string())
        .collect();
    assert!(
        lemmas.contains(&expected.to_string()),
        "expected {expected} among loop's frame[1] lemmas {lemmas:?}"
    );
}
