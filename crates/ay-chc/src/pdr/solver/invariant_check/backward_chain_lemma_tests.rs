// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The #1306 backward-chain lemma must be closed over the query predicate's
//! canonical variables (#5805): a free query local reaches every clause the
//! frame is conjoined with and is captured there by a same-named variable.

#![allow(clippy::unwrap_used)]
use super::*;
use crate::pdr::PdrConfig;
use crate::{ChcParser, ClauseHead};

/// `src` feeds `loop`, whose step has a head argument named `J` of sort Int;
/// the query names a Bool local `J`. The backward chain through the entry
/// clause proves the error unreachable (it enters at `loop(A, A)`), which is
/// what sends the query constraint into frame[1] of `loop`. The step pins `J`
/// with two inequalities because the parser inlines a head variable's
/// defining equality into the head, which would leave no `J` to collide.
fn problem(query_constraint: &str, query_locals: &str) -> String {
    format!(
        r#"
(set-logic HORN)
(declare-fun src (Int) Bool)
(declare-fun loop (Int Int) Bool)
(assert (forall ((A Int)) (=> (= A 0) (src A))))
(assert (forall ((A Int) (J Int) (K Int))
  (=> (and (src A) (= J A) (= K A)) (loop J K))))
(assert (forall ((A Int) (B Int) (J Int) (K Int))
  (=> (and (loop A B) (>= J (+ A 1)) (<= J (+ A 1)) (= K (+ B 1))) (loop J K))))
(assert (forall ((A Int) (B Int) {query_locals})
  (=> (and (loop A B) {query_constraint}) false)))
(check-sat)
"#
    )
}

/// A solver on `problem` with `src`'s exact invariant in frame[1] (the
/// backward chain needs one for the source predicate) and nothing for `loop`
/// (so the query reaches the backward-chain branch), after the safety check.
fn solve_backward_chain(input: &str) -> (PdrSolver, PredicateId) {
    let problem = ChcParser::parse(input).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let src = solver.problem.get_predicate_by_name("src").unwrap().id;
    let lp = solver.problem.get_predicate_by_name("loop").unwrap().id;
    let x = solver.canonical_vars(src).unwrap()[0].clone();
    let init = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0));
    solver.frames[1].add_lemma(Lemma::new(src, init, 1));
    let _ = solver.check_invariants_prove_safety();
    (solver, lp)
}

/// The names that occur in `expr` under more than one sort.
fn names_with_two_sorts(expr: &ChcExpr) -> Vec<String> {
    let vars = expr.vars();
    let mut mixed: Vec<String> = vars
        .iter()
        .filter(|v| vars.iter().any(|w| w.name == v.name && w.sort != v.sort))
        .map(|v| v.name.clone())
        .collect();
    mixed.dedup();
    mixed
}

#[test]
fn backward_chain_lemma_does_not_carry_a_bool_query_local_into_an_int_step_5805() {
    let (solver, lp) = solve_backward_chain(&problem("(= J (< A B)) J", "(J Bool)"));
    let canon = solver.canonical_vars(lp).unwrap().to_vec();

    // The construction `check_single_body_predecessor` builds for the
    // self-loop: its constraint and frame[1] of `loop` on the body, translated
    // to canonical names through the head arguments `(J (+ B 1))`. Before the fix
    // frame[1] held `¬(J = (__p1_a0 < __p1_a1) ∧ J)` with the query's `J:Bool`
    // free, and this translation mapped it onto the Int slot `__p1_a0` (the
    // `substitute_name_map` sort tripwire; in release, one symbol, two sorts).
    let (step, head_args) = solver
        .problem
        .clauses()
        .iter()
        .find_map(|c| match (&c.head, c.body.predicates.as_slice()) {
            (ClauseHead::Predicate(h, args), [(b, _)]) if *h == lp && *b == lp => Some((c, args)),
            _ => None,
        })
        .unwrap();
    let (_, body_args) = &step.body.predicates[0];
    let frame = solver.frames[1]
        .get_predicate_constraint(lp)
        .unwrap_or(ChcExpr::Bool(true));
    let frame_on_body = solver.apply_to_args(lp, &frame, body_args).unwrap();
    let step_constraint = step.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
    let transition = ChcExpr::and(step_constraint, frame_on_body);
    let translated = PdrSolver::translate_to_canonical_names(&transition, head_args, &canon);
    assert_eq!(names_with_two_sorts(&translated), Vec::<String>::new());

    // And the source of it: no frame[1] lemma of any predicate mentions a
    // variable that is not one of that predicate's canonical variables.
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

/// The #1306 capability the fix must keep: a query closed over the predicate
/// arguments still gives frame[1] of `loop` exactly `¬error`.
#[test]
fn backward_chain_lemma_still_pushes_a_closed_error_1306() {
    let (solver, lp) = solve_backward_chain(&problem("(< A B)", ""));
    let canon = solver.canonical_vars(lp).unwrap().to_vec();
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let query = solver
        .problem
        .clauses()
        .iter()
        .find(|c| c.is_query())
        .unwrap();
    let error = query.body.constraint.clone().unwrap().substitute(&[
        (a, ChcExpr::var(canon[0].clone())),
        (b, ChcExpr::var(canon[1].clone())),
    ]);
    let expected = ChcExpr::not(error);
    assert!(
        solver.frames[1]
            .lemmas
            .iter()
            .any(|l| l.predicate == lp && l.formula == expected),
        "frame[1] lacks {expected}: {:?}",
        solver.frames[1].lemmas
    );
}

/// Closed means name AND sort: a local spelled like a canonical variable but
/// of another sort is still a local.
#[test]
fn backward_chain_lemma_requires_canonical_name_and_sort() {
    let problem = ChcParser::parse(&problem("(< A B)", "")).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());
    let lp = solver.problem.get_predicate_by_name("loop").unwrap().id;
    let canon = solver.canonical_vars(lp).unwrap().to_vec();
    let a0 = ChcExpr::var(canon[0].clone());
    let a1 = ChcExpr::var(canon[1].clone());

    let closed = ChcExpr::lt(a0.clone(), a1);
    assert_eq!(
        solver.backward_chain_lemma(&closed, &canon),
        Some(ChcExpr::not(closed))
    );

    let local = ChcExpr::and(
        ChcExpr::lt(a0.clone(), ChcExpr::int(3)),
        ChcExpr::var(ChcVar::new("J", ChcSort::Bool)),
    );
    assert_eq!(solver.backward_chain_lemma(&local, &canon), None);

    let wrong_sort = ChcExpr::and(
        ChcExpr::lt(a0, ChcExpr::int(3)),
        ChcExpr::var(ChcVar::new(canon[1].name.clone(), ChcSort::Bool)),
    );
    assert_eq!(solver.backward_chain_lemma(&wrong_sort, &canon), None);
}

/// Facts plus a self-loop: the backward chain may not skip the loop. `P` starts
/// at 0 and steps by 1, so the error `x = 1` is reachable in one step from a
/// fact state; a check that skipped the self-loop called it unreachable.
#[test]
fn backward_chain_does_not_skip_the_self_loop_of_a_predicate_with_facts() {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (= y (+ x 1))) (P y))))
(assert (forall ((x Int)) (=> (and (P x) (= x 1)) false)))
(check-sat)
"#,
    )
    .unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let p = solver.problem.get_predicate_by_name("P").unwrap().id;
    let canon = solver.canonical_vars(p).unwrap().to_vec();
    let error = ChcExpr::eq(ChcExpr::var(canon[0].clone()), ChcExpr::int(1));
    assert!(
        !solver.check_backward_chain_safety(p, &error, &canon),
        "x = 1 is one self-loop step from the fact x = 0"
    );
}
