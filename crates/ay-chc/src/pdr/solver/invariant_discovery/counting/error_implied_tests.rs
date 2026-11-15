// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Error-implied discovery may only push lemmas closed over the query
//! predicate's canonical variables (#5805's shape, third site).

#![allow(clippy::unwrap_used)]
use super::*;
use crate::pdr::PdrConfig;
use crate::smt::executor_sort_guard::unsupported_executor_expr_reason;
use crate::{ChcParser, ClauseHead};

/// `src` feeds `loop`, whose step has a head argument `J` of sort Int. The
/// query is `loop(A, B) ∧ guard ∧ A ≠ B`, the simple negated-equality shape,
/// from which error-implied discovery derives `loop`'s frame[1] lemma
/// `¬guard ∨ A = B` without an inductiveness check. The step pins `J` with two
/// inequalities because the parser inlines a head variable's defining
/// equality into the head, which would leave no `J` to collide.
fn problem(query_locals: &str, guard: &str) -> String {
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
  (=> (and (loop A B) {guard} (not (= A B))) false)))
(check-sat)
"#
    )
}

/// A solver on `problem` after error-implied discovery, with `loop`'s id.
fn discover(input: &str) -> (PdrSolver, PredicateId) {
    let mut solver = PdrSolver::new(ChcParser::parse(input).unwrap(), PdrConfig::default());
    let lp = solver.problem.get_predicate_by_name("loop").unwrap().id;
    solver.discover_error_implied_invariants();
    (solver, lp)
}

/// Whether the query clause's constraint still mentions `var` (so the test is
/// not vacuous after parsing).
fn query_mentions(solver: &PdrSolver, var: &ChcVar) -> bool {
    solver
        .problem
        .clauses()
        .iter()
        .filter(|c| c.is_query())
        .any(|c| c.body.constraint.iter().any(|e| e.vars().contains(var)))
}

/// Every frame[1] lemma is closed over its predicate's canonical variables.
fn assert_frame1_closed(solver: &PdrSolver) {
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

/// The query's Bool local `J` in the guard (the solver splits the query on
/// `(or J (> B 5))`, one half guarded by `J` alone): the lemma `¬J ∨ A = B`
/// kept `J:Bool` free in frame[1] of `loop`, and the step's own translation to
/// canonical names mapped it onto the Int slot of its head argument `J` (the
/// `substitute_name_map` sort tripwire in a debug build; in release, the Int
/// `__p1_a0` in a Bool position).
#[test]
fn error_implied_lemma_does_not_carry_a_bool_query_local_into_an_int_step() {
    let (solver, lp) = discover(&problem("(J Bool)", "(or J (> B 5))"));
    assert!(query_mentions(&solver, &ChcVar::new("J", ChcSort::Bool)));
    let canon = solver.canonical_vars(lp).unwrap().to_vec();

    // What `check_single_body_predecessor` builds for the self-loop: its
    // constraint and frame[1] of `loop` on the body, translated to canonical
    // names through the head arguments.
    let (step, head_args) = solver
        .problem
        .clauses()
        .iter()
        .find_map(|c| match (&c.head, c.body.predicates.as_slice()) {
            (ClauseHead::Predicate(h, args), [(b, _)]) if *h == lp && *b == lp => Some((c, args)),
            _ => None,
        })
        .unwrap();
    assert!(head_args.contains(&ChcExpr::var(ChcVar::new("J", ChcSort::Int))));
    let (_, body_args) = &step.body.predicates[0];
    let frame = solver.frames[1]
        .get_predicate_constraint(lp)
        .unwrap_or(ChcExpr::Bool(true));
    let frame_on_body = solver.apply_to_args(lp, &frame, body_args).unwrap();
    let step_constraint = step.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
    let transition = ChcExpr::and(step_constraint, frame_on_body);
    let translated = PdrSolver::translate_to_canonical_names(&transition, head_args, &canon);
    assert_eq!(names_with_two_sorts(&translated), Vec::<String>::new());
    for conjunct in translated.conjuncts() {
        assert_eq!(
            unsupported_executor_expr_reason(conjunct),
            None,
            "in {conjunct}"
        );
    }

    assert_frame1_closed(&solver);
}

/// The same-sort case, the shape of 022c-horn_000's query (a guard conjunct
/// over Int locals `G`, `H` only): no tripwire, but free `G`, `H` would be
/// silently captured by any clause that names a variable `G` or `H`.
#[test]
fn error_implied_lemma_does_not_carry_int_query_locals() {
    let (solver, _) = discover(&problem("(G Int) (H Int)", "(> G H) (> B 5)"));
    assert!(query_mentions(&solver, &ChcVar::new("G", ChcSort::Int)));
    assert_frame1_closed(&solver);
}

/// The capability the check must keep: a guard closed over the predicate's
/// arguments still gives `loop` the lemma `¬guard ∨ __p1_a0 = __p1_a1`.
#[test]
fn error_implied_lemma_is_still_pushed_for_a_closed_guard() {
    let (solver, lp) = discover(&problem("", "(> B 5)"));
    let canon = solver.canonical_vars(lp).unwrap().to_vec();
    let conclusion = ChcExpr::eq(
        ChcExpr::var(canon[0].clone()),
        ChcExpr::var(canon[1].clone()),
    );
    let pushed = solver.frames[1].lemmas.iter().any(|lemma| {
        lemma.predicate == lp
            && matches!(&lemma.formula, ChcExpr::Op(ChcOp::Or, args)
                if args.len() == 2
                    && matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Not, _))
                    && *args[1] == conclusion)
    });
    assert!(
        pushed,
        "expected `(or (not guard) {conclusion})` among {:?}",
        solver.frames[1].lemmas
    );
    assert_frame1_closed(&solver);
}
