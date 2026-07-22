// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::parser::ChcParser;
use crate::pdr::config::PdrConfig;
use crate::pdr::frame::{Frame, Lemma};
use crate::pdr::solver::PdrSolver;
use crate::smt::SmtResult;
use crate::ChcExpr;

/// #6366 regression: ITE transitions must not cause false non-inductive results.
///
/// Tests that the PDR inductiveness checks correctly identify `x >= 0` as
/// inductive for a transition with ITE: `x' = ite(x >= 5, x - 5, x + 1)`.
///
/// Originally the incremental solver returned spurious Sat for ITE clauses,
/// requiring a fall-through to non-incremental case-splitting. After W5's
/// DPLL(T) variable-mapping fix (0ccc93a54), the incremental solver may
/// correctly handle some ITE formulas directly. The end-to-end PDR checks
/// must give correct results regardless of the incremental path taken.
#[test]
fn test_ite_transition_incremental_fallthrough_6366() {
    let smt2 = "(set-logic HORN)(declare-fun inv (Int) Bool)\
        (assert (forall ((x Int)) (=> (= x 0) (inv x))))\
        (assert (forall ((x Int) (x_next Int))\
          (=> (and (inv x) (= x_next (ite (>= x 5) (- x 5) (+ x 1)))) (inv x_next))))\
        (check-sat)";
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();
    let transition = solver
        .problem
        .transitions()
        .next()
        .expect("expected one transition clause")
        .clone();
    let clause_constraint = transition
        .body
        .constraint
        .clone()
        .expect("transition should carry the ITE background");
    let head_args = match &transition.head {
        crate::ClauseHead::Predicate(_, args) => args.as_slice(),
        crate::ClauseHead::False => panic!("expected predicate head"),
    };
    let (body_pred, body_args) = &transition.body.predicates[0];
    assert_eq!(*body_pred, inv, "test requires a self-loop transition");

    let lemma = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(0));
    let blocking = ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0));
    let lemma_on_body = solver
        .apply_to_args(inv, &lemma, body_args)
        .expect("body args should instantiate lemma");
    let blocking_on_head = solver
        .apply_to_args(inv, &blocking, head_args)
        .expect("head args should instantiate blocking formula");

    // The full query (with ITE case-split) is UNSAT: x >= 0 is inductive.
    let full_query = solver.bound_int_vars(ChcExpr::and_all([
        lemma_on_body,
        clause_constraint,
        blocking_on_head,
    ]));
    let simplified = full_query.propagate_equalities();
    let (full_result, _) = PdrSolver::check_sat_with_ite_case_split(
        &mut solver.smt,
        solver.config.verbose,
        &simplified,
    );
    assert!(
        matches!(
            full_result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "case-split query must be UNSAT; got {full_result:?}"
    );

    // End-to-end PDR inductiveness checks: all must agree the lemma is inductive.
    solver.frames.push(Frame::default());
    solver.frames.push(Frame::default());
    assert!(
        solver.is_self_inductive_blocking(&blocking, inv),
        "is_self_inductive_blocking must accept inductive lemma with ITE transition"
    );
    assert!(
        solver.is_strictly_self_inductive_blocking(&blocking, inv),
        "is_strictly_self_inductive_blocking must accept inductive lemma with ITE transition"
    );
    solver.frames[1].add_lemma(Lemma::new(inv, lemma.clone(), 1));
    assert!(
        solver.can_push_lemma(&Lemma::new(inv, lemma, 1), 1),
        "can_push_lemma must accept inductive lemma with ITE transition"
    );
}
