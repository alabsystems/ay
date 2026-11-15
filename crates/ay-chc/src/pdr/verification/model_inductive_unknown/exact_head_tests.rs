// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::pdr::PdrConfig;
use crate::{ChcParser, ClauseHead};
use std::time::Duration;

const TRANSITION: &str = r#"
(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(assert (forall ((x Int)) (=> (A x) (B x))))
"#;

fn check_unknown_fallback(valid: bool) {
    let problem = ChcParser::parse(TRANSITION).unwrap();
    assert_eq!(problem.clauses().len(), 1);
    let clause = problem.clauses()[0].clone();
    let ClauseHead::Predicate(head_pred, args) = &clause.head else {
        panic!("transition head");
    };
    assert_eq!(args.len(), 1);
    let x = args[0].clone();
    let body = if valid {
        ChcExpr::gt(x.clone(), ChcExpr::Int(0))
    } else {
        ChcExpr::ge(x.clone(), ChcExpr::Int(0))
    };
    let head = ChcExpr::not(ChcExpr::eq(x, ChcExpr::Int(0)));
    assert_eq!(
        PdrSolver::filter_blocking_lemmas(&head),
        ChcExpr::Bool(true)
    );
    assert_eq!(PdrSolver::filter_blocking_lemmas_aggressive(&body), body);
    assert!(PdrSolver::fixed_int_subst_from_conjuncts(&body).is_empty());
    let query = ChcExpr::and(body.clone(), ChcExpr::not(head.clone()));
    let mut solver = PdrSolver::new(
        problem,
        PdrConfig {
            strict_proofs: true,
            preserve_original_clauses: true,
            ..PdrConfig::default()
        },
    );
    let result = solver
        .smt
        .check_sat_with_timeout(&query, Duration::from_secs(2));
    if valid {
        assert!(
            matches!(
                result,
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
            ),
            "got {result:?}"
        );
    } else {
        assert!(matches!(result, SmtResult::Sat(_)), "got {result:?}");
    }
    solver.smt.reset();
    let mut used_filtered = false;
    // Invoke the Unknown fallback directly: no timing-dependent fake timeout
    // and no injected accepting SMT result. Its retries check real formulas.
    let failure = solver.handle_unknown_transition_clause(
        &clause,
        0,
        &body,
        &query,
        &head,
        head_pred,
        Duration::from_secs(2),
        None,
        None,
        &mut used_filtered,
    );
    assert_eq!(failure.is_none(), valid, "got {failure:?}");
    // The positive reaches the filtered-body strategy, but the strict query
    // still contains the original head. The invalid case must not pass it.
    assert_eq!(used_filtered, valid);
}

#[test]
fn unknown_fallback_rejects_satisfiable_original_head_violation() {
    check_unknown_fallback(false);
}

#[test]
fn unknown_fallback_accepts_exact_head_proof() {
    check_unknown_fallback(true);
}
