// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::pdr::PdrConfig;
use crate::{CancellationToken, ChcParser, ChcSort, ChcVar};

const SOURCE: &str = r#"
(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(declare-fun C (Int Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (A x))))
(assert (forall ((x Int)) (=> (= x 1) (B x))))
(assert (forall ((a Int) (b Int)) (=> (and (A a) (B b)) (C a b))))
"#;

fn solver(token: CancellationToken) -> PdrSolver {
    PdrSolver::new(
        ChcParser::parse(SOURCE).unwrap(),
        PdrConfig {
            preserve_original_clauses: true,
            use_must_summaries: false,
            use_mixed_summaries: false,
            cancellation_token: Some(token),
            ..PdrConfig::default()
        },
    )
}

#[test]
fn malformed_later_fact_does_not_publish_an_earlier_partial_context() {
    for wrong_sort in [false, true] {
        let mut solver = solver(CancellationToken::new());
        let clause = solver.problem.clauses()[2].clone();
        let mut contexts = vec![ChcExpr::Bool(true)];
        assert!(append_fact_fallbacks(&solver, &mut contexts, 2, &clause).is_some());
        assert_eq!(
            contexts.len(),
            3,
            "both actual fact contexts must be present"
        );
        let fact = &mut solver.problem.clauses_mut()[1];
        if wrong_sort {
            // The head still binds x:Int. A name-only census would silently
            // overwrite the incompatible Bool local and keep a partial rename.
            fact.body.constraint = Some(ChcExpr::var(ChcVar::new("x", ChcSort::Bool)));
        } else {
            let crate::ClauseHead::Predicate(_, args) = &mut fact.head else {
                panic!("fact")
            };
            args.clear();
        }
        let original = vec![ChcExpr::Bool(true)];
        let mut contexts = original.clone();
        assert!(append_fact_fallbacks(&solver, &mut contexts, 2, &clause).is_none());
        assert_eq!(
            contexts, original,
            "failed joins publish no partial constraints"
        );
        let pred = solver.problem.lookup_predicate("C").unwrap();
        assert!(!solver.is_entry_inductive(&ChcExpr::Bool(true), pred, 1));
    }
}

#[test]
fn stopped_fact_join_is_none_not_an_empty_or_false_predecessor() {
    let token = CancellationToken::new();
    let solver = solver(token.clone());
    let clause = solver.problem.clauses()[2].clone();
    let original = vec![ChcExpr::Bool(true)];
    let mut contexts = original.clone();
    token.cancel();
    assert!(append_fact_fallbacks(&solver, &mut contexts, 2, &clause).is_none());
    assert_eq!(contexts, original);
    // A different, open attempt demonstrates that the fixture has real joins.
    token.reset();
    assert!(append_fact_fallbacks(&solver, &mut contexts, 2, &clause).is_some());
    assert_eq!(contexts.len(), 3);
}
