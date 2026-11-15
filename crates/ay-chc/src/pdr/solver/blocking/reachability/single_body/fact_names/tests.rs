// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcOp, ChcParser, ChcSort};
use std::sync::Arc;

const COLLISIONS: &str = r#"
(set-logic HORN)
(declare-fun B (Int Int) Bool)
(declare-fun __lvl0_fact_0_x_1_1 () Int)
(assert (forall ((x Int) (x_1 Int))
  (=> (and (= x 0) (= x_1 1)) (B x x_1))))
(assert (forall ((__lvl0_fact_0_x Int))
  (=> (and (B __lvl0_fact_0_x 1) (= __lvl0_fact_0_x_1_1 9)) false)))
(check-sat)
"#;

fn fact(problem: &ChcProblem) -> (&ChcExpr, &[ChcExpr]) {
    let clause = &problem.clauses()[0];
    let ClauseHead::Predicate(_, args) = &clause.head else {
        panic!("expected fact head");
    };
    (clause.body.constraint.as_ref().unwrap(), args)
}

#[test]
fn source_and_sibling_collisions_have_stable_exact_renaming() {
    let problem = ChcParser::parse(COLLISIONS).unwrap();
    let names = SourceNames::collect(&problem, &mut || true).unwrap();
    assert!(names.used.contains("__lvl0_fact_0_x"));
    assert!(names.used.contains("__lvl0_fact_0_x_1_1"));
    let (constraint, args) = fact(&problem);
    let result = names
        .rename(constraint, args, "__lvl0_fact_0_", [], &mut || true)
        .unwrap();
    let fresh_x = ChcVar::new("__lvl0_fact_0_x_1", ChcSort::Int);
    let fresh_x_1 = ChcVar::new("__lvl0_fact_0_x_1_2", ChcSort::Int);
    assert_eq!(
        result.1,
        [
            ChcExpr::var(fresh_x.clone()),
            ChcExpr::var(fresh_x_1.clone())
        ]
    );
    let expected = [
        (ChcVar::new("x", ChcSort::Int), ChcExpr::var(fresh_x)),
        (ChcVar::new("x_1", ChcSort::Int), ChcExpr::var(fresh_x_1)),
    ];
    assert_eq!(result.0, constraint.substitute(&expected));
    let unrelated = ChcExpr::var(ChcVar::new("later_query_local", ChcSort::Bool));
    assert_eq!(
        Some(result.clone()),
        names.rename(
            constraint,
            args,
            "__lvl0_fact_0_",
            [&unrelated],
            &mut || true,
        )
    );
    // The allocated name is not re-suffixed by a POB change: doing that could
    // reuse a cached clause/fact segment whose background had different names.
    assert!(names
        .rename(
            constraint,
            args,
            "__lvl0_fact_0_",
            [&result.1[0]],
            &mut || true
        )
        .is_none());
    assert_eq!(
        Some(result),
        names.rename(constraint, args, "__lvl0_fact_0_", [], &mut || true)
    );
}

#[test]
fn exact_postcheck_refuses_depth_truncated_substitution() {
    let names = SourceNames {
        used: FxHashSet::from_iter(["x".to_owned()]),
    };
    let mut deep = ChcExpr::var(ChcVar::new("x", ChcSort::Bool));
    for _ in 0..crate::expr::MAX_EXPR_RECURSION_DEPTH + 2 {
        deep = ChcExpr::Op(ChcOp::Not, vec![Arc::new(deep)]);
    }
    let mut found = false;
    walk([&deep], &mut || true, |expr| {
        found |= matches!(expr, ChcExpr::Var(_));
        Some(())
    })
    .unwrap();
    assert!(found, "the independent census must reach the deep variable");
    assert!(names
        .rename(&deep, &[], "__lvl0_fact_0_", [], &mut || true)
        .is_none());
    let shallow = ChcExpr::not(ChcExpr::var(ChcVar::new("x", ChcSort::Bool)));
    assert!(names
        .rename(&shallow, &[], "__lvl0_fact_0_", [], &mut || true)
        .is_some());
}

#[test]
fn malformed_same_name_different_sort_fact_refuses() {
    let names = SourceNames {
        used: FxHashSet::from_iter(["x".to_owned()]),
    };
    let constraint = ChcExpr::var(ChcVar::new("x", ChcSort::Bool));
    let args = [ChcExpr::var(ChcVar::new("x", ChcSort::Int))];
    assert!(names
        .rename(&constraint, &args, "__lvl0_fact_0_", [], &mut || true)
        .is_none());
}

#[test]
fn every_observed_stop_refuses_even_if_callback_would_recover() {
    let problem = ChcParser::parse(COLLISIONS).unwrap();
    let (constraint, args) = fact(&problem);
    let run = |open: &mut dyn FnMut() -> bool| {
        let mut open = || open();
        let names = SourceNames::collect(&problem, &mut open)?;
        names.rename(constraint, args, "__lvl0_fact_0_", [], &mut open)
    };
    let mut total = 0;
    assert!(run(&mut || {
        total += 1;
        true
    })
    .is_some());
    assert!(total > 10);
    for stop in 1..=total {
        let mut seen = 0;
        assert!(
            run(&mut || {
                seen += 1;
                seen != stop
            })
            .is_none(),
            "stop {stop}"
        );
        assert_eq!(seen, stop, "an observed stop must not be polled away");
    }
}
