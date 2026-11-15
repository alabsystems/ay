// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

fn growth_input() -> Vec<ChcExpr> {
    vec![
        ChcExpr::eq(var("x"), nested_f(var("y"), 250)),
        ChcExpr::eq(var("y"), nested_f(var("z"), 250)),
    ]
}

#[test]
fn composition_growth_is_refused_before_the_next_legacy_traversal() {
    let mut input = growth_input();
    let original = input.clone();
    let mut progress = || true;
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
    assert!(names.check_all(&input).is_some());
    assert!(substitute(&mut input, &mut names).is_none());
    assert!(names.stopped());
    assert_eq!(input, original);
    for expression in input.into_iter().chain(original) {
        ChcExpr::iterative_drop(expression);
    }
}

#[test]
fn growth_failure_after_an_earlier_replacement_keeps_the_entire_round() {
    let mut input = vec![ChcExpr::eq(var("w"), ChcExpr::Int(0))];
    input.extend(growth_input());
    let original = input.clone();
    assert_eq!(live_substitute(&mut input), None);
    assert_eq!(input, original);
    for expression in input.into_iter().chain(original) {
        ChcExpr::iterative_drop(expression);
    }
}

fn attempt(input: &mut Vec<ChcExpr>, progress: &mut dyn FnMut() -> bool) -> Option<usize> {
    let mut names = AcyclicNames::new(&ChcProblem::new(), progress)?;
    let result = substitute(input, &mut names);
    if result.is_none() {
        assert!(names.stopped());
        assert!(names.poll().is_none());
    }
    result
}

#[test]
fn every_callback_refusal_is_terminal_and_only_complete_rounds_remain() {
    let input = vec![
        ChcExpr::eq(var("x"), ChcExpr::Int(1)),
        ChcExpr::ne(var("x"), ChcExpr::Int(2)),
    ];
    let mut calls = 0usize;
    let mut expected = input.clone();
    let expected_count = attempt(&mut expected, &mut || {
        calls += 1;
        true
    })
    .unwrap();
    assert!(expected.is_empty());
    assert!((10..4000).contains(&calls));
    for ordinal in 1..=calls {
        let mut actual = input.clone();
        let mut observed = 0;
        assert!(attempt(&mut actual, &mut || {
            observed += 1;
            observed != ordinal
        })
        .is_none());
        assert_eq!(observed, ordinal);
        assert!(
            actual == input || actual == expected,
            "partial round at {ordinal}/{calls}"
        );
    }
    let mut retry = input;
    assert_eq!(attempt(&mut retry, &mut || true), Some(expected_count));
    assert_eq!(retry, expected);
}

#[test]
fn cycle_dependency_walk_polls_and_refuses_every_ordinal() {
    let input = vec![
        ChcExpr::eq(var("a"), call("f", var("b"))),
        ChcExpr::eq(var("b"), call("f", var("c"))),
        ChcExpr::eq(var("c"), call("f", var("a"))),
    ];
    let mut calls = 0usize;
    let expected = {
        let mut progress = || {
            calls += 1;
            true
        };
        let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
        candidates::collect(&input, &mut names).unwrap()
    };
    assert!((10..4000).contains(&calls));
    for ordinal in 1..=calls {
        let mut observed = 0;
        let mut progress = || {
            observed += 1;
            observed != ordinal
        };
        let result = AcyclicNames::new(&ChcProblem::new(), &mut progress)
            .and_then(|mut names| candidates::collect(&input, &mut names));
        assert!(result.is_none());
        assert_eq!(observed, ordinal);
    }
    assert_eq!(expected, oracle::collect(&input));
}

#[test]
fn pre_refusal_keeps_even_an_existing_contradiction_unchanged() {
    let mut input = vec![ChcExpr::Bool(false), ChcExpr::Bool(true)];
    let original = input.clone();
    assert!(attempt(&mut input, &mut || false).is_none());
    assert_eq!(input, original);
}
