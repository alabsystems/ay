// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

fn attempt(
    conjuncts: &mut Vec<ChcExpr>,
    env: &mut DetHashMap<String, IntInterval>,
    progress: &mut dyn FnMut() -> bool,
) -> Option<()> {
    let mut names = AcyclicNames::new(&ChcProblem::new(), progress)?;
    let result = simplify(conjuncts, env, &local_scope(), &mut names);
    if result.is_none() {
        assert!(names.stopped());
        assert!(names.poll().is_none());
    }
    result
}

#[test]
fn every_callback_refusal_keeps_complete_rounds_and_refuses_final_publication() {
    let input = vec![boolean("b"), ChcExpr::or(boolean("b"), boolean("c"))];
    let initial_env: DetHashMap<_, _> = [("seed".to_owned(), IntInterval::exact(3))]
        .into_iter()
        .collect();
    let mut expected = input.clone();
    let mut expected_env = initial_env.clone();
    let mut calls = 0usize;
    assert_eq!(
        attempt(&mut expected, &mut expected_env, &mut || {
            calls += 1;
            true
        }),
        Some(())
    );
    assert!(expected.is_empty());
    assert_eq!(expected_env, initial_env);
    assert!((10..4000).contains(&calls));
    for ordinal in 1..=calls {
        let mut actual = input.clone();
        let mut env = initial_env.clone();
        let mut observed = 0;
        assert!(attempt(&mut actual, &mut env, &mut || {
            observed += 1;
            observed != ordinal
        })
        .is_none());
        assert_eq!(observed, ordinal);
        assert!(actual == input || actual == expected);
        assert_eq!(env, initial_env);
    }
    let mut retry = input;
    let mut env = initial_env;
    assert_eq!(attempt(&mut retry, &mut env, &mut || true), Some(()));
    assert_eq!(retry, expected);
    assert_eq!(env, expected_env);
}

#[test]
fn cancellation_never_turns_boolean_conflict_into_success() {
    let input = vec![boolean("b"), ChcExpr::not(boolean("b"))];
    let mut output = input.clone();
    let mut env = DetHashMap::default();
    assert!(attempt(&mut output, &mut env, &mut || false).is_none());
    assert_eq!(output, input);
    assert_eq!(attempt(&mut output, &mut env, &mut || true), Some(()));
    assert_eq!(output, vec![ChcExpr::Bool(false)]);
}

#[test]
fn interrupted_bound_collection_never_commits_only_one_endpoint() {
    let input = vec![
        ChcExpr::ge(integer("x"), ChcExpr::Int(1)),
        ChcExpr::le(integer("x"), ChcExpr::Int(1)),
    ];
    let expected_env: DetHashMap<_, _> = [("x".to_owned(), IntInterval::exact(1))]
        .into_iter()
        .collect();
    let mut expected = input.clone();
    let mut completed_env = DetHashMap::default();
    let mut calls = 0usize;
    assert_eq!(
        attempt(&mut expected, &mut completed_env, &mut || {
            calls += 1;
            true
        }),
        Some(())
    );
    assert_eq!(completed_env, expected_env);
    assert_eq!(expected, input);
    assert!((10..4000).contains(&calls));
    for ordinal in 1..=calls {
        let mut actual = input.clone();
        let mut env = DetHashMap::default();
        let mut observed = 0;
        assert!(attempt(&mut actual, &mut env, &mut || {
            observed += 1;
            observed != ordinal
        })
        .is_none());
        assert_eq!(observed, ordinal);
        assert_eq!(actual, input);
        assert!(
            env.is_empty() || env == expected_env,
            "partial interval at {ordinal}/{calls}"
        );
    }
}
