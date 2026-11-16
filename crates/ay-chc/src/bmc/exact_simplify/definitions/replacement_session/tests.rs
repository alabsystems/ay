// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::{ChcOp, ChcProblem, ChcSort, ChcVar};
use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::Arc;

fn var(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, ChcSort::Int))
}

fn nested(mut expression: ChcExpr, edges: usize) -> ChcExpr {
    for _ in 0..edges {
        expression = ChcExpr::FuncApp("f".to_owned(), ChcSort::Int, vec![Arc::new(expression)]);
    }
    expression
}

fn counted<T>(operation: impl FnOnce(&mut AcyclicNames<'_>) -> T) -> (T, usize) {
    let polls = Cell::new(0usize);
    let mut progress = || {
        polls.set(polls.get() + 1);
        true
    };
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
    polls.set(0);
    let result = operation(&mut names);
    (result, polls.get())
}

#[test]
fn substitutions_match_legacy_for_aliases_shared_dags_and_repeated_inputs() {
    let shared = Arc::new(nested(var("x"), 3));
    let repeated = ChcExpr::Op(
        ChcOp::Add,
        vec![Arc::clone(&shared), Arc::clone(&shared), shared],
    );
    let inputs = [var("x"), var("y"), repeated.clone(), repeated, var("free")];
    let mut map = DetHashMap::default();
    map.insert("x".to_owned(), nested(var("y"), 2));
    map.insert("y".to_owned(), ChcExpr::Int(3));
    let (legacy, _) = counted(|names| {
        inputs
            .iter()
            .map(|input| names.substitute(input, &map).unwrap())
            .collect::<Vec<_>>()
    });
    let (prepared, _) = counted(|names| {
        let mut session = ReplacementSession::new(&map, names);
        inputs
            .iter()
            .map(|input| session.substitute(input).unwrap())
            .collect::<Vec<_>>()
    });
    assert_eq!(prepared, legacy);
    // Name substitution is simultaneous, not recursively composed through y.
    assert_eq!(prepared[0], nested(var("y"), 2));
    assert_eq!(prepared[1], ChcExpr::Int(3));
}

#[test]
fn one_map_admission_saves_exactly_the_repeated_rhs_scan_polls() {
    let mut map = DetHashMap::default();
    for index in 0..3 {
        map.insert(format!("x{index}"), nested(ChcExpr::Int(index), 40));
    }
    let inputs = (0..6)
        .map(|index| var(&format!("x{}", index % 3)))
        .collect::<Vec<_>>();
    let (legacy, legacy_polls) = counted(|names| {
        inputs
            .iter()
            .map(|input| names.substitute(input, &map))
            .collect::<Option<Vec<_>>>()
    });
    let (prepared, prepared_polls) = counted(|names| {
        let mut session = ReplacementSession::new(&map, names);
        inputs
            .iter()
            .map(|input| session.substitute(input))
            .collect::<Option<Vec<_>>>()
    });
    let ((), rhs_polls) = counted(|names| {
        for replacement in map.values() {
            names.check(replacement).unwrap();
        }
    });
    assert!(prepared.is_some());
    assert_eq!(prepared, legacy);
    assert!(rhs_polls > 100);
    assert_eq!(
        legacy_polls - prepared_polls,
        (inputs.len() - 1) * rhs_polls
    );
    // This measures existing admission/control visits, not elapsed time or
    // work inside the unchanged pure substitution and simplification methods.
}

#[test]
fn lazy_admission_preserves_empty_first_input_and_early_false_order() {
    let too_deep = nested(ChcExpr::Int(0), crate::expr::MAX_EXPR_RECURSION_DEPTH);
    let mut map = DetHashMap::default();
    map.insert("x".to_owned(), too_deep.clone());
    let (empty, _) = counted(|names| super::super::build_round(&[], &map, names));
    assert_eq!(empty.unwrap().conjuncts, [] as [ChcExpr; 0]);

    // A distinct cheap RHS makes an eager-map regression observably add polls
    // before the deep input refuses, rather than failing at an identical walk.
    map.insert("x".to_owned(), ChcExpr::Int(0));
    let (legacy, legacy_polls) = counted(|names| names.substitute(&too_deep, &map));
    let (prepared, prepared_polls) =
        counted(|names| ReplacementSession::new(&map, names).substitute(&too_deep));
    assert!(legacy.is_none() && prepared.is_none());
    assert_eq!(prepared_polls, legacy_polls);

    // Even false must admit the replacement map, as in the old per-input path.
    map.insert("x".to_owned(), too_deep.clone());
    let (invalid, _) =
        counted(|names| super::super::build_round(&[ChcExpr::Bool(false)], &map, names));
    assert!(invalid.is_none());
    map.insert("x".to_owned(), ChcExpr::Int(0));
    let input = [ChcExpr::Bool(false), too_deep.clone()];
    let (early_false, _) = counted(|names| super::super::build_round(&input, &map, names));
    let round = early_false.unwrap();
    assert_eq!(round.conjuncts, vec![ChcExpr::Bool(false)]);
    assert_eq!(round.changed, 0);
    ChcExpr::iterative_drop(too_deep);
    for expression in input {
        ChcExpr::iterative_drop(expression);
    }
}

#[test]
fn every_session_poll_refusal_is_sticky_without_repolling() {
    let mut map = DetHashMap::default();
    map.insert("x".to_owned(), nested(ChcExpr::Int(1), 2));
    let input = var("x");
    let ((), total) = counted(|names| {
        let mut session = ReplacementSession::new(&map, names);
        session.substitute(&input).unwrap();
        session.substitute(&input).unwrap();
    });
    assert!((10..200).contains(&total));
    for ordinal in 1..=total {
        let polls = Cell::new(0usize);
        let armed = Cell::new(false);
        let mut progress = || {
            if armed.get() {
                polls.set(polls.get() + 1);
                polls.get() != ordinal
            } else {
                true
            }
        };
        let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
        armed.set(true);
        {
            let mut session = ReplacementSession::new(&map, &mut names);
            assert!(session
                .substitute(&input)
                .and_then(|_| session.substitute(&input))
                .is_none());
            assert!(session.substitute(&input).is_none());
            assert!(session.with_names(AcyclicNames::poll).is_none());
        }
        assert!(names.stopped());
        assert!(names.poll().is_none());
        assert_eq!(polls.get(), ordinal);
    }
}

#[test]
fn caught_callback_or_pure_operation_panic_cannot_rearm_session_or_owner() {
    let map = DetHashMap::default();
    let panic_now = Cell::new(false);
    let polls = Cell::new(0usize);
    let mut progress = || {
        polls.set(polls.get() + 1);
        assert!(!panic_now.get(), "controlled callback panic");
        true
    };
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
    {
        let mut session = ReplacementSession::new(&map, &mut names);
        session.substitute(&ChcExpr::Int(1)).unwrap();
        panic_now.set(true);
        assert!(catch_unwind(AssertUnwindSafe(|| session.substitute(&ChcExpr::Int(2)))).is_err());
        panic_now.set(false);
        let stopped_at = polls.get();
        assert!(session.substitute(&ChcExpr::Int(3)).is_none());
        assert_eq!(polls.get(), stopped_at);
    }
    assert!(names.stopped());

    // Inject a panic into the same guarded operation wrapper used around the
    // pure substitution. No production panic hook or substitute variant exists.
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
    {
        let mut session = ReplacementSession::new(&map, &mut names);
        session.substitute(&ChcExpr::Int(1)).unwrap();
        assert!(catch_unwind(AssertUnwindSafe(|| {
            session.with_names::<()>(|_| panic!("pure operation panic"))
        }))
        .is_err());
        // Drop while pending must poison the owner even without a retry.
    }
    let stopped_at = polls.get();
    assert!(names.stopped());
    assert!(names.poll().is_none());
    assert_eq!(polls.get(), stopped_at);
}

#[test]
fn refusal_without_control_poll_still_poisoned_on_retry_and_drop() {
    let map = DetHashMap::default();
    let ((), polls) = counted(|names| {
        {
            let mut session = ReplacementSession::new(&map, names);
            assert!(session.with_names::<()>(|_| None).is_none());
            assert!(session.substitute(&ChcExpr::Bool(true)).is_none());
        }
        assert!(names.stopped());
        assert!(names.poll().is_none());
    });
    assert_eq!(polls, 0);
}

#[test]
fn admitted_map_never_skips_later_input_or_expanded_output_checks() {
    let mut map = DetHashMap::default();
    map.insert("x".to_owned(), nested(ChcExpr::Int(0), 1));
    let input = nested(var("x"), crate::expr::MAX_EXPR_RECURSION_DEPTH - 1);
    let ((), _) = counted(|names| {
        let mut session = ReplacementSession::new(&map, names);
        session.substitute(&var("x")).unwrap();
        // Both input and replacement are admitted independently, but their
        // composition reaches the unchanged depth refusal boundary.
        assert!(session.substitute(&input).is_none());
    });
    let too_deep = nested(ChcExpr::Int(0), crate::expr::MAX_EXPR_RECURSION_DEPTH);
    let ((), _) = counted(|names| {
        let mut session = ReplacementSession::new(&map, names);
        session.substitute(&var("x")).unwrap();
        assert!(session.substitute(&too_deep).is_none());
    });
    ChcExpr::iterative_drop(input);
    ChcExpr::iterative_drop(too_deep);
}

#[test]
fn changed_map_requires_new_admission_after_the_old_borrow_ends() {
    let mut map = DetHashMap::default();
    map.insert("x".to_owned(), ChcExpr::Int(1));
    let ((), _) = counted(|names| {
        {
            let mut session = ReplacementSession::new(&map, names);
            assert_eq!(session.substitute(&var("x")), Some(ChcExpr::Int(1)));
        }
        map.insert("x".to_owned(), ChcExpr::Int(2));
        {
            let mut session = ReplacementSession::new(&map, names);
            assert_eq!(session.substitute(&var("x")), Some(ChcExpr::Int(2)));
        }
        map.insert(
            "x".to_owned(),
            nested(ChcExpr::Int(3), crate::expr::MAX_EXPR_RECURSION_DEPTH),
        );
        assert!(ReplacementSession::new(&map, names)
            .substitute(&var("x"))
            .is_none());
        assert!(names.stopped());
    });
    for expression in map.into_values() {
        ChcExpr::iterative_drop(expression);
    }
}
