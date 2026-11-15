// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::{ChcOp, ChcProblem, ClauseBody, HornClause, SmtValue};

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn square() -> ChcExpr {
    ChcExpr::mul(var("x"), var("x"))
}

fn bounds() -> FxHashMap<String, IntInterval> {
    FxHashMap::from_iter([(
        "x".to_owned(),
        IntInterval {
            lower: Some(0),
            upper: Some(2),
        },
    )])
}

fn attempt(input: &mut Vec<ChcExpr>, progress: &mut dyn FnMut() -> bool) -> Option<usize> {
    let mut names = AcyclicNames::new(&ChcProblem::new(), progress)?;
    let result = linearize(input, &bounds(), &mut names);
    if result.is_none() {
        assert!(names.stopped());
        assert!(names.poll().is_none());
    }
    result
}

fn evaluates(expression: &ChcExpr, x: i128, p: i128) -> bool {
    let model = FxHashMap::from_iter([
        ("x".to_owned(), SmtValue::Int(x)),
        ("p".to_owned(), SmtValue::Int(p)),
    ]);
    match crate::expr::evaluate_expr(expression, &model) {
        Some(SmtValue::Bool(value)) => value,
        other => panic!("finite polynomial fixture must evaluate: {other:?}"),
    }
}

#[test]
fn square_envelope_preserves_original_models_but_is_not_equivalent() {
    let original = ChcExpr::eq(var("p"), square());
    let mut output = vec![original.clone()];
    assert_eq!(attempt(&mut output, &mut || true), Some(1));
    let relaxed = ChcExpr::and_all(output);
    for x in 0..=2 {
        assert!(evaluates(&original, x, x * x));
        assert!(evaluates(&relaxed, x, x * x));
    }
    assert!(!evaluates(&original, 1, 2));
    assert!(
        evaluates(&relaxed, 1, 2),
        "SAT still requires original replay"
    );
}

#[test]
fn standalone_auxiliary_avoids_current_variable_and_function_symbols() {
    let function = ChcExpr::FuncApp(
        "__bmc_square_lia_aux_0".to_owned(),
        ChcSort::Int,
        Vec::new(),
    );
    let mut input = vec![ChcExpr::eq(
        square(),
        ChcExpr::add(function.clone(), var("__bmc_square_lia_aux_1")),
    )];
    assert_eq!(attempt(&mut input, &mut || true), Some(1));
    let variables: DetHashSet<_> = input
        .iter()
        .flat_map(ChcExpr::vars)
        .map(|variable| variable.name)
        .collect();
    assert!(!variables.contains("__bmc_square_lia_aux_0"));
    assert!(variables.contains("__bmc_square_lia_aux_1"));
    assert!(variables.contains("__bmc_square_lia_aux_2"));
    assert!(input.iter().any(|expression| {
        matches!(expression, ChcExpr::Op(ChcOp::Eq, args)
            if args.iter().any(|arg| matches!(arg.as_ref(), ChcExpr::Op(ChcOp::Add, children)
                if children.iter().any(|child| child.as_ref() == &function))))
    }));
}

#[test]
fn standalone_auxiliary_uses_the_global_source_disjoint_suffix() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("__bmc_square_lia_aux_0", Vec::new());
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        false,
    ))));
    let mut progress = || true;
    let mut names = AcyclicNames::new(&problem, &mut progress).unwrap();
    let mut input = vec![ChcExpr::eq(square(), ChcExpr::Int(1))];
    assert_eq!(linearize(&mut input, &bounds(), &mut names), Some(1));
    let variables: DetHashSet<_> = input
        .iter()
        .flat_map(ChcExpr::vars)
        .map(|variable| variable.name)
        .collect();
    assert!(variables.contains("__bmc_square_lia_aux_0__ay_exact_0"));
    assert!(!variables.contains("__bmc_square_lia_aux_0"));
}

#[test]
fn noncolliding_relaxations_keep_legacy_counts_and_output_order() {
    for input in [
        vec![ChcExpr::Bool(true)],
        vec![ChcExpr::eq(var("p"), square())],
        vec![ChcExpr::gt(square(), ChcExpr::Int(1))],
        vec![
            ChcExpr::eq(var("p"), square()),
            ChcExpr::eq(var("q"), square()),
            ChcExpr::gt(square(), ChcExpr::Int(1)),
        ],
    ] {
        let mut expected = input.clone();
        let count = BmcSolver::linearize_bounded_squares_in_conjuncts(&mut expected, &bounds());
        let mut actual = input;
        assert_eq!(attempt(&mut actual, &mut || true), Some(count));
        assert_eq!(actual, expected);
    }
}

#[test]
fn every_square_callback_refusal_keeps_the_original_vector() {
    let input = vec![ChcExpr::gt(square(), ChcExpr::Int(1))];
    let mut expected = input.clone();
    let mut calls = 0;
    assert_eq!(
        attempt(&mut expected, &mut || {
            calls += 1;
            true
        }),
        Some(1)
    );
    assert!((10..20_000).contains(&calls));
    for ordinal in 1..=calls {
        let mut actual = input.clone();
        let mut observed = 0;
        assert_eq!(
            attempt(&mut actual, &mut || {
                observed += 1;
                observed != ordinal
            }),
            None
        );
        assert_eq!(observed, ordinal);
        assert_eq!(actual, input, "partial square output at {ordinal}/{calls}");
    }
    let mut retry = input;
    assert_eq!(attempt(&mut retry, &mut || true), Some(1));
    assert_eq!(retry, expected);
}

#[test]
fn square_replacement_preserves_shared_scalar_subtrees() {
    let mut expression = Arc::new(square());
    for _ in 0..8 {
        expression = Arc::new(ChcExpr::FuncApp(
            "g".to_owned(),
            ChcSort::Int,
            vec![Arc::clone(&expression), expression],
        ));
    }
    let replacements = FxHashMap::from_iter([(square(), var("aux"))]);
    let mut progress = || true;
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
    let rewritten = rewrite::replace(&expression, &replacements, &mut names).unwrap();
    let ChcExpr::FuncApp(_, _, children) = &rewritten else {
        panic!("preserved application");
    };
    assert!(Arc::ptr_eq(&children[0], &children[1]));
    assert_eq!(rewritten.vars(), vec![ChcVar::new("aux", ChcSort::Int)]);
}
