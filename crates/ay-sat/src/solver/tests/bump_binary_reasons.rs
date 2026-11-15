// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-bump-binary-reasons`: reason-side bumping through binary literal
//! reasons (#8034) marks the single antecedent as analyzed when switched on,
//! and leaves the reason side untouched otherwise.

use super::*;

fn switched(value: Option<bool>) -> ay_core::sat_ab_test_override::Guard {
    ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        bump_binary_reasons: value,
        ..Default::default()
    })
}

/// Decision `d` at level 1 and `a` implied by the binary clause `(a | -d)`.
fn decided_and_binary_implied() -> (Solver, Literal, Literal) {
    let mut solver = Solver::new(3);
    let d = Literal::positive(Variable(0));
    let a = Literal::positive(Variable(1));
    solver.decide(d);
    solver.enqueue_binary_reason(a, d.negated());
    assert!(matches!(
        solver.var_reason_kind(1),
        ReasonKind::BinaryLiteral(_)
    ));
    (solver, d, a)
}

#[test]
fn switched_on_marks_the_binary_antecedent() {
    let _guard = switched(Some(true));
    let (mut solver, _d, a) = decided_and_binary_implied();
    let mut extra = 0;
    solver.add_reason_literals_to_analyzed(a, 1, &mut extra, 100);
    assert_eq!(extra, 1);
    assert!(solver.var_data[0].is_seen());
}

#[test]
fn default_leaves_the_binary_reason_side_alone() {
    let _guard = switched(None);
    let (mut solver, _d, a) = decided_and_binary_implied();
    let mut extra = 0;
    solver.add_reason_literals_to_analyzed(a, 1, &mut extra, 100);
    assert_eq!(extra, 0);
    assert!(!solver.var_data[0].is_seen());
}

#[test]
fn switched_on_respects_the_limit() {
    let _guard = switched(Some(true));
    let (mut solver, _d, a) = decided_and_binary_implied();
    let mut extra = 5;
    solver.add_reason_literals_to_analyzed(a, 1, &mut extra, 5);
    assert_eq!(extra, 5);
    assert!(!solver.var_data[0].is_seen());
}
