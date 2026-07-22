// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the public interpolation API (`SmtContext::get_interpolant`).

use super::*;
use crate::interpolant_validation::is_valid_interpolant_with_check_sat;
use crate::smt::SmtContext;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// Validate Craig interpolation properties for a candidate interpolant.
fn assert_valid_interpolant(
    a: &[ChcExpr],
    b: &[ChcExpr],
    interpolant: &ChcExpr,
    shared_vars: &FxHashSet<String>,
) {
    let a_conj = ChcExpr::and_all(a.to_vec());
    let b_conj = ChcExpr::and_all(b.to_vec());
    let timeout = std::time::Duration::from_secs(5);

    assert!(
        is_valid_interpolant_with_check_sat(&a_conj, &b_conj, interpolant, shared_vars, |query| {
            let mut smt = SmtContext::new();
            smt.check_sat_with_timeout(query, timeout)
        }),
        "Interpolant {interpolant} failed Craig property validation"
    );
}

// --- QF_LIA tests ---

#[test]
fn test_get_interpolant_lia_bound_contradiction() {
    // A: x >= 10
    // B: x <= 5
    // UNSAT; interpolant should be some I with A |= I, I /\ B unsat
    let mut smt = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);

    let a = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10))];
    let b = vec![ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(5))];

    match smt.get_interpolant(&a, &b) {
        InterpolationResult::Unsat(interp) => {
            let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();
            assert_valid_interpolant(&a, &b, &interp, &shared);
        }
        InterpolationResult::Unknown => {
            panic!("Expected interpolant for simple bound contradiction")
        }
    }
}

#[test]
fn test_get_interpolant_lia_two_variables() {
    // A: x >= 10, y <= 0
    // B: x <= 5, y >= 5
    // Both contradictions; interpolant uses shared vars only
    let mut smt = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let a = vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10)),
        ChcExpr::le(ChcExpr::var(y.clone()), ChcExpr::Int(0)),
    ];
    let b = vec![
        ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(5)),
        ChcExpr::ge(ChcExpr::var(y), ChcExpr::Int(5)),
    ];

    match smt.get_interpolant(&a, &b) {
        InterpolationResult::Unsat(interp) => {
            let shared: FxHashSet<String> =
                ["x".to_string(), "y".to_string()].into_iter().collect();
            assert_valid_interpolant(&a, &b, &interp, &shared);
        }
        InterpolationResult::Unknown => {
            // Acceptable: some strategies may not handle multi-variable cases
        }
    }
}

#[test]
fn test_get_interpolant_sat_input_returns_unknown() {
    // A: x >= 0
    // B: x <= 10
    // SAT; should return Unknown (no interpolant for SAT formulas)
    let mut smt = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);

    let a = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(0))];
    let b = vec![ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(10))];

    match smt.get_interpolant(&a, &b) {
        InterpolationResult::Unknown => { /* correct: A /\ B is SAT */ }
        InterpolationResult::Unsat(_) => {
            panic!("Should not produce interpolant for satisfiable conjunction")
        }
    }
}

#[test]
fn test_get_interpolant_empty_a_returns_unknown() {
    let mut smt = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);

    let a: Vec<ChcExpr> = vec![];
    let b = vec![ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(5))];

    assert!(matches!(
        smt.get_interpolant(&a, &b),
        InterpolationResult::Unknown
    ));
}

#[test]
fn test_get_interpolant_empty_b_returns_unknown() {
    let mut smt = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);

    let a = vec![ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(10))];
    let b: Vec<ChcExpr> = vec![];

    assert!(matches!(
        smt.get_interpolant(&a, &b),
        InterpolationResult::Unknown
    ));
}

#[test]
fn test_get_interpolant_shared_variable_locality() {
    // A: x >= 10, private_a >= 0
    // B: x <= 5
    // Interpolant must not mention private_a
    let mut smt = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let private_a = ChcVar::new("private_a", ChcSort::Int);

    let a = vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10)),
        ChcExpr::ge(ChcExpr::var(private_a), ChcExpr::Int(0)),
    ];
    let b = vec![ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(5))];

    match smt.get_interpolant(&a, &b) {
        InterpolationResult::Unsat(interp) => {
            let interp_vars: FxHashSet<String> =
                interp.vars().into_iter().map(|v| v.name).collect();
            assert!(
                !interp_vars.contains("private_a"),
                "Interpolant must not mention private A-side variable, got vars: {interp_vars:?}"
            );
            let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();
            assert_valid_interpolant(&a, &b, &interp, &shared);
        }
        InterpolationResult::Unknown => {
            panic!("Expected interpolant for simple bound contradiction")
        }
    }
}

#[test]
fn test_get_interpolant_with_shared_vars_explicit() {
    // Same as bound contradiction but with explicit shared vars
    let mut smt = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);

    let a = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10))];
    let b = vec![ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(5))];
    let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();

    match smt.get_interpolant_with_shared_vars(&a, &b, &shared) {
        InterpolationResult::Unsat(interp) => {
            assert_valid_interpolant(&a, &b, &interp, &shared);
        }
        InterpolationResult::Unknown => {
            panic!("Expected interpolant for simple bound contradiction")
        }
    }
}

#[test]
fn test_get_interpolant_lia_transitivity() {
    // A: x - y <= 3
    // B: y - x <= -5  (i.e., x - y >= 5)
    // UNSAT because x - y can't be both <= 3 and >= 5
    let mut smt = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let a = vec![ChcExpr::le(
        ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::Int(3),
    )];
    let b = vec![ChcExpr::ge(
        ChcExpr::sub(ChcExpr::var(x), ChcExpr::var(y)),
        ChcExpr::Int(5),
    )];

    match smt.get_interpolant(&a, &b) {
        InterpolationResult::Unsat(interp) => {
            let shared: FxHashSet<String> =
                ["x".to_string(), "y".to_string()].into_iter().collect();
            assert_valid_interpolant(&a, &b, &interp, &shared);
        }
        InterpolationResult::Unknown => {
            // Acceptable: transitivity detection is a heuristic
        }
    }
}

#[test]
fn test_get_interpolant_equality_contradiction() {
    // A: x = 7
    // B: x = 3
    // UNSAT
    let mut smt = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);

    let a = vec![ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(7))];
    let b = vec![ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(3))];

    match smt.get_interpolant(&a, &b) {
        InterpolationResult::Unsat(interp) => {
            let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();
            assert_valid_interpolant(&a, &b, &interp, &shared);
        }
        InterpolationResult::Unknown => {
            // Acceptable: equality contradictions may not be caught by all strategies
        }
    }
}
