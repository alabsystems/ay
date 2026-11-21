// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The parity-space route answers only with a checked model (AY-SAT-2).

use super::{parity_space_model, parity_space_shape_admits};

fn parse(text: &str) -> ay_sat::DimacsFormula {
    ay_sat::parse_dimacs(text).expect("parse")
}

/// x1 ^ x2 ^ x3 = 1 and x3 ^ x4 ^ x5 = 0, with x1 ^ x2 ^ x3 = 1 written as
/// three clauses plus the binary (x1 | x2) that blocks the fourth.
const NEAR_PURE_XOR: &str = "p cnf 5 8
-1 -2 3 0
-1 2 -3 0
1 -2 -3 0
1 2 0
3 4 -5 0
3 -4 5 0
-3 4 5 0
-3 -4 -5 0
";

#[test]
fn a_near_pure_xor_formula_gets_a_model_that_satisfies_every_clause() {
    let formula = parse(NEAR_PURE_XOR);
    let model = parity_space_model(&formula).expect("the route answers this formula");
    assert!(model.len() >= formula.num_vars);
    for clause in &formula.clauses {
        assert!(
            clause
                .iter()
                .any(|lit| model[lit.variable().index()] == lit.is_positive()),
            "clause {clause:?} unsatisfied"
        );
    }
}

/// x1 ^ x2 = 1, x2 ^ x3 = 1 and x1 ^ x3 = 1, as binary clauses.
const INCONSISTENT_XOR: &str = "p cnf 3 6
1 2 0
-1 -2 0
2 3 0
-2 -3 0
1 3 0
-1 -3 0
";

#[test]
fn an_inconsistent_xor_formula_is_left_to_the_ordinary_search() {
    // x1 ^ x2 = 1, x2 ^ x3 = 1, x1 ^ x3 = 1: no solution. The route must not
    // answer; the proof-producing search certifies UNSAT.
    let formula = parse(INCONSISTENT_XOR);
    assert!(parity_space_model(&formula).is_none());
}

#[test]
fn a_formula_without_xor_structure_is_left_to_the_ordinary_search() {
    let formula = parse("p cnf 3 2\n1 2 3 0\n-1 -2 0\n");
    assert!(parity_space_model(&formula).is_none());
}

#[test]
fn the_route_is_off_with_its_switch_or_a_zero_budget() {
    let formula = parse(NEAR_PURE_XOR);
    {
        let _off = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            parity_space_route: Some(false),
            ..Default::default()
        });
        assert!(parity_space_model(&formula).is_none());
    }
    {
        let _zero = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            parity_space_budget_ms: Some(0),
            ..Default::default()
        });
        assert!(parity_space_model(&formula).is_none());
    }
    let _on = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        parity_space_route: Some(true),
        parity_space_budget_ms: Some(60_000),
        ..Default::default()
    });
    assert!(parity_space_model(&formula).is_some());
}

#[test]
fn the_shape_check_admits_only_formulas_with_enough_short_clauses() {
    let formula = parse(NEAR_PURE_XOR);
    assert!(parity_space_shape_admits(&formula.clauses));
    // Three units and one binary: 1 of 4 clauses could be an XOR's.
    let formula = parse("p cnf 3 4\n1 0\n2 0\n3 0\n1 2 0\n");
    assert!(!parity_space_shape_admits(&formula.clauses));
    // Exactly half is enough.
    let formula = parse("p cnf 3 2\n1 0\n2 3 0\n");
    assert!(parity_space_shape_admits(&formula.clauses));
}
