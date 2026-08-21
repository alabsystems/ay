// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{is_replayable_linear_row, propagation_reaches_conflict};
use crate::propagation::PbPropagator;
use crate::types::{PbConstraint, PbLit, PbRel, PbTerm};

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn row(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

fn term(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![lit(var)],
    }
}

#[test]
fn immediately_conflicting_row_is_a_conflict() {
    // -x1 - x2 >= 1 can never hold: negative slack under the empty
    // assignment, exactly the shape an objective-improving row takes when the
    // objective cannot go below its optimum on the cube alone.
    let mut propagator = PbPropagator::new();
    propagator.add_from_pb_constraint(&row(vec![term(-1, 1), term(-1, 2)], 1));
    assert!(propagation_reaches_conflict(&mut propagator));
}

#[test]
fn propagation_chain_reaches_conflict() {
    // x1 + x2 >= 2 forces both true; -x1 - x2 >= -1 (i.e. x1 + x2 <= 1) then
    // conflicts. Needs real propagation, not just a slack check on one row.
    let mut propagator = PbPropagator::new();
    propagator.add_from_pb_constraint(&row(vec![term(1, 1), term(1, 2)], 2));
    propagator.add_from_pb_constraint(&row(vec![term(-1, 1), term(-1, 2)], -1));
    assert!(propagation_reaches_conflict(&mut propagator));
}

#[test]
fn satisfiable_database_has_no_conflict() {
    // x1 + x2 >= 1 with x1 + x2 <= 1: satisfiable and propagation-free.
    let mut propagator = PbPropagator::new();
    propagator.add_from_pb_constraint(&row(vec![term(1, 1), term(1, 2)], 1));
    propagator.add_from_pb_constraint(&row(vec![term(-1, 1), term(-1, 2)], -1));
    assert!(!propagation_reaches_conflict(&mut propagator));
}

#[test]
fn non_linear_and_oversized_rows_are_not_replayable() {
    let non_linear = PbConstraint {
        terms: vec![PbTerm {
            coeff: 1,
            lits: vec![lit(1), lit(2)],
        }],
        rel: PbRel::Ge,
        rhs: 1,
    };
    assert!(!is_replayable_linear_row(&non_linear));

    let oversized = row(vec![term(i128::MAX, 1), term(i128::MAX, 2)], 1);
    assert!(!is_replayable_linear_row(&oversized));

    assert!(is_replayable_linear_row(&row(
        vec![term(3, 1), term(-2, 2)],
        1
    )));
}
