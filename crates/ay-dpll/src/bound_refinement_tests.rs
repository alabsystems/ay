// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::materialize_bound_refinement_atom_term;
use ay_core::{BoundRefinementRequest, Sort, Symbol, TermData, TermStore};
use num_rational::BigRational;
use num_traits::Zero;

#[test]
fn test_materialize_relative_lower_refinement_preserves_ge_surface_form() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let atom = materialize_bound_refinement_atom_term(
        &mut terms,
        &BoundRefinementRequest {
            variable: x,
            rhs_term: Some(y),
            bound_value: BigRational::zero(),
            is_upper: false,
            is_integer: false,
            reason: Vec::new(),
        },
    );

    assert_eq!(
        terms.get(atom),
        &TermData::App(Symbol::named(">="), vec![x, y]),
        "relative lower refinement replay must preserve lhs-rhs direction"
    );
}

#[test]
fn test_materialize_direct_lower_refinement_stays_canonicalized() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let atom = materialize_bound_refinement_atom_term(
        &mut terms,
        &BoundRefinementRequest {
            variable: x,
            rhs_term: None,
            bound_value: BigRational::from_integer(3.into()),
            is_upper: false,
            is_integer: false,
            reason: Vec::new(),
        },
    );
    let three = terms.mk_rational(BigRational::from_integer(3.into()));

    assert_eq!(
        terms.get(atom),
        &TermData::App(Symbol::named("<="), vec![three, x]),
        "direct lower refinements should keep the canonical <= form"
    );
}
