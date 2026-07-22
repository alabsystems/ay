// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound refinement atom materialization.
//!
//! Shared helper for constructing term atoms from `BoundRefinementRequest`
//! values. Used by the incremental split-loop pipeline.

/// Materialize a bound refinement request into a term atom.
///
/// Constructs the appropriate `<=` or `>=` atom from the request's variable,
/// bound value, and optional RHS term. Integer bounds are floor/ceil rounded.
///
/// Relative lower refinements preserve the raw `>=` surface form instead of
/// routing through `mk_ge()`, which canonicalizes to `(<= rhs lhs)`. LRA uses
/// the original `lhs - rhs` direction to reuse the same slack row on replay;
/// flipping the operands re-registers the atom under the opposite slack and can
/// cause the same relative refinement to be rediscovered on the next split-loop
/// pass.
pub(crate) fn materialize_bound_refinement_atom_term(
    terms: &mut ay_core::TermStore,
    request: &ay_core::BoundRefinementRequest,
) -> ay_core::TermId {
    let bound_term = if request.is_integer {
        let int_bound = if request.is_upper {
            request.bound_value.floor().to_integer()
        } else {
            request.bound_value.ceil().to_integer()
        };
        terms.mk_int(int_bound)
    } else {
        terms.mk_rational(request.bound_value.clone())
    };
    let rhs_term = if let Some(rhs) = request.rhs_term {
        if num_traits::Zero::is_zero(&request.bound_value) {
            rhs
        } else {
            terms.mk_add(vec![rhs, bound_term])
        }
    } else {
        bound_term
    };
    if request.is_upper {
        terms.mk_le(request.variable, rhs_term)
    } else if request.rhs_term.is_some() {
        terms.mk_app(
            ay_core::Symbol::named(">="),
            vec![request.variable, rhs_term],
            ay_core::Sort::Bool,
        )
    } else {
        terms.mk_ge(request.variable, rhs_term)
    }
}

#[cfg(test)]
#[path = "bound_refinement_tests.rs"]
mod tests;
