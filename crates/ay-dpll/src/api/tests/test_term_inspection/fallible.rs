// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! No-solve controls for authenticated DATA introspection.

use crate::api::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn refused_by_both(solver: &Solver, term: Term) {
    let sort = catch_unwind(AssertUnwindSafe(|| solver.try_term_sort(term)));
    assert!(matches!(
        sort,
        Ok(Err(SolverError::InvalidTermHandle {
            operation: "term_sort",
            ..
        }))
    ));
    let text = catch_unwind(AssertUnwindSafe(|| solver.try_render_term_canonical(term)));
    assert!(matches!(
        text,
        Ok(Err(SolverError::InvalidTermHandle {
            operation: "render_term_canonical",
            ..
        }))
    ));
}

#[test]
fn foreign_raw_and_out_of_range_handles_are_typed_refusals() {
    let mut first = Solver::new(Logic::All);
    let mut second = Solver::new(Logic::All);
    let foreign = first.declare_const("foreign", Sort::Bool);
    let local = second.declare_const("local", Sort::Bool);
    assert_eq!(foreign.to_raw(), local.to_raw());
    for invalid in [
        foreign,
        Term::from_raw(local.to_raw()),
        Term::from_raw(u32::MAX),
    ] {
        refused_by_both(&second, invalid);
    }
    assert_eq!(second.try_term_sort(local).ok(), Some(Sort::Bool));
}

#[test]
fn valid_variable_and_built_term_data_matches_legacy_methods() {
    let mut solver = Solver::new(Logic::All);
    let scalar = solver.declare_const("scalar", Sort::bitvec(8));
    let sum = solver
        .try_bvadd(scalar, scalar)
        .expect("same-sort BV addition");
    let array = solver.declare_const("array", Sort::array(Sort::Int, Sort::Bool));
    let reserved = solver.declare_const("let", Sort::Bool);
    let negated = solver.try_not(reserved).expect("Bool negation");
    for term in [scalar, sum, array, reserved, negated] {
        assert_eq!(
            solver.try_term_sort(term).ok(),
            Some(solver.term_sort(term))
        );
        assert_eq!(
            solver.try_render_term_canonical(term).ok(),
            Some(solver.render_term_canonical(term))
        );
    }
}

#[test]
fn reset_refuses_old_authority_even_when_numeric_id_repeats() {
    let mut solver = Solver::new(Logic::All);
    let stale = solver.declare_const("before_reset", Sort::Bool);
    solver.try_reset().expect("full reset");
    let current = solver.declare_const("after_reset", Sort::Bool);
    assert_eq!(stale.to_raw(), current.to_raw());
    assert_ne!(stale, current);
    refused_by_both(&solver, stale);
    assert_eq!(solver.try_term_sort(current).ok(), Some(Sort::Bool));
    assert_eq!(
        solver.try_render_term_canonical(current).ok(),
        Some(solver.render_term_canonical(current))
    );
}

#[test]
fn discarded_and_reborn_entry_handles_never_alias_live_data() {
    let mut solver = Solver::new(Logic::All);
    let checkpoint = solver.terms().rollback_checkpoint();
    // Only this deliberately retained negative handle escapes the speculative
    // scratch fixture. No assertion, declaration map, model or proof uses it.
    let id = solver
        .terms_mut()
        .mk_fresh_named_var("discarded", Sort::Int);
    let discarded = solver.wrap_term(id);
    solver.terms_mut().rollback_to(checkpoint);
    refused_by_both(&solver, discarded);
    let current_id = solver.terms_mut().mk_fresh_named_var("reborn", Sort::Bool);
    let current = solver.wrap_term(current_id);
    assert_eq!(discarded.to_raw(), current.to_raw());
    assert_ne!(discarded, current);
    refused_by_both(&solver, discarded);
    assert_eq!(solver.try_term_sort(current).ok(), Some(Sort::Bool));
    assert_eq!(
        solver.try_render_term_canonical(current).ok(),
        Some(solver.render_term_canonical(current))
    );
}

#[test]
fn logical_scope_changes_preserve_live_sort_and_render_data() {
    let mut solver = Solver::new(Logic::All);
    let before = solver.declare_const("before_scope", Sort::Bool);
    solver.try_push().expect("push");
    let inside = solver.declare_const("inside_scope", Sort::Int);
    let before_text = solver.try_render_term_canonical(before).expect("live Bool");
    let inside_text = solver.try_render_term_canonical(inside).expect("live Int");
    solver.try_pop().expect("pop");
    solver.try_reset_assertions().expect("preserve term arena");
    assert_eq!(solver.try_term_sort(before).ok(), Some(Sort::Bool));
    assert_eq!(solver.try_term_sort(inside).ok(), Some(Sort::Int));
    assert_eq!(
        solver.try_render_term_canonical(before).ok(),
        Some(before_text)
    );
    assert_eq!(
        solver.try_render_term_canonical(inside).ok(),
        Some(inside_text)
    );
}
