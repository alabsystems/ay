// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #inc-dead-atoms: the split machinery must report every atom it maps onto
//! an EXISTING SAT var, so the session-persistent split loop can revive an
//! atom it had withheld from the theory as dead. A missed report leaves a
//! split clause satisfiable through a literal the theory never hears about.

#![allow(clippy::panic)]

use super::{encode_split_pair_incremental, ensure_incremental_atom_encoded};
use crate::incremental_proof_cache::IncrementalNegationCache;
use ay_core::{Sort, TermStore};
use ay_sat::Solver as SatSolver;

#[test]
fn split_pair_reuse_of_an_encoded_atom_is_reported_only_when_armed() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let lt = terms.mk_lt(x, y);
    let gt = terms.mk_gt(x, y);
    let mut solver = SatSolver::new(0);
    let mut term_to_var = super::HashMap::default();
    let mut var_to_term = super::HashMap::default();
    let mut next_var = 0;
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);
    negations.set_track_atom_reuse(true);

    // First encoding mints both atoms: nothing was re-used.
    encode_split_pair_incremental(
        &terms,
        &mut solver,
        &mut term_to_var,
        &mut var_to_term,
        &mut next_var,
        &mut negations,
        (lt, gt),
    )
    .expect("fresh split encodes");
    assert!(negations.take_reused_atoms().is_empty());

    // Re-encoding maps both onto their existing vars: both are reported.
    encode_split_pair_incremental(
        &terms,
        &mut solver,
        &mut term_to_var,
        &mut var_to_term,
        &mut next_var,
        &mut negations,
        (lt, gt),
    )
    .expect("repeated split reuses its vars");
    assert_eq!(negations.take_reused_atoms(), vec![lt, gt]);
    assert!(negations.take_reused_atoms().is_empty(), "take drains");

    // Disarmed (every non-persistent caller): reuse is not recorded.
    negations.set_track_atom_reuse(false);
    encode_split_pair_incremental(
        &terms,
        &mut solver,
        &mut term_to_var,
        &mut var_to_term,
        &mut next_var,
        &mut negations,
        (lt, gt),
    )
    .expect("repeated split reuses its vars");
    assert!(negations.take_reused_atoms().is_empty());
}

#[test]
fn ensure_encoded_reports_a_preexisting_atom_var() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let le = terms.mk_le(x, y);
    let mut solver = SatSolver::new(0);
    solver.ensure_num_vars(4);
    let mut term_to_var = super::HashMap::default();
    let mut var_to_term = super::HashMap::default();
    // `le` was Tseitin-encoded by an earlier (now popped) assertion.
    term_to_var.insert(le, 3);
    var_to_term.insert(3, le);
    let mut next_var = 4;
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);
    negations.set_track_atom_reuse(true);

    let var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut term_to_var,
        &mut var_to_term,
        &mut next_var,
        &mut negations,
        le,
    );
    assert_eq!(var.id(), 3, "the existing var is reused");
    assert_eq!(negations.take_reused_atoms(), vec![le]);
}
