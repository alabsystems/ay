// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{CnfLit, FpEncodingCache, RoundingMode, TermStore};
use ay_core::{Sort, Symbol, TheorySolver};
use std::collections::BTreeMap;

fn assert_empty_namespace(solver: &FpSolver<'_>) {
    let FpEncodingCache {
        term_to_fp,
        bv_term_bits,
        next_var,
        cached_false,
        cached_true,
        bool_input_lits,
        to_bv_unspec_sites,
        ieee_nan_encodings,
        rm_terms,
    } = solver.export_cache();
    assert!(term_to_fp.is_empty());
    assert!(bv_term_bits.is_empty());
    assert_eq!(next_var, 1);
    assert_eq!(cached_false, None);
    assert_eq!(cached_true, None);
    assert!(bool_input_lits.is_empty());
    assert!(to_bv_unspec_sites.is_empty());
    assert!(ieee_nan_encodings.is_empty());
    assert!(rm_terms.is_empty());
    assert!(solver.clauses().is_empty());
    assert!(solver.pending_condition_links.is_empty());
    assert!(!solver.has_encoding_gap());
}

#[test]
fn reset_prevents_old_boolean_inputs_from_aliasing_new_inputs() {
    let mut terms = TermStore::new();
    let old = terms.mk_var("old", Sort::Bool);
    let new = terms.mk_var("new", Sort::Bool);
    let mut solver = FpSolver::new(&terms);
    assert_eq!(solver.encode_bool_condition(old), 1);
    assert_eq!(solver.bool_input_lits().len(), 1);

    solver.reset();
    assert_empty_namespace(&solver);
    let new_lit = solver.encode_bool_condition(new);
    let old_lit = solver.encode_bool_condition(old);
    assert_eq!((new_lit, old_lit), (1, 2));
    assert_ne!(new_lit, old_lit);
    assert_eq!(solver.encode_bool_condition(old), old_lit);
    assert_eq!(solver.num_vars(), 2);
}

#[test]
fn reset_rebuilds_nan_encodings_and_their_constraints() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(3, 4));
    let y = terms.mk_var("y", Sort::FloatingPoint(3, 4));
    let b = terms.mk_var("prefix", Sort::Bool);
    let mut solver = FpSolver::new(&terms);
    solver.bitblast_to_ieee_bv(x);
    assert_eq!(solver.ieee_nan_encodings.len(), 1);
    assert!(!solver.clauses().is_empty());
    solver.reset();
    assert_empty_namespace(&solver);

    let mut fresh = FpSolver::new(&terms);
    for current in [&mut solver, &mut fresh] {
        assert_eq!(current.encode_bool_condition(b), 1);
    }
    for term in [x, y] {
        assert_eq!(
            solver.bitblast_to_ieee_bv(term),
            fresh.bitblast_to_ieee_bv(term)
        );
        assert_eq!(solver.ieee_nan_encodings.len(), 1);
    }
    assert_eq!(solver.ieee_nan_encodings, fresh.ieee_nan_encodings);
    assert_eq!(solver.num_vars(), fresh.num_vars());
    assert_eq!(solver.clauses(), fresh.clauses());
    let bits = &solver.ieee_nan_encodings[&(3, 3)];
    assert_eq!(bits.len(), 7);
    // Production NaN encoding pins a nonzero payload, not just cached bits.
    assert!(solver.clauses().iter().any(|c| c.literals() == &bits[..3]));
}

fn conversions(solver: &mut FpSolver<'_>, x: crate::TermId) -> Vec<Vec<CnfLit>> {
    [false, false, true]
        .into_iter()
        .map(|signed| solver.bitblast_to_bv(x, RoundingMode::RTZ, 2, signed))
        .collect()
}

#[test]
fn reset_rebuilds_only_current_conversion_congruence_sites() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(3, 4));
    let mut solver = FpSolver::new(&terms);
    conversions(&mut solver, x);
    assert_eq!(solver.to_bv_unspec_sites.len(), 3);
    solver.reset();
    assert_empty_namespace(&solver);

    let mut fresh = FpSolver::new(&terms);
    assert_eq!(conversions(&mut solver, x), conversions(&mut fresh, x));
    assert_eq!(solver.to_bv_unspec_sites.len(), 3);
    assert_eq!(solver.num_vars(), fresh.num_vars());
    assert_eq!(solver.clauses(), fresh.clauses());
    for (actual, expected) in solver
        .to_bv_unspec_sites
        .iter()
        .zip(&fresh.to_bv_unspec_sites)
    {
        assert_eq!(actual.input.sign, expected.input.sign);
        assert_eq!(actual.input.exponent, expected.input.exponent);
        assert_eq!(actual.input.significand, expected.input.significand);
        assert_eq!(actual.unspec, expected.unspec);
        assert_eq!(actual.is_signed, expected.is_signed);
    }
}

#[test]
fn reset_drops_pending_proxies_and_gap_but_keeps_external_tseitin_names() {
    let mut terms = TermStore::new();
    let condition = terms.mk_var("condition", Sort::Bool);
    let opaque = terms.mk_app(
        Symbol::named("opaque_condition"),
        vec![condition],
        Sort::Bool,
    );
    let mapping = BTreeMap::from([(condition, 41)]);
    let mut solver = FpSolver::new_with_tseitin(&terms, &mapping);
    assert_eq!(solver.encode_bool_condition(condition), 1);
    assert_eq!(solver.pending_condition_links, vec![(1, 41)]);
    solver.encode_bool_condition(opaque);
    assert!(solver.has_encoding_gap());
    solver.check();
    let stats = solver.collect_statistics();
    solver.reset();
    assert_empty_namespace(&solver);
    assert_eq!(solver.term_to_cnf.as_ref(), Some(&mapping));
    assert_eq!(solver.collect_statistics(), stats);

    let mut fresh = FpSolver::new_with_tseitin(&terms, &mapping);
    assert_eq!(
        solver.encode_bool_condition(condition),
        fresh.encode_bool_condition(condition)
    );
    assert_eq!(solver.take_pending_condition_links(), vec![(1, 41)]);
    assert_eq!(fresh.take_pending_condition_links(), vec![(1, 41)]);
    assert!(solver.take_pending_condition_links().is_empty());
    solver.encode_bool_condition(opaque);
    assert!(solver.take_encoding_gap());
}

#[test]
fn reset_of_imported_cache_is_a_fresh_namespace_even_after_clause_drain() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Bool);
    let x = terms.mk_var("x", Sort::FloatingPoint(3, 4));
    let bv = terms.mk_var("bv", Sort::bitvec(2));
    let mut first = FpSolver::new(&terms);
    first.encode_bool_condition(b);
    first.bitblast_to_ieee_bv(x);
    first.bitblast_bv_term(bv, 2);
    conversions(&mut first, x);
    let cache = first.export_cache();
    let retained = first.take_clauses();
    assert!(!retained.is_empty());
    let mut next = FpSolver::new(&terms);
    // Import ordinarily accompanies `retained` in the same external SAT
    // namespace. Reset then discards that namespace, not merely new clauses.
    next.import_cache(cache);
    assert!(!next.bv_term_bits().is_empty());
    assert!(!next.bool_input_lits().is_empty());
    next.reset();
    assert_empty_namespace(&next);
    let mut fresh = FpSolver::new(&terms);
    assert_eq!(next.bitblast_bv_term(bv, 2), fresh.bitblast_bv_term(bv, 2));
    assert_eq!(next.num_vars(), 2);
    assert_eq!(
        next.encode_bool_condition(b),
        fresh.encode_bool_condition(b)
    );
}
