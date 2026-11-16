// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Sort, Symbol};
use std::collections::BTreeMap;

#[test]
fn finish_moves_complete_caches_links_and_clauses_without_disguising_a_gap() {
    let mut terms = TermStore::new();
    let condition = terms.mk_var("linked-condition", Sort::Bool);
    let free = terms.mk_var("free-condition", Sort::Bool);
    let opaque = terms.mk_app(Symbol::named("opaque"), [condition], Sort::Bool);
    let fp = terms.mk_var("fp", Sort::FloatingPoint(3, 4));
    let bv = terms.mk_var("bv", Sort::bitvec(2));
    let mapping = BTreeMap::from([(condition, 41)]);
    let mut solver = FpSolver::new_with_tseitin(&terms, &mapping);
    solver.encode_bool_condition(condition);
    solver.encode_bool_condition(free);
    solver.encode_bool_condition(opaque);
    solver.bitblast_to_ieee_bv(fp);
    solver.bitblast_bv_term(bv, 2);
    solver.bitblast_to_bv(fp, RoundingMode::RTZ, 2, true);
    solver.bitblast_to_bv(fp, RoundingMode::RTZ, 2, false);
    assert!(solver.has_encoding_gap());
    assert_ne!(solver.clauses().len(), 0);
    assert_eq!(solver.pending_condition_links.len(), 1);
    assert_eq!(solver.to_bv_unspec_sites.len(), 2);
    assert_ne!(solver.term_to_fp.len(), 0);
    assert_ne!(solver.bv_term_bits.len(), 0);
    assert_ne!(solver.bool_input_lits.len(), 0);
    assert_ne!(solver.ieee_nan_encodings.len(), 0);
    assert!(solver.cached_false.is_some());
    assert!(solver.cached_true.is_some());
    let expected = solver.export_cache();
    let clauses = solver.clauses().to_vec();
    let links = solver.pending_condition_links.clone();
    let clauses_ptr = solver.clauses.as_ptr();
    let links_ptr = solver.pending_condition_links.as_ptr();
    let fp_ptr = solver.term_to_fp[&fp].exponent.as_ptr();
    let bv_ptr = solver.bv_term_bits[&bv].as_ptr();
    let sites_ptr = solver.to_bv_unspec_sites.as_ptr();
    let nan_ptr = solver.ieee_nan_encodings[&(3, 3)].as_ptr();
    let mut stop = |_| false;
    let built = FpConstruction::new(solver, &mut stop)
        .unwrap()
        .finish()
        .unwrap();
    assert_eq!(built.clauses, clauses);
    assert_eq!(built.pending_condition_links, links);
    parity::assert_cache(&built.cache, &expected);
    assert!(built.has_encoding_gap);
    assert_eq!(built.clauses.as_ptr(), clauses_ptr);
    assert_eq!(built.pending_condition_links.as_ptr(), links_ptr);
    assert_eq!(built.cache.term_to_fp[&fp].exponent.as_ptr(), fp_ptr);
    assert_eq!(built.cache.bv_term_bits[&bv].as_ptr(), bv_ptr);
    assert_eq!(built.cache.to_bv_unspec_sites.as_ptr(), sites_ptr);
    assert_eq!(built.cache.ieee_nan_encodings[&(3, 3)].as_ptr(), nan_ptr);
}

#[test]
fn cancellation_is_not_an_encoding_gap_or_a_successful_empty_artifact() {
    let mut terms = TermStore::new();
    let condition = terms.mk_var("condition", Sort::Bool);
    let opaque = terms.mk_app(Symbol::named("opaque"), [condition], Sort::Bool);
    let mut solver = FpSolver::new(&terms);
    solver.encode_bool_condition(opaque);
    assert!(solver.has_encoding_gap());
    let mut stop = |p: FpBuildProgress| p.stage == FpBuildStage::Finalize;
    let transaction = FpConstruction::new(solver, &mut stop).unwrap();
    assert!(matches!(
        transaction.finish(),
        Err(FpBuildError::Interrupted)
    ));

    let mut allow = |_| false;
    let built = FpConstruction::new(FpSolver::new(&terms), &mut allow)
        .unwrap()
        .finish()
        .unwrap();
    assert_eq!(built.clauses.len(), 0);
    assert_eq!(built.pending_condition_links.len(), 0);
    assert!(!built.has_encoding_gap);
    assert_eq!(built.cache.next_var, 1);
}
