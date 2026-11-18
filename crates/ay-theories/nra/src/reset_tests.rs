// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::Sort;

use super::*;

fn install_certificate_sentinel(solver: &mut NraSolver<'_>) {
    // Lifecycle invalidation must not need to inspect or revalidate evidence.
    solver.last_unsat_certificate = Some(sos::SosCertificate {
        basis: Vec::new(),
        gram: Vec::new(),
        terms: Vec::new(),
        rhs: BigRational::zero(),
    });
    assert!(solver.took_sos_unsat_certificate());
}

#[test]
fn test_nra_reset_clears_unsat_certificate() {
    let terms = TermStore::new();
    let mut solver = NraSolver::new(&terms);
    // A structural sentinel is sufficient here: reset must discard the cached
    // certificate without inspecting it. Certificate verification is covered
    // independently by the SOS tests.
    solver.last_unsat_certificate = Some(sos::SosCertificate {
        basis: Vec::new(),
        gram: Vec::new(),
        terms: Vec::new(),
        rhs: BigRational::zero(),
    });
    assert!(solver.took_sos_unsat_certificate());

    solver.reset();

    assert!(!solver.took_sos_unsat_certificate());
}

#[test]
fn nra_sos_assert_literal_invalidates_last_check_evidence() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let positive = terms.mk_gt(x, zero);
    let mut solver = NraSolver::new(&terms);
    install_certificate_sentinel(&mut solver);

    solver.assert_literal(positive, true);

    assert!(!solver.took_sos_unsat_certificate());
    assert!(solver.render_sos_unsat_certificate("stale").is_none());
}

#[test]
fn nra_sos_push_invalidates_last_check_evidence() {
    let terms = TermStore::new();
    let mut solver = NraSolver::new(&terms);
    install_certificate_sentinel(&mut solver);

    solver.push();

    assert!(!solver.took_sos_unsat_certificate());
    assert!(solver.render_sos_unsat_certificate("stale").is_none());
}

#[test]
fn nra_sos_pop_invalidates_last_check_evidence() {
    let terms = TermStore::new();
    let mut solver = NraSolver::new(&terms);
    solver.push();
    install_certificate_sentinel(&mut solver);

    solver.pop();

    assert!(!solver.took_sos_unsat_certificate());
    assert!(solver.render_sos_unsat_certificate("stale").is_none());
}

#[test]
fn nra_sos_shared_equality_invalidates_last_check_evidence() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let mut solver = NraSolver::new(&terms);
    install_certificate_sentinel(&mut solver);

    solver.assert_shared_equality(x, y, &[]);

    assert!(!solver.took_sos_unsat_certificate());
    assert!(solver.render_sos_unsat_certificate("stale").is_none());
}

#[test]
fn nra_sos_shared_disequality_invalidates_last_check_evidence() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let mut solver = NraSolver::new(&terms);
    install_certificate_sentinel(&mut solver);

    solver.assert_shared_disequality(x, y, &[]);

    assert!(!solver.took_sos_unsat_certificate());
    assert!(solver.render_sos_unsat_certificate("stale").is_none());
}

/// `term_to_multipoly` is memoized per instance: converting the same
/// term twice yields an equal polynomial and registers cache hits,
/// including for unsupported (None) terms; the conversion is a pure
/// function of immutable term structure, so no invalidation exists.
#[test]
fn test_multipoly_cache_replays_conversions() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let expr = terms.mk_add(vec![xy, x]);
    let unsupported = terms.mk_div(x, y);
    let solver = NraSolver::new(&terms);

    let first = solver.term_to_multipoly(expr);
    assert!(first.is_some());
    let hits0 = solver.multipoly_cache_hits.get();
    let second = solver.term_to_multipoly(expr);
    assert_eq!(
        first.map(|p| p.terms),
        second.map(|p| p.terms),
        "cached conversion must be identical"
    );
    assert!(
        solver.multipoly_cache_hits.get() > hits0,
        "second conversion of the same term must hit the cache"
    );

    assert!(solver.term_to_multipoly(unsupported).is_none());
    let hits1 = solver.multipoly_cache_hits.get();
    assert!(solver.term_to_multipoly(unsupported).is_none());
    assert!(
        solver.multipoly_cache_hits.get() > hits1,
        "unsupported conversions are cached as None too"
    );
}
