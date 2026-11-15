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
