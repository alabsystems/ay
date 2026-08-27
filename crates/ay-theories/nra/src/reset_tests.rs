// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

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
