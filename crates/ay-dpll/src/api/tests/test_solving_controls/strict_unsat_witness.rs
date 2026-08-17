// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{Logic, Solver};

#[test]
fn result_retains_chokepoint_emission_witness() {
    let mut solver = Solver::new(Logic::QfLia);
    let contradiction = solver.bool_const(false);
    solver.assert_term(contradiction);

    let verified = solver.check_sat();
    assert!(verified.is_unsat());
    assert!(
        verified.has_unsat_emission_witness(),
        "query-authorized Unsat must retain its one-shot witness"
    );
    assert!(
        verified.was_unsat_strictly_verified(),
        "the authored false root must publish through its checked refutation"
    );
    assert!(
        !verified.was_unsat_independently_verified()
            && !verified.was_unsat_exact_semantically_verified(),
        "strict proof authority must remain disjoint from the other UNSAT classes"
    );
}
