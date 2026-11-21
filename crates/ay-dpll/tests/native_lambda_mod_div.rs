// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{Logic, Solver, Sort};
use std::time::Duration;

fn parity_array(strict: bool, contradiction: bool) -> Solver {
    let mut solver = Solver::new(Logic::All);
    solver.set_timeout(Some(Duration::from_millis(5000)));
    solver.set_produce_proofs(strict);
    if strict {
        solver
            .try_set_option(":check-proofs-strict", "true")
            .expect("strict proof mode");
    }
    let z = solver.fresh_var("z", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let remainder = solver.modulo(z, two);
    let even = solver.eq(remainder, zero);
    let value = solver.ite(even, one, zero);
    let lambda = solver.lambda_array(z, value);
    let x = solver.declare_const("x", Sort::Int);
    let m = solver.declare_const("m", Sort::array(Sort::Int, Sort::Int));
    let definition = solver.eq(m, lambda);
    solver.assert_term(definition);
    for (index, expected) in [(zero, one), (one, zero), (x, one)] {
        let cell = solver.select(m, index);
        let read = solver.eq(cell, expected);
        solver.assert_term(read);
    }
    if contradiction {
        let cell = solver.select(m, one);
        let opposite_read = solver.eq(cell, one);
        solver.assert_term(opposite_read);
    }
    solver
}

#[test]
fn lambda_mod_div_proofless_native_alias_validates_sat() {
    let details = parity_array(false, false).check_sat_with_details();
    assert!(
        details
            .accept_for_consumer()
            .is_ok_and(|verdict| verdict.is_sat()),
        "{details:?}",
    );
    assert!(details.result.was_model_validated() && details.result.has_sat_emission_witness());
}

#[test]
fn lambda_mod_div_strict_native_alias_validates_sat() {
    let details = parity_array(true, false).check_sat_with_details();
    assert!(
        details
            .accept_for_consumer()
            .is_ok_and(|verdict| verdict.is_sat()),
        "{details:?}",
    );
    assert!(details.result.was_model_validated() && details.result.has_sat_emission_witness());
}

#[test]
fn lambda_mod_div_strict_native_conflicting_reads_certify_unsat() {
    let details = parity_array(true, true).check_sat_with_details();
    assert!(
        details
            .accept_for_consumer()
            .is_ok_and(|verdict| verdict.is_unsat()),
        "{details:?}",
    );
    assert!(details.verification.unsat_proof_strictly_verified);
}
