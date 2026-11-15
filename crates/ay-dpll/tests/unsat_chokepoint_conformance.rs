// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conformance pin for mandatory public UNSAT certification.

use ay_dpll::api::{Logic, Solver, Sort};

#[test]
fn public_boolean_unsat_carries_strict_emission_witness() {
    let mut solver = Solver::new(Logic::QfUf);
    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "a strict-valid contradiction must remain UNSAT"
    );
    assert!(
        result.has_unsat_emission_witness(),
        "public UNSAT must consume the private exact-query capability"
    );
    assert!(result.was_unsat_strictly_verified());
    assert_eq!(result.accept_for_consumer(), Ok(result.result()));
}

#[test]
fn assumption_unsat_certificate_is_bound_to_temporary_literal() {
    let mut solver = Solver::new(Logic::QfUf);
    let p = solver.declare_const("p", Sort::Bool);
    solver.assert_term(p);
    let not_p = solver.not(p);

    let result = solver.check_sat_assuming(&[not_p]);
    assert!(result.is_unsat());
    assert!(result.has_unsat_emission_witness());
    assert!(result.was_unsat_strictly_verified());

    // The assumption is query-local. Its removal must start a different epoch
    // and may not reuse the preceding UNSAT capability.
    let followup = solver.check_sat();
    assert!(followup.is_sat());
    assert!(!followup.has_unsat_emission_witness());
}

#[test]
fn quantified_ufbv_unsat_is_exactly_certified_or_fails_closed() {
    let mut solver = Solver::new(Logic::All);
    let bv4 = Sort::bitvec(4);
    let x = solver.fresh_var("x", bv4.clone());
    let f = solver.declare_fun("f", std::slice::from_ref(&bv4), bv4.clone());
    let fx = solver.apply(&f, &[x]);
    let reflexive = solver.eq(fx, fx);
    let impossible = solver.not(reflexive);
    let forall = solver.forall(&[x], impossible);
    solver.assert_term(forall);

    let result = solver.check_sat();
    assert!(!result.is_sat(), "forall x. f(x) != f(x) must never be SAT");
    if result.is_unsat() {
        assert!(result.has_unsat_emission_witness());
        assert_eq!(
            usize::from(result.was_unsat_strictly_verified())
                + usize::from(result.was_unsat_independently_verified())
                + usize::from(result.was_unsat_exact_semantically_verified())
                + usize::from(result.was_unsat_corroborated()),
            1,
            "public UNSAT must retain exactly one sealed certification class"
        );
    } else {
        assert!(result.is_unknown());
        assert!(!result.has_unsat_emission_witness());
    }
}
