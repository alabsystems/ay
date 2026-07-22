// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates
// Part of #6214: verification-consumer QF_LIA preservation VC returns false SAT.
//
// Root cause: verification-consumer bug — alias substitution applied to invariants but
// not to loop condition, creating a formula with unconstrained variable.
// ay correctly returns SAT for the malformed formula and UNSAT for the
// correctly-formed formula.

#![allow(deprecated)]

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

/// Correctly-formed preservation VC: all uses of `bound` are consistent.
///   i >= 0 ∧ i <= bound ∧ i < bound ∧ i' = i + 1 ∧ ¬(i' >= 0 ∧ i' <= bound)
/// Expected: UNSAT
#[test]
fn test_preservation_vc_consistent_unsat() {
    let mut solver = Solver::new(Logic::QfLia);

    let i = solver.declare_const("i", Sort::Int);
    let bound = solver.declare_const("bound", Sort::Int);
    let i_prime = solver.declare_const("i_prime", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    let c1 = solver.ge(i, zero);
    solver.assert_term(c1);
    let c2 = solver.le(i, bound);
    solver.assert_term(c2);
    let c3 = solver.lt(i, bound);
    solver.assert_term(c3);

    let i_plus_one = solver.add(i, one);
    let c4 = solver.eq(i_prime, i_plus_one);
    solver.assert_term(c4);

    let ip_ge_0 = solver.ge(i_prime, zero);
    let ip_le_bound = solver.le(i_prime, bound);
    let conj = solver.and(ip_ge_0, ip_le_bound);
    let neg = solver.not(conj);
    solver.assert_term(neg);

    assert_eq!(
        solver.check_sat(),
        SolveResult::unsat(),
        "Consistent preservation VC is UNSAT"
    );
}

/// Malformed preservation VC from verification-consumer's alias substitution bug:
/// invariants use `n` (substituted from `bound`) but condition still uses `bound`.
///   i >= 0 ∧ i <= n ∧ i < bound ∧ i' = i + 1 ∧ ¬(i' >= 0 ∧ i' <= n)
/// Expected: SAT (counterexample: n=0, i=0, bound=1, i'=1)
#[test]
fn test_preservation_vc_alias_mismatch_sat() {
    let mut solver = Solver::new(Logic::QfLia);

    let i = solver.declare_const("i", Sort::Int);
    let n = solver.declare_const("n", Sort::Int);
    let bound = solver.declare_const("bound", Sort::Int);
    let i_prime = solver.declare_const("i_prime", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // Invariants with `n` (substituted)
    let c1 = solver.ge(i, zero);
    solver.assert_term(c1);
    let c2 = solver.le(i, n);
    solver.assert_term(c2);

    // Condition still uses `bound` (NOT substituted)
    let c3 = solver.lt(i, bound);
    solver.assert_term(c3);

    let i_plus_one = solver.add(i, one);
    let c4 = solver.eq(i_prime, i_plus_one);
    solver.assert_term(c4);

    // Negated primed invariants use `n`
    let ip_ge_0 = solver.ge(i_prime, zero);
    let ip_le_n = solver.le(i_prime, n);
    let conj = solver.and(ip_ge_0, ip_le_n);
    let neg = solver.not(conj);
    solver.assert_term(neg);

    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "Alias-mismatched formula IS satisfiable (verification-consumer bug, not ay bug)"
    );
}
