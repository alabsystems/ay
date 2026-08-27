// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SOUNDNESS BARRIER for #7892, end to end.
//!
//! `IncrementalBvState::pop` keeps the whole bit-blast — the SAT solver, its
//! learned clauses, `term_to_bits`, the Tseitin mapping — instead of tearing it
//! down. That is safe only because every clause the BV incremental path
//! installs globally is scope-independent.
//!
//! Exactly one global generator on that path reads the assertion set:
//! `build_bv_eq_congruence_batch`. For an ASSERTED `a = b` and predicates
//! `(= a c)`, `(= b c)` it used to emit the bare equivalence
//!
//! ```text
//!     [-(a = c),  (b = c)]        [ (a = c), -(b = c)]
//! ```
//!
//! whose conclusion holds only under the hypothesis `a = b`. Installed
//! globally, it outlived the `pop` of the scope that asserted the hypothesis,
//! and the next scope inherited a constraint the user never wrote: a false
//! UNSAT. The teardown was hiding that, not preventing it.
//!
//! Guarding both clauses with `-(a = b)` makes them theory tautologies, valid
//! in every scope. THIS test is what stands between the retained bit-blast and
//! that false UNSAT — it fails if the guard is dropped.
//!
//! Cross-checked against bitwuzla 0.9.1 and z3: both answer `sat` for the
//! second scope.

use ay_dpll::api::{Logic, Solver, Sort};
use ntest::timeout;

/// After popping the scope that asserted `a = b`, the constraint set
/// `a = c ∧ b ≠ c` is satisfiable (take `a = c = 0`, `b = 1`).
///
/// A leaked congruence equivalence forces `(a = c) ↔ (b = c)` and makes it
/// UNSAT — which AY's strict certification then publishes as `unknown`. Either
/// verdict fails this assertion.
#[test]
#[timeout(30_000)]
fn bv_eq_congruence_does_not_leak_past_the_pop_that_retracts_its_hypothesis() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.declare_const("a", Sort::bitvec(4));
    let b = solver.declare_const("b", Sort::bitvec(4));
    let c = solver.declare_const("c", Sort::bitvec(4));

    let eq_ab = solver.eq(a, b);
    let eq_ac = solver.eq(a, c);
    let eq_bc = solver.eq(b, c);

    solver.try_push().expect("push scope 1");
    solver.try_assert_term(eq_ab).expect("assert a = b");
    // Force BOTH congruence partners to be bit-blasted inside this scope, so
    // the generator has the triangle it keys on.
    let not_bc = solver.not(eq_bc);
    let partners = solver.or(eq_ac, not_bc);
    solver.try_assert_term(partners).expect("assert partners");
    assert!(
        solver.check_sat_with_details().result.is_sat(),
        "scope 1 (a = b together with (a = c) or b != c) is satisfiable"
    );
    solver.try_pop().expect("pop scope 1");

    solver.try_push().expect("push scope 2");
    solver.try_assert_term(eq_ac).expect("assert a = c");
    let not_bc = solver.not(eq_bc);
    solver.try_assert_term(not_bc).expect("assert b != c");
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat(),
        "a = c with b != c is SAT once a = b is popped; got {:?}. An \
         unguarded BV equality-congruence clause leaked (a = c) <-> (b = c) \
         past the pop that retracted its hypothesis (#7892).",
        details.result
    );
    solver.try_pop().expect("pop scope 2");
}
