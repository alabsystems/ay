// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_UFNIA `check-sat-assuming` scoped fallback (#uf-nia-assuming).
//!
//! UF + nonlinear-int queries used to hard-fail closed to `Unknown` on the
//! assumption path, even when the verdict follows from the EUF+LIA layer
//! alone. That bit the `produce-unsat-cores` redirect (named assertions are
//! re-solved as assumptions), making named-core-mode clients incomplete for
//! any query that so much as *contains* a nonlinear product.
//!
//! Motivating client shape (deductive-checks divisor-guarded Euclidean div/mod
//! lemma instantiation, verifier issue #2778): `a / b`, `a % b` over
//! unbounded ints with a SYMBOLIC divisor are encoded as uninterpreted
//! functions `eucdiv(a, b)` / `eucmod(a, b)` constrained by ground
//! divisor-guarded axioms
//!
//! ```text
//! b != 0 -> a == eucdiv(a,b)*b + eucmod(a,b)     (nonlinear product!)
//! b != 0 -> 0 <= eucmod(a,b)
//! b >  0 -> eucmod(a,b) < b
//! b <  0 -> eucmod(a,b) < -b
//! a >= 0 && b > 0 -> eucdiv(a,b) >= 0            (direct sign lemma)
//! ```
//!
//! leaving division by zero uninterpreted. The upstream Verus `nonlinear.rs`
//! `test4` goal (`0 <= x && 0 < d ==> 0 <= x/d`) is then decided by the
//! DIRECT SIGN LEMMA in pure EUF+LIA — but the reconstruction axiom's
//! `eucdiv(a,b)*b` product flips logic detection to QF_UFNIA, which the
//! assumption path refused wholesale.
//!
//! The fix routes QfUfnia/QfUfnira/QfUfnra through the same scoped-assumption
//! fallback as quantified/FP assumption checks: solve `base ∧ assumptions`
//! with the full pipeline (verdict-identical), conservative all-assumptions
//! core on UNSAT, model re-validation on SAT, still fail-closed Unknown when
//! the pipeline cannot decide.

#![allow(deprecated)]

use ay_dpll::api::{Logic, Solver, Sort, Term};
use ntest::timeout;

/// Build the divisor-guarded Euclidean axiom set over UF `eucdiv`/`eucmod`
/// for the pair `(x, d)` and assert it (unnamed). Returns `(q, r)`.
fn assert_guarded_euclid_axioms(solver: &mut Solver, x: Term, d: Term) -> (Term, Term) {
    let eucdiv = solver.declare_fun("eucdiv", &[Sort::Int, Sort::Int], Sort::Int);
    let eucmod = solver.declare_fun("eucmod", &[Sort::Int, Sort::Int], Sort::Int);
    let q = solver.try_apply(&eucdiv, &[x, d]).unwrap();
    let r = solver.try_apply(&eucmod, &[x, d]).unwrap();
    let zero = solver.int_const(0);

    let d_eq0 = solver.eq(d, zero);
    let guard = solver.not(d_eq0);

    // b != 0 -> a == q*b + r    (the nonlinear product q*b)
    let qd = solver.mul(q, d);
    let recon = solver.add(qd, r);
    let recon_eq = solver.eq(recon, x);
    let l1 = solver.implies(guard, recon_eq);
    solver.assert_term(l1);

    // b != 0 -> 0 <= r
    let r_ge0 = solver.ge(r, zero);
    let l2 = solver.implies(guard, r_ge0);
    solver.assert_term(l2);

    // b > 0 -> r < b
    let d_pos = solver.gt(d, zero);
    let r_lt_d = solver.lt(r, d);
    let l3 = solver.implies(d_pos, r_lt_d);
    solver.assert_term(l3);

    // b < 0 -> r < -b
    let d_neg = solver.lt(d, zero);
    let neg_d = solver.sub(zero, d);
    let r_lt_neg_d = solver.lt(r, neg_d);
    let l4 = solver.implies(d_neg, r_lt_neg_d);
    solver.assert_term(l4);

    // a >= 0 && b > 0 -> q >= 0   (direct quotient-sign lemma)
    let x_ge0 = solver.ge(x, zero);
    let ante = solver.and(x_ge0, d_pos);
    let q_ge0 = solver.ge(q, zero);
    let l5 = solver.implies(ante, q_ge0);
    solver.assert_term(l5);

    (q, r)
}

/// UNSAT direction through the `produce-unsat-cores` NAMED-assertion
/// redirect — the exact deductive-checks `test4` shape. Named premises `x >= 0`,
/// `d > 0` and named negated goal `q < 0` contradict the (unnamed) direct
/// sign lemma. Before #uf-nia-assuming this returned Unknown(Incomplete);
/// it must be UNSAT.
#[test]
#[timeout(15_000)]
fn uf_nia_cores_redirect_decides_unsat() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let d = solver.declare_const("d", Sort::Int);
    let (q, _r) = assert_guarded_euclid_axioms(&mut solver, x, d);

    let zero = solver.int_const(0);
    let x_ge0 = solver.ge(x, zero);
    solver.try_assert_named(x_ge0, "premise_x_nonneg").unwrap();
    let d_pos = solver.gt(d, zero);
    solver.try_assert_named(d_pos, "premise_d_pos").unwrap();
    let q_lt0 = solver.lt(q, zero);
    solver.try_assert_named(q_lt0, "negated_goal").unwrap();

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "x>=0, d>0, guarded Euclidean axioms, q<0 must be UNSAT under the \
         cores redirect (got {result:?})"
    );

    // The conservative core contract: every reported name is one of the
    // named assertions (no fabricated members).
    let core = solver.try_get_unsat_core().expect("core must be available");
    for name in &core {
        assert!(
            ["premise_x_nonneg", "premise_d_pos", "negated_goal"].contains(&name.as_str()),
            "core member '{name}' is not a named assertion"
        );
    }
}

/// Same UNSAT shape through the DIRECT `check_sat_assuming` API (no cores
/// redirect): base = guarded axioms, assumptions = premises + negated goal.
#[test]
#[timeout(15_000)]
fn uf_nia_check_sat_assuming_direct_decides_unsat() {
    let mut solver = Solver::try_new(Logic::All).unwrap();

    let x = solver.declare_const("x", Sort::Int);
    let d = solver.declare_const("d", Sort::Int);
    let (q, _r) = assert_guarded_euclid_axioms(&mut solver, x, d);

    let zero = solver.int_const(0);
    let x_ge0 = solver.ge(x, zero);
    let d_pos = solver.gt(d, zero);
    let q_lt0 = solver.lt(q, zero);

    let result = solver.check_sat_assuming(&[x_ge0, d_pos, q_lt0]);
    assert!(
        result.result().is_unsat(),
        "direct check_sat_assuming must decide the UF+NIA shape UNSAT (got {:?})",
        result.result()
    );
}

/// SOUNDNESS (no false UNSAT): dropping the `d > 0` premise makes `q < 0`
/// satisfiable (e.g. `x = 1, d = -1` forces `q = -1` under the guarded
/// axioms). The fallback must NOT report UNSAT here.
#[test]
#[timeout(15_000)]
fn uf_nia_cores_redirect_sat_direction_not_unsat() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let d = solver.declare_const("d", Sort::Int);
    let (q, _r) = assert_guarded_euclid_axioms(&mut solver, x, d);

    let zero = solver.int_const(0);
    let x_ge0 = solver.ge(x, zero);
    solver.try_assert_named(x_ge0, "premise_x_nonneg").unwrap();
    let q_lt0 = solver.lt(q, zero);
    solver.try_assert_named(q_lt0, "negated_goal").unwrap();

    let result = solver.check_sat();
    assert!(
        !result.is_unsat(),
        "x>=0 alone does NOT force q>=0 (d may be negative); UNSAT would be \
         a false refutation (got {result:?})"
    );
}
