// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `is_expression_forced_to_value` must respect the SIGN of the ratio between
//! the queried expression and a matching tableau row.
//!
//! `(<= y z)` and `(not (< z y))` register two slacks, `s1 = y - z` and
//! `s2 = z - y`. `s1 <= 0` and `s2 >= 0` both say `y - z <= 0`: one side
//! only. Counting `s2`'s LOWER bound as a lower bound on `y - z` (ignoring the
//! negative ratio) "pinned" `y - z` to 0 and turned the disequality `y != z`
//! into a false conflict — a false UNSAT on the incremental QF_LRA lanes
//! (fuzz_ite seed 101 script 163; fuzz_pushpop seed 12 script 44).

use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;

fn rat(n: i64) -> BigRational {
    BigRational::from(BigInt::from(n))
}

/// Build `y`, `z`, the atoms `(<= y z)`, `(< z y)` and `(= lhs rhs)` where the
/// equality compares `k*y` with `k*z` (k = 1 or 2 — the scaled spelling hits the
/// proportional-row path, the plain one the same-coefficient path).
fn one_sided_setup(terms: &mut TermStore, scale: i64) -> (TermId, TermId, TermId, TermId, TermId) {
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let le_yz = terms.mk_le(y, z);
    let lt_zy = terms.mk_lt(z, y);
    let eq = if scale == 1 {
        terms.mk_eq(y, z)
    } else {
        let k = terms.mk_rational(rat(scale));
        let ky = terms.mk_mul(vec![k, y]);
        let kz = terms.mk_mul(vec![k, z]);
        terms.mk_eq(ky, kz)
    };
    (y, z, le_yz, lt_zy, eq)
}

fn assert_one_sided_diseq_not_refuted(scale: i64) {
    let mut terms = TermStore::new();
    let (_y, _z, le_yz, lt_zy, eq) = one_sided_setup(&mut terms, scale);
    let mut solver = LraSolver::new(&terms);
    for atom in [le_yz, lt_zy, eq] {
        solver.register_atom(atom);
    }
    solver.assert_literal(le_yz, true);
    solver.assert_literal(eq, false);
    solver.assert_literal(lt_zy, false);
    // y <= z, z >= y, y != z: satisfiable (y < z). Drive the check the way the
    // DPLL(T) loop does: a split request is fine, a conflict is a false UNSAT.
    for _ in 0..4 {
        let result = solver.check();
        assert!(
            !matches!(
                result,
                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
            ),
            "scale {scale}: y <= z, not (z < y), y != z is satisfiable, got {result:?}"
        );
        if is_sat_like(&result) {
            return;
        }
    }
}

#[test]
fn one_sided_bounds_from_opposite_slacks_do_not_pin_a_disequality() {
    assert_one_sided_diseq_not_refuted(1);
}

#[test]
fn one_sided_bounds_from_opposite_slacks_do_not_pin_a_scaled_disequality() {
    assert_one_sided_diseq_not_refuted(2);
}

/// The genuine two-sided case must still be detected as forced: `y <= z` and
/// `not (y < z)` (i.e. `z <= y`) DO pin `y - z` to 0 through the opposite slack.
#[test]
fn two_sided_bounds_from_opposite_slacks_still_pin() {
    for scale in [1, 2] {
        let mut terms = TermStore::new();
        let y = terms.mk_var("y", Sort::Real);
        let z = terms.mk_var("z", Sort::Real);
        let le_yz = terms.mk_le(y, z);
        let le_zy = terms.mk_le(z, y);
        let eq = if scale == 1 {
            terms.mk_eq(y, z)
        } else {
            let k = terms.mk_rational(rat(scale));
            let ky = terms.mk_mul(vec![k, y]);
            let kz = terms.mk_mul(vec![k, z]);
            terms.mk_eq(ky, kz)
        };
        let mut solver = LraSolver::new(&terms);
        for atom in [le_yz, le_zy, eq] {
            solver.register_atom(atom);
        }
        solver.assert_literal(le_yz, true);
        solver.assert_literal(le_zy, true);
        solver.assert_literal(eq, false);
        let mut refuted = false;
        for _ in 0..4 {
            let result = solver.check();
            if matches!(
                result,
                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
            ) {
                refuted = true;
                break;
            }
            assert!(
                !is_sat_like(&result),
                "scale {scale}: y <= z, z <= y, y != z is UNSAT, got {result:?}"
            );
        }
        assert!(
            refuted,
            "scale {scale}: the pinned disequality must be refuted"
        );
    }
}
