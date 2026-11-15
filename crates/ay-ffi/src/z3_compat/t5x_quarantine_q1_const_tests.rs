// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the T5 design's P0.2 quarantine, implementer X
//! (`~/ay-bench/campaign/2026-10-02-T5-DESIGN.md` §4 P0.2), item Q1 for the
//! CONSTANT-style binders (`Z3_mk_forall_const`, `Z3_mk_exists_const`,
//! `Z3_mk_lambda_const`): their bodies' loose de Bruijn variables, and the
//! binder identity of a reused name.
//!
//! The pins are `q1_const_pins.py`, `q3_vars_pins.py` and `extra_pins.py`
//! (`~/ay-bench/campaign/t5design-probes/t5x/`, with their `*.real.out` from
//! z3-solver 5.1.0.0 via that directory's `run.py`).

use std::ptr;

use super::t5x_quarantine_support::*;

/// z3 abstracts a `_const` binder's constants without shifting the body's
/// own variables, so a loose `(:var 0)` is captured by the last binder
/// (`q1_const_pins.py` 1-2, libz3 5.1.0): `Exists([x], x != Var(0))` is
/// `(exists ((x Int)) (distinct x x))`, unsat, negation sat; `ForAll([x, y],
/// x - y == Var(0) + Var(1))` is `(= (- x y) (+ y x))`, unsat, negation sat.
/// AY left the variable free and answered sat.
#[test]
fn q1_const_binder_captures_loose_variables_like_z3() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let (x, y) = (konst(c, c"x", int_sort), konst(c, c"y", int_sort));
        let (v0, v1) = (Z3_mk_bound(c, 0, int_sort), Z3_mk_bound(c, 1, int_sort));
        let body = not(c, Z3_mk_eq(c, x, v0));
        let q = Z3_mk_exists_const(c, 0, 1, &raw const x, 0, ptr::null(), body);
        assert_ne!(q, 0, "{}", error_text(c));
        assert!(!text(c, q).contains(":var"), "{}", text(c, q));
        assert_eq!(check(c, &[q]), Z3_L_FALSE, "z3: unsat");
        assert_eq!(check(c, &[not(c, q)]), Z3_L_TRUE, "z3: sat");
        let lhs = Z3_mk_sub(c, 2, [x, y].as_ptr());
        let body = Z3_mk_eq(c, lhs, add(c, &[v0, v1]));
        let q = Z3_mk_forall_const(c, 0, 2, [x, y].as_ptr(), 0, ptr::null(), body);
        assert_ne!(q, 0, "{}", error_text(c));
        assert_eq!(check(c, &[q]), Z3_L_FALSE, "z3: unsat");
        assert_eq!(check(c, &[not(c, q)]), Z3_L_TRUE, "z3: sat");
        Z3_del_context(c);
    }
}

/// A variable past the `_const` binder names the enclosing scope: z3's
/// `ForAll([x], Var(1) > x)` keeps it loose, and `substitute_vars(.., 5)`
/// gives `(forall ((x Int)) (> 5 x))`, unsat (`q1_const_pins.py` 3). AY did
/// not shift it, so `substitute_vars` missed it.
#[test]
fn q1_const_binder_shifts_outer_variables() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let x = konst(c, c"x", int_sort);
        let body = Z3_mk_gt(c, Z3_mk_bound(c, 1, int_sort), x);
        let q = Z3_mk_forall_const(c, 0, 1, &raw const x, 0, ptr::null(), body);
        assert_ne!(q, 0, "{}", error_text(c));
        let five = int(c, 5);
        let closed = Z3_substitute_vars(c, q, 1, &raw const five);
        assert_ne!(closed, 0, "{}", error_text(c));
        assert!(!text(c, closed).contains(":var"), "{}", text(c, closed));
        assert_eq!(check(c, &[closed]), Z3_L_FALSE, "z3: unsat");
        Z3_del_context(c);
    }
}

/// A loose variable whose sort differs from the binder it would be captured
/// by is refused (z3 builds the ill-sorted `(exists ((x Int)) x)`,
/// `q1_const_pins.py` 4; `judge_sound/j6.py`).
#[test]
fn q1_const_binder_refuses_an_ill_sorted_loose_variable() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let x = konst(c, c"x", int_sort);
        let vb = Z3_mk_bound(c, 0, Z3_mk_bool_sort(c));
        let q = Z3_mk_exists_const(c, 0, 1, &raw const x, 0, ptr::null(), vb);
        assert_eq!(q, 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        let vr = Z3_mk_bound(c, 0, Z3_mk_real_sort(c));
        let l = Z3_mk_lambda_const(c, 1, &raw const x, vr);
        assert_eq!(l, 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_del_context(c);
    }
}

/// `Z3_mk_lambda_const` binds loose variables the same way
/// (`q1_const_pins.py` 5-6): `Lambda([x], x + Var(0))` is `(lambda ((x Int))
/// (+ x x))`, so `Select(L, 3) != 6` is unsat; `Lambda([x], x + Var(1))`
/// with `Var(0) -> 10` makes `Select(.., 3) != 13` unsat. AY answered sat
/// for both.
#[test]
fn q1_lambda_const_binds_and_shifts_loose_variables() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let x = konst(c, c"x", int_sort);
        let l = Z3_mk_lambda_const(
            c,
            1,
            &raw const x,
            add(c, &[x, Z3_mk_bound(c, 0, int_sort)]),
        );
        assert_ne!(l, 0, "{}", error_text(c));
        let at_3 = Z3_mk_select(c, l, int(c, 3));
        assert_eq!(check(c, &[Z3_mk_eq(c, at_3, int(c, 6))]), Z3_L_TRUE);
        assert_eq!(
            check(c, &[not(c, Z3_mk_eq(c, at_3, int(c, 6)))]),
            Z3_L_FALSE
        );
        let l = Z3_mk_lambda_const(
            c,
            1,
            &raw const x,
            add(c, &[x, Z3_mk_bound(c, 1, int_sort)]),
        );
        assert_ne!(l, 0, "{}", error_text(c));
        let ten = int(c, 10);
        let l = Z3_substitute_vars(c, l, 1, &raw const ten);
        assert_ne!(l, 0, "{}", error_text(c));
        let at_3 = Z3_mk_select(c, l, int(c, 3));
        assert_eq!(
            check(c, &[not(c, Z3_mk_eq(c, at_3, int(c, 13)))]),
            Z3_L_FALSE
        );
        Z3_del_context(c);
    }
}

/// An inner binder of the bound constant's own name would capture the loose
/// variable AY resolves to that constant, so the construction is refused.
/// z3: `ForAll([x], ForAll([x], x > Var(1)))` is `forall x. forall x!1. x!1 >
/// x`, unsat (`q3_vars_pins.py` 9); AY must not answer sat.
#[test]
fn q1_const_binder_refuses_capture_by_an_inner_binder() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let x = konst(c, c"x", int_sort);
        let body = Z3_mk_gt(c, x, Z3_mk_bound(c, 1, int_sort));
        let inner = Z3_mk_forall_const(c, 0, 1, &raw const x, 0, ptr::null(), body);
        assert_ne!(inner, 0, "{}", error_text(c));
        let q = Z3_mk_forall_const(c, 0, 1, &raw const x, 0, ptr::null(), inner);
        assert_eq!(q, 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_del_context(c);
    }
}

/// A binder name reused at a FiniteSet sort and at its characteristic array
/// sort (one AY engine sort) gets two binders: the second must not re-sort
/// the first (z3 keeps both sorts: `extra_pins.py` e). AY handed both
/// quantifiers one binder constant and recorded the second sort over the
/// first. (`forall s:FiniteSet(Int). 1 in s` and `forall s:Array(Int, Bool)
/// i:Int. s[i]`; the array's variable is `(:var 1)`, as one de Bruijn index
/// cannot carry both public sorts in AY.)
#[test]
fn q1_binder_reused_at_a_finite_set_and_its_array_keeps_both_sorts() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let (int_sort, bool_sort) = (Z3_mk_int_sort(c), Z3_mk_bool_sort(c));
        let set_sort = Z3_mk_finite_set_sort(c, int_sort);
        assert!(!set_sort.is_null(), "{}", error_text(c));
        let array_sort = Z3_mk_array_sort(c, int_sort, bool_sort);
        let member = Z3_mk_finite_set_member(c, int(c, 1), Z3_mk_bound(c, 0, set_sort));
        assert_ne!(member, 0, "{}", error_text(c));
        let q_set = db_quantifier(c, true, &[set_sort], &[c"s"], &[], member);
        assert_ne!(q_set, 0, "{}", error_text(c));
        let read = Z3_mk_select(
            c,
            Z3_mk_bound(c, 1, array_sort),
            Z3_mk_bound(c, 0, int_sort),
        );
        let q_array = db_quantifier(c, true, &[array_sort, int_sort], &[c"s", c"i"], &[], read);
        assert_ne!(q_array, 0, "{}", error_text(c));
        assert_eq!(Z3_get_quantifier_bound_sort(c, q_set, 0), set_sort);
        assert_eq!(Z3_get_quantifier_bound_sort(c, q_array, 0), array_sort);
        Z3_del_context(c);
    }
}
