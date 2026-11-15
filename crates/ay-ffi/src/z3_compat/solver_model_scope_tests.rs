// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression battery for the Z3 C API check publishing invalid or leaky
//! models (measured through z3py 5.1.0 on 2026-09-30):
//!
//! 1. `Z3_mk_power` built a raw `^` application that the engine decided as an
//!    uninterpreted function: `x^2 = 2 ∧ x > 0` answered `sat` with `x = 1/2`,
//!    and `xi = 2^xi` answered `sat` with `xi = 0` (z3: `unknown`).
//! 2. `x * x = 2 ∧ x > 0` answered `sat` with an EMPTY model: the engine's
//!    validated model assigns `x` an irrational `(root-obj ...)` the API model
//!    cannot carry, and the value was silently dropped.
//! 3. A solver's model listed constants asserted only in OTHER solvers of the
//!    same context (the context's engine prints every declared symbol).
//!
//! The invariant pinned here: a published `sat` carries a model under which
//! the solver's own assertions evaluate to `true` (with model completion), an
//! unsupported construct yields `unknown` with a reason, and a handle's model
//! lists exactly the symbols of that handle's goal.

use std::ffi::{CStr, CString};

use super::*;

pub(super) unsafe fn mk_ctx() -> Z3_context {
    // SAFETY: the configuration is live while the context is constructed and
    // is deleted only after `Z3_mk_context` has finished consuming it.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        ctx
    }
}

pub(super) unsafe fn named_const(c: Z3_context, name: &str, sort: Z3_sort) -> Z3_ast {
    let name = CString::new(name).expect("test symbol has no NUL");
    // SAFETY: `c` and `sort` are live handles of the same context; `name` is
    // NUL-terminated and outlives the call.
    unsafe { Z3_mk_const(c, Z3_mk_string_symbol(c, name.as_ptr()), sort) }
}

/// `Z3_model_eval(m, t, completion = true)` is the Boolean `true`.
pub(super) unsafe fn evaluates_true(c: Z3_context, m: Z3_model, t: Z3_ast) -> bool {
    let mut out: Z3_ast = 0;
    // SAFETY: live context/model/term handles; `out` is a valid out-pointer.
    unsafe { Z3_model_eval(c, m, t, true, &raw mut out) && Z3_get_bool_value(c, out) == Z3_L_TRUE }
}

/// Every assertion of `s` holds in its published model, or `s` did not publish
/// `sat` and explains why.
pub(super) unsafe fn sat_only_with_valid_model(
    c: Z3_context,
    s: Z3_solver,
    assertions: &[Z3_ast],
) -> c_int {
    // SAFETY: live context and solver handles; `assertions` are live terms.
    unsafe {
        let r = Z3_solver_check(c, s);
        if r == Z3_L_TRUE {
            let m = Z3_solver_get_model(c, s);
            assert!(!m.is_null(), "a published sat must carry a model");
            for &a in assertions {
                assert!(
                    evaluates_true(c, m, a),
                    "published sat model violates its own assertion; model:\n{}",
                    CStr::from_ptr(Z3_model_to_string(c, m)).to_string_lossy()
                );
            }
        } else if r == Z3_L_UNDEF {
            let reason = CStr::from_ptr(Z3_solver_get_reason_unknown(c, s)).to_string_lossy();
            assert!(!reason.is_empty(), "unknown must carry a reason");
        }
        r
    }
}

/// Names of the constants the published model of `s` lists, sorted.
pub(super) unsafe fn model_const_names(c: Z3_context, s: Z3_solver) -> Vec<String> {
    // SAFETY: live context/solver; the solver's last check was sat.
    unsafe {
        let m = Z3_solver_get_model(c, s);
        assert!(!m.is_null());
        let mut names: Vec<String> = (0..Z3_model_get_num_consts(c, m))
            .map(|i| {
                let d = Z3_model_get_const_decl(c, m, i);
                CStr::from_ptr(Z3_get_symbol_string(c, Z3_get_decl_name(c, d)))
                    .to_string_lossy()
                    .into_owned()
            })
            .collect();
        names.sort();
        names
    }
}

#[test]
fn power_square_root_of_two_is_never_published_with_an_invalid_model() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let x = named_const(c, "x", Z3_mk_real_sort(c));
        let two = Z3_mk_real(c, 2, 1);
        let zero = Z3_mk_real(c, 0, 1);
        // z3py `x**2 == 2, x > 0`: a Real power with a Real literal exponent.
        let squared = Z3_mk_eq(c, Z3_mk_power(c, x, two), two);
        let positive = Z3_mk_gt(c, x, zero);
        // The same constraint over the product, so the check of the model does
        // not depend on the evaluator folding `^`.
        let product = Z3_mk_eq(c, Z3_mk_mul(c, 2, [x, x].as_ptr()), two);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, squared);
        Z3_solver_assert(c, s, positive);
        let r = sat_only_with_valid_model(c, s, &[product, positive]);
        assert_ne!(r, Z3_L_FALSE, "x^2 = 2 has the positive root sqrt(2)");
        Z3_del_context(c);
    }
}

#[test]
fn product_square_root_of_two_is_never_published_with_a_lossy_model() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let x = named_const(c, "x", Z3_mk_real_sort(c));
        let two = Z3_mk_real(c, 2, 1);
        let zero = Z3_mk_real(c, 0, 1);
        let product = Z3_mk_eq(c, Z3_mk_mul(c, 2, [x, x].as_ptr()), two);
        let positive = Z3_mk_gt(c, x, zero);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, product);
        Z3_solver_assert(c, s, positive);
        let r = sat_only_with_valid_model(c, s, &[product, positive]);
        assert_ne!(r, Z3_L_FALSE, "x * x = 2 has the positive root sqrt(2)");
        if r == Z3_L_UNDEF {
            // The engine found and validated the algebraic model; the refusal
            // names the value the API could not carry.
            let reason = CStr::from_ptr(Z3_solver_get_reason_unknown(c, s)).to_string_lossy();
            assert!(reason.contains("root-obj"), "unexpected reason: {reason}");
        }
        Z3_del_context(c);
    }
}

#[test]
fn power_with_a_positive_integer_literal_exponent_is_decided_exactly() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        // Real: x^2 = 4 ∧ x > 0 has the unique model x = 2.
        let x = named_const(c, "x", Z3_mk_real_sort(c));
        let two = Z3_mk_real(c, 2, 1);
        let four = Z3_mk_real(c, 4, 1);
        let zero = Z3_mk_real(c, 0, 1);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_eq(c, Z3_mk_power(c, x, two), four));
        Z3_solver_assert(c, s, Z3_mk_gt(c, x, zero));
        let pinned = Z3_mk_eq(c, x, two);
        assert_eq!(sat_only_with_valid_model(c, s, &[pinned]), Z3_L_TRUE);

        // Int: n^3 = 27 has the unique model n = 3; n^3 = 26 has none. As in
        // z3, the power of an Int is Real-sorted.
        let int = Z3_mk_int_sort(c);
        let n = named_const(c, "n", int);
        let three = Z3_mk_int(c, 3, int);
        let cube = Z3_mk_power(c, n, three);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_eq(c, cube, Z3_mk_real(c, 27, 1)));
        let pinned = Z3_mk_eq(c, n, three);
        assert_eq!(sat_only_with_valid_model(c, s, &[pinned]), Z3_L_TRUE);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_eq(c, cube, Z3_mk_real(c, 26, 1)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);

        // The public AST stays a structural power (only the engine sees the
        // product): z3py prints and inspects it as `n**3`.
        let text = CStr::from_ptr(Z3_ast_to_string(c, cube)).to_string_lossy();
        assert!(text.contains('^'), "power AST was rewritten: {text}");
        Z3_del_context(c);
    }
}

#[test]
fn power_without_a_positive_integer_literal_exponent_is_unknown() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        // z3py `SimpleSolver().add(xi == 2**xi)` (z3py lifts `xi` to Real to
        // meet the Real-sorted power): z3 answers unknown.
        let xi = named_const(c, "xi", int);
        let s = Z3_mk_simple_solver(c);
        let symbolic = Z3_mk_eq(
            c,
            Z3_mk_int2real(c, xi),
            Z3_mk_power(c, Z3_mk_int(c, 2, int), xi),
        );
        Z3_solver_assert(c, s, symbolic);
        assert_eq!(sat_only_with_valid_model(c, s, &[]), Z3_L_UNDEF);

        // 0^0 and 0^-1 are unspecified in z3 (not 1): a zero or negative
        // exponent is not lowered, so the check must not decide it.
        let x = named_const(c, "x", Z3_mk_real_sort(c));
        for exponent in [Z3_mk_real(c, 0, 1), Z3_mk_real(c, -1, 1)] {
            let s = Z3_mk_solver(c);
            let five = Z3_mk_real(c, 5, 1);
            Z3_solver_assert(c, s, Z3_mk_eq(c, Z3_mk_power(c, x, exponent), five));
            assert_eq!(sat_only_with_valid_model(c, s, &[]), Z3_L_UNDEF);
        }
        Z3_del_context(c);
    }
}

#[test]
fn a_solver_model_lists_only_its_own_goal_symbols() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let p = named_const(c, "p", Z3_mk_bool_sort(c));
        let xi = named_const(c, "xi", int);
        let f_name = CString::new("f").expect("no NUL");
        let f = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, f_name.as_ptr()),
            1,
            [int].as_ptr(),
            int,
        );
        let f0 = Z3_mk_app(c, f, 1, [Z3_mk_int(c, 0, int)].as_ptr());

        let s1 = Z3_mk_solver(c);
        Z3_solver_assert(c, s1, p);
        Z3_solver_assert(c, s1, Z3_mk_eq(c, f0, Z3_mk_int(c, 10, int)));
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, Z3_mk_gt(c, xi, Z3_mk_int(c, 3, int)));

        assert_eq!(Z3_solver_check(c, s1), Z3_L_TRUE);
        assert_eq!(model_const_names(c, s1), ["p"]);
        assert_eq!(Z3_model_get_num_funcs(c, Z3_solver_get_model(c, s1)), 1);

        assert_eq!(Z3_solver_check(c, s2), Z3_L_TRUE);
        assert_eq!(model_const_names(c, s2), ["xi"]);
        assert_eq!(Z3_model_get_num_funcs(c, Z3_solver_get_model(c, s2)), 0);

        // An assumption's symbol belongs to the check (z3 lists it).
        let q = named_const(c, "q", Z3_mk_bool_sort(c));
        assert_eq!(
            Z3_solver_check_assumptions(c, s2, 1, [q].as_ptr()),
            Z3_L_TRUE
        );
        assert_eq!(model_const_names(c, s2), ["q", "xi"]);

        // push/pop keep working and keep the scope exact.
        Z3_solver_push(c, s2);
        Z3_solver_assert(c, s2, Z3_mk_lt(c, xi, Z3_mk_int(c, 0, int)));
        assert_eq!(Z3_solver_check(c, s2), Z3_L_FALSE);
        Z3_solver_pop(c, s2, 1);
        assert_eq!(Z3_solver_check(c, s2), Z3_L_TRUE);
        assert_eq!(model_const_names(c, s2), ["xi"]);

        // Re-checking s1 after s2's checks still lists only s1's symbols.
        assert_eq!(Z3_solver_check(c, s1), Z3_L_TRUE);
        assert_eq!(model_const_names(c, s1), ["p"]);
        Z3_del_context(c);
    }
}
