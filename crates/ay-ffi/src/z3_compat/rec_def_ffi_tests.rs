// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression battery for the P1.1 recursive-definition repairs (skeptic
//! findings, 2026-07-18):
//!
//! 1. **Builtin-name conflation** — `Z3_add_rec_def` on a name AY matches
//!    structurally as a builtin operator (`+`, `-`, `*`, …) must be REJECTED;
//!    accepting it spliced the user body into builtin arithmetic (confirmed
//!    wrong-`sat` with an invalid model, plus the wrong-`unsat` twin).
//! 2. **Undefined-recursive-declaration window** — a check whose expansion
//!    unfolds a defined body that reaches a rec-DECLARED-but-UNDEFINED
//!    function must fail closed (z3 4.15.4 answers `unsat` in that window
//!    while a plain-UF reading answers `sat`; AY releases neither).
//! 3. **Redefinition** — a second `Z3_add_rec_def` for the same name is
//!    rejected (z3 parity), keeping the registry add-only.
//! 4. **Stale model eval** — a model minted before a definition existed
//!    refuses to evaluate rec-mentioning terms once the registry has grown
//!    (it must never re-answer its own constraints through a later
//!    definition).
//! 5. **Liveness** — the symbolic-argument / divergent grind class fails
//!    closed in seconds, releasing UNSAT from the goal alone where possible
//!    (`f(n)==4 ∧ false` must be `unsat`, not a 30-112s `unknown`).

use std::ptr;
use std::time::Instant;

use super::*;

unsafe fn mk_ctx() -> Z3_context {
    let cfg = Z3_mk_config();
    let ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    ctx
}

/// Declare `name : Int^arity -> Int` through `Z3_mk_rec_func_decl`.
unsafe fn rec_decl_int(ctx: Z3_context, name: &std::ffi::CStr, arity: usize) -> Z3_func_decl {
    let int_sort = Z3_mk_int_sort(ctx);
    let domain: Vec<Z3_sort> = vec![int_sort; arity];
    Z3_mk_rec_func_decl(
        ctx,
        Z3_mk_string_symbol(ctx, name.as_ptr()),
        arity as std::ffi::c_uint,
        if arity == 0 {
            ptr::null()
        } else {
            domain.as_ptr()
        },
        int_sort,
    )
}

/// Finding 1 (skeptic #2): a rec def named `+` must be rejected, builtin
/// arithmetic must answer exactly as before, and no axiom may linger.
#[test]
fn test_rec_def_builtin_operator_name_rejected_and_builtin_intact() {
    unsafe {
        let ctx = mk_ctx();
        let int_sort = Z3_mk_int_sort(ctx);
        let plus = rec_decl_int(ctx, c"+", 2);
        assert!(!plus.is_null(), "declaring '+' stays z3-compatible");
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"y".as_ptr()), int_sort);
        let args = [x, y];
        let body = Z3_mk_mul(ctx, 2, args.as_ptr()); // '+' := '*'
        Z3_add_rec_def(ctx, plus, 2, args.as_ptr(), body);
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_INVALID_ARG,
            "a builtin-operator rec def must be rejected"
        );

        // Builtin + is untouched: 2 + 3 == 6 is UNSAT, == 5 is SAT.
        let two = Z3_mk_int(ctx, 2, int_sort);
        let three = Z3_mk_int(ctx, 3, int_sort);
        let sum_args = [two, three];
        let sum = Z3_mk_add(ctx, 2, sum_args.as_ptr());
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, sum, Z3_mk_int(ctx, 6, int_sort)));
        assert_eq!(
            Z3_solver_check(ctx, solver),
            Z3_L_FALSE,
            "2 + 3 == 6 must stay unsat after the rejected '+' definition"
        );
        let solver2 = Z3_mk_solver(ctx);
        Z3_solver_assert(
            ctx,
            solver2,
            Z3_mk_eq(ctx, sum, Z3_mk_int(ctx, 5, int_sort)),
        );
        assert_eq!(
            Z3_solver_check(ctx, solver2),
            Z3_L_TRUE,
            "2 + 3 == 5 must stay sat after the rejected '+' definition"
        );
        Z3_del_context(ctx);
    }
}

/// Finding 2 (skeptic #1): `f := g2 + 1` with `g2` rec-declared but never
/// defined. z3 answers `unsat` for BOTH `f(2)==5` and `f(2)==1`; the plain-UF
/// reading answers `sat`. AY must release NEITHER (fail-closed `unknown`),
/// while DIRECT use of the undefined `g2` stays plain-UF (`sat`, z3 parity).
#[test]
fn test_undefined_rec_decl_through_defined_body_fails_closed() {
    unsafe {
        let ctx = mk_ctx();
        let int_sort = Z3_mk_int_sort(ctx);
        let g2 = rec_decl_int(ctx, c"g2w", 1);
        let f = rec_decl_int(ctx, c"fw", 1);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"xw".as_ptr()), int_sort);
        let g2x = Z3_mk_app(ctx, g2, 1, [x].as_ptr());
        let one = Z3_mk_int(ctx, 1, int_sort);
        let body = Z3_mk_add(ctx, 2, [g2x, one].as_ptr());
        Z3_add_rec_def(ctx, f, 1, [x].as_ptr(), body);
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        let two = Z3_mk_int(ctx, 2, int_sort);
        let f2 = Z3_mk_app(ctx, f, 1, [two].as_ptr());
        for target in [5, 1] {
            let solver = Z3_mk_solver(ctx);
            Z3_solver_assert(
                ctx,
                solver,
                Z3_mk_eq(ctx, f2, Z3_mk_int(ctx, target, int_sort)),
            );
            assert_eq!(
                Z3_solver_check(ctx, solver),
                Z3_L_UNDEF,
                "f(2)=={target} through an undefined rec decl must fail closed"
            );
        }

        // DIRECT use of the undefined rec decl: both AY and z3 answer sat.
        let g2_2 = Z3_mk_app(ctx, g2, 1, [two].as_ptr());
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(
            ctx,
            solver,
            Z3_mk_eq(ctx, g2_2, Z3_mk_int(ctx, 4, int_sort)),
        );
        assert_eq!(
            Z3_solver_check(ctx, solver),
            Z3_L_TRUE,
            "direct use of an undefined rec decl stays plain-UF (z3 parity)"
        );
        Z3_del_context(ctx);
    }
}

/// Finding 3 (skeptic #1): redefinition is rejected (z3 parity: "function ...
/// has already been given a definition") and the FIRST definition stays
/// authoritative.
#[test]
fn test_rec_def_redefinition_rejected() {
    unsafe {
        let ctx = mk_ctx();
        let int_sort = Z3_mk_int_sort(ctx);
        let f = rec_decl_int(ctx, c"fredef", 1);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"xr".as_ptr()), int_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let body1 = Z3_mk_add(ctx, 2, [x, one].as_ptr());
        Z3_add_rec_def(ctx, f, 1, [x].as_ptr(), body1);
        assert_eq!(Z3_get_error_code(ctx), Z3_OK, "first definition accepted");

        let body2 = Z3_mk_add(ctx, 2, [x, two].as_ptr());
        Z3_add_rec_def(ctx, f, 1, [x].as_ptr(), body2);
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_INVALID_ARG,
            "redefinition must be rejected (z3 parity)"
        );

        // The FIRST definition still decides.
        let three = Z3_mk_int(ctx, 3, int_sort);
        let f3 = Z3_mk_app(ctx, f, 1, [three].as_ptr());
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, f3, Z3_mk_int(ctx, 4, int_sort)));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE, "f(3)==4 (x+1)");
        let solver2 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver2, Z3_mk_eq(ctx, f3, Z3_mk_int(ctx, 5, int_sort)));
        assert_eq!(
            Z3_solver_check(ctx, solver2),
            Z3_L_FALSE,
            "f(3)==5 must stay unsat under the first definition"
        );
        Z3_del_context(ctx);
    }
}

/// Finding 3's model surface: a model minted while the registry was smaller
/// refuses to evaluate rec-mentioning terms (it must never re-answer its own
/// certifying constraint through a definition it predates).
#[test]
fn test_stale_model_refuses_rec_eval_after_registry_growth() {
    unsafe {
        let ctx = mk_ctx();
        let int_sort = Z3_mk_int_sort(ctx);
        let f = rec_decl_int(ctx, c"fstale", 1);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"xs".as_ptr()), int_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let body = Z3_mk_add(ctx, 2, [x, one].as_ptr());
        Z3_add_rec_def(ctx, f, 1, [x].as_ptr(), body);
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        let three = Z3_mk_int(ctx, 3, int_sort);
        let f3 = Z3_mk_app(ctx, f, 1, [three].as_ptr());
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, f3, Z3_mk_int(ctx, 4, int_sort)));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        // Same epoch: eval f(3) == 4 works.
        let mut out: Z3_ast = 0;
        assert!(
            Z3_model_eval(ctx, model, f3, true, &mut out),
            "same-epoch eval of f(3) must succeed"
        );

        // Grow the registry with a NEW definition (redefinition is rejected,
        // so growth is the only way the registry can change).
        let g = rec_decl_int(ctx, c"gstale", 1);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let gbody = Z3_mk_add(ctx, 2, [x, two].as_ptr());
        Z3_add_rec_def(ctx, g, 1, [x].as_ptr(), gbody);
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        let mut out2: Z3_ast = 0;
        assert!(
            !Z3_model_eval(ctx, model, f3, true, &mut out2),
            "stale-epoch eval of a rec-mentioning term must be refused"
        );
        Z3_del_context(ctx);
    }
}

/// Finding 1 liveness (skeptic #1, 1a): the symbolic-argument grind class.
/// `f(n)==4 ∧ false` must be UNSAT (goal-only residual solve, z3 parity —
/// previously a 112s `unknown`), `f(n)==4` alone must fail closed to UNDEF,
/// and both must return in seconds, not minutes.
#[test]
fn test_symbolic_recursion_fails_closed_fast_and_ground_false_is_unsat() {
    unsafe {
        let ctx = mk_ctx();
        let int_sort = Z3_mk_int_sort(ctx);
        let f = rec_decl_int(ctx, c"fsym", 1);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"xg".as_ptr()), int_sort);
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let one = Z3_mk_int(ctx, 1, int_sort);
        let xm1 = Z3_mk_sub(ctx, 2, [x, one].as_ptr());
        let fxm1 = Z3_mk_app(ctx, f, 1, [xm1].as_ptr());
        let recur = Z3_mk_add(ctx, 2, [two, fxm1].as_ptr());
        let body = Z3_mk_ite(ctx, Z3_mk_le(ctx, x, zero), zero, recur);
        Z3_add_rec_def(ctx, f, 1, [x].as_ptr(), body);
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        let n = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"n".as_ptr()), int_sort);
        let fn_app = Z3_mk_app(ctx, f, 1, [n].as_ptr());
        let goal_eq = Z3_mk_eq(ctx, fn_app, Z3_mk_int(ctx, 4, int_sort));

        let start = Instant::now();
        // With literal false in the goal, the residual goal-only solve must
        // answer UNSAT (fewer constraints than the definitional problem —
        // sound), matching z3.
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, goal_eq);
        Z3_solver_assert(ctx, solver, Z3_mk_false(ctx));
        assert_eq!(
            Z3_solver_check(ctx, solver),
            Z3_L_FALSE,
            "f(n)==4 AND false must be unsat, not unknown"
        );

        // Alone, the symbolic recursion fails closed.
        let solver2 = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver2, goal_eq);
        assert_eq!(
            Z3_solver_check(ctx, solver2),
            Z3_L_UNDEF,
            "symbolic-argument recursion must fail closed"
        );
        assert!(
            start.elapsed() < std::time::Duration::from_secs(30),
            "the grind class must fail closed in seconds (was 98-112s), took {:?}",
            start.elapsed()
        );
        Z3_del_context(ctx);
    }
}
