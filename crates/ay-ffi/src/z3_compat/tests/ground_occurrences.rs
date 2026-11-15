// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::ptr;

use super::*;

/// The C API deliberately keeps the supplied bound constant's AST identity.
/// E-matching must distinguish its bound and free *occurrences* regardless of
/// which assertion first reaches the shared `f(x)` DAG node.
#[test]
fn test_z3_compat_shared_binder_free_ground_occurrences_both_orders() {
    // SAFETY: All handles are created and used within this test's context;
    // none escape, and the context is deleted after both solver checks.
    unsafe {
        let cfg = Z3_mk_config();
        Z3_set_param_value(cfg, c"timeout".as_ptr(), c"30000".as_ptr());
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), int_sort);
        let domain = [int_sort];
        let f = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, c"f".as_ptr()),
            1,
            domain.as_ptr(),
            int_sort,
        );
        let args = [x];
        let f_x = Z3_mk_app(ctx, f, 1, args.as_ptr());
        let zero = Z3_mk_int(ctx, 0, int_sort);
        let axiom_body = Z3_mk_ge(ctx, f_x, zero);
        let bound = [x];
        let axiom = Z3_mk_forall_const(ctx, 0, 1, bound.as_ptr(), 0, ptr::null(), axiom_body);
        assert_ne!(axiom, 0);
        // The body z3 returns names the binder by de Bruijn index, so it is
        // not the caller's body (libz3 5.1.0, measured 2026-10-09:
        // `ForAll([x], f(x) >= 0).body()` is `(>= (f (:var 0)) 0)`, eq to
        // `f(Var(0)) >= 0`, not eq to `f(x) >= 0`). The engine's quantifier
        // still shares the caller's `f(x)` node, which the checks below need.
        let var0 = Z3_mk_bound(ctx, 0, int_sort);
        let f_var0 = Z3_mk_app(ctx, f, 1, [var0].as_ptr());
        let introspected = Z3_get_quantifier_body(ctx, axiom);
        assert!(Z3_is_eq_ast(ctx, introspected, Z3_mk_ge(ctx, f_var0, zero)));
        assert!(!Z3_is_eq_ast(ctx, introspected, axiom_body));
        let goal = Z3_mk_lt(ctx, f_x, zero);

        for axiom_first in [true, false] {
            let solver = Z3_mk_solver(ctx);
            let assertions = if axiom_first {
                [axiom, goal]
            } else {
                [goal, axiom]
            };
            for assertion in assertions {
                Z3_solver_assert(ctx, solver, assertion);
            }
            assert_eq!(
                Z3_solver_check(ctx, solver),
                Z3_L_FALSE,
                "shared C-API binder/free `f(x)` must refute in either assertion order"
            );
        }

        Z3_del_context(ctx);
    }
}
