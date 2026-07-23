// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for Track B batch 3a: engine-backed C-API (mk set/lambda, fp numeral
//! introspection, substitute/is_ground/update_term, mk_model, qe).

use super::super::*;

unsafe fn ctx() -> Z3_context {
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

unsafe fn error_message(c: Z3_context) -> String {
    let code = unsafe { Z3_get_error_code(c) };
    // SAFETY: `c` is live and `Z3_get_error_msg` returns context-owned storage.
    unsafe {
        std::ffi::CStr::from_ptr(Z3_get_error_msg(c, code))
            .to_string_lossy()
            .into_owned()
    }
}

#[test]
fn fp_numeral_introspection() {
    unsafe {
        let c = ctx();
        let s = Z3_mk_fpa_sort_32(c);

        let nan = Z3_mk_fpa_nan(c, s);
        assert!(Z3_fpa_is_numeral(c, nan));
        assert!(Z3_fpa_is_numeral_nan(c, nan));
        assert!(!Z3_fpa_is_numeral_inf(c, nan));
        assert!(!Z3_fpa_is_numeral_zero(c, nan));

        let inf = Z3_mk_fpa_inf(c, s, false); // +inf
        assert!(Z3_fpa_is_numeral_inf(c, inf));
        assert!(Z3_fpa_is_numeral_positive(c, inf));

        let zero = Z3_mk_fpa_zero(c, s, false); // +0
        assert!(Z3_fpa_is_numeral_zero(c, zero));

        // A finite normal value: 1.5
        let onefive = Z3_mk_fpa_numeral_double(c, 1.5, s);
        assert!(Z3_fpa_is_numeral(c, onefive));
        assert!(Z3_fpa_is_numeral_normal(c, onefive));
        let mut sgn: bool = true;
        assert!(Z3_fpa_get_numeral_sign(c, onefive, &raw mut sgn));
        assert!(!sgn); // positive → sign bit false

        // A symbolic FP const is NOT a numeral.
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), s);
        assert!(!Z3_fpa_is_numeral(c, x));

        Z3_del_context(c);
    }
}

#[test]
fn set_operations_are_well_sorted() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let full = Z3_mk_full_set(c, int);
        let empty = Z3_mk_empty_set(c, int);
        let u = Z3_mk_set_union(c, 2, [full, empty].as_ptr());
        let i = Z3_mk_set_intersect(c, 2, [full, empty].as_ptr());
        let d = Z3_mk_set_difference(c, full, empty);
        let comp = Z3_mk_set_complement(c, empty);
        for t in [u, i, d, comp] {
            assert_ne!(t, 0);
            // A set is an (Array elem Bool)
            assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, t)), Z3_ARRAY_SORT);
        }
        Z3_del_context(c);
    }
}

#[test]
fn mk_model_is_non_null() {
    unsafe {
        let c = ctx();
        let m = Z3_mk_model(c);
        assert!(!m.is_null());
        Z3_del_context(c);
    }
}

#[test]
fn is_ground_and_substitute() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int);
        let y = Z3_mk_const(c, Z3_mk_string_symbol(c, c"y".as_ptr()), int);
        // (+ x y) is ground (only declared consts, no bound vars)
        let sum = Z3_mk_add(c, 2, [x, y].as_ptr());
        assert!(Z3_is_ground(c, sum));

        // substitute x -> y in (+ x y) gives (+ y y)
        let from = [x];
        let to = [y];
        let subst = Z3_substitute(c, sum, 1, from.as_ptr(), to.as_ptr());
        assert_ne!(subst, 0);
        Z3_del_context(c);
    }
}

#[test]
fn update_term_count_mismatch_returns_input_with_actual_iob_diagnostic() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"update_x".as_ptr()), int);
        let y = Z3_mk_const(c, Z3_mk_string_symbol(c, c"update_y".as_ptr()), int);
        let sum = Z3_mk_add(c, 2, [x, y].as_ptr());

        let result = Z3_update_term(c, sum, 1, [x].as_ptr());
        assert_eq!(result, sum, "failed update must return the input AST");
        assert_eq!(Z3_get_error_code(c), Z3_IOB);
        let message = error_message(c);
        assert!(
            message.contains("term expects 2 immediate children, got 1"),
            "unexpected update diagnostic: {message}"
        );
        assert_ne!(message, "Z3_update_term: argument count mismatch");

        Z3_del_context(c);
    }
}

#[test]
fn update_term_sort_and_handle_failures_report_typed_solver_errors() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"typed_update_x".as_ptr()), int);
        let y = Z3_mk_const(c, Z3_mk_string_symbol(c, c"typed_update_y".as_ptr()), int);
        let sum = Z3_mk_add(c, 2, [x, y].as_ptr());
        let truth = Z3_mk_true(c);

        let sort_failure = Z3_update_term(c, sum, 2, [truth, y].as_ptr());
        assert_eq!(sort_failure, sum, "sort failure must return the input AST");
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        let message = error_message(c);
        assert!(
            message.contains("sort mismatch in update_term"),
            "unexpected sort diagnostic: {message}"
        );
        assert!(!message.contains("argument count mismatch"));

        let invalid = u64::from(u32::MAX) + 1;
        let handle_failure = Z3_update_term(c, sum, 2, [invalid, y].as_ptr());
        assert_eq!(
            handle_failure, sum,
            "invalid replacement must return the input AST"
        );
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        let message = error_message(c);
        assert!(
            message.contains(
                "replacement at position 0 AST handle 4294967296 belongs to a different context"
            ),
            "unexpected handle diagnostic: {message}"
        );
        assert!(!message.contains("argument count mismatch"));

        let source_failure = Z3_update_term(c, invalid, 0, ptr::null());
        assert_eq!(
            source_failure, invalid,
            "invalid source must be returned unchanged"
        );
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        let message = error_message(c);
        assert!(
            message.contains("source AST handle 4294967296 belongs to a different context"),
            "unexpected source diagnostic: {message}"
        );

        Z3_del_context(c);
    }
}

#[test]
fn update_term_rejects_null_wrapping_tagged_and_foreign_context_ast_handles() {
    unsafe {
        let c = ctx();
        let bool_sort = Z3_mk_bool_sort(c);
        let p = Z3_mk_const(
            c,
            Z3_mk_string_symbol(c, c"raw_update_p".as_ptr()),
            bool_sort,
        );
        let q = Z3_mk_const(
            c,
            Z3_mk_string_symbol(c, c"raw_update_q".as_ptr()),
            bool_sort,
        );
        let not_p = Z3_mk_not(c, p);

        let null_child = Z3_update_term(c, not_p, 1, [0].as_ptr());
        assert_eq!(null_child, not_p);
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(error_message(c).contains("replacement at position 0 AST handle is null"));

        let wrapping = (not_p & !TERM_AST_PAYLOAD_MASK) | (u64::from(u32::MAX) + 2);
        let wrapping_child = Z3_update_term(c, not_p, 1, [wrapping].as_ptr());
        assert_eq!(wrapping_child, not_p);
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(error_message(c).contains("exceeds the maximum term payload"));

        let tagged_sort = Z3_sort_to_ast(c, bool_sort);
        let tagged_child = Z3_update_term(c, not_p, 1, [tagged_sort].as_ptr());
        assert_eq!(tagged_child, not_p);
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(error_message(c).contains("is tagged and does not denote a term"));

        let foreign = ctx();
        let foreign_bool = Z3_mk_bool_sort(foreign);
        let _foreign_p = Z3_mk_const(
            foreign,
            Z3_mk_string_symbol(foreign, c"foreign_raw_update_p".as_ptr()),
            foreign_bool,
        );
        let foreign_q = Z3_mk_const(
            foreign,
            Z3_mk_string_symbol(foreign, c"foreign_raw_update_q".as_ptr()),
            foreign_bool,
        );
        assert_eq!(
            foreign_q & TERM_AST_PAYLOAD_MASK,
            q & TERM_AST_PAYLOAD_MASK,
            "fixture must exercise a colliding per-context term id"
        );
        assert_ne!(
            foreign_q, q,
            "the opaque handle must retain its context discriminator"
        );
        let foreign_child = Z3_update_term(c, not_p, 1, [foreign_q].as_ptr());
        assert_eq!(foreign_child, not_p);
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(error_message(c).contains("belongs to a different context"));

        let null_array = Z3_update_term(c, not_p, 1, ptr::null());
        assert_eq!(null_array, not_p);
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(error_message(c).contains("replacement AST array is null"));

        let null_source = Z3_update_term(c, 0, 0, ptr::null());
        assert_eq!(null_source, 0);
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(error_message(c).contains("source AST handle is null"));

        let valid = Z3_update_term(c, not_p, 1, [q].as_ptr());
        assert_ne!(valid, 0, "valid update remains accepted after failures");
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        Z3_del_context(foreign);
        Z3_del_context(c);
    }
}

#[test]
fn update_term_accepts_parser_and_accessor_handles_without_sort_cache_entries() {
    unsafe {
        let c = ctx();
        let parsed = Z3_parse_smtlib2_string(
            c,
            c"(declare-const p Bool)
              (declare-const q Bool)
              (declare-fun f (Bool Bool) Bool)
              (assert (f (f p q) q))
              (assert (forall ((x Int)) (> x 0)))"
                .as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_ast_vector_size(c, parsed), 2);

        // Parser roots are context-owned live terms even though the parser
        // bridge does not populate the FFI surface-sort cache for every node.
        let parsed_root = Z3_ast_vector_get(c, parsed, 0);
        assert_eq!(Z3_get_app_num_args(c, parsed_root), 2);
        let parsed_child = Z3_get_app_arg(c, parsed_root, 0);
        let parsed_rhs = Z3_get_app_arg(c, parsed_root, 1);
        let rebuilt_root = Z3_update_term(c, parsed_root, 2, [parsed_child, parsed_rhs].as_ptr());
        assert_eq!(rebuilt_root, parsed_root);
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        // Children returned by application accessors have the same status.
        // Exercise both the accessor-produced source and its unrecorded
        // accessor-produced replacements.
        assert_eq!(Z3_get_app_num_args(c, parsed_child), 2);
        let lhs = Z3_get_app_arg(c, parsed_child, 0);
        let rhs = Z3_get_app_arg(c, parsed_child, 1);
        let rebuilt_child = Z3_update_term(c, parsed_child, 2, [lhs, rhs].as_ptr());
        assert_eq!(rebuilt_child, parsed_child);
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        // Quantifier-body accessors likewise return valid arena terms without
        // requiring a prior `record_ast_sort` call.
        let quantified = Z3_ast_vector_get(c, parsed, 1);
        let body = Z3_get_quantifier_body(c, quantified);
        assert_eq!(Z3_get_app_num_args(c, body), 2);
        let body_lhs = Z3_get_app_arg(c, body, 0);
        let body_rhs = Z3_get_app_arg(c, body, 1);
        let rebuilt_body = Z3_update_term(c, body, 2, [body_lhs, body_rhs].as_ptr());
        assert_eq!(rebuilt_body, body);
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        Z3_del_context(c);
    }
}

#[test]
fn solver_and_core_constructors_reject_foreign_context_term_asts() {
    unsafe {
        let local = ctx();
        let foreign = ctx();
        let local_bool = Z3_mk_bool_sort(local);
        let foreign_bool = Z3_mk_bool_sort(foreign);
        let local_p = Z3_mk_const(
            local,
            Z3_mk_string_symbol(local, c"context_owned_p".as_ptr()),
            local_bool,
        );
        let foreign_p = Z3_mk_const(
            foreign,
            Z3_mk_string_symbol(foreign, c"foreign_p".as_ptr()),
            foreign_bool,
        );
        assert_eq!(
            local_p & TERM_AST_PAYLOAD_MASK,
            foreign_p & TERM_AST_PAYLOAD_MASK,
            "fixture must use colliding local term ids"
        );
        assert_ne!(local_p, foreign_p);

        let solver = Z3_mk_solver(local);
        Z3_solver_assert(local, solver, foreign_p);
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);
        assert_eq!(
            Z3_ast_vector_size(local, Z3_solver_get_assertions(local, solver)),
            0,
            "a foreign formula must not alias and enter the local assertion stack"
        );

        let negated = Z3_mk_not(local, foreign_p);
        assert_eq!(negated, 0);
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);
        assert!(error_message(local).contains("belongs to a different context"));

        let equality = Z3_mk_eq(local, local_p, foreign_p);
        assert_eq!(equality, 0);
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);

        let assumption_result = Z3_solver_check_assumptions(local, solver, 1, [foreign_p].as_ptr());
        assert_eq!(assumption_result, Z3_L_UNDEF);
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);

        Z3_del_context(foreign);
        Z3_del_context(local);
    }
}

#[test]
fn identity_and_singleton_builders_do_not_launder_foreign_term_asts() {
    unsafe {
        let local = ctx();
        let foreign = ctx();

        // `char.to_int` is intentionally an identity at the core-term level.
        // It must authenticate before returning the input handle, or a foreign
        // low-payload collision would be re-exported as if it belonged locally.
        let local_char = Z3_mk_char(local, 65);
        let foreign_char = Z3_mk_char(foreign, 65);
        assert_eq!(
            local_char & TERM_AST_PAYLOAD_MASK,
            foreign_char & TERM_AST_PAYLOAD_MASK
        );
        assert_eq!(Z3_mk_char_to_int(local, foreign_char), 0);
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);
        assert_eq!(Z3_mk_char_to_int(local, local_char), local_char);

        // The one-argument set-union fast path also returns its sole operand.
        // Authentication must happen before that fast path.
        let local_int = Z3_mk_int_sort(local);
        let foreign_int = Z3_mk_int_sort(foreign);
        let local_set = Z3_mk_empty_set(local, local_int);
        let foreign_set = Z3_mk_empty_set(foreign, foreign_int);
        assert_eq!(
            local_set & TERM_AST_PAYLOAD_MASK,
            foreign_set & TERM_AST_PAYLOAD_MASK
        );
        assert_eq!(
            Z3_mk_set_union(local, 1, [foreign_set].as_ptr()),
            0,
            "a singleton identity path must not return a foreign handle"
        );
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);
        assert_eq!(Z3_mk_set_union(local, 1, [local_set].as_ptr()), local_set);

        Z3_del_context(foreign);
        Z3_del_context(local);
    }
}

#[test]
fn goal_formula_accessor_does_not_reexport_a_foreign_context_term() {
    unsafe {
        let local = ctx();
        let foreign = ctx();
        let local_bool = Z3_mk_bool_sort(local);
        let foreign_bool = Z3_mk_bool_sort(foreign);
        let local_p = Z3_mk_const(
            local,
            Z3_mk_string_symbol(local, c"goal_accessor_local_p".as_ptr()),
            local_bool,
        );
        let foreign_p = Z3_mk_const(
            foreign,
            Z3_mk_string_symbol(foreign, c"goal_accessor_foreign_p".as_ptr()),
            foreign_bool,
        );
        assert_eq!(
            local_p & TERM_AST_PAYLOAD_MASK,
            foreign_p & TERM_AST_PAYLOAD_MASK,
            "fixture must exercise a colliding local term id"
        );

        let goal = Z3_mk_goal(foreign, false, false, false);
        Z3_goal_assert(foreign, goal, foreign_p);
        assert_eq!(Z3_goal_formula(foreign, goal, 0), foreign_p);

        assert_eq!(
            Z3_goal_formula(local, goal, 0),
            0,
            "an accessor must not re-export a stored foreign AST under another context"
        );
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);
        assert!(error_message(local).contains("belongs to a different context"));

        Z3_del_context(foreign);
        Z3_del_context(local);
    }
}

#[test]
fn pattern_accessors_authenticate_the_pattern_owner() {
    unsafe {
        let local = ctx();
        let foreign = ctx();
        let local_bool = Z3_mk_bool_sort(local);
        let foreign_bool = Z3_mk_bool_sort(foreign);
        let local_p = Z3_mk_const(
            local,
            Z3_mk_string_symbol(local, c"pattern_owner_local_p".as_ptr()),
            local_bool,
        );
        let foreign_p = Z3_mk_const(
            foreign,
            Z3_mk_string_symbol(foreign, c"pattern_owner_foreign_p".as_ptr()),
            foreign_bool,
        );
        assert_eq!(
            local_p & TERM_AST_PAYLOAD_MASK,
            foreign_p & TERM_AST_PAYLOAD_MASK,
            "fixture must exercise colliding trigger term ids"
        );

        let pattern = Z3_mk_pattern(foreign, 1, &raw const foreign_p);
        assert!(!pattern.is_null());
        assert_eq!(Z3_pattern_to_ast(foreign, pattern), foreign_p);
        assert_eq!(Z3_pattern_to_ast(local, pattern), 0);
        assert_eq!(Z3_get_error_code(local), Z3_INVALID_ARG);
        assert!(error_message(local).contains("different context"));

        Z3_del_context(foreign);
        Z3_del_context(local);
    }
}

#[test]
fn translate_authenticates_the_ast_against_its_declared_source_context() {
    unsafe {
        let source = ctx();
        let foreign = ctx();
        let target = ctx();
        let source_bool = Z3_mk_bool_sort(source);
        let foreign_bool = Z3_mk_bool_sort(foreign);
        let source_p = Z3_mk_const(
            source,
            Z3_mk_string_symbol(source, c"translate_source_p".as_ptr()),
            source_bool,
        );
        let foreign_p = Z3_mk_const(
            foreign,
            Z3_mk_string_symbol(foreign, c"translate_foreign_p".as_ptr()),
            foreign_bool,
        );
        assert_eq!(
            source_p & TERM_AST_PAYLOAD_MASK,
            foreign_p & TERM_AST_PAYLOAD_MASK,
            "fixture must exercise a colliding source term id"
        );

        assert_eq!(Z3_translate(source, foreign_p, target), 0);
        assert_eq!(Z3_get_error_code(target), Z3_INVALID_ARG);
        assert!(error_message(target).contains("different source context"));

        // The same-context identity shortcut is also an authentication
        // boundary and must not launder the foreign handle unchanged.
        assert_eq!(Z3_translate(source, foreign_p, source), 0);
        assert_eq!(Z3_get_error_code(source), Z3_INVALID_ARG);

        let translated = Z3_translate(source, source_p, target);
        assert_ne!(translated, 0);
        assert_ne!(translated, source_p);
        assert_eq!(Z3_get_error_code(target), Z3_OK);

        Z3_del_context(target);
        Z3_del_context(foreign);
        Z3_del_context(source);
    }
}

#[test]
fn str_lex_ops_build() {
    unsafe {
        let c = ctx();
        let s = Z3_mk_string_sort(c);
        let a = Z3_mk_const(c, Z3_mk_string_symbol(c, c"a".as_ptr()), s);
        let b = Z3_mk_const(c, Z3_mk_string_symbol(c, c"b".as_ptr()), s);
        let le = Z3_mk_str_le(c, a, b);
        let lt = Z3_mk_str_lt(c, a, b);
        assert_ne!(le, 0);
        assert_ne!(lt, 0);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, le)), Z3_BOOL_SORT);
        Z3_del_context(c);
    }
}

/// Render an AST via `Z3_ast_to_string` (test helper).
unsafe fn ast_str(c: Z3_context, a: Z3_ast) -> String {
    // SAFETY: caller passes a live context and AST from that context.
    unsafe {
        std::ffi::CStr::from_ptr(Z3_ast_to_string(c, a))
            .to_string_lossy()
            .into_owned()
    }
}

/// Regression (2026-07-10 re-audit, gap #4 WRONG-RESULT): the de Bruijn
/// `Z3_mk_lambda` path must resolve `__db{k}` bound occurrences into the
/// named binder vars. Before the fix, `select((lambda x:Int. x+1), 41)`
/// "simplified" to the OPEN term `(+ __db0 1)` instead of `42` (libz3: `42`),
/// and the lambda printed the nonstandard `(lambda-array x ...)` shape
/// instead of z3's `(lambda ((x Int)) (+ x 1))`.
#[test]
fn lambda_de_bruijn_beta_reduction_and_print() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        // lambda x:Int. x + 1  (body over de Bruijn index 0)
        let db0 = Z3_mk_bound(c, 0, int);
        let one = Z3_mk_int(c, 1, int);
        let add_args = [db0, one];
        let body = Z3_mk_add(c, 2, add_args.as_ptr());
        let xn = Z3_mk_string_symbol(c, c"x".as_ptr());
        let lam = Z3_mk_lambda(c, 1, &raw const int, &raw const xn, body);
        assert_ne!(lam, 0);
        // z3-standard binder shape, no internal `lambda-array` / `__db` names.
        assert_eq!(ast_str(c, lam), "(lambda ((x Int)) (+ x 1))");
        // Beta reduction: select at 41 → 42, twin-checked vs libz3.
        let sel = Z3_mk_select(c, lam, Z3_mk_int(c, 41, int));
        let simp = Z3_simplify(c, sel);
        let s = ast_str(c, simp);
        assert_eq!(s, "42", "select(lambda x. x+1, 41) must simplify to 42");
        assert!(!s.contains("__db"), "no open de Bruijn var may leak: {s}");
        Z3_del_context(c);
    }
}

/// Nested de Bruijn lambdas: `select((lambda x. select((lambda y. x+y), 10)), 5)`
/// must evaluate to `15` (libz3-twin-checked) — the outer binder's occurrence
/// inside the inner lambda is index 1, and surviving indices must be
/// re-anchored when the inner binder is constructed/reduced.
#[test]
fn lambda_de_bruijn_nested_beta_reduction() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let db0 = Z3_mk_bound(c, 0, int);
        let db1 = Z3_mk_bound(c, 1, int);
        let a2 = [db1, db0];
        let inner_body = Z3_mk_add(c, 2, a2.as_ptr()); // x + y
        let yn = Z3_mk_string_symbol(c, c"y".as_ptr());
        let inner = Z3_mk_lambda(c, 1, &raw const int, &raw const yn, inner_body);
        let inner_sel = Z3_mk_select(c, inner, Z3_mk_int(c, 10, int));
        let xn = Z3_mk_string_symbol(c, c"x".as_ptr());
        let outer = Z3_mk_lambda(c, 1, &raw const int, &raw const xn, inner_sel);
        let outer_sel = Z3_mk_select(c, outer, Z3_mk_int(c, 5, int));
        let s = ast_str(c, Z3_simplify(c, outer_sel));
        assert_eq!(s, "15", "nested lambda beta reduction must yield 15");
        Z3_del_context(c);
    }
}

/// Solver-path verdicts for select-over-lambda must match libz3:
/// `(= (select (lambda x. x+1) 41) 42)` is sat; `(= ... 43)` alone is unsat.
#[test]
fn lambda_select_solver_verdicts_match_z3() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let db0 = Z3_mk_bound(c, 0, int);
        let one = Z3_mk_int(c, 1, int);
        let add_args = [db0, one];
        let body = Z3_mk_add(c, 2, add_args.as_ptr());
        let xn = Z3_mk_string_symbol(c, c"x".as_ptr());
        let lam = Z3_mk_lambda(c, 1, &raw const int, &raw const xn, body);
        let sel = Z3_mk_select(c, lam, Z3_mk_int(c, 41, int));

        let s1 = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s1);
        Z3_solver_assert(c, s1, Z3_mk_eq(c, sel, Z3_mk_int(c, 42, int)));
        assert_eq!(Z3_solver_check(c, s1), Z3_L_TRUE, "= 42 must be sat");

        let s2 = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s2);
        Z3_solver_assert(c, s2, Z3_mk_eq(c, sel, Z3_mk_int(c, 43, int)));
        assert_eq!(
            Z3_solver_check(c, s2),
            Z3_L_FALSE,
            "= 43 alone must be unsat"
        );
        Z3_del_context(c);
    }
}
