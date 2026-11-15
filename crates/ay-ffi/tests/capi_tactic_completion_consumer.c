// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C consumer for the Z3-compatible Tactic-combinator completion C API:
//   Z3_tactic_skip / _fail / _fail_if / _fail_if_not_decided / _when / _cond /
//   _try_for / _par_and_then / _par_or / _get_descr / _get_param_descrs, plus
//   Z3_tactic_apply_ex.
//
// Each combinator is BUILT and then actually RUN via Z3_tactic_apply on a real
// goal; the observable ApplyResult (num_subgoals + per-subgoal size, or an honest
// apply-failure) is asserted. Every expected value is what libz3 4.15.4 returns
// for the SAME goal+tactic — so this single source compiles and runs against BOTH
// ay-ffi (default) and libz3 (`-DAY_TWIN_USE_Z3 -lz3`), and both must pass the
// identical shared assertions. That is the cross-check: ay's observable
// apply-result behavior == libz3's.
//
// Leaf tactics are skip/fail/split-clause (whose apply-results are identical in
// ay and libz3, independent of formula-simplification shape) and the probes
// is-qflia / is-qfbv (already cross-checked in the goal/probe consumer). A
// non-aborting error handler is installed so an expected tactic FAILURE surfaces
// as (apply == NULL, error-code != Z3_OK) instead of libz3's default abort.

#ifdef AY_TWIN_USE_Z3
#include <z3.h>
#else
#include "ay.h"
#include "ay_z3_compat.h"
#endif

#include <stdio.h>
#include <string.h>
#include <limits.h>

static int g_pass = 0;
static int g_fail = 0;

#define CHECK_U(actual, expected, what)                                        \
    do {                                                                       \
        unsigned a_ = (unsigned)(actual);                                      \
        unsigned e_ = (unsigned)(expected);                                    \
        if (a_ == e_) {                                                        \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s: got %u want %u\n", (what), a_, e_);               \
        }                                                                      \
    } while (0)

#define CHECK_B(actual, expected, what)                                        \
    do {                                                                       \
        int a_ = (actual) ? 1 : 0;                                             \
        int e_ = (expected) ? 1 : 0;                                           \
        if (a_ == e_) {                                                        \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s: got %d want %d\n", (what), a_, e_);               \
        }                                                                      \
    } while (0)

// A non-aborting error handler: an honest tactic failure sets the error code and
// returns NULL; without this, libz3's default handler would abort the process.
#ifdef AY_TWIN_USE_Z3
static void err_handler(Z3_context c, Z3_error_code e) { (void)c; (void)e; }
#else
static void err_handler(Z3_context c, unsigned int e) { (void)c; (void)e; }
#endif

static Z3_context C;

// inc_ref a freshly built tactic (libz3 requires it; ay's inc_ref is a no-op).
static Z3_tactic T(Z3_tactic t) { Z3_tactic_inc_ref(C, t); return t; }

// Apply t to g. On success: *pn = num_subgoals, *psz0 = size of subgoal 0.
// Returns 1 on success, 0 on an honest apply-failure (NULL + error set).
static int t_apply(Z3_tactic t, Z3_goal g, unsigned *pn, unsigned *psz0) {
    Z3_apply_result r = Z3_tactic_apply(C, t, g);
    if (r == NULL || Z3_get_error_code(C) != Z3_OK) {
        return 0;
    }
    Z3_apply_result_inc_ref(C, r);
    unsigned n = Z3_apply_result_get_num_subgoals(C, r);
    if (pn) *pn = n;
    if (psz0) {
        *psz0 = (n > 0) ? Z3_goal_size(C, Z3_apply_result_get_subgoal(C, r, 0)) : 0u;
    }
    Z3_apply_result_dec_ref(C, r);
    return 1;
}

// Assert that applying t to g yields exactly `n` subgoals whose subgoal[0] has
// size `sz0` (an ApplyResult cross-check).
static void expect_ok(Z3_tactic t, Z3_goal g, unsigned n, unsigned sz0,
                      const char *what) {
    unsigned gotn = 999, gotsz = 999;
    int ok = t_apply(t, g, &gotn, &gotsz);
    CHECK_B(ok, 1, what);
    if (ok) {
        CHECK_U(gotn, n, what);
        CHECK_U(gotsz, sz0, what);
    }
}

// Assert that applying t to g is an HONEST failure (apply == NULL + error set).
static void expect_fail(Z3_tactic t, Z3_goal g, const char *what) {
    int ok = t_apply(t, g, NULL, NULL);
    CHECK_B(ok, 0, what);
}

static Z3_ast int_var(const char *n) {
    return Z3_mk_const(C, Z3_mk_string_symbol(C, n), Z3_mk_int_sort(C));
}
static Z3_ast bool_var(const char *n) {
    return Z3_mk_const(C, Z3_mk_string_symbol(C, n), Z3_mk_bool_sort(C));
}

/* The parameter changes actual sequence rewriting, not just a descriptor.
 * A prefix predicate preserves the power until the rewriter runs (AY's
 * equality constructor can already lower a fixed-word power to membership
 * and length constraints). Inspect the actual typed word operand. */
static void polynomial_parameters(void) {
    Z3_sort real = Z3_mk_real_sort(C);
    Z3_ast x = Z3_mk_const(C, Z3_mk_string_symbol(C, "som_x"), real);
    Z3_ast one = Z3_mk_real(C, 1, 1), two = Z3_mk_real(C, 2, 1);
    Z3_ast left_args[] = { x, one }, right_args[] = { x, two };
    Z3_ast left = Z3_mk_add(C, 2, left_args), right = Z3_mk_add(C, 2, right_args);
    Z3_ast factors[] = { left, right };
    Z3_ast source = Z3_mk_mul(C, 2, factors);
    Z3_params parameters = Z3_mk_params(C);
    Z3_params_inc_ref(C, parameters);
    Z3_symbol som = Z3_mk_string_symbol(C, "som");
    Z3_params_set_bool(C, parameters, som, true);
    Z3_ast result = Z3_simplify_ex(C, source, parameters);
    CHECK_B(result != 0, 1, "SOM direct rewrite succeeds");
    if (result) {
        CHECK_U(Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))), Z3_OP_ADD, "SOM expands product into a sum");
        CHECK_U(Z3_get_app_num_args(C, Z3_to_app(C, result)), 3, "SOM combines equal monomials");
        Z3_solver solver = Z3_mk_solver(C);
        Z3_solver_inc_ref(C, solver);
        Z3_solver_assert(C, solver, Z3_mk_eq(C, x, Z3_mk_real(C, 3, 1)));
        Z3_solver_assert(C, solver, Z3_mk_not(C, Z3_mk_eq(C, result, Z3_mk_real(C, 20, 1))));
        CHECK_B(Z3_solver_check(C, solver) == Z3_L_FALSE, 1, "rewritten polynomial has exact original value");
        Z3_solver_dec_ref(C, solver);
    }
    Z3_params_set_bool(C, parameters, Z3_mk_string_symbol(C, "flat"), false);
    result = Z3_simplify_ex(C, source, parameters);
    CHECK_B(result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))) == Z3_OP_MUL, 1, "direct flat=false disables SOM");
    Z3_params_set_bool(C, parameters, Z3_mk_string_symbol(C, "flat"), true);
    Z3_params_set_uint(C, parameters, Z3_mk_string_symbol(C, "som_blowup"), 0);
    result = Z3_simplify_ex(C, source, parameters);
    CHECK_B(result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))) == Z3_OP_MUL, 1, "SOM blowup zero retains product of sums");
    Z3_params_set_uint(C, parameters, Z3_mk_string_symbol(C, "som_blowup"), 10);
    Z3_params_set_uint(C, parameters, som, 42);
    result = Z3_simplify_ex(C, source, parameters);
    CHECK_B(result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))) == Z3_OP_MUL, 1, "direct wrong-type SOM falls back to default");
    Z3_params_set_bool(C, parameters, som, true);
    Z3_goal goal = Z3_mk_goal(C, false, false, false);
    Z3_goal_inc_ref(C, goal);
    Z3_goal_assert(C, goal, Z3_mk_eq(C, source, Z3_mk_real(C, 0, 1)));
    Z3_tactic simplify = T(Z3_mk_tactic(C, "simplify"));
    Z3_tactic configured = T(Z3_tactic_using_params(C, simplify, parameters));
    Z3_apply_result applied = Z3_tactic_apply(C, configured, goal);
    CHECK_B(applied != 0, 1, "using-params executes actual polynomial rewrite");
    if (applied) {
        Z3_apply_result_inc_ref(C, applied);
        Z3_goal output = Z3_apply_result_get_subgoal(C, applied, 0);
        const char *text = Z3_goal_to_string(C, output);
        CHECK_B(text != 0 && strstr(text, "(+") != 0, 1, "using-params output contains collected sum");
        Z3_apply_result_dec_ref(C, applied);
    }
    Z3_global_param_set("rewriter.som", "true");
    result = Z3_simplify(C, source);
    CHECK_B(result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))) == Z3_OP_ADD, 1, "global SOM affects ordinary simplify");
    Z3_global_param_set("rewriter.som", "false");
    result = Z3_simplify(C, source);
    CHECK_B(result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))) == Z3_OP_MUL, 1, "global SOM false restores default behavior");
    Z3_ast nested_args[] = { left, two };
    Z3_ast nested = Z3_mk_add(C, 2, nested_args);
    Z3_ast scaled_args[] = { Z3_mk_real(C, 3, 1), nested };
    Z3_ast scaled = Z3_mk_mul(C, 2, scaled_args);
    Z3_params_set_bool(C, parameters, som, false);
    Z3_params_set_bool(C, parameters, Z3_mk_string_symbol(C, "flat"), false);
    result = Z3_simplify_ex(C, scaled, parameters);
    CHECK_B(result != 0, 1, "generated scalar products normalize with flat=false");
    if (result) {
        printf("SOM_FLAT_FALSE arity=%u text=%s\n", Z3_get_app_num_args(C, Z3_to_app(C, result)), Z3_ast_to_string(C, result));
        CHECK_U(Z3_get_app_num_args(C, Z3_to_app(C, result)), 2, "flat=false keeps nested sum AST despite flattened printer display");
        Z3_ast nested_result = Z3_get_app_arg(C, Z3_to_app(C, result), 1);
        CHECK_B(nested_result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, nested_result))) == Z3_OP_ADD, 1, "generated scalar product recursively distributes");
    }
#ifndef AY_TWIN_USE_Z3
    Z3_goal core_goal = Z3_mk_goal(C, false, true, false);
    Z3_goal_inc_ref(C, core_goal);
    Z3_goal_assert(C, core_goal, Z3_mk_eq(C, source, Z3_mk_real(C, 0, 1)));
    CHECK_B(Z3_tactic_apply(C, configured, core_goal) == 0 && Z3_get_error_code(C) != Z3_OK, 1, "SOM never invents a proof/core converter");
    Z3_goal_dec_ref(C, core_goal);
#endif
    Z3_global_param_set("rewriter.max_power_expansion", "4");
    Z3_ast count_args[] = { Z3_mk_int(C, 1, Z3_mk_int_sort(C)), Z3_mk_int(C, 2, Z3_mk_int_sort(C)) };
    Z3_ast count = Z3_mk_add(C, 2, count_args);
    Z3_ast repeated = Z3_simplify(C, Z3_mk_seq_power(C, Z3_mk_string(C, "ab"), count));
    CHECK_B(repeated != 0 && strcmp(Z3_ast_to_string(C, repeated), "\"ababab\"") == 0, 1, "ring-folded exponent reaches sequence normal form");
    Z3_global_param_set("rewriter.max_power_expansion", "2");
    Z3_params_dec_ref(C, parameters);
    Z3_goal_dec_ref(C, goal);
}

static void sequence_power_parameters(void) {
    Z3_ast base = Z3_mk_string(C, "ab");
    Z3_ast n = Z3_mk_int(C, 3, Z3_mk_int_sort(C));
    Z3_ast source = Z3_mk_seq_power(C, base, n);
    Z3_ast word = Z3_mk_const(C, Z3_mk_string_symbol(C, "power_word"), Z3_mk_string_sort(C));
    Z3_goal goal = Z3_mk_goal(C, false, false, false);
    Z3_goal_inc_ref(C, goal);
    Z3_goal_assert(C, goal, Z3_mk_seq_prefix(C, source, word));
    for (unsigned limit = 2; limit <= 4; limit += 2) {
        Z3_global_param_set("rewriter.max_power_expansion", limit == 2 ? "2" : "4");
        Z3_tactic simplify = T(Z3_mk_tactic(C, "simplify"));
        Z3_params p = Z3_mk_params(C);
        Z3_params_inc_ref(C, p);
        Z3_apply_result result = Z3_tactic_apply_ex(C, simplify, goal, p);
        CHECK_B(result != NULL, 1, "sequence parameter is accepted by the real tactic");
        if (result != NULL) {
            Z3_apply_result_inc_ref(C, result);
            CHECK_U(Z3_apply_result_get_num_subgoals(C, result), 1, "sequence rewrite has one goal");
            Z3_goal output = Z3_apply_result_get_subgoal(C, result, 0);
            CHECK_U(Z3_goal_size(C, output), 1, "sequence predicate retained");
            Z3_ast predicate = Z3_goal_formula(C, output, 0);
            Z3_app app = Z3_to_app(C, predicate);
            unsigned arity = Z3_get_app_num_args(C, app);
            int found = 0;
            for (unsigned i = 0; i < arity; ++i) {
                Z3_ast child = Z3_get_app_arg(C, app, i);
                if (limit == 2) {
                    found |= Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, child))) == Z3_OP_SEQ_POWER;
                } else if (Z3_is_string(C, child)) {
                    found |= strcmp(Z3_get_string(C, child), "ababab") == 0;
                }
            }
            CHECK_B(found, 1, "threshold controls retained power versus actual literal repetition");
            Z3_apply_result_dec_ref(C, result);
        }
        Z3_params_dec_ref(C, p);
    }
    Z3_global_param_set("rewriter.max_power_expansion", "2");
    Z3_tactic simplify = T(Z3_mk_tactic(C, "simplify"));
    Z3_params local = Z3_mk_params(C);
    Z3_params_inc_ref(C, local);
    Z3_params_set_uint(C, local, Z3_mk_string_symbol(C, "max_power_expansion"), 4);
    CHECK_B(Z3_tactic_apply_ex(C, simplify, goal, local) == NULL, 1,
            "module setting is not accepted as a local tactic parameter");
    CHECK_B(Z3_tactic_using_params(C, simplify, local) == NULL, 1,
            "using-params preserves the upstream descriptor boundary");
    Z3_params_dec_ref(C, local);
    Z3_goal_dec_ref(C, goal);
}

/* Primary direct-API observations: unlike tactic_apply_ex, upstream's term
 * simplifier does not validate against the tactic descriptor set. */
static void direct_simplifier_parameters(void) {
    Z3_ast base = Z3_mk_string(C, "ab");
    Z3_ast source = Z3_mk_seq_power(C, base, Z3_mk_int(C, 3, Z3_mk_int_sort(C)));
    enum DirectKind { DIRECT_UINT, DIRECT_BOOL };
    const struct { const char *name; const char *key; enum DirectKind kind; unsigned value; } cases[] = {
        {"local_power", "max_power_expansion", DIRECT_UINT, 4},
        {"wrong_power_type", "max_power_expansion", DIRECT_BOOL, 1},
        {"unknown_uint", "not_a_real_simplifier_parameter", DIRECT_UINT, 4},
        {"zero_steps", "max_steps", DIRECT_UINT, 0},
        {"zero_memory", "max_memory", DIRECT_UINT, 0},
        {"zero_timeout", "timeout", DIRECT_UINT, 0},
        {"ctrl_c_false", "ctrl_c", DIRECT_BOOL, 0},
    };
    Z3_global_param_set("rewriter.max_power_expansion", "2");
    for (unsigned i = 0; i < sizeof(cases)/sizeof(cases[0]); ++i) {
        Z3_params p = Z3_mk_params(C);
        Z3_params_inc_ref(C, p);
        Z3_symbol key = Z3_mk_string_symbol(C, cases[i].key);
        if (cases[i].kind == DIRECT_UINT) Z3_params_set_uint(C, p, key, cases[i].value);
        else Z3_params_set_bool(C, p, key, cases[i].value != 0);
        Z3_ast result = Z3_simplify_ex(C, source, p);
        unsigned error = Z3_get_error_code(C);
        printf("DIRECT %s error=%u result=%s\n", cases[i].name, error,
               result == 0 ? "NULL" : Z3_ast_to_string(C, result));
        if (i == 0) {
            CHECK_B(result != 0 && Z3_is_string(C, result) && strcmp(Z3_get_string(C, result), "ababab") == 0, 1,
                    "direct local sequence setting really expands the literal");
        } else if (i == 3 || i == 4) {
            CHECK_B(result == 0 && error == Z3_EXCEPTION, 1, "direct zero work/memory restriction refuses");
        } else if (i == 2) {
#ifdef AY_TWIN_USE_Z3
            CHECK_B(result != 0, 1, "reference direct API ignores an unknown key");
#else
            CHECK_B(result == 0 && error == Z3_EXCEPTION, 1, "AY explicitly refuses unsupported direct keys");
#endif
        } else {
            CHECK_B(result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))) == Z3_OP_SEQ_POWER, 1,
                    "direct defaults and wrong-type fallback retain the power");
        }
        Z3_params_dec_ref(C, p);
    }
    Z3_global_param_set("rewriter.max_power_expansion", "4");
    Z3_ast result = Z3_simplify(C, source);
    printf("DIRECT global_power error=%u result=%s\n", Z3_get_error_code(C), result == 0 ? "NULL" : Z3_ast_to_string(C, result));
    CHECK_B(result != 0 && Z3_is_string(C, result) && strcmp(Z3_get_string(C, result), "ababab") == 0, 1,
            "plain direct simplify consumes the actual global setting");
    Z3_params local = Z3_mk_params(C);
    Z3_params_inc_ref(C, local);
    Z3_params_set_uint(C, local, Z3_mk_string_symbol(C, "max_power_expansion"), 2);
    result = Z3_simplify_ex(C, source, local);
    CHECK_B(result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))) == Z3_OP_SEQ_POWER, 1,
            "direct local setting overrides a larger global setting");
    Z3_params_dec_ref(C, local);
    Z3_ast args[2] = {bool_var("direct_p"), bool_var("direct_q")};
    Z3_ast conjunction = Z3_mk_and(C, 2, args);
    local = Z3_mk_params(C);
    Z3_params_inc_ref(C, local);
    Z3_params_set_bool(C, local, Z3_mk_string_symbol(C, "elim_and"), true);
    result = Z3_simplify_ex(C, conjunction, local);
    CHECK_B(result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))) == Z3_OP_NOT, 1,
            "direct elim_and performs De Morgan rewriting");
    Z3_params_dec_ref(C, local);
    Z3_global_param_set("rewriter.max_power_expansion", "1");
    Z3_ast nested = Z3_mk_seq_power(C, source, Z3_mk_int(C, 2, Z3_mk_int_sort(C)));
    result = Z3_simplify(C, nested);
    CHECK_B(result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))) == Z3_OP_SEQ_POWER, 1,
            "nested powers normalize while the small cap retains a power");
    if (result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))) == Z3_OP_SEQ_POWER) {
        Z3_app app = Z3_to_app(C, result);
        int count = 0;
        CHECK_B(Z3_get_numeral_int(C, Z3_get_app_arg(C, app, 1), &count) && count == 6, 1,
                "nested normalization multiplies exponents before expansion");
        Z3_ast word = Z3_get_app_arg(C, app, 0);
        CHECK_B(Z3_is_string(C, word) && strcmp(Z3_get_string(C, word), "ab") == 0, 1,
                "nested normalization keeps the original word");
    }
    local = Z3_mk_params(C);
    Z3_params_inc_ref(C, local);
    Z3_params_set_uint(C, local, Z3_mk_string_symbol(C, "max_power_expansion"), 8);
    result = Z3_simplify_ex(C, nested, local);
    CHECK_B(result != 0 && Z3_is_string(C, result) && strcmp(Z3_get_string(C, result), "abababababab") == 0, 1,
            "a raised local cap recursively materializes the nested word");
    Z3_params_dec_ref(C, local);
    Z3_ast symbolic_count = Z3_mk_const(C, Z3_mk_string_symbol(C, "direct_count_n"), Z3_mk_int_sort(C));
    Z3_ast symbolic_inner = Z3_mk_seq_power(C, source, symbolic_count);
    Z3_ast symbolic_outer = Z3_mk_seq_power(C, symbolic_inner, Z3_mk_int(C, 2, Z3_mk_int_sort(C)));
    result = Z3_simplify(C, symbolic_outer);
    CHECK_B(result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))) == Z3_OP_SEQ_POWER, 1,
            "deep symbolic repetition retains the bounded power normal form");
    if (result != 0 && Z3_get_decl_kind(C, Z3_get_app_decl(C, Z3_to_app(C, result))) == Z3_OP_SEQ_POWER) {
        Z3_ast exponent = Z3_get_app_arg(C, Z3_to_app(C, result), 1);
        Z3_app product = Z3_to_app(C, exponent);
        bool binary_product = Z3_get_decl_kind(C, Z3_get_app_decl(C, product)) == Z3_OP_MUL
            && Z3_get_app_num_args(C, product) == 2;
        CHECK_B(binary_product, 1, "deep symbolic exponent has one flat binary product");
        if (binary_product) {
            int coefficient = 0;
            CHECK_B(Z3_get_numeral_int(C, Z3_get_app_arg(C, product, 0), &coefficient) && coefficient == 6, 1,
                    "deep symbolic exponent combines the coefficient to six");
            CHECK_B(Z3_is_eq_ast(C, Z3_get_app_arg(C, product, 1), symbolic_count), 1,
                    "deep symbolic exponent preserves the exact authored integer leaf");
        }
    }
    Z3_global_param_set("rewriter.max_power_expansion", "2");
}

/* Current pinned 5.3.3 addition: inspect a real model of the transformed
 * subgoal through its converter. Either retained definitions (AY) or genuine
 * elimination reconstruction (Z3) must satisfy BOTH original equations. */
static void field_tactic_model(const char *tactic_name, bool models) {
    Z3_sort f = Z3_mk_finite_field_sort(C, "7");
    Z3_ast x = Z3_mk_const(C, Z3_mk_string_symbol(C, "field_x"), f);
    Z3_ast y = Z3_mk_const(C, Z3_mk_string_symbol(C, "field_y"), f);
    Z3_ast three = Z3_mk_numeral(C, "3", f);
    Z3_ast two = Z3_mk_numeral(C, "2", f);
    Z3_ast args[2] = {x, y};
    Z3_ast original[2] = {Z3_mk_eq(C, x, three),
        Z3_mk_eq(C, Z3_mk_ff_add(C, 2, args), two)};
    Z3_goal g = Z3_mk_goal(C, models, false, false);
    Z3_goal_inc_ref(C, g);
    Z3_goal_assert(C, g, original[0]);
    Z3_goal_assert(C, g, original[1]);
    if (!models) {
        Z3_goal copy = Z3_goal_translate(C, g, C);
        CHECK_B(copy != NULL, 1, "model-generation policy survives goal copy");
        if (copy != NULL) {
            Z3_goal_inc_ref(C, copy);
            Z3_goal_dec_ref(C, g);
            g = copy;
        }
    }
    Z3_tactic t = T(Z3_mk_tactic(C, tactic_name));
    Z3_apply_result r = Z3_tactic_apply(C, t, g);
    CHECK_B(r != NULL, 1, "field tactic applies");
    if (r != NULL) {
        Z3_apply_result_inc_ref(C, r);
        CHECK_U(Z3_apply_result_get_num_subgoals(C, r), 1, "field single subgoal");
        Z3_goal h = Z3_apply_result_get_subgoal(C, r, 0);
        /* The API returns a separate temporary goal wrapper. Creating the
         * solver below replaces that temporary even while r stays retained. */
        Z3_goal_inc_ref(C, h);
        Z3_solver s = Z3_mk_solver(C);
        Z3_solver_inc_ref(C, s);
        for (unsigned k = 0; k < Z3_goal_size(C, h); ++k)
            Z3_solver_assert(C, s, Z3_goal_formula(C, h, k));
        CHECK_U(Z3_solver_check(C, s), Z3_L_TRUE, "transformed field goal SAT");
        Z3_model m = Z3_solver_get_model(C, s);
        Z3_model_inc_ref(C, m);
        /* With models disabled upstream attaches no converter. An empty
         * caller model must copy without inventing the required field witness. */
        Z3_model input = models ? m : Z3_mk_model(C);
        if (!models) Z3_model_inc_ref(C, input);
        Z3_model converted = Z3_goal_convert_model(C, h, input);
        CHECK_B(converted != NULL, 1, "field model converts");
        if (converted != NULL) {
            Z3_model_inc_ref(C, converted);
            if (!models)
                CHECK_U(Z3_model_get_num_consts(C, converted), 0,
                        "models-disabled goal preserves empty interpretations");
            for (unsigned k = 0; models && k < 2; ++k) {
                Z3_ast value = 0;
                CHECK_B(Z3_model_eval(C, converted, original[k], true, &value), 1,
                        "original field formula evaluates");
                Z3_lbool verdict = Z3_get_bool_value(C, value);
                if (verdict != Z3_L_TRUE)
                    printf("field conversion failure: tactic=%s root=%u model=%s\n",
                           tactic_name, k, Z3_model_to_string(C, converted));
                CHECK_U(verdict, Z3_L_TRUE,
                        "converted model satisfies original field formula");
            }
            Z3_model_dec_ref(C, converted);
        }
        if (!models) Z3_model_dec_ref(C, input);
        Z3_model_dec_ref(C, m);
        Z3_solver_dec_ref(C, s);
        Z3_goal_dec_ref(C, h);
        Z3_apply_result_dec_ref(C, r);
    }
    Z3_tactic_dec_ref(C, t);
    Z3_goal_dec_ref(C, g);
}

/* These are semantic parameter controls, not catalog/count ceremonies. The
 * same source is run against the authenticated pinned 5.3.3 reference. */
static int has_and(Z3_ast a) {
    if (Z3_get_ast_kind(C, a) != Z3_APP_AST) return 0;
    Z3_app app = Z3_to_app(C, a);
    if (Z3_get_decl_kind(C, Z3_get_app_decl(C, app)) == Z3_OP_AND) return 1;
    for (unsigned i = 0; i < Z3_get_app_num_args(C, app); ++i)
        if (has_and(Z3_get_app_arg(C, app, i))) return 1;
    return 0;
}

static void tactic_parameter_behavior(void) {
    Z3_ast p = bool_var("parameter_p");
    Z3_ast q = bool_var("parameter_q");
    Z3_ast r = bool_var("parameter_r");
    Z3_ast pair[2] = {p, q};
    Z3_ast disjuncts[2] = {Z3_mk_and(C, 2, pair), r};
    Z3_ast original = Z3_mk_or(C, 2, disjuncts);
    Z3_goal goal = Z3_mk_goal(C, true, false, false);
    Z3_goal_inc_ref(C, goal);
    Z3_goal_assert(C, goal, original);
    Z3_tactic simplify = T(Z3_mk_tactic(C, "simplify"));
    Z3_params options = Z3_mk_params(C);
    Z3_params_inc_ref(C, options);
    Z3_symbol elim = Z3_mk_string_symbol(C, "elim_and");
    Z3_symbol steps = Z3_mk_string_symbol(C, "max_steps");
    Z3_params_set_bool(C, options, elim, true);
    Z3_tactic configured = T(Z3_tactic_using_params(C, simplify, options));
    /* Later mutations of the params OBJECT do not change its stored snapshot. */
    Z3_params_set_bool(C, options, elim, false);
    Z3_apply_result applied = Z3_tactic_apply_ex(C, configured, goal, options);
    CHECK_B(applied != NULL, 1, "stored elim_and overrides later update");
    if (applied != NULL) {
        Z3_apply_result_inc_ref(C, applied);
        Z3_goal out = Z3_apply_result_get_subgoal(C, applied, 0);
        Z3_ast rewritten = Z3_goal_formula(C, out, 0);
        CHECK_B(has_and(original), 1, "input really contains conjunction");
        CHECK_B(has_and(rewritten), 0, "elim_and really rewrites conjunction");
        Z3_solver solver = Z3_mk_solver(C);
        Z3_solver_inc_ref(C, solver);
        Z3_solver_assert(C, solver, Z3_mk_not(C, Z3_mk_eq(C, original, rewritten)));
        CHECK_U(Z3_solver_check(C, solver), Z3_L_FALSE,
                "rewritten formula has exactly the original models");
        Z3_solver_dec_ref(C, solver);
        Z3_apply_result_dec_ref(C, applied);
    }
    Z3_params zero = Z3_mk_params(C);
    Z3_params_inc_ref(C, zero);
    Z3_params_set_uint(C, zero, steps, 0);
    applied = Z3_tactic_apply_ex(C, simplify, goal, zero);
    CHECK_B(applied == NULL, 1, "zero rewrite budget is enforced");
    CHECK_B(Z3_get_error_code(C) != Z3_OK, 1, "budget refusal is an error");
    expect_fail(simplify, goal, "apply_ex settings persist on shared tactic");
    Z3_tactic fallback = T(Z3_tactic_or_else(C, simplify, T(Z3_tactic_skip(C))));
    applied = Z3_tactic_apply(C, fallback, goal);
    CHECK_B(applied != NULL, 1, "local budget refusal permits healthy original fallback");
    if (applied != NULL) {
        Z3_apply_result_inc_ref(C, applied);
        CHECK_B(Z3_is_eq_ast(C, original, Z3_goal_formula(C,
            Z3_apply_result_get_subgoal(C, applied, 0), 0)), 1,
            "fallback preserves the original unrewritten goal");
        Z3_apply_result_dec_ref(C, applied);
    }
    Z3_params unbounded = Z3_mk_params(C);
    Z3_params_inc_ref(C, unbounded);
    Z3_params_set_uint(C, unbounded, steps, UINT_MAX);
    Z3_tactic restored = T(Z3_tactic_using_params(C, simplify, unbounded));
    applied = Z3_tactic_apply_ex(C, restored, goal, zero);
    CHECK_B(applied != NULL, 1, "stored max_steps overrides outer zero budget");
    if (applied != NULL) {
        Z3_apply_result_inc_ref(C, applied);
        Z3_apply_result_dec_ref(C, applied);
    }
    expect_ok(simplify, goal, 1, 1, "shared underlying update remains observable");
    Z3_params memory = Z3_mk_params(C);
    Z3_params_inc_ref(C, memory);
    Z3_params_set_uint(C, memory, Z3_mk_string_symbol(C, "max_memory"), 0);
    Z3_tactic memory_tactic = T(Z3_tactic_using_params(C,
        T(Z3_mk_tactic(C, "simplify")), memory));
    expect_fail(memory_tactic, goal, "zero memory checkpoint is enforced");
    Z3_params wrong = Z3_mk_params(C);
    Z3_params_inc_ref(C, wrong);
    Z3_params_set_symbol(C, wrong, elim, Z3_mk_string_symbol(C, "true"));
    CHECK_B(Z3_tactic_using_params(C, simplify, wrong) == NULL, 1,
            "symbol true cannot impersonate Boolean parameter");
    Z3_params_set_bool(C, wrong, elim, true);
    Z3_tactic corrected = Z3_tactic_using_params(C, simplify, wrong);
    CHECK_B(corrected != NULL, 1, "last typed setter replaces old invalid value");
    if (corrected != NULL) Z3_tactic_inc_ref(C, corrected);
    CHECK_B(Z3_tactic_using_params(C, T(Z3_mk_tactic(C, "ff2bv")), zero) == NULL, 1,
            "unsupported primitive parameter is not ignored");
    expect_ok(T(Z3_tactic_try_for(C, T(Z3_tactic_skip(C)), 0)), goal, 1, 1,
              "zero timer disables only its own deadline");
    expect_ok(T(Z3_tactic_try_for(C, T(Z3_tactic_skip(C)), UINT_MAX)), goal, 1, 1,
              "UINT_MAX timer is disabled");
#ifndef AY_TWIN_USE_Z3
    Z3_tactic alias = T(Z3_tactic_with(C, simplify, unbounded));
    expect_ok(alias, goal, 1, 1, "with alias retains genuine parameter behavior");
#endif
    Z3_param_descrs descriptions = Z3_tactic_get_param_descrs(C, simplify);
    CHECK_B(descriptions != NULL, 1, "actual simplifier descriptors available");
    if (descriptions != NULL) {
        Z3_param_descrs_inc_ref(C, descriptions);
        CHECK_U(Z3_param_descrs_get_kind(C, descriptions, elim), Z3_PK_BOOL,
                "elim_and has Boolean descriptor");
        CHECK_U(Z3_param_descrs_get_kind(C, descriptions, steps), Z3_PK_UINT,
                "max_steps has unsigned descriptor");
        Z3_param_descrs_dec_ref(C, descriptions);
    }
    Z3_params_dec_ref(C, wrong);
    Z3_params_dec_ref(C, memory);
    Z3_params_dec_ref(C, unbounded);
    Z3_params_dec_ref(C, zero);
    Z3_params_dec_ref(C, options);
    Z3_goal_dec_ref(C, goal);
}

int main(void) {
    setbuf(stdout, NULL);
#ifdef AY_TWIN_USE_Z3
    /* z3_api.h documents that compaction can erase intermediary variables
     * required by Z3_goal_convert_model. Keep those actual converter inputs. */
    Z3_global_param_set("model.compact", "false");
    Z3_global_param_set("memory_max_size", "256");
#endif
    Z3_config cfg = Z3_mk_config();
    C = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_set_error_handler(C, err_handler);
    direct_simplifier_parameters();
    polynomial_parameters();
    sequence_power_parameters();
    field_tactic_model("ff-simplify", true);
    field_tactic_model("ff2bv", true);
    field_tactic_model("ff2bv", false);
    tactic_parameter_behavior();
    Z3_sort I = Z3_mk_int_sort(C);

    // ---- Goals ----
    // g: QF_LIA, size 1, UNDECIDED — {(< 0 x)}.
    Z3_ast x = int_var("x");
    Z3_goal g = Z3_mk_goal(C, false, false, false);
    Z3_goal_inc_ref(C, g);
    Z3_goal_assert(C, g, Z3_mk_lt(C, Z3_mk_int(C, 0, I), x));
    // ge: empty goal (decided-SAT).
    Z3_goal ge = Z3_mk_goal(C, false, false, false);
    Z3_goal_inc_ref(C, ge);
    // gf: {false} (decided-UNSAT), size 1.
    Z3_goal gf = Z3_mk_goal(C, false, false, false);
    Z3_goal_inc_ref(C, gf);
    Z3_goal_assert(C, gf, Z3_mk_false(C));
    // gor: {(or a b)} — a clause, size 1 (for split-clause).
    Z3_ast a = bool_var("a");
    Z3_ast b = bool_var("b");
    Z3_ast or_args[2] = {a, b};
    Z3_goal gor = Z3_mk_goal(C, false, false, false);
    Z3_goal_inc_ref(C, gor);
    Z3_goal_assert(C, gor, Z3_mk_or(C, 2, or_args));

    // ---- Probes ----
    // is-qflia: TRUE on g (LIA) and on gor (propositional subset).
    // is-qfbv:  FALSE on g (LIA), but TRUE on gor (propositional subset).
    // has-quantifiers: FALSE on both g and gor (a reliable "false" probe on gor).
    Z3_probe qflia = Z3_mk_probe(C, "is-qflia");
    Z3_probe_inc_ref(C, qflia);
    Z3_probe qfbv = Z3_mk_probe(C, "is-qfbv");
    Z3_probe_inc_ref(C, qfbv);
    Z3_probe hasq = Z3_mk_probe(C, "has-quantifiers");
    Z3_probe_inc_ref(C, hasq);

    // ---- Leaf tactics ----
    Z3_tactic skip = T(Z3_tactic_skip(C));
    Z3_tactic fail = T(Z3_tactic_fail(C));
    Z3_tactic sc = T(Z3_mk_tactic(C, "split-clause"));

    // ---- skip / fail primitives ----
    expect_ok(skip, g, 1, 1, "skip=identity on g");
    expect_fail(fail, g, "fail always fails on g");

    // ---- fail_if(p): fails iff p HOLDS (libz3's real behavior) ----
    expect_fail(T(Z3_tactic_fail_if(C, qflia)), g, "fail_if(is-qflia=true) fails");
    expect_ok(T(Z3_tactic_fail_if(C, qfbv)), g, 1, 1, "fail_if(is-qfbv=false)=skip");

    // ---- fail_if_not_decided: identity only on a trivially decided goal ----
    expect_fail(T(Z3_tactic_fail_if_not_decided(C)), g, "fifnd fails on undecided g");
    expect_ok(T(Z3_tactic_fail_if_not_decided(C)), ge, 1, 0, "fifnd=identity on empty");
    expect_ok(T(Z3_tactic_fail_if_not_decided(C)), gf, 1, 1, "fifnd=identity on false");

    // ---- when(p, t): applies t iff p holds, else skip ----
    expect_ok(T(Z3_tactic_when(C, qflia, skip)), g, 1, 1, "when(true, skip)=skip");
    expect_ok(T(Z3_tactic_when(C, qfbv, fail)), g, 1, 1, "when(false, fail)=skip");
    // when(true, split-clause) on gor -> split runs (2 subgoals).
    expect_ok(T(Z3_tactic_when(C, qflia, sc)), gor, 2, 1, "when(true, split-clause) runs");

    // ---- cond(p, t1, t2): picks the branch; a chosen-branch failure PROPAGATES ----
    expect_ok(T(Z3_tactic_cond(C, qflia, skip, fail)), g, 1, 1, "cond(true, skip, fail)=skip");
    expect_fail(T(Z3_tactic_cond(C, qfbv, skip, fail)), g, "cond(false, skip, fail)=fail");
    // cond(true, split-clause, skip) on gor -> t1 (split) runs => 2 subgoals.
    expect_ok(T(Z3_tactic_cond(C, qflia, sc, skip)), gor, 2, 1, "cond(true, split, skip)");
    // cond(false, skip, split-clause) on gor -> t2 (split) runs => 2 subgoals.
    // has-quantifiers is FALSE on the quantifier-free clause goal gor.
    expect_ok(T(Z3_tactic_cond(C, hasq, skip, sc)), gor, 2, 1, "cond(false, skip, split)");

    // ---- try_for(t, ms): genuine timer, generous bound for these cases ----
    expect_ok(T(Z3_tactic_try_for(C, skip, 5000)), g, 1, 1, "try_for(skip, 5000)=skip");
    expect_ok(T(Z3_tactic_try_for(C, sc, 5000)), gor, 2, 1, "try_for(split-clause, 5000) runs");

    // ---- par_and_then(t1, t2): t1 then t2 on every subgoal (sequential in ay) ----
    expect_ok(T(Z3_tactic_par_and_then(C, skip, skip)), g, 1, 1, "par_and_then(skip, skip)");
    // split-clause makes 2 subgoals; skip on each keeps 2 subgoals of size 1.
    expect_ok(T(Z3_tactic_par_and_then(C, sc, skip)), gor, 2, 1, "par_and_then(split, skip)");

    // ---- and_then composition also runs the second on each subgoal ----
    expect_ok(T(Z3_tactic_and_then(C, sc, skip)), gor, 2, 1, "and_then(split, skip)");

    // ---- par_or(n, ts): first success wins (or-else fold in ay) ----
    {
        Z3_tactic ts1[2] = {fail, skip};
        expect_ok(T(Z3_tactic_par_or(C, 2, ts1)), g, 1, 1, "par_or(fail, skip)=skip");
        Z3_tactic ts2[2] = {skip, fail};
        expect_ok(T(Z3_tactic_par_or(C, 2, ts2)), g, 1, 1, "par_or(skip, fail)=skip");
        Z3_tactic ts3[2] = {fail, fail};
        expect_fail(T(Z3_tactic_par_or(C, 2, ts3)), g, "par_or(fail, fail)=fail");
    }

    // ---- Empty apply_ex settings preserve the ordinary tactic behavior ----
    {
        Z3_params pr = Z3_mk_params(C);
        Z3_params_inc_ref(C, pr);
        Z3_apply_result r = Z3_tactic_apply_ex(C, sc, gor, pr);
        CHECK_B(r != NULL, 1, "apply_ex(split-clause) non-null");
        if (r != NULL) {
            Z3_apply_result_inc_ref(C, r);
            CHECK_U(Z3_apply_result_get_num_subgoals(C, r), 2, "apply_ex num_subgoals");
            CHECK_U(Z3_goal_size(C, Z3_apply_result_get_subgoal(C, r, 0)), 1,
                    "apply_ex subgoal0 size");
            Z3_apply_result_dec_ref(C, r);
        }
        // apply_ex on fail is an honest failure too.
        Z3_apply_result rf = Z3_tactic_apply_ex(C, fail, g, pr);
        CHECK_B(rf == NULL, 1, "apply_ex(fail) is NULL");
        Z3_params_dec_ref(C, pr);
    }

    // ---- Z3_tactic_get_descr: a real per-name description string ----
    CHECK_B(Z3_tactic_get_descr(C, "skip") != NULL, 1, "descr(skip) non-null");
    CHECK_B(Z3_tactic_get_descr(C, "fail") != NULL, 1, "descr(fail) non-null");
    CHECK_B(Z3_tactic_get_descr(C, "simplify") != NULL, 1, "descr(simplify) non-null");
    CHECK_B(Z3_tactic_get_descr(C, "bit-blast") != NULL, 1, "descr(bit-blast) non-null");
    CHECK_B(Z3_tactic_get_descr(C, "split-clause") != NULL, 1, "descr(split-clause) non-null");
    CHECK_B(Z3_tactic_get_descr(C, "qe-light") != NULL, 1, "descr(qe-light) non-null");

#ifndef AY_TWIN_USE_Z3
    // ---- AY-only honesty checks (libz3 aborts / diverges on these) ----
    // get_descr: `cnf` is not a Z3 5.0.0 tactic and ay no longer accepts it
    // (115efdbb0; tactics_ffi_tests pins the same NULL), so it is an unknown
    // name like any other: an honest NULL + error.
    CHECK_B(Z3_tactic_get_descr(C, "cnf") == NULL, 1, "descr(cnf)=NULL (not a Z3 5 tactic)");
    CHECK_B(Z3_tactic_get_descr(C, "not-a-tactic") == NULL, 1, "descr(unknown)=NULL");
    // get_param_descrs: honest-empty (a REAL size-0 descriptor set, never a fake).
    Z3_param_descrs pd = Z3_tactic_get_param_descrs(C, skip);
    CHECK_B(pd != NULL, 1, "get_param_descrs non-null");
    if (pd != NULL) {
        Z3_param_descrs_inc_ref(C, pd);
        CHECK_U(Z3_param_descrs_size(C, pd), 0, "get_param_descrs honest-empty size 0");
        Z3_param_descrs_dec_ref(C, pd);
    }
    // Null-operand combinators are an honest NULL + Z3_INVALID_ARG (libz3 aborts).
    CHECK_B(Z3_tactic_when(C, qflia, NULL) == NULL, 1, "when(null tactic)=NULL");
    CHECK_B(Z3_tactic_cond(C, qflia, NULL, skip) == NULL, 1, "cond(null t1)=NULL");
    CHECK_B(Z3_tactic_fail_if(C, NULL) == NULL, 1, "fail_if(null probe)=NULL");
    CHECK_B(Z3_tactic_par_and_then(C, skip, NULL) == NULL, 1, "par_and_then(null)=NULL");
    CHECK_B(Z3_tactic_par_or(C, 0, NULL) == NULL, 1, "par_or(0, NULL)=NULL");
    CHECK_B(Z3_tactic_try_for(C, NULL, 100) == NULL, 1, "try_for(null)=NULL");
    CHECK_B(Z3_tactic_get_param_descrs(C, NULL) == NULL, 1, "get_param_descrs(null)=NULL");
#endif

    if (g_fail == 0) {
        printf("All %d tactic-completion C consumer checks passed\n", g_pass);
        return 0;
    }
    printf("%d checks passed, %d FAILED\n", g_pass, g_fail);
    return 1;
}
