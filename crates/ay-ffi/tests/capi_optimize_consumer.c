// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C consumer for the Z3-compatible Optimize completion C API (Z3_optimize_*).
//
// Builds real optimization problems and exercises the new surface:
//   - push / pop backtracking scopes,
//   - get_objectives / get_assertions,
//   - get_upper / get_lower (scalar) and get_upper_as_vector /
//     get_lower_as_vector (the [a,b,c] = a*inf + b + c*eps rep),
//   - assert_and_track + get_unsat_core,
//   - from_string parsing a (maximize) script,
//   - get_statistics / get_reason_unknown,
//   - set_params / get_help / get_param_descrs.
//
// Every expected value is what libz3 returns for the SAME problem, so this ONE
// source compiles and runs against BOTH ay-ffi (default) and libz3
// (-DAY_TWIN_USE_Z3). The shared assertions are the cross-check: ay's observable
// behavior == libz3's on the supported optimize surface. Where the two are
// documented to diverge (objective NORMALIZATION in get_objectives; unsat-core
// MINIMIZATION; the exact param_descrs SET), only structural facts (sizes, the
// optimum numeral, membership) are compared — never a representation z3 and ay
// legitimately differ on.

#ifdef AY_TWIN_USE_Z3
#include <z3.h>
#else
#include "ay.h"
#include "ay_z3_compat.h"
#endif

#include <stdio.h>
#include <string.h>

static int g_pass = 0;
static int g_fail = 0;

#define CHECK_U(actual, expected, what)                                        \
    do {                                                                       \
        long a_ = (long)(actual);                                              \
        long e_ = (long)(expected);                                            \
        if (a_ == e_) {                                                        \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s: got %ld want %ld\n", (what), a_, e_);             \
        }                                                                      \
    } while (0)

#define CHECK_B(cond, what)                                                    \
    do {                                                                       \
        if (cond) {                                                            \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s\n", (what));                                       \
        }                                                                      \
    } while (0)

static Z3_ast int_var(Z3_context c, const char *n) {
    return Z3_mk_const(c, Z3_mk_string_symbol(c, n), Z3_mk_int_sort(c));
}
static Z3_ast bool_var(Z3_context c, const char *n) {
    return Z3_mk_const(c, Z3_mk_string_symbol(c, n), Z3_mk_bool_sort(c));
}

// Read the integer value of a numeral AST (returns a sentinel on failure).
static int numeral(Z3_context c, Z3_ast a) {
    int v = -424242;
    if (a == 0) return -424242;
    if (!Z3_get_numeral_int(c, a, &v)) return -424242;
    return v;
}

// ---------------------------------------------------------------------------
// Scenario 1: maximize x s.t. 0 <= x < 10 (Int).  Optimum = 9.
// Exercises maximize, check, get_upper/get_lower (scalar) and _as_vector,
// get_objectives, get_assertions, then push/pop scoping.
// ---------------------------------------------------------------------------
static void scenario_bounded_maximize(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_optimize o = Z3_mk_optimize(c);
    Z3_optimize_inc_ref(c, o);

    Z3_ast x = int_var(c, "x");
    Z3_ast zero = Z3_mk_int(c, 0, Z3_mk_int_sort(c));
    Z3_ast ten = Z3_mk_int(c, 10, Z3_mk_int_sort(c));
    Z3_ast ge0 = Z3_mk_ge(c, x, zero);
    Z3_ast lt10 = Z3_mk_lt(c, x, ten);
    Z3_optimize_assert(c, o, ge0);
    Z3_optimize_assert(c, o, lt10);

    unsigned obj = Z3_optimize_maximize(c, o, x);
    CHECK_U(obj, 0, "maximize objective index");

    // get_assertions: 2 hard constraints.
    Z3_ast_vector asserts = Z3_optimize_get_assertions(c, o);
    CHECK_U(Z3_ast_vector_size(c, asserts), 2, "get_assertions size");

    // get_objectives: 1 objective.
    Z3_ast_vector objs = Z3_optimize_get_objectives(c, o);
    CHECK_U(Z3_ast_vector_size(c, objs), 1, "get_objectives size");

    int r = Z3_optimize_check(c, o, 0, NULL);
    CHECK_U(r, Z3_L_TRUE, "check bounded maximize == sat");

    // Scalar optimum == 9.
    CHECK_U(numeral(c, Z3_optimize_get_upper(c, o, obj)), 9, "get_upper == 9");
    CHECK_U(numeral(c, Z3_optimize_get_lower(c, o, obj)), 9, "get_lower == 9");

    // Vector optimum: length 3, [a,b,c] = a*inf + b + c*eps = [0, 9, 0].
    Z3_ast_vector uv = Z3_optimize_get_upper_as_vector(c, o, obj);
    CHECK_U(Z3_ast_vector_size(c, uv), 3, "get_upper_as_vector length 3");
    CHECK_U(numeral(c, Z3_ast_vector_get(c, uv, 0)), 0, "upper_as_vector a==0");
    CHECK_U(numeral(c, Z3_ast_vector_get(c, uv, 1)), 9, "upper_as_vector b==9");
    CHECK_U(numeral(c, Z3_ast_vector_get(c, uv, 2)), 0, "upper_as_vector c==0");

    Z3_ast_vector lv = Z3_optimize_get_lower_as_vector(c, o, obj);
    CHECK_U(Z3_ast_vector_size(c, lv), 3, "get_lower_as_vector length 3");
    CHECK_U(numeral(c, Z3_ast_vector_get(c, lv, 1)), 9, "lower_as_vector b==9");

    // statistics + reason-unknown are queryable after a check.
    Z3_stats st = Z3_optimize_get_statistics(c, o);
    CHECK_B(st != NULL, "get_statistics non-null");
    CHECK_B(Z3_stats_to_string(c, st) != NULL, "stats_to_string non-null");
    CHECK_B(Z3_optimize_get_reason_unknown(c, o) != NULL,
            "get_reason_unknown non-null");

    // --- push/pop scoping: add x < 5, optimum becomes 4, pop restores 9. ---
    Z3_optimize_push(c, o);
    Z3_ast five = Z3_mk_int(c, 5, Z3_mk_int_sort(c));
    Z3_optimize_assert(c, o, Z3_mk_lt(c, x, five));
    Z3_ast_vector scoped_asserts = Z3_optimize_get_assertions(c, o);
    CHECK_U(Z3_ast_vector_size(c, scoped_asserts), 3,
            "get_assertions size in scope == 3");
    int r2 = Z3_optimize_check(c, o, 0, NULL);
    CHECK_U(r2, Z3_L_TRUE, "check in scope == sat");
    CHECK_U(numeral(c, Z3_optimize_get_upper(c, o, obj)), 4,
            "scoped optimum == 4");
    Z3_optimize_pop(c, o);
    CHECK_U(Z3_ast_vector_size(c, Z3_optimize_get_assertions(c, o)), 2,
            "get_assertions size after pop == 2");
    int r3 = Z3_optimize_check(c, o, 0, NULL);
    CHECK_U(r3, Z3_L_TRUE, "check after pop == sat");
    CHECK_U(numeral(c, Z3_optimize_get_upper(c, o, obj)), 9,
            "optimum after pop == 9");

    Z3_optimize_dec_ref(c, o);
    Z3_del_context(c);
}

// ---------------------------------------------------------------------------
// Scenario 2: minimize via from_string, then optimize.
//   minimize y s.t. y >= 3, y <= 100  ->  optimum 3.
// ---------------------------------------------------------------------------
static void scenario_from_string(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_optimize o = Z3_mk_optimize(c);
    Z3_optimize_inc_ref(c, o);

    const char *script =
        "(declare-const y Int)\n"
        "(assert (>= y 3))\n"
        "(assert (<= y 100))\n"
        "(minimize y)\n";
    Z3_optimize_from_string(c, o, script);
    CHECK_U(Z3_get_error_code(c), Z3_OK, "from_string no error");

    CHECK_U(Z3_ast_vector_size(c, Z3_optimize_get_objectives(c, o)), 1,
            "from_string objectives size == 1");

    int r = Z3_optimize_check(c, o, 0, NULL);
    CHECK_U(r, Z3_L_TRUE, "from_string check == sat");
    CHECK_U(numeral(c, Z3_optimize_get_lower(c, o, 0)), 3,
            "from_string minimize optimum == 3");

    Z3_optimize_dec_ref(c, o);
    Z3_del_context(c);
}

// ---------------------------------------------------------------------------
// Scenario 3: assert_and_track + get_unsat_core.
//   track (x >= 5) as p1, track (x <= 3) as p2  ->  UNSAT.
// libz3 returns the participating core {p1,p2} (size 2). AY's Optimize engine
// cannot extract a participating-only core (it does not thread check-time
// assumptions), so rather than return an over-approximate full-tracked-set core
// that could include NON-participating literals (a wrong value), AY honestly
// returns an EMPTY core. Documented divergence (see ay_z3_compat.h). The tracked
// constraints are still asserted, so the UNSAT verdict itself is correct.
// ---------------------------------------------------------------------------
static void scenario_unsat_core(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_optimize o = Z3_mk_optimize(c);
    Z3_optimize_inc_ref(c, o);

    Z3_ast x = int_var(c, "x");
    Z3_ast five = Z3_mk_int(c, 5, Z3_mk_int_sort(c));
    Z3_ast three = Z3_mk_int(c, 3, Z3_mk_int_sort(c));
    Z3_ast ge5 = Z3_mk_ge(c, x, five);
    Z3_ast le3 = Z3_mk_le(c, x, three);
    Z3_ast p1 = bool_var(c, "p1");
    Z3_ast p2 = bool_var(c, "p2");
    Z3_optimize_assert_and_track(c, o, ge5, p1);
    Z3_optimize_assert_and_track(c, o, le3, p2);

    int r = Z3_optimize_check(c, o, 0, NULL);
    CHECK_U(r, Z3_L_FALSE, "tracked problem == unsat");

    Z3_ast_vector core = Z3_optimize_get_unsat_core(c, o);
#ifdef AY_TWIN_USE_Z3
    CHECK_U(Z3_ast_vector_size(c, core), 2, "z3: unsat core size == 2");
#else
    // AY honest divergence: participating-only optimize cores are unsupported
    // (no assumption threading) -> empty core, never an over-approximate/wrong one.
    CHECK_U(Z3_ast_vector_size(c, core), 0, "ay: optimize unsat core empty (documented)");
#endif

    Z3_optimize_dec_ref(c, o);
    Z3_del_context(c);
}

// ---------------------------------------------------------------------------
// Scenario 4: soft constraints (weighted partial MaxSMT via assert_soft).
//   hard: a OR b ; soft (a, w1), soft (not a, w1), soft (b, w5).
// Reachable optimum satisfies b and one of {a, !a}: max satisfied weight = 6.
// Just assert the check is SAT and a model is available.
// ---------------------------------------------------------------------------
static void scenario_soft(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_optimize o = Z3_mk_optimize(c);
    Z3_optimize_inc_ref(c, o);

    Z3_ast a = bool_var(c, "a");
    Z3_ast b = bool_var(c, "b");
    Z3_ast args[2] = {a, b};
    Z3_optimize_assert(c, o, Z3_mk_or(c, 2, args));
    Z3_optimize_assert_soft(c, o, a, "1", NULL);
    Z3_optimize_assert_soft(c, o, Z3_mk_not(c, a), "1", NULL);
    Z3_optimize_assert_soft(c, o, b, "5", NULL);

    int r = Z3_optimize_check(c, o, 0, NULL);
    CHECK_U(r, Z3_L_TRUE, "soft problem == sat");
    CHECK_B(Z3_optimize_get_model(c, o) != NULL, "soft model non-null");

    Z3_optimize_dec_ref(c, o);
    Z3_del_context(c);
}

// ---------------------------------------------------------------------------
// Scenario 5: params / help / param_descrs.
// ---------------------------------------------------------------------------
static void scenario_params(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_optimize o = Z3_mk_optimize(c);
    Z3_optimize_inc_ref(c, o);

    Z3_params p = Z3_mk_params(c);
    Z3_params_set_uint(c, p, Z3_mk_string_symbol(c, "timeout"), 5000);
    Z3_optimize_set_params(c, o, p);
    CHECK_U(Z3_get_error_code(c), Z3_OK, "set_params no error");

    CHECK_B(Z3_optimize_get_help(c, o) != NULL, "get_help non-null");

    Z3_param_descrs pd = Z3_optimize_get_param_descrs(c, o);
    CHECK_B(pd != NULL, "get_param_descrs non-null");
    CHECK_B(Z3_param_descrs_size(c, pd) >= 1, "param_descrs size >= 1");
    CHECK_B(Z3_param_descrs_to_string(c, pd) != NULL,
            "param_descrs to_string non-null");

    Z3_optimize_dec_ref(c, o);
    Z3_del_context(c);
}

int main(void) {
    scenario_bounded_maximize();
    scenario_from_string();
    scenario_unsat_core();
    scenario_soft();
    scenario_params();

    printf("pass=%d fail=%d\n", g_pass, g_fail);
    if (g_fail == 0) {
        printf("optimize C consumer checks passed\n");
        return 0;
    }
    return 1;
}
