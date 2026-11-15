// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C consumer pinning the validity and scope of models published by
// Z3_solver_check (measured through z3py 5.1.0 on 2026-09-30, where AY
// answered sat with x = 1/2 for x^2 = 2, sat with an EMPTY model for
// x * x = 2, sat with xi = 0 for xi = 2^xi, and listed constants asserted
// only in sibling solvers of the same context).
//
// Invariant: a published sat carries a model under which the solver's own
// assertions evaluate to true with model completion; anything else is not
// sat (unknown carries a reason); a solver's model lists exactly the symbols
// of its own goal. Every check holds for libz3 5.1.0 too (`-DAY_TWIN_USE_Z3`):
// z3 publishes the algebraic model sqrt(2) and answers unknown for xi = 2^xi.

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

#define CHECK(cond, what)                                                      \
    do {                                                                       \
        if (cond) {                                                            \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s\n", (what));                                       \
        }                                                                      \
    } while (0)

static Z3_ast named(Z3_context c, const char *n, Z3_sort s) {
    return Z3_mk_const(c, Z3_mk_string_symbol(c, n), s);
}

static int eval_true(Z3_context c, Z3_model m, Z3_ast t) {
    Z3_ast v = NULL;
    return Z3_model_eval(c, m, t, true, &v) && v != NULL &&
           Z3_get_bool_value(c, v) == Z3_L_TRUE;
}

// Check `s`; when it publishes sat, every formula in `holds` must evaluate to
// true in its model; when it answers unknown, the reason must be non-empty.
static Z3_lbool check_valid(Z3_context c, Z3_solver s, const Z3_ast *holds,
                            unsigned n, const char *what) {
    Z3_lbool r = Z3_solver_check(c, s);
    if (r == Z3_L_TRUE) {
        Z3_model m = Z3_solver_get_model(c, s);
        CHECK(m != NULL, what);
        if (m != NULL) {
            Z3_model_inc_ref(c, m);
            for (unsigned i = 0; i < n; i++) {
                if (!eval_true(c, m, holds[i])) {
                    printf("  model: %s\n", Z3_model_to_string(c, m));
                }
                CHECK(eval_true(c, m, holds[i]), what);
            }
            Z3_model_dec_ref(c, m);
        }
    } else if (r == Z3_L_UNDEF) {
        const char *reason = Z3_solver_get_reason_unknown(c, s);
        CHECK(reason != NULL && reason[0] != '\0', what);
    }
    return r;
}

static int model_has_only(Z3_context c, Z3_solver s, const char *a,
                          const char *b) {
    Z3_model m = Z3_solver_get_model(c, s);
    if (m == NULL) {
        return 0;
    }
    unsigned want = b == NULL ? 1 : 2;
    unsigned n = Z3_model_get_num_consts(c, m);
    int ok = n == want;
    for (unsigned i = 0; ok && i < n; i++) {
        Z3_func_decl d = Z3_model_get_const_decl(c, m, i);
        const char *name = Z3_get_symbol_string(c, Z3_get_decl_name(c, d));
        ok = strcmp(name, a) == 0 || (b != NULL && strcmp(name, b) == 0);
    }
    return ok;
}

int main(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_sort real = Z3_mk_real_sort(c);
    Z3_sort int_s = Z3_mk_int_sort(c);

    Z3_ast x = named(c, "x", real);
    Z3_ast two = Z3_mk_real(c, 2, 1);
    Z3_ast zero = Z3_mk_real(c, 0, 1);
    Z3_ast xx_args[2] = {x, x};
    Z3_ast xx_eq_2 = Z3_mk_eq(c, Z3_mk_mul(c, 2, xx_args), two);
    Z3_ast x_pos = Z3_mk_gt(c, x, zero);

    // 1. x^2 = 2, x > 0 (z3py `x**2 == 2`): sqrt(2) or not sat.
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(c, s, Z3_mk_eq(c, Z3_mk_power(c, x, two), two));
        Z3_solver_assert(c, s, x_pos);
        Z3_ast holds[2] = {xx_eq_2, x_pos};
        Z3_lbool r = check_valid(c, s, holds, 2, "power sqrt2 model valid");
        CHECK(r != Z3_L_FALSE, "power sqrt2 not unsat");
        Z3_solver_dec_ref(c, s);
    }

    // 2. x * x = 2, x > 0: the same, via the product.
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(c, s, xx_eq_2);
        Z3_solver_assert(c, s, x_pos);
        Z3_ast holds[2] = {xx_eq_2, x_pos};
        Z3_lbool r = check_valid(c, s, holds, 2, "product sqrt2 model valid");
        CHECK(r != Z3_L_FALSE, "product sqrt2 not unsat");
        Z3_solver_dec_ref(c, s);
    }

    // 3. x^2 = 4, x > 0: decided exactly, x = 2.
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(
            c, s, Z3_mk_eq(c, Z3_mk_power(c, x, two), Z3_mk_real(c, 4, 1)));
        Z3_solver_assert(c, s, x_pos);
        Z3_ast holds[1] = {Z3_mk_eq(c, x, two)};
        CHECK(check_valid(c, s, holds, 1, "x^2 = 4 model is x = 2") == Z3_L_TRUE,
              "x^2 = 4 sat");
        Z3_solver_dec_ref(c, s);
    }

    // 4. xi = 2^xi over Int (z3py `SimpleSolver().add(xi == 2**xi)`, the
    //    power being Real-sorted): z3 answers unknown; it must never be sat
    //    with an invalid model.
    Z3_ast xi = named(c, "xi", int_s);
    {
        Z3_solver s = Z3_mk_simple_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(
            c, s,
            Z3_mk_eq(c, Z3_mk_int2real(c, xi),
                     Z3_mk_power(c, Z3_mk_int(c, 2, int_s), xi)));
        CHECK(check_valid(c, s, NULL, 0, "xi = 2^xi") == Z3_L_UNDEF,
              "xi = 2^xi is unknown");
        Z3_solver_dec_ref(c, s);
    }

    // 5. Model scope: each solver lists only its own goal's symbols.
    {
        Z3_ast p = named(c, "p", Z3_mk_bool_sort(c));
        Z3_solver s1 = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s1);
        Z3_solver_assert(c, s1, p);
        Z3_solver s2 = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s2);
        Z3_solver_assert(c, s2, Z3_mk_gt(c, xi, Z3_mk_int(c, 3, int_s)));

        CHECK(Z3_solver_check(c, s1) == Z3_L_TRUE, "s1 sat");
        CHECK(model_has_only(c, s1, "p", NULL), "s1 model lists only p");
        CHECK(Z3_solver_check(c, s2) == Z3_L_TRUE, "s2 sat");
        CHECK(model_has_only(c, s2, "xi", NULL), "s2 model lists only xi");

        Z3_ast q = named(c, "q", Z3_mk_bool_sort(c));
        CHECK(Z3_solver_check_assumptions(c, s2, 1, &q) == Z3_L_TRUE,
              "s2 sat under q");
        CHECK(model_has_only(c, s2, "xi", "q"), "s2 model lists xi and q");

        Z3_solver_push(c, s2);
        Z3_solver_assert(c, s2, Z3_mk_lt(c, xi, Z3_mk_int(c, 0, int_s)));
        CHECK(Z3_solver_check(c, s2) == Z3_L_FALSE, "s2 pushed unsat");
        Z3_solver_pop(c, s2, 1);
        CHECK(Z3_solver_check(c, s2) == Z3_L_TRUE, "s2 popped sat");
        CHECK(model_has_only(c, s2, "xi", NULL), "s2 popped model lists xi");

        Z3_solver_dec_ref(c, s2);
        Z3_solver_dec_ref(c, s1);
    }

    // 6. Z3 types `^` as Real even over Int operands, so `a^2 / 2` is real
    //    division: a = 3, a^2 / 2 = 4 is unsat (9/2 != 4). An Int-sorted
    //    power made it integer `div` and answered sat.
    {
        Z3_ast a = named(c, "a", int_s);
        Z3_ast sq = Z3_mk_power(c, a, Z3_mk_int(c, 2, int_s));
        CHECK(Z3_get_sort_kind(c, Z3_get_sort(c, sq)) == Z3_REAL_SORT,
              "Int ^ Int has sort Real");
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(c, s, Z3_mk_eq(c, a, Z3_mk_int(c, 3, int_s)));
        Z3_solver_assert(
            c, s,
            Z3_mk_eq(c, Z3_mk_div(c, sq, Z3_mk_real(c, 2, 1)), Z3_mk_real(c, 4, 1)));
        CHECK(Z3_solver_check(c, s) != Z3_L_TRUE, "a = 3, a^2 / 2 = 4 is not sat");
        Z3_solver_dec_ref(c, s);
    }

    // 7. Function tables keep rows and values at negative Int points
    //    (they were dropped: f(-1) = 5, f(2) = 6 published f = [else -> 6]).
    {
        Z3_sort dom[1] = {int_s};
        Z3_func_decl f = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "f"), 1, dom, int_s);
        Z3_func_decl pr = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "pr"), 1, dom,
                                          Z3_mk_bool_sort(c));
        Z3_ast m1[1] = {Z3_mk_int(c, -1, int_s)};
        Z3_ast p2[1] = {Z3_mk_int(c, 2, int_s)};
        Z3_ast p5[1] = {Z3_mk_int(c, 5, int_s)};
        Z3_ast p1[1] = {Z3_mk_int(c, 1, int_s)};
        Z3_ast holds[4] = {
            Z3_mk_eq(c, Z3_mk_app(c, f, 1, m1), Z3_mk_int(c, 5, int_s)),
            Z3_mk_eq(c, Z3_mk_app(c, f, 1, p2), Z3_mk_int(c, 6, int_s)),
            Z3_mk_app(c, pr, 1, m1),
            Z3_mk_not(c, Z3_mk_app(c, pr, 1, p5)),
        };
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        for (unsigned i = 0; i < 4; i++) {
            Z3_solver_assert(c, s, holds[i]);
        }
        CHECK(check_valid(c, s, holds, 4, "negative-point rows kept") == Z3_L_TRUE,
              "negative-point rows sat");
        Z3_solver_dec_ref(c, s);

        Z3_ast neg[1] = {Z3_mk_eq(c, Z3_mk_app(c, f, 1, p1), Z3_mk_int(c, -1, int_s))};
        s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(c, s, neg[0]);
        CHECK(check_valid(c, s, neg, 1, "negative else kept") == Z3_L_TRUE,
              "negative else sat");
        Z3_solver_dec_ref(c, s);
    }

    // 8. A bit-vector-ranged function reaches the model (it was missing).
    {
        Z3_sort bv8 = Z3_mk_bv_sort(c, 8);
        Z3_sort dom[1] = {bv8};
        Z3_func_decl bf = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "bf"), 1, dom, bv8);
        Z3_ast zero8 = Z3_mk_int(c, 0, bv8);
        Z3_ast args[1] = {zero8};
        Z3_ast holds[1] = {Z3_mk_bvult(c, zero8, Z3_mk_app(c, bf, 1, args))};
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(c, s, holds[0]);
        CHECK(check_valid(c, s, holds, 1, "bv-ranged table kept") == Z3_L_TRUE,
              "bv-ranged table sat");
        Z3_model m = Z3_solver_get_model(c, s);
        CHECK(m != NULL && Z3_model_get_num_funcs(c, m) == 1, "bf is in the model");
        CHECK(m != NULL && Z3_model_has_interp(c, m, bf), "bf has an interpretation");
        Z3_solver_dec_ref(c, s);
    }

    // 9. Building a Real-ranged UF application elsewhere in the context, and
    //    evaluating a model, never empties another check's published model.
    {
        Z3_sort dom[1] = {int_s};
        Z3_func_decl h = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "h"), 1, dom, real);
        Z3_ast b = named(c, "b", int_s);
        Z3_ast bargs[1] = {b};
        (void)Z3_mk_app(c, h, 1, bargs); // built, never asserted
        Z3_sort arr_s = Z3_mk_array_sort(c, int_s, int_s);
        Z3_ast arr = named(c, "A", arr_s);
        Z3_ast holds[2] = {
            Z3_mk_eq(c, Z3_mk_select(c, arr, b), Z3_mk_int(c, 7, int_s)),
            Z3_mk_eq(c, b, Z3_mk_int(c, 2, int_s)),
        };
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(c, s, holds[0]);
        Z3_solver_assert(c, s, holds[1]);
        CHECK(check_valid(c, s, holds, 2, "array model next to a Real UF") ==
                  Z3_L_TRUE,
              "array model next to a Real UF sat");
        Z3_model m = Z3_solver_get_model(c, s);
        if (m != NULL) {
            Z3_ast v = NULL;
            (void)Z3_model_eval(c, m, holds[0], true, &v);
        }
        CHECK(check_valid(c, s, holds, 2, "re-check after eval") == Z3_L_TRUE,
              "re-check after eval sat");
        Z3_solver_dec_ref(c, s);
    }

    // 10. A quantifier's bound variable is not a model constant.
    {
        Z3_ast q0 = named(c, "q0", int_s);
        Z3_app bound[1] = {Z3_to_app(c, q0)};
        Z3_ast body = Z3_mk_lt(c, q0, Z3_mk_int(c, 0, int_s));
        Z3_solver s = Z3_mk_simple_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(c, s, Z3_mk_exists_const(c, 0, 1, bound, 0, NULL, body));
        CHECK(Z3_solver_check(c, s) == Z3_L_TRUE, "exists q0 < 0 sat");
        Z3_model m = Z3_solver_get_model(c, s);
        CHECK(m != NULL && Z3_model_get_num_consts(c, m) == 0,
              "bound q0 is not listed in the model");
        Z3_solver_dec_ref(c, s);
    }

    // 11. Z3_mk_numeral reads decimals (z3py passes every float this way).
    {
        Z3_ast d = Z3_mk_numeral(c, "2.5", real);
        CHECK(d != NULL && strcmp(Z3_get_numeral_string(c, d), "5/2") == 0,
              "2.5 is the numeral 5/2");
        Z3_ast e = Z3_mk_numeral(c, "1e2", real);
        CHECK(e != NULL && strcmp(Z3_get_numeral_string(c, e), "100") == 0,
              "1e2 is the numeral 100");
    }

    // 12. The model evaluator folds a ground power: 2^3 = 8.
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        CHECK(Z3_solver_check(c, s) == Z3_L_TRUE, "empty goal sat");
        Z3_model m = Z3_solver_get_model(c, s);
        Z3_ast v = NULL;
        Z3_ast eight = Z3_mk_power(c, Z3_mk_int(c, 2, int_s), Z3_mk_int(c, 3, int_s));
        CHECK(m != NULL && Z3_model_eval(c, m, Z3_mk_eq(c, eight, Z3_mk_real(c, 8, 1)),
                                         true, &v) &&
                  Z3_get_bool_value(c, v) == Z3_L_TRUE,
              "2^3 evaluates to 8");
        Z3_solver_dec_ref(c, s);
    }

    // 13. A mixed Int/Real conjunction is sat with a valid model (z3: sat; AY
    //     answered unknown when its own model gate refused the model it built).
    {
        Z3_ast ia = named(c, "ia", int_s);
        Z3_ast ib = named(c, "ib", int_s);
        Z3_ast rx = named(c, "rx", real);
        Z3_ast ry = named(c, "ry", real);
        Z3_ast bp = named(c, "bp", Z3_mk_bool_sort(c));
        Z3_ast parts[3] = {Z3_mk_lt(c, ib, ia), Z3_mk_eq(c, ry, rx), bp};
        Z3_ast holds[1] = {Z3_mk_and(c, 3, parts)};
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(c, s, holds[0]);
        CHECK(check_valid(c, s, holds, 1, "mixed Int/Real conjunction") == Z3_L_TRUE,
              "mixed Int/Real conjunction is sat");
        Z3_solver_dec_ref(c, s);
    }

    // 14. Solver and Optimize share a context, as in z3py's default context
    //     (Z3_mk_optimize used to fail once a Solver existed).
    {
        Z3_ast ox = named(c, "ox", int_s);
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(c, s, Z3_mk_gt(c, ox, Z3_mk_int(c, 100, int_s)));
        CHECK(Z3_solver_check(c, s) == Z3_L_TRUE, "solver before optimize sat");
        Z3_optimize o = Z3_mk_optimize(c);
        CHECK(o != NULL, "Z3_mk_optimize next to a Solver");
        if (o != NULL) {
            Z3_optimize_inc_ref(c, o);
            Z3_optimize_assert(c, o, Z3_mk_le(c, ox, Z3_mk_int(c, 7, int_s)));
            unsigned h = Z3_optimize_maximize(c, o, ox);
            CHECK(Z3_optimize_check(c, o, 0, NULL) == Z3_L_TRUE, "optimize sat");
            CHECK(Z3_solver_check(c, s) == Z3_L_TRUE, "solver after optimize sat");
            Z3_ast upper = Z3_optimize_get_upper(c, o, h);
            int v = 0;
            CHECK(upper != NULL && Z3_get_numeral_int(c, upper, &v) && v == 7,
                  "optimum 7 survives a later Solver check");
            Z3_optimize_dec_ref(c, o);
        }
        Z3_solver_dec_ref(c, s);
    }

    Z3_del_context(c);
    printf("%d passed, %d failed\n", g_pass, g_fail);
    if (g_fail != 0) {
        return 1;
    }
    printf("model validity consumer tests passed\n");
    return 0;
}
