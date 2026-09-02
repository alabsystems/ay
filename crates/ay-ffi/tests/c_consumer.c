// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Minimal Z3 C API consumer for ay-ffi header compatibility test (#4990).
//
// This program exercises the core Z3 API workflow that external consumers
// (Lean, KLEE, Seahorn) use: create context, declare variables, assert
// constraints, check satisfiability, inspect model. If this compiles and
// links against libay_ffi, the header is compatible.

#include "ay.h"
#include "ay_z3_compat.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

// Core workflow: create, assert, check-sat, model, cleanup
static int test_basic_sat(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Declare integer variable x
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x");
    Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);

    // Assert x > 0
    Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
    Z3_ast x_gt_0 = Z3_mk_gt(ctx, x, zero);

    // Assert x < 10
    Z3_ast ten = Z3_mk_int(ctx, 10, int_sort);
    Z3_ast x_lt_10 = Z3_mk_lt(ctx, x, ten);

    Z3_solver solver = Z3_mk_solver(ctx);

    Z3_solver_assert(ctx, solver, x_gt_0);
    Z3_solver_assert(ctx, solver, x_lt_10);

    int result = Z3_solver_check(ctx, solver);
    assert(result == Z3_L_TRUE);

    // Get model and inspect
    Z3_model model = Z3_solver_get_model(ctx, solver);
    assert(model != NULL);

    unsigned int num_consts = Z3_model_get_num_consts(ctx, model);
    (void)num_consts; // may be 0 or 1 depending on implementation

    Z3_string model_str = Z3_model_to_string(ctx, model);
    assert(model_str != NULL);
    printf("Model: %s\n", model_str);

    Z3_del_context(ctx);
    return 0;
}

// Arithmetic and boolean operations
static int test_arithmetic(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast two = Z3_mk_int(ctx, 2, int_sort);
    Z3_ast three = Z3_mk_int(ctx, 3, int_sort);

    // 2 + 3
    Z3_ast args[2] = { two, three };
    Z3_ast sum = Z3_mk_add(ctx, 2, args);
    assert(sum != 0);

    // 2 * 3
    Z3_ast prod = Z3_mk_mul(ctx, 2, args);
    assert(prod != 0);

    // 2 ^ 3
    Z3_ast power = Z3_mk_power(ctx, two, three);
    assert(power != 0);

    // Numeral inspection
    assert(Z3_is_numeral_ast(ctx, two));

    unsigned int val = 0;
    bool ok = Z3_get_numeral_uint(ctx, two, &val);
    assert(ok);
    assert(val == 2);

    Z3_del_context(ctx);
    return 0;
}

// Sort and symbol inspection
static int test_sorts_and_symbols(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Sorts
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort real_sort = Z3_mk_real_sort(ctx);
    Z3_sort bv8 = Z3_mk_bv_sort(ctx, 8);

    assert(Z3_get_sort_kind(ctx, bool_sort) == Z3_BOOL_SORT);
    assert(Z3_get_sort_kind(ctx, int_sort) == Z3_INT_SORT);
    assert(Z3_get_sort_kind(ctx, real_sort) == Z3_REAL_SORT);
    assert(Z3_get_sort_kind(ctx, bv8) == Z3_BV_SORT);

    assert(Z3_is_eq_sort(ctx, int_sort, Z3_mk_int_sort(ctx)));
    assert(!Z3_is_eq_sort(ctx, int_sort, bool_sort));

    // Symbols
    Z3_symbol str_sym = Z3_mk_string_symbol(ctx, "hello");
    assert(Z3_get_symbol_kind(ctx, str_sym) == Z3_STRING_SYMBOL);

    Z3_symbol int_sym = Z3_mk_int_symbol(ctx, 42);
    assert(Z3_get_symbol_kind(ctx, int_sym) == Z3_INT_SYMBOL);
    assert(Z3_get_symbol_int(ctx, int_sym) == 42);

    Z3_del_context(ctx);
    return 0;
}

// Boolean and bitvector operations
static int test_bv_and_bool(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Boolean
    Z3_ast t = Z3_mk_true(ctx);
    Z3_ast f = Z3_mk_false(ctx);
    assert(Z3_get_bool_value(ctx, t) == Z3_L_TRUE);
    assert(Z3_get_bool_value(ctx, f) == Z3_L_FALSE);

    Z3_ast not_t = Z3_mk_not(ctx, t);
    assert(not_t != 0);

    // Bitvector
    Z3_sort bv8 = Z3_mk_bv_sort(ctx, 8);
    assert(Z3_get_bv_sort_size(ctx, bv8) == 8);

    Z3_symbol a_sym = Z3_mk_string_symbol(ctx, "a");
    Z3_symbol b_sym = Z3_mk_string_symbol(ctx, "b");
    Z3_ast a = Z3_mk_const(ctx, a_sym, bv8);
    Z3_ast b = Z3_mk_const(ctx, b_sym, bv8);

    Z3_ast bvand = Z3_mk_bvand(ctx, a, b);
    Z3_ast bvor = Z3_mk_bvor(ctx, a, b);
    Z3_ast bvxor = Z3_mk_bvxor(ctx, a, b);
    Z3_ast bvadd = Z3_mk_bvadd(ctx, a, b);
    assert(bvand != 0);
    assert(bvor != 0);
    assert(bvxor != 0);
    assert(bvadd != 0);

    Z3_del_context(ctx);
    return 0;
}

// Error handling
static int test_error_handling(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    unsigned int err = Z3_get_error_code(ctx);
    assert(err == Z3_OK);

    Z3_string msg = Z3_get_error_msg(ctx, Z3_OK);
    // msg may be NULL or a string, both acceptable
    (void)msg;

    Z3_del_context(ctx);
    return 0;
}

// Native AY timeout/statistics API
static int test_ay_timeout_statistics(void) {
    AYSolver* solver = ay_solver_new();
    assert(solver != NULL);

    assert(ay_get_timeout(solver) == 0);
    ay_set_timeout(solver, 1000);
    assert(ay_get_timeout(solver) == 1000);
    ay_set_timeout(solver, 0);
    assert(ay_get_timeout(solver) == 0);

    const char* input = "(set-logic QF_UF)(declare-const p Bool)(assert p)(check-sat)";
    int result = ay_solve_smtlib(solver, input);
    assert(result == AY_SAT);

    char* stats = ay_get_statistics(solver);
    assert(stats != NULL);
    assert(strstr(stats, ":conflicts") != NULL);
    assert(strstr(stats, ":decisions") != NULL);
    ay_string_free(stats);

    ay_solver_free(solver);
    return 0;
}

// Reference counting on an RC context (z3py-style discipline).
//
// Bookkeeping only: ASTs are arena-interned and never freed by ref counting.
// Counts detect dec-below-zero (Z3_DEC_REF_ERROR) and an RC context behaves
// differently from a plain Z3_mk_context (where inc/dec_ref are no-ops).
static int test_refcounting(void) {
    // (a) RC context: balanced inc/dec leaves Z3_OK; (b) extra dec -> error.
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context_rc(cfg);
    Z3_del_config(cfg);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x");
    Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);
    assert(x != 0);

    Z3_inc_ref(ctx, x);
    Z3_inc_ref(ctx, x);
    Z3_dec_ref(ctx, x);
    Z3_dec_ref(ctx, x);
    assert(Z3_get_error_code(ctx) == Z3_OK);

    Z3_dec_ref(ctx, x); // dec-below-zero
    assert(Z3_get_error_code(ctx) == Z3_DEC_REF_ERROR);

    Z3_del_context(ctx);

    // (c) NON-rc context: unbalanced dec_ref is a no-op -> Z3_OK.
    Z3_config cfg2 = Z3_mk_config();
    Z3_context ctx2 = Z3_mk_context(cfg2);
    Z3_del_config(cfg2);

    Z3_sort int_sort2 = Z3_mk_int_sort(ctx2);
    Z3_symbol y_sym = Z3_mk_string_symbol(ctx2, "y");
    Z3_ast y = Z3_mk_const(ctx2, y_sym, int_sort2);
    assert(y != 0);

    Z3_inc_ref(ctx2, y);
    Z3_dec_ref(ctx2, y);
    Z3_dec_ref(ctx2, y); // unbalanced, but no-op on a non-RC context
    assert(Z3_get_error_code(ctx2) == Z3_OK);

    Z3_del_context(ctx2);
    return 0;
}

// Optimize (MaxSMT) sub-API: hard + weighted soft constraints (Phase 3).
//
// Hard: (or a b). Soft: ¬a:1, ¬b:1. Optimum is SAT with exactly one soft
// satisfied (exactly one of a,b true). Plus a WEIGHTED case where the
// weight-optimum differs from the count-optimum, to confirm the exact-weight
// engine is reached.
static int test_optimize_maxsat(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "a"), bool_sort);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), bool_sort);

    Z3_optimize opt = Z3_mk_optimize(ctx);
    assert(opt != NULL);
    Z3_optimize_inc_ref(ctx, opt);

    // Hard: (or a b)
    Z3_ast or_args[2] = { a, b };
    Z3_ast a_or_b = Z3_mk_or(ctx, 2, or_args);
    Z3_optimize_assert(ctx, opt, a_or_b);

    // Soft: ¬a:1, ¬b:1
    Z3_ast not_a = Z3_mk_not(ctx, a);
    Z3_ast not_b = Z3_mk_not(ctx, b);
    unsigned i0 = Z3_optimize_assert_soft(ctx, opt, not_a, "1", NULL);
    unsigned i1 = Z3_optimize_assert_soft(ctx, opt, not_b, "1", NULL);
    assert(i0 == 0);
    assert(i1 == 1);
    assert(Z3_get_error_code(ctx) == Z3_OK);

    int res = Z3_optimize_check(ctx, opt, 0, NULL);
    assert(res == Z3_L_TRUE);

    Z3_model model = Z3_optimize_get_model(ctx, opt);
    assert(model != NULL);

    // Verify exactly one of a,b is true at the optimum.
    Z3_ast va_ast = 0, vb_ast = 0;
    bool oka = Z3_model_eval(ctx, model, a, true, &va_ast);
    bool okb = Z3_model_eval(ctx, model, b, true, &vb_ast);
    assert(oka && okb);
    int va = Z3_get_bool_value(ctx, va_ast);
    int vb = Z3_get_bool_value(ctx, vb_ast);
    assert(va == Z3_L_TRUE || vb == Z3_L_TRUE);          // hard (or a b)
    assert((va == Z3_L_TRUE) != (vb == Z3_L_TRUE));      // exactly one soft sat

    Z3_optimize_dec_ref(ctx, opt);
    Z3_del_context(ctx);

    // WEIGHTED case: hard a => (¬b ∧ ¬c); soft a:5, b:1, c:1.
    // Weight-optimum satisfies a (weight 5), gives up b,c (weight 2).
    // A count-first optimizer would wrongly give up a alone (weight 5).
    Z3_config cfg2 = Z3_mk_config();
    Z3_context ctx2 = Z3_mk_context(cfg2);
    Z3_del_config(cfg2);

    Z3_sort bs2 = Z3_mk_bool_sort(ctx2);
    Z3_ast a2 = Z3_mk_const(ctx2, Z3_mk_string_symbol(ctx2, "a"), bs2);
    Z3_ast b2 = Z3_mk_const(ctx2, Z3_mk_string_symbol(ctx2, "b"), bs2);
    Z3_ast c2 = Z3_mk_const(ctx2, Z3_mk_string_symbol(ctx2, "c"), bs2);

    Z3_optimize opt2 = Z3_mk_optimize(ctx2);

    // (or (not a) (and (not b) (not c)))
    Z3_ast na = Z3_mk_not(ctx2, a2);
    Z3_ast nb = Z3_mk_not(ctx2, b2);
    Z3_ast nc = Z3_mk_not(ctx2, c2);
    Z3_ast and_args[2] = { nb, nc };
    Z3_ast nb_and_nc = Z3_mk_and(ctx2, 2, and_args);
    Z3_ast or2_args[2] = { na, nb_and_nc };
    Z3_ast hard = Z3_mk_or(ctx2, 2, or2_args);
    Z3_optimize_assert(ctx2, opt2, hard);

    Z3_optimize_assert_soft(ctx2, opt2, a2, "5", NULL);
    Z3_optimize_assert_soft(ctx2, opt2, b2, "1", NULL);
    Z3_optimize_assert_soft(ctx2, opt2, c2, "1", NULL);

    int res2 = Z3_optimize_check(ctx2, opt2, 0, NULL);
    assert(res2 == Z3_L_TRUE);

    Z3_model m2 = Z3_optimize_get_model(ctx2, opt2);
    assert(m2 != NULL);

    Z3_ast a2v = 0, b2v = 0, c2v = 0;
    Z3_model_eval(ctx2, m2, a2, true, &a2v);
    Z3_model_eval(ctx2, m2, b2, true, &b2v);
    Z3_model_eval(ctx2, m2, c2, true, &c2v);
    // Exact-weight optimum: a true, b false, c false.
    assert(Z3_get_bool_value(ctx2, a2v) == Z3_L_TRUE);
    assert(Z3_get_bool_value(ctx2, b2v) == Z3_L_FALSE);
    assert(Z3_get_bool_value(ctx2, c2v) == Z3_L_FALSE);

    // assumptions are unsupported -> honest Z3_L_UNDEF.
    Z3_ast assumptions[1] = { a2 };
    int res3 = Z3_optimize_check(ctx2, opt2, 1, assumptions);
    assert(res3 == Z3_L_UNDEF);
    assert(Z3_get_error_code(ctx2) == Z3_INVALID_ARG);

    Z3_del_context(ctx2);
    return 0;
}

// Arithmetic objectives: maximize/minimize + get_lower/get_upper.
// (a) maximize x under 0<=x<=10 -> 10 (z3-verified).
// (b) lexicographic maximize x then y under x+y<=10 -> x=10, y=0 (z3-verified).
static int test_optimize_objectives(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), int_sort);
    Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
    Z3_ast ten = Z3_mk_int(ctx, 10, int_sort);

    Z3_optimize opt = Z3_mk_optimize(ctx);
    Z3_optimize_inc_ref(ctx, opt);
    Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, x, zero));
    Z3_optimize_assert(ctx, opt, Z3_mk_le(ctx, x, ten));

    unsigned obj = Z3_optimize_maximize(ctx, opt, x);
    assert(obj == 0);
    assert(Z3_get_error_code(ctx) == Z3_OK);

    int res = Z3_optimize_check(ctx, opt, 0, NULL);
    assert(res == Z3_L_TRUE);

    int64_t lo = 0, up = 0;
    bool oklo = Z3_get_numeral_int64(ctx, Z3_optimize_get_lower(ctx, opt, obj), &lo);
    bool okup = Z3_get_numeral_int64(ctx, Z3_optimize_get_upper(ctx, opt, obj), &up);
    assert(oklo && okup);
    assert(lo == 10);   // exact optimum (z3-verified)
    assert(up == 10);

    Z3_optimize_dec_ref(ctx, opt);
    Z3_del_context(ctx);

    // (b) Lexicographic two-objective.
    Z3_config cfg2 = Z3_mk_config();
    Z3_context ctx2 = Z3_mk_context(cfg2);
    Z3_del_config(cfg2);

    Z3_sort is2 = Z3_mk_int_sort(ctx2);
    Z3_ast x2 = Z3_mk_const(ctx2, Z3_mk_string_symbol(ctx2, "x"), is2);
    Z3_ast y2 = Z3_mk_const(ctx2, Z3_mk_string_symbol(ctx2, "y"), is2);
    Z3_ast z2 = Z3_mk_int(ctx2, 0, is2);
    Z3_ast t2 = Z3_mk_int(ctx2, 10, is2);

    Z3_optimize opt2 = Z3_mk_optimize(ctx2);
    Z3_ast add_args[2] = { x2, y2 };
    Z3_ast sum = Z3_mk_add(ctx2, 2, add_args);
    Z3_optimize_assert(ctx2, opt2, Z3_mk_le(ctx2, sum, t2));
    Z3_optimize_assert(ctx2, opt2, Z3_mk_ge(ctx2, x2, z2));
    Z3_optimize_assert(ctx2, opt2, Z3_mk_ge(ctx2, y2, z2));

    unsigned ox = Z3_optimize_maximize(ctx2, opt2, x2);
    unsigned oy = Z3_optimize_maximize(ctx2, opt2, y2);
    assert(ox == 0 && oy == 1);

    int res2 = Z3_optimize_check(ctx2, opt2, 0, NULL);
    assert(res2 == Z3_L_TRUE);

    int64_t vx = 0, vy = 0;
    Z3_get_numeral_int64(ctx2, Z3_optimize_get_upper(ctx2, opt2, ox), &vx);
    Z3_get_numeral_int64(ctx2, Z3_optimize_get_upper(ctx2, opt2, oy), &vy);
    assert(vx == 10);   // lex maximizes x first (z3-verified)
    assert(vy == 0);    // then y, forced to 0

    Z3_del_context(ctx2);
    return 0;
}

// Z3_substitute: simultaneous, hash-consed subterm replacement.
// (a) (+ x 1)[x:=5] eager-folds to 6 and equals directly-built (+ 5 1).
// (b) simultaneous swap x<->y in (- x y) yields (- y x), not (- x x).
// (c) sort mismatch (Int x -> Bool b) sets Z3_SORT_ERROR and returns `a`.
static int test_substitute(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), int_sort);
    Z3_ast y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y"), int_sort);
    Z3_ast one = Z3_mk_int(ctx, 1, int_sort);
    Z3_ast five = Z3_mk_int(ctx, 5, int_sort);

    // (a) (+ x 1)[x := 5] == (+ 5 1) == 6
    Z3_ast add_args[2] = { x, one };
    Z3_ast expr = Z3_mk_add(ctx, 2, add_args);
    Z3_ast from1[1] = { x };
    Z3_ast to1[1] = { five };
    Z3_ast got = Z3_substitute(ctx, expr, 1, from1, to1);
    assert(got != 0);

    Z3_ast direct_args[2] = { five, one };
    Z3_ast direct = Z3_mk_add(ctx, 2, direct_args);
    assert(got == direct);              // hash-consing identity
    int v = 0;
    assert(Z3_get_numeral_int(ctx, got, &v));
    assert(v == 6);                     // eager-folded to 6

    // (b) simultaneous swap (- x y) -> (- y x)
    Z3_ast sub_xy[2] = { x, y };
    Z3_ast sub_expr = Z3_mk_sub(ctx, 2, sub_xy);
    Z3_ast from2[2] = { x, y };
    Z3_ast to2[2] = { y, x };
    Z3_ast swapped = Z3_substitute(ctx, sub_expr, 2, from2, to2);
    Z3_ast sub_yx[2] = { y, x };
    Z3_ast expected = Z3_mk_sub(ctx, 2, sub_yx);
    assert(swapped == expected);
    assert(swapped != sub_expr);

    // num_exprs==0 is a no-op
    assert(Z3_substitute(ctx, expr, 0, from1, to1) == expr);

    // (c) sort mismatch -> Z3_SORT_ERROR, returns `a`
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), bool_sort);
    Z3_ast from3[1] = { x };
    Z3_ast to3[1] = { b };
    Z3_ast bad = Z3_substitute(ctx, expr, 1, from3, to3);
    assert(bad == expr);
    assert(Z3_get_error_code(ctx) == Z3_SORT_ERROR);

    Z3_del_context(ctx);
    return 0;
}

// Z3_simplify / Z3_simplify_ex: real simplification, logically equivalent.
static int test_simplify(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), int_sort);

    // (a) closed arithmetic folds to a numeral: simplify(2 + 3) == 5
    Z3_ast two = Z3_mk_int(ctx, 2, int_sort);
    Z3_ast three = Z3_mk_int(ctx, 3, int_sort);
    Z3_ast sum_args[2] = { two, three };
    Z3_ast sum = Z3_mk_add(ctx, 2, sum_args);
    Z3_ast simp_sum = Z3_simplify(ctx, sum);
    int v = 0;
    assert(Z3_get_numeral_int(ctx, simp_sum, &v));
    assert(v == 5);

    // (b) identity: simplify(x + 0) == x
    Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
    Z3_ast xz_args[2] = { x, zero };
    Z3_ast xz = Z3_mk_add(ctx, 2, xz_args);
    assert(Z3_simplify(ctx, xz) == x);

    // (c) And(true, p) -> p
    Z3_ast p = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "p"), bool_sort);
    Z3_ast and_args[2] = { Z3_mk_true(ctx), p };
    Z3_ast conj = Z3_mk_and(ctx, 2, and_args);
    assert(Z3_simplify(ctx, conj) == p);

    // (d) ite(true, a, b) -> a
    Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "a"), int_sort);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), int_sort);
    Z3_ast ite = Z3_mk_ite(ctx, Z3_mk_true(ctx), a, b);
    assert(Z3_simplify(ctx, ite) == a);

    // (e) (select (store a i v) i) -> v
    Z3_sort arr_sort = Z3_mk_array_sort(ctx, int_sort, int_sort);
    Z3_ast arr = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "arr"), arr_sort);
    Z3_ast i = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "i"), int_sort);
    Z3_ast vv = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "vv"), int_sort);
    Z3_ast stored = Z3_mk_store(ctx, arr, i, vv);
    Z3_ast sel = Z3_mk_select(ctx, stored, i);
    assert(Z3_simplify(ctx, sel) == vv);

    // (f) SOUNDNESS: simplify(e) equivalent to e — not(e = simplify(e)) is UNSAT.
    Z3_ast e_args[2] = { x, three };
    Z3_ast e = Z3_mk_add(ctx, 2, e_args);
    Z3_ast s = Z3_simplify(ctx, e);
    Z3_ast neq = Z3_mk_not(ctx, Z3_mk_eq(ctx, e, s));
    Z3_solver solver = Z3_mk_solver(ctx);
    Z3_solver_assert(ctx, solver, neq);
    assert(Z3_solver_check(ctx, solver) == Z3_L_FALSE);

    // (g) Z3_simplify_ex matches Z3_simplify (params ignored).
    Z3_params params = Z3_mk_params(ctx);
    assert(Z3_simplify_ex(ctx, sum, params) == Z3_simplify(ctx, sum));

    Z3_del_context(ctx);
    return 0;
}

// Sequence & string constructors (#phase3-seq)
static int test_seq_strings(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // String sort reports Z3_SEQ_SORT.
    Z3_sort str_sort = Z3_mk_string_sort(ctx);
    assert(Z3_get_sort_kind(ctx, str_sort) == Z3_SEQ_SORT);

    // (str.++ "ab" "c") == "abc"  -> sat
    Z3_ast ab = Z3_mk_string(ctx, "ab");
    Z3_ast c1 = Z3_mk_string(ctx, "c");
    Z3_ast abc = Z3_mk_string(ctx, "abc");
    Z3_ast cat_args[2] = { ab, c1 };
    Z3_ast cat = Z3_mk_seq_concat(ctx, 2, cat_args);
    Z3_ast cat_eq = Z3_mk_eq(ctx, cat, abc);

    Z3_solver s1 = Z3_mk_solver(ctx);
    Z3_solver_assert(ctx, s1, cat_eq);
    assert(Z3_solver_check(ctx, s1) == Z3_L_TRUE);

    // (str.len "abc") == 3 -> sat
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast len = Z3_mk_seq_length(ctx, abc);
    Z3_ast three = Z3_mk_int(ctx, 3, int_sort);
    Z3_solver s2 = Z3_mk_solver(ctx);
    Z3_solver_assert(ctx, s2, Z3_mk_eq(ctx, len, three));
    assert(Z3_solver_check(ctx, s2) == Z3_L_TRUE);

    // (str.contains "abc" "b") -> sat ; (str.contains "abc" "x") -> unsat
    Z3_ast b = Z3_mk_string(ctx, "b");
    Z3_ast x = Z3_mk_string(ctx, "x");
    Z3_solver s3 = Z3_mk_solver(ctx);
    Z3_solver_assert(ctx, s3, Z3_mk_seq_contains(ctx, abc, b));
    assert(Z3_solver_check(ctx, s3) == Z3_L_TRUE);
    Z3_solver s4 = Z3_mk_solver(ctx);
    Z3_solver_assert(ctx, s4, Z3_mk_seq_contains(ctx, abc, x));
    assert(Z3_solver_check(ctx, s4) == Z3_L_FALSE);

    Z3_del_context(ctx);
    return 0;
}

// Algebraic datatypes: declare Option<Int> = none | some(value: Int) via the
// Z3 constructor/datatype API, then assert (is-some x) /\ (value x) = 5 -> sat,
// and (is-none (some 5)) -> unsat (cross-checked against z3 -in). (#phase3-dt)
static int test_datatypes(void) {
    // SAT case: declare Option, assert (is-some x) and (= (value x) 5).
    {
        Z3_config cfg = Z3_mk_config();
        Z3_context ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        Z3_sort int_sort = Z3_mk_int_sort(ctx);

        // none (nullary)
        Z3_symbol none_name = Z3_mk_string_symbol(ctx, "none");
        Z3_symbol none_rec = Z3_mk_string_symbol(ctx, "is-none");
        Z3_constructor none_ctor =
            Z3_mk_constructor(ctx, none_name, none_rec, 0, NULL, NULL, NULL);
        assert(none_ctor != NULL);

        // some(value: Int)
        Z3_symbol some_name = Z3_mk_string_symbol(ctx, "some");
        Z3_symbol some_rec = Z3_mk_string_symbol(ctx, "is-some");
        Z3_symbol value_name = Z3_mk_string_symbol(ctx, "value");
        Z3_symbol field_names[1] = { value_name };
        Z3_sort field_sorts[1] = { int_sort };
        unsigned int sort_refs[1] = { 0 };
        Z3_constructor some_ctor = Z3_mk_constructor(
            ctx, some_name, some_rec, 1, field_names, field_sorts, sort_refs);
        assert(some_ctor != NULL);

        Z3_symbol dt_name = Z3_mk_string_symbol(ctx, "OptionInt");
        Z3_constructor ctors[2] = { none_ctor, some_ctor };
        Z3_sort dt_sort = Z3_mk_datatype(ctx, dt_name, 2, ctors);
        assert(dt_sort != NULL);

        Z3_func_decl some_decl = NULL, some_tester = NULL, some_acc[1] = { NULL };
        Z3_query_constructor(ctx, some_ctor, 1, &some_decl, &some_tester, some_acc);
        assert(some_decl != NULL && some_tester != NULL && some_acc[0] != NULL);

        Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x");
        Z3_ast x = Z3_mk_const(ctx, x_sym, dt_sort);
        assert(x != 0);

        Z3_ast x_arg[1] = { x };
        Z3_ast is_some_x = Z3_mk_app(ctx, some_tester, 1, x_arg);
        Z3_ast value_x = Z3_mk_app(ctx, some_acc[0], 1, x_arg);
        assert(is_some_x != 0 && value_x != 0);
        Z3_ast five = Z3_mk_int(ctx, 5, int_sort);
        Z3_ast eq = Z3_mk_eq(ctx, value_x, five);

        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, is_some_x);
        Z3_solver_assert(ctx, solver, eq);
        assert(Z3_solver_check(ctx, solver) == Z3_L_TRUE);

        Z3_model model = Z3_solver_get_model(ctx, solver);
        assert(model != NULL);
        Z3_string model_str = Z3_model_to_string(ctx, model);
        assert(model_str != NULL);

        Z3_del_constructor(ctx, none_ctor);
        Z3_del_constructor(ctx, some_ctor);
        Z3_del_context(ctx);
    }

    // UNSAT case: (is-none (some 5)).
    {
        Z3_config cfg = Z3_mk_config();
        Z3_context ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        Z3_sort int_sort = Z3_mk_int_sort(ctx);
        Z3_constructor none_ctor = Z3_mk_constructor(
            ctx, Z3_mk_string_symbol(ctx, "none"), NULL, 0, NULL, NULL, NULL);
        Z3_symbol value_name = Z3_mk_string_symbol(ctx, "value");
        Z3_symbol field_names[1] = { value_name };
        Z3_sort field_sorts[1] = { int_sort };
        unsigned int sort_refs[1] = { 0 };
        Z3_constructor some_ctor = Z3_mk_constructor(
            ctx, Z3_mk_string_symbol(ctx, "some"), NULL, 1, field_names,
            field_sorts, sort_refs);

        Z3_constructor ctors[2] = { none_ctor, some_ctor };
        Z3_sort dt_sort =
            Z3_mk_datatype(ctx, Z3_mk_string_symbol(ctx, "OptionInt"), 2, ctors);
        assert(dt_sort != NULL);

        Z3_func_decl some_decl = NULL;
        Z3_query_constructor(ctx, some_ctor, 1, &some_decl, NULL, NULL);
        Z3_func_decl none_tester = NULL;
        Z3_query_constructor(ctx, none_ctor, 0, NULL, &none_tester, NULL);
        assert(some_decl != NULL && none_tester != NULL);

        Z3_ast five = Z3_mk_int(ctx, 5, int_sort);
        Z3_ast five_arg[1] = { five };
        Z3_ast some_5 = Z3_mk_app(ctx, some_decl, 1, five_arg);
        Z3_ast some5_arg[1] = { some_5 };
        Z3_ast is_none = Z3_mk_app(ctx, none_tester, 1, some5_arg);

        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, is_none);
        assert(Z3_solver_check(ctx, solver) == Z3_L_FALSE);

        Z3_del_constructor(ctx, none_ctor);
        Z3_del_constructor(ctx, some_ctor);
        Z3_del_context(ctx);
    }

    return 0;
}

// Fixedpoint (CHC): declare a relation, add Horn rules for a bounded counter
// transition system, and query reachability. Verdicts come from ay-chc.
//
// Polarity (Z3 fixedpoint, cross-checked against `z3`):
//   reachable goal  => Z3_L_TRUE  (UNSAFE / sat)
//   unreachable goal => Z3_L_FALSE (SAFE   / unsat)
//
//   inv(0)                          ; init
//   inv(x) /\ x < 10 => inv(x+1)    ; transition
//
// SAFE query:   inv(x) /\ x > 100  (unreachable)  -> Z3_L_FALSE
// UNSAFE query: inv(x) /\ x > 5     (reachable)    -> Z3_L_TRUE
static int test_fixedpoint(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);

    Z3_fixedpoint fp = Z3_mk_fixedpoint(ctx);
    Z3_fixedpoint_inc_ref(ctx, fp);

    // (declare-rel inv (Int))
    Z3_symbol inv_sym = Z3_mk_string_symbol(ctx, "inv");
    Z3_func_decl inv = Z3_mk_func_decl(ctx, inv_sym, 1, &int_sort, bool_sort);
    Z3_fixedpoint_register_relation(ctx, fp, inv);

    Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x");
    Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);
    Z3_app x_app = Z3_to_app(ctx, x);
    Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
    Z3_ast one = Z3_mk_int(ctx, 1, int_sort);
    Z3_ast ten = Z3_mk_int(ctx, 10, int_sort);

    // init: forall x. (=> (= x 0) (inv x))
    Z3_ast x_eq_0 = Z3_mk_eq(ctx, x, zero);
    Z3_ast inv_x = Z3_mk_app(ctx, inv, 1, &x);
    Z3_ast init_body = Z3_mk_implies(ctx, x_eq_0, inv_x);
    Z3_ast init_rule = Z3_mk_forall_const(ctx, 0, 1, &x_app, 0, NULL, init_body);
    Z3_fixedpoint_add_rule(ctx, fp, init_rule, NULL);

    // transition: forall x. (=> (and (inv x) (< x 10)) (inv (+ x 1)))
    Z3_ast x_lt_10 = Z3_mk_lt(ctx, x, ten);
    Z3_ast inv_x2 = Z3_mk_app(ctx, inv, 1, &x);
    Z3_ast and_args[2] = { inv_x2, x_lt_10 };
    Z3_ast trans_ante = Z3_mk_and(ctx, 2, and_args);
    Z3_ast add_args[2] = { x, one };
    Z3_ast x_plus_1 = Z3_mk_add(ctx, 2, add_args);
    Z3_ast inv_xp1 = Z3_mk_app(ctx, inv, 1, &x_plus_1);
    Z3_ast trans_body = Z3_mk_implies(ctx, trans_ante, inv_xp1);
    Z3_ast trans_rule = Z3_mk_forall_const(ctx, 0, 1, &x_app, 0, NULL, trans_body);
    Z3_fixedpoint_add_rule(ctx, fp, trans_rule, NULL);

    // UNSAFE query: (and (inv qx) (> qx 5)) is reachable.
    Z3_symbol qx_sym = Z3_mk_string_symbol(ctx, "qx");
    Z3_ast qx = Z3_mk_const(ctx, qx_sym, int_sort);
    Z3_ast inv_qx = Z3_mk_app(ctx, inv, 1, &qx);
    Z3_ast five = Z3_mk_int(ctx, 5, int_sort);
    Z3_ast qx_gt_5 = Z3_mk_gt(ctx, qx, five);
    Z3_ast unsafe_goal_args[2] = { inv_qx, qx_gt_5 };
    Z3_ast unsafe_goal = Z3_mk_and(ctx, 2, unsafe_goal_args);
    int unsafe_res = Z3_fixedpoint_query(ctx, fp, unsafe_goal);
    assert(unsafe_res == Z3_L_TRUE);

    // SAFE query: (and (inv qx) (> qx 100)) is unreachable.
    Z3_ast hundred = Z3_mk_int(ctx, 100, int_sort);
    Z3_ast inv_qx2 = Z3_mk_app(ctx, inv, 1, &qx);
    Z3_ast qx_gt_100 = Z3_mk_gt(ctx, qx, hundred);
    Z3_ast safe_goal_args[2] = { inv_qx2, qx_gt_100 };
    Z3_ast safe_goal = Z3_mk_and(ctx, 2, safe_goal_args);
    int safe_res = Z3_fixedpoint_query(ctx, fp, safe_goal);
    assert(safe_res == Z3_L_FALSE);

    Z3_ast answer = Z3_fixedpoint_get_answer(ctx, fp);
    assert(answer != NULL);
    assert(strcmp(Z3_ast_to_string(ctx, answer), "false") == 0);

    Z3_string dump = Z3_fixedpoint_to_string(ctx, fp, 0, NULL);
    assert(dump != NULL && strstr(dump, "declare-rel inv") != NULL);

    Z3_fixedpoint_dec_ref(ctx, fp);
    Z3_del_context(ctx);
    return 0;
}

// Tactics: build elim-and, compose, and solve via Z3_mk_solver_from_tactic.
//
// SOUNDNESS: the tactic-solver verdict MUST equal a plain solver's on the same
// goal (the tactic is equivalence-preserving). Also checks the honest error path
// for an unknown tactic name (NULL + Z3_INVALID_ARG).
static int test_tactics(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort bs = Z3_mk_bool_sort(ctx);
    Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "a"), bs);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), bs);
    Z3_ast c = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "c"), bs);

    // (and (and a b) c) — a nested AND that elim-and has real work on.
    Z3_ast inner_args[2] = { a, b };
    Z3_ast inner = Z3_mk_and(ctx, 2, inner_args);
    Z3_ast outer_args[2] = { inner, c };
    Z3_ast goal = Z3_mk_and(ctx, 2, outer_args);

    // Plain solver baseline.
    Z3_solver plain = Z3_mk_solver(ctx);
    Z3_solver_assert(ctx, plain, goal);
    int base = Z3_solver_check(ctx, plain);
    assert(base == Z3_L_TRUE);

    // elim-and tactic + and_then composition.
    Z3_tactic t1 = Z3_mk_tactic(ctx, "elim-and");
    assert(t1 != NULL);
    assert(Z3_get_error_code(ctx) == Z3_OK);
    Z3_tactic_inc_ref(ctx, t1);
    Z3_tactic t2 = Z3_mk_tactic(ctx, "elim-and");
    Z3_tactic seq = Z3_tactic_and_then(ctx, t1, t2);
    assert(seq != NULL);

    // Honest error path: unknown tactic name -> NULL + Z3_INVALID_ARG.
    Z3_tactic bad = Z3_mk_tactic(ctx, "no-such-tactic");
    assert(bad == NULL);
    assert(Z3_get_error_code(ctx) == Z3_INVALID_ARG);

    // Solver from tactic: same verdict as the plain solver, valid model.
    Z3_solver ts = Z3_mk_solver_from_tactic(ctx, seq);
    assert(ts != NULL);
    Z3_solver_assert(ctx, ts, goal);
    int res = Z3_solver_check(ctx, ts);
    assert(res == base);

    Z3_model model = Z3_solver_get_model(ctx, ts);
    assert(model != NULL);
    Z3_ast va = 0;
    bool oka = Z3_model_eval(ctx, model, a, true, &va);
    assert(oka);
    assert(Z3_get_bool_value(ctx, va) == Z3_L_TRUE);  // only model sets a,b,c true

    Z3_tactic_dec_ref(ctx, t1);
    Z3_del_context(ctx);

    // UNSAT case: (and (and a (not a)) b) via a tactic-solver -> UNSAT, matching
    // a plain solver.
    Z3_config cfg2 = Z3_mk_config();
    Z3_context ctx2 = Z3_mk_context(cfg2);
    Z3_del_config(cfg2);

    Z3_sort bs2 = Z3_mk_bool_sort(ctx2);
    Z3_ast a2 = Z3_mk_const(ctx2, Z3_mk_string_symbol(ctx2, "a"), bs2);
    Z3_ast b2 = Z3_mk_const(ctx2, Z3_mk_string_symbol(ctx2, "b"), bs2);
    Z3_ast na2 = Z3_mk_not(ctx2, a2);
    Z3_ast in2_args[2] = { a2, na2 };
    Z3_ast in2 = Z3_mk_and(ctx2, 2, in2_args);
    Z3_ast out2_args[2] = { in2, b2 };
    Z3_ast goal2 = Z3_mk_and(ctx2, 2, out2_args);

    Z3_solver plain2 = Z3_mk_solver(ctx2);
    Z3_solver_assert(ctx2, plain2, goal2);
    int base2 = Z3_solver_check(ctx2, plain2);
    assert(base2 == Z3_L_FALSE);

    Z3_tactic ft = Z3_mk_tactic(ctx2, "elim-and");
    Z3_solver ts2 = Z3_mk_solver_from_tactic(ctx2, ft);
    Z3_solver_assert(ctx2, ts2, goal2);
    int res2 = Z3_solver_check(ctx2, ts2);
    assert(res2 == base2);  // UNSAT == UNSAT

    Z3_del_context(ctx2);
    return 0;
}

// Proofs (Alethe): after an UNSAT check with proof production enabled, the
// solver must hand back its real Alethe proof artifact via Z3_solver_get_proof /
// Z3_solver_get_proof_string. The HONESTY half of the test is the important
// half: a SAT result and a proofs-disabled run must both return NULL with
// Z3_INVALID_USAGE — never a fabricated proof.
static int test_proofs(void) {
    // --- UNSAT + proofs enabled: real Alethe text is returned. ---
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort bs = Z3_mk_bool_sort(ctx);
    Z3_ast p = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "p"), bs);
    Z3_ast not_p = Z3_mk_not(ctx, p);  // p AND (not p) is UNSAT

    Z3_solver solver = Z3_mk_solver(ctx);
    Z3_solver_set_proof_production(ctx, solver, true);
    assert(Z3_solver_get_proof_production(ctx, solver));
    Z3_solver_assert(ctx, solver, p);
    Z3_solver_assert(ctx, solver, not_p);

    assert(Z3_solver_check(ctx, solver) == Z3_L_FALSE);

    Z3_ast proof = Z3_solver_get_proof(ctx, solver);
    assert(proof != 0);                              // non-null handle
    assert(Z3_get_error_code(ctx) == Z3_OK);
    Z3_string proof_text = Z3_ast_to_string(ctx, proof);
    assert(proof_text != NULL);
    // Real Alethe text carries structural markers, not the generic placeholder.
    assert(strstr(proof_text, "assume") != NULL ||
           strstr(proof_text, "step") != NULL ||
           strstr(proof_text, "(cl") != NULL);
    assert(strncmp(proof_text, "(ast ", 5) != 0);    // not the term placeholder
    assert(strncmp(proof_text, "(error", 6) != 0);   // not an error sexpr

    // The direct string accessor returns the same kind of artifact.
    Z3_string proof_str = Z3_solver_get_proof_string(ctx, solver);
    assert(proof_str != NULL);
    assert(strstr(proof_str, "assume") != NULL ||
           strstr(proof_str, "step") != NULL ||
           strstr(proof_str, "(cl") != NULL);

    Z3_del_context(ctx);

    // --- HONEST: SAT result returns NULL + Z3_INVALID_USAGE (no proof). ---
    Z3_config cfg2 = Z3_mk_config();
    Z3_context ctx2 = Z3_mk_context(cfg2);
    Z3_del_config(cfg2);
    Z3_sort bs2 = Z3_mk_bool_sort(ctx2);
    Z3_ast q = Z3_mk_const(ctx2, Z3_mk_string_symbol(ctx2, "q"), bs2);
    Z3_solver solver2 = Z3_mk_solver(ctx2);
    Z3_solver_set_proof_production(ctx2, solver2, true);
    Z3_solver_assert(ctx2, solver2, q);
    assert(Z3_solver_check(ctx2, solver2) == Z3_L_TRUE);
    assert(Z3_solver_get_proof(ctx2, solver2) == 0);
    assert(Z3_get_error_code(ctx2) == Z3_INVALID_USAGE);
    assert(Z3_solver_get_proof_string(ctx2, solver2) == NULL);
    assert(Z3_get_error_code(ctx2) == Z3_INVALID_USAGE);
    Z3_del_context(ctx2);

    // --- HONEST: UNSAT but proofs DISABLED returns NULL + Z3_INVALID_USAGE. ---
    Z3_config cfg3 = Z3_mk_config();
    Z3_context ctx3 = Z3_mk_context(cfg3);
    Z3_del_config(cfg3);
    Z3_sort bs3 = Z3_mk_bool_sort(ctx3);
    Z3_ast r = Z3_mk_const(ctx3, Z3_mk_string_symbol(ctx3, "r"), bs3);
    Z3_ast not_r = Z3_mk_not(ctx3, r);
    Z3_solver solver3 = Z3_mk_solver(ctx3);  // proofs OFF by default
    assert(!Z3_solver_get_proof_production(ctx3, solver3));
    Z3_solver_assert(ctx3, solver3, r);
    Z3_solver_assert(ctx3, solver3, not_r);
    assert(Z3_solver_check(ctx3, solver3) == Z3_L_FALSE);
    assert(Z3_solver_get_proof(ctx3, solver3) == 0);
    assert(Z3_get_error_code(ctx3) == Z3_INVALID_USAGE);
    Z3_del_context(ctx3);

    return 0;
}

// Floating-point (IEEE-754 / FPA): build (fp.add RNE a b), solve, and check a
// predicate plus an FP soundness property. The FP semantics come from AY's core
// FP theory; this subtest only drives the Z3_mk_fpa_* C surface.
static int test_floating_point(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Float32 sort and two FP constants.
    Z3_sort f32 = Z3_mk_fpa_sort_single(ctx);
    assert(f32 != NULL);
    Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "a"), f32);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), f32);

    Z3_ast rne = Z3_mk_fpa_rne(ctx);
    assert(rne != 0);

    // FP numerals 1.0, 2.0, 3.0.
    Z3_ast one = Z3_mk_fpa_numeral_double(ctx, 1.0, f32);
    Z3_ast two = Z3_mk_fpa_numeral_double(ctx, 2.0, f32);
    Z3_ast three = Z3_mk_fpa_numeral_double(ctx, 3.0, f32);

    // (fp.add RNE a b) is interpreted: a==1, b==2, a+b==3  => SAT.
    Z3_ast sum = Z3_mk_fpa_add(ctx, rne, a, b);
    assert(sum != 0);
    assert(Z3_get_error_code(ctx) == Z3_OK);

    Z3_ast a_eq = Z3_mk_fpa_eq(ctx, a, one);
    Z3_ast b_eq = Z3_mk_fpa_eq(ctx, b, two);
    Z3_ast s_eq = Z3_mk_fpa_eq(ctx, sum, three);

    Z3_solver solver = Z3_mk_solver(ctx);
    Z3_solver_assert(ctx, solver, a_eq);
    Z3_solver_assert(ctx, solver, b_eq);
    Z3_solver_assert(ctx, solver, s_eq);
    assert(Z3_solver_check(ctx, solver) == Z3_L_TRUE);

    Z3_model model = Z3_solver_get_model(ctx, solver);
    assert(model != NULL);
    Z3_string model_str = Z3_model_to_string(ctx, model);
    assert(model_str != NULL);

    Z3_del_context(ctx);

    // Predicate: NaN AND Infinite is impossible => UNSAT.
    Z3_config cfg2 = Z3_mk_config();
    Z3_context ctx2 = Z3_mk_context(cfg2);
    Z3_del_config(cfg2);
    Z3_sort f32b = Z3_mk_fpa_sort_single(ctx2);
    Z3_ast x = Z3_mk_const(ctx2, Z3_mk_string_symbol(ctx2, "x"), f32b);
    Z3_ast is_nan = Z3_mk_fpa_is_nan(ctx2, x);
    Z3_ast is_inf = Z3_mk_fpa_is_infinite(ctx2, x);
    Z3_solver solver2 = Z3_mk_solver(ctx2);
    Z3_solver_assert(ctx2, solver2, is_nan);
    Z3_solver_assert(ctx2, solver2, is_inf);
    assert(Z3_solver_check(ctx2, solver2) == Z3_L_FALSE);
    Z3_del_context(ctx2);

    // SOUNDNESS: x + 0.0 == x is NOT FP-valid (fails for NaN). The negation must
    // be SAT — the solver knows FP is not real arithmetic.
    Z3_config cfg3 = Z3_mk_config();
    Z3_context ctx3 = Z3_mk_context(cfg3);
    Z3_del_config(cfg3);
    Z3_sort f32c = Z3_mk_fpa_sort_single(ctx3);
    Z3_ast y = Z3_mk_const(ctx3, Z3_mk_string_symbol(ctx3, "y"), f32c);
    Z3_ast rne3 = Z3_mk_fpa_rne(ctx3);
    Z3_ast pzero = Z3_mk_fpa_zero(ctx3, f32c, false);
    Z3_ast y_sum = Z3_mk_fpa_add(ctx3, rne3, y, pzero);
    Z3_ast y_eq = Z3_mk_fpa_eq(ctx3, y_sum, y);
    Z3_ast y_neq = Z3_mk_not(ctx3, y_eq);
    Z3_solver solver3 = Z3_mk_solver(ctx3);
    Z3_solver_assert(ctx3, solver3, y_neq);
    assert(Z3_solver_check(ctx3, solver3) == Z3_L_TRUE);

    // HONEST ERROR: an FP constructor on a non-FP sort returns null + SORT_ERROR.
    Z3_sort int_sort = Z3_mk_int_sort(ctx3);
    Z3_ast bad = Z3_mk_fpa_nan(ctx3, int_sort);
    assert(bad == 0);
    assert(Z3_get_error_code(ctx3) == Z3_SORT_ERROR);

    Z3_del_context(ctx3);
    return 0;
}

// Sets, modelled as (Array elem Bool) (#capi_breadth).
//
// Each independent case uses a FRESH context (historical style; solvers on one
// context are independent since the multi-solver fix, but fresh contexts keep
// each case's term arena separate too).
// SOUNDNESS via AY's own verdicts (each cross-checked against z3):
//   (a) member(5, add(5, empty Int))                 -> SAT (5 is in {5})
//   (b) member(5, del(5, full Int))                  -> UNSAT (5 removed)
//   (c) member(3, add(5, empty Int))                 -> UNSAT (only 5 is in)
//   (d) NOT member(7, full Int)                      -> UNSAT (full holds all)
// Also checks set sort kind is Array.

// One membership check in a fresh context. `which`: 0=add/5, 1=del/5, 2=add/3.
static int set_member_check(int elem, int which) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast five = Z3_mk_int(ctx, 5, int_sort);
    Z3_ast e = Z3_mk_int(ctx, elem, int_sort);
    Z3_ast set;
    if (which == 1) {
        set = Z3_mk_set_del(ctx, Z3_mk_full_set(ctx, int_sort), five);
    } else {
        set = Z3_mk_set_add(ctx, Z3_mk_empty_set(ctx, int_sort), five);
    }
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_assert(ctx, s, Z3_mk_set_member(ctx, e, set));
    int r = Z3_solver_check(ctx, s);
    Z3_del_context(ctx);
    return r;
}

static int test_sets(void) {
    // Set sort is an array sort.
    {
        Z3_config cfg = Z3_mk_config();
        Z3_context ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        Z3_sort int_sort = Z3_mk_int_sort(ctx);
        Z3_sort set_sort = Z3_mk_set_sort(ctx, int_sort);
        assert(set_sort != NULL);
        assert(Z3_get_sort_kind(ctx, set_sort) == Z3_ARRAY_SORT);
        assert(Z3_mk_empty_set(ctx, int_sort) != 0);
        assert(Z3_mk_full_set(ctx, int_sort) != 0);
        Z3_del_context(ctx);
    }

    assert(set_member_check(5, 0) == Z3_L_TRUE);   // (a) 5 in {5}
    assert(set_member_check(5, 1) == Z3_L_FALSE);  // (b) 5 in (del 5 full)
    assert(set_member_check(3, 2) == Z3_L_FALSE);  // (c) 3 in {5}

    // (d) NOT (7 in full) -> UNSAT (every element is a member of the full set)
    {
        Z3_config cfg = Z3_mk_config();
        Z3_context ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        Z3_sort int_sort = Z3_mk_int_sort(ctx);
        Z3_ast seven = Z3_mk_int(ctx, 7, int_sort);
        Z3_ast full = Z3_mk_full_set(ctx, int_sort);
        Z3_solver s = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s, Z3_mk_not(ctx, Z3_mk_set_member(ctx, seven, full)));
        assert(Z3_solver_check(ctx, s) == Z3_L_FALSE);
        Z3_del_context(ctx);
    }
    return 0;
}

// Regular expressions / sequence-regex bridge (#capi_breadth).
//
// Each membership case runs in a FRESH context (see test_sets rationale).
// SOUNDNESS via AY's own verdicts (each cross-checked against z3):
//   (a) "ab" in (re.++ (str.to.re "a") (str.to.re "b"))   -> SAT
//   (b) "ba" in (re.++ (str.to.re "a") (str.to.re "b"))   -> UNSAT
//   (c) "aaa" in (re.* (str.to.re "a"))                    -> SAT
//   (d) "" in (re.+ (str.to.re "a"))                       -> UNSAT (>=1 rep)
//   (e) "b" in (re.union (str.to.re "a") (str.to.re "b"))  -> SAT

// kind: 0=concat ab, 1=star a, 2=plus a, 3=union ab. Checks (in_re word RE).
static int regex_member_check(const char* word, int kind) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_ast ra = Z3_mk_seq_to_re(ctx, Z3_mk_string(ctx, "a"));
    Z3_ast rb = Z3_mk_seq_to_re(ctx, Z3_mk_string(ctx, "b"));
    Z3_ast re;
    if (kind == 0) {
        Z3_ast args[2] = { ra, rb };
        re = Z3_mk_re_concat(ctx, 2, args);
    } else if (kind == 1) {
        re = Z3_mk_re_star(ctx, ra);
    } else if (kind == 2) {
        re = Z3_mk_re_plus(ctx, ra);
    } else {
        Z3_ast args[2] = { ra, rb };
        re = Z3_mk_re_union(ctx, 2, args);
    }
    assert(re != 0);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_assert(ctx, s, Z3_mk_seq_in_re(ctx, Z3_mk_string(ctx, word), re));
    int r = Z3_solver_check(ctx, s);
    Z3_del_context(ctx);
    return r;
}

static int test_regex(void) {
    assert(regex_member_check("ab", 0) == Z3_L_TRUE);   // (a)
    assert(regex_member_check("ba", 0) == Z3_L_FALSE);  // (b)
    assert(regex_member_check("aaa", 1) == Z3_L_TRUE);  // (c)
    assert(regex_member_check("", 2) == Z3_L_FALSE);    // (d)
    assert(regex_member_check("b", 3) == Z3_L_TRUE);    // (e)

    // HONEST: empty n==0 union/concat -> Z3_INVALID_ARG, returns 0.
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_ast bad_un = Z3_mk_re_union(ctx, 0, NULL);
    assert(bad_un == 0);
    assert(Z3_get_error_code(ctx) == Z3_INVALID_ARG);
    Z3_ast bad_cat = Z3_mk_re_concat(ctx, 0, NULL);
    assert(bad_cat == 0);
    assert(Z3_get_error_code(ctx) == Z3_INVALID_ARG);

    Z3_del_context(ctx);
    return 0;
}

// String-literal accessors and version/global-param surface (#capi_breadth).
static int test_string_accessors(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_ast hello = Z3_mk_string(ctx, "hello");
    assert(Z3_is_string(ctx, hello));
    Z3_string got = Z3_get_string(ctx, hello);
    assert(got != NULL);
    assert(strcmp(got, "hello") == 0);
    assert(Z3_get_string_length(ctx, hello) == 5);

    // A non-literal string term (str.++ x y) is NOT a string literal.
    Z3_sort str_sort = Z3_mk_string_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), str_sort);
    Z3_ast cat_args[2] = { x, hello };
    Z3_ast cat = Z3_mk_seq_concat(ctx, 2, cat_args);
    assert(!Z3_is_string(ctx, cat));
    assert(Z3_get_string(ctx, cat) == NULL);
    assert(Z3_get_string_length(ctx, cat) == 0);

    // An Int numeral is not a string.
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast five = Z3_mk_int(ctx, 5, int_sort);
    assert(!Z3_is_string(ctx, five));
    assert(Z3_get_string(ctx, five) == NULL);

    // Version APIs report the pinned Z3 5.1.0 compatibility identity.
    unsigned int major = 0, minor = 0, build = 0, revision = 0;
    Z3_get_version(&major, &minor, &build, &revision);
    assert(major == 5);
    assert(minor == 1);
    assert(build == 0);
    assert(revision == 0);
    Z3_string ver = Z3_get_full_version();
    assert(ver != NULL);
    assert(strstr(ver, "(Z3 5.1.0.0 compatible)") != NULL);

    // Global params are sound no-ops (must not crash or change state).
    Z3_global_param_set("smt.random_seed", "1");
    Z3_global_param_reset_all();
    assert(Z3_get_error_code(ctx) == Z3_OK);

    Z3_del_context(ctx);
    return 0;
}

// Multi-solver independence (regression): two Z3_solver handles on ONE
// context own independent assertion stacks, like real z3. THE BUG: every
// solver handle silently aliased the context's single shared solver, so
// s1: x>5 and s2: x<3 merged into x>5 AND x<3 and BOTH checks came back
// UNSAT; real z3 4.15.4 answers SAT for each. Models must satisfy each
// solver's OWN constraints only.
static int test_multi_solver_independence(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), int_sort);

    Z3_solver s1 = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s1);
    Z3_solver s2 = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s2);

    Z3_solver_assert(ctx, s1, Z3_mk_gt(ctx, x, Z3_mk_int(ctx, 5, int_sort)));
    Z3_solver_assert(ctx, s2, Z3_mk_lt(ctx, x, Z3_mk_int(ctx, 3, int_sort)));

    // Both independently SAT (the bug made both UNSAT).
    assert(Z3_solver_check(ctx, s1) == Z3_L_TRUE);
    assert(Z3_solver_check(ctx, s2) == Z3_L_TRUE);

    // Each model satisfies its own solver's constraint.
    Z3_model m1 = Z3_solver_get_model(ctx, s1);
    Z3_model m2 = Z3_solver_get_model(ctx, s2);
    assert(m1 != NULL && m2 != NULL);
    Z3_ast v1 = 0, v2 = 0;
    int64_t i1 = 0, i2 = 0;
    assert(Z3_model_eval(ctx, m1, x, true, &v1));
    assert(Z3_model_eval(ctx, m2, x, true, &v2));
    assert(Z3_get_numeral_int64(ctx, v1, &i1));
    assert(Z3_get_numeral_int64(ctx, v2, &i2));
    assert(i1 > 5);
    assert(i2 < 3);

    // Narrow s1 to 5 < x < 7 (pins x=6); s2 is untouched.
    Z3_solver_assert(ctx, s1, Z3_mk_lt(ctx, x, Z3_mk_int(ctx, 7, int_sort)));
    assert(Z3_solver_check(ctx, s1) == Z3_L_TRUE);
    m1 = Z3_solver_get_model(ctx, s1);
    assert(Z3_model_eval(ctx, m1, x, true, &v1));
    assert(Z3_get_numeral_int64(ctx, v1, &i1));
    assert(i1 == 6);
    assert(Z3_solver_check(ctx, s2) == Z3_L_TRUE);

    Z3_solver_dec_ref(ctx, s1);
    Z3_solver_dec_ref(ctx, s2);
    Z3_del_context(ctx);
    return 0;
}

int main(void) {
    printf("ay-ffi C consumer test (#4990)\n");

    test_basic_sat();
    printf("  PASS: basic_sat\n");

    test_multi_solver_independence();
    printf("  PASS: multi_solver_independence\n");

    test_arithmetic();
    printf("  PASS: arithmetic\n");

    test_sorts_and_symbols();
    printf("  PASS: sorts_and_symbols\n");

    test_bv_and_bool();
    printf("  PASS: bv_and_bool\n");

    test_error_handling();
    printf("  PASS: error_handling\n");

    test_ay_timeout_statistics();
    printf("  PASS: ay_timeout_statistics\n");

    test_refcounting();
    printf("  PASS: refcounting\n");

    test_optimize_maxsat();
    printf("  PASS: optimize_maxsat\n");

    test_optimize_objectives();
    printf("  PASS: optimize_objectives\n");

    test_substitute();
    printf("  PASS: substitute\n");

    test_simplify();
    printf("  PASS: simplify\n");

    test_seq_strings();
    printf("  PASS: seq_strings\n");

    test_datatypes();
    printf("  PASS: datatypes\n");

    test_fixedpoint();
    printf("  PASS: fixedpoint\n");

    test_tactics();
    printf("  PASS: tactics\n");

    test_floating_point();
    printf("  PASS: floating_point\n");

    test_proofs();
    printf("  PASS: proofs\n");

    test_sets();
    printf("  PASS: sets\n");

    test_regex();
    printf("  PASS: regex\n");

    test_string_accessors();
    printf("  PASS: string_accessors\n");

    printf("All 21 C consumer tests passed.\n");
    return 0;
}
