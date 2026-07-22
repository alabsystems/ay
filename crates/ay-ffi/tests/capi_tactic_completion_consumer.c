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

int main(void) {
    setbuf(stdout, NULL);
    Z3_config cfg = Z3_mk_config();
    C = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_set_error_handler(C, err_handler);
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

    // ---- try_for(t, ms): behaves like t (ay's passes always terminate) ----
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

    // ---- Z3_tactic_apply_ex: same result as Z3_tactic_apply (params ignored) ----
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
    // get_descr: the `cnf` alias is a documented ay superset (libz3 has no `cnf`
    // tactic and would abort); an unknown name is an honest NULL + error.
    CHECK_B(Z3_tactic_get_descr(C, "cnf") != NULL, 1, "descr(cnf) non-null (ay alias)");
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
