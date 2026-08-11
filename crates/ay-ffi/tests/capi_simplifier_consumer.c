// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C consumer for the Z3-compatible Simplifier C API:
//   Z3_mk_simplifier / Z3_simplifier_inc_ref / _dec_ref / _and_then /
//   _using_params / _get_descr / _get_help / _get_param_descrs, plus
//   Z3_solver_add_simplifier.
//
// A simplifier is a preprocessing transformer attached to a solver so the solver
// runs it before each check-sat. The registry check freezes the exact 37 names
// and order reported by Z3 5.0.0. The core semantic check builds a simplifier
// (`solve-eqs` and_then `propagate-values`), ATTACH it to a solver, assert a
// formula, and confirm the verdict is PRESERVED — it equals both (a) the verdict
// of a plain solver without the simplifier and (b) what libz3 returns for the
// same goal+simplifier. Because that is exactly what libz3 does too, this single
// source compiles and runs against BOTH ay-ffi (default) and libz3
// (`-DAY_TWIN_USE_Z3 -lz3`), and both must pass the identical shared assertions.
// That is the cross-check: ay's observable simplifier behavior == libz3's.
//
// A non-aborting error handler is installed so an honest rejection (e.g.
// mk_simplifier on an unknown name -> NULL + error) surfaces as a return value
// instead of libz3's default abort.

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

#define CHECK_I(actual, expected, what)                                        \
    do {                                                                       \
        int a_ = (int)(actual);                                                \
        int e_ = (int)(expected);                                              \
        if (a_ == e_) {                                                        \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s: got %d want %d\n", (what), a_, e_);               \
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

#ifdef AY_TWIN_USE_Z3
static void err_handler(Z3_context c, Z3_error_code e) { (void)c; (void)e; }
#else
static void err_handler(Z3_context c, unsigned int e) { (void)c; (void)e; }
#endif

static Z3_context C;

static const char *z3_5_simplifiers[] = {
    "bit2int",
    "bit-blast",
    "bv1-blast",
    "cheap-fourier-motzkin",
    "elim-term-ite",
    "max-bv-sharing",
    "pull-nested-quantifiers",
    "push-app-ite-conservative",
    "push-app-ite",
    "ng-push-app-ite-conservative",
    "ng-push-app-ite",
    "randomizer",
    "refine-injectivity",
    "simplify",
    "qe-light",
    "card2bv",
    "factor",
    "propagate-ineqs",
    "propagate-bv-bounds",
    "bv-divrem-bounds",
    "bv-slice",
    "bvarray2uf",
    "blast-term-ite",
    "cofactor-term-ite",
    "demodulator",
    "der",
    "distribute-forall",
    "dom-simplify",
    "elim-unconstrained",
    "elim-predicates",
    "fold-unfold",
    "injectivity",
    "propagate-values",
    "reduce-args",
    "solve-eqs",
    "special-relations",
    "euf-completion",
};

// inc_ref a freshly built simplifier (libz3 requires it; ay's inc_ref is a no-op).
static Z3_simplifier S(Z3_simplifier s) { Z3_simplifier_inc_ref(C, s); return s; }

// Build the LIA goal {x = y+1, y = 2, cmp(x, 2-or-3)} on solver `s`.
// sat==1 -> {x > 2} (SAT, x=3); sat==0 -> {x < 3} (UNSAT, x would be 3).
static void assert_lia(Z3_solver s, int sat) {
    Z3_sort I = Z3_mk_int_sort(C);
    Z3_ast x = Z3_mk_const(C, Z3_mk_string_symbol(C, "x"), I);
    Z3_ast y = Z3_mk_const(C, Z3_mk_string_symbol(C, "y"), I);
    Z3_ast one = Z3_mk_int(C, 1, I);
    Z3_ast two = Z3_mk_int(C, 2, I);
    Z3_ast three = Z3_mk_int(C, 3, I);
    Z3_ast yp1_args[2] = {y, one};
    Z3_ast yp1 = Z3_mk_add(C, 2, yp1_args);
    Z3_solver_assert(C, s, Z3_mk_eq(C, x, yp1));
    Z3_solver_assert(C, s, Z3_mk_eq(C, y, two));
    if (sat) {
        Z3_solver_assert(C, s, Z3_mk_gt(C, x, two));
    } else {
        Z3_solver_assert(C, s, Z3_mk_lt(C, x, three));
    }
}

// Solve the LIA goal on a plain solver (no simplifier). Returns the lbool verdict.
static int solve_plain(int sat) {
    Z3_solver s = Z3_mk_solver(C);
    Z3_solver_inc_ref(C, s);
    assert_lia(s, sat);
    int r = Z3_solver_check(C, s);
    Z3_solver_dec_ref(C, s);
    return r;
}

// Solve the LIA goal via a solver with `comp` attached. Returns the lbool verdict.
static int solve_with_simplifier(Z3_simplifier comp, int sat) {
    Z3_solver base = Z3_mk_solver(C);
    Z3_solver_inc_ref(C, base);
    Z3_solver s = Z3_solver_add_simplifier(C, base, comp);
    Z3_solver_inc_ref(C, s);
    assert_lia(s, sat);
    int r = Z3_solver_check(C, s);
    return r;
}

int main(void) {
    setbuf(stdout, NULL);
    Z3_config cfg = Z3_mk_config();
    C = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_set_error_handler(C, err_handler);

    // ---- mk_simplifier: shared real-z3 simplifier names build (non-null) ----
    const char *shared[] = {"simplify", "solve-eqs", "propagate-values",
                            "qe-light", "bit-blast"};
    for (int i = 0; i < 5; i++) {
        Z3_simplifier s = Z3_mk_simplifier(C, shared[i]);
        CHECK_B(s != NULL, 1, shared[i]);
        CHECK_I(Z3_get_error_code(C), Z3_OK, "mk shared name err OK");
    }

    // ---- get_descr: shared names return a real non-empty string, err OK ----
    for (int i = 0; i < 5; i++) {
        Z3_string d = Z3_simplifier_get_descr(C, shared[i]);
        CHECK_B(d != NULL && d[0] != '\0', 1, shared[i]);
        CHECK_I(Z3_get_error_code(C), Z3_OK, "descr shared name err OK");
    }

    // ---- mk_simplifier(unknown) -> NULL on both ay and libz3 ----
    Z3_simplifier bad = Z3_mk_simplifier(C, "not-a-real-simplifier");
    CHECK_B(bad == NULL, 1, "mk(unknown)=NULL");

    // ---- and_then compose + get_help(non-null) ----
    Z3_simplifier se = S(Z3_mk_simplifier(C, "solve-eqs"));
    Z3_simplifier pv = S(Z3_mk_simplifier(C, "propagate-values"));
    Z3_simplifier comp = S(Z3_simplifier_and_then(C, se, pv));
    CHECK_B(comp != NULL, 1, "and_then(solve-eqs, propagate-values) non-null");
    Z3_string help = Z3_simplifier_get_help(C, comp);
    CHECK_B(help != NULL, 1, "get_help(comp) non-null");

    // ---- using_params returns a usable simplifier ----
    Z3_params pr = Z3_mk_params(C);
    Z3_params_inc_ref(C, pr);
    Z3_simplifier withp = S(Z3_simplifier_using_params(C, comp, pr));
    CHECK_B(withp != NULL, 1, "using_params(comp) non-null");

    // ==== CORE CROSS-CHECK: verdict preservation ====
    // Baseline (no simplifier) and simplifier-attached verdicts must be EQUAL,
    // and this holds identically for ay and libz3 (the shared assertion).
    int plain_sat = solve_plain(1);
    int simp_sat = solve_with_simplifier(comp, 1);
    CHECK_I(plain_sat, Z3_L_TRUE, "plain SAT verdict");
    CHECK_I(simp_sat, plain_sat, "simplifier preserves SAT verdict");

    int plain_unsat = solve_plain(0);
    int simp_unsat = solve_with_simplifier(comp, 0);
    CHECK_I(plain_unsat, Z3_L_FALSE, "plain UNSAT verdict");
    CHECK_I(simp_unsat, plain_unsat, "simplifier preserves UNSAT verdict");

    // Also cross-check with the using_params-wrapped simplifier (same verdict).
    CHECK_I(solve_with_simplifier(withp, 1), Z3_L_TRUE, "using_params preserves SAT");
    CHECK_I(solve_with_simplifier(withp, 0), Z3_L_FALSE, "using_params preserves UNSAT");

    // A single-simplifier attach (`simplify`) also preserves the verdict.
    Z3_simplifier simp = S(Z3_mk_simplifier(C, "simplify"));
    CHECK_I(solve_with_simplifier(simp, 1), Z3_L_TRUE, "simplify preserves SAT");
    CHECK_I(solve_with_simplifier(simp, 0), Z3_L_FALSE, "simplify preserves UNSAT");

    // ---- Exact Z3 5.0.0 registry: 37 names, same order, all constructible ----
    unsigned int num_simplifiers = Z3_get_num_simplifiers(C);
    CHECK_I(num_simplifiers, 37, "Z3 5.0.0 simplifier count");
    for (unsigned int i = 0; i < 37; i++) {
        Z3_string got = Z3_get_simplifier_name(C, i);
        CHECK_B(got != NULL, 1, "enumerated simplifier name non-null");
        if (got != NULL) {
            CHECK_B(strcmp(got, z3_5_simplifiers[i]) == 0, 1,
                    "enumerated simplifier matches Z3 5.0.0 order");
        }
        Z3_simplifier entry = Z3_mk_simplifier(C, z3_5_simplifiers[i]);
        CHECK_B(entry != NULL, 1, "enumerated Z3 5.0.0 simplifier builds");
        Z3_string entry_descr =
            Z3_simplifier_get_descr(C, z3_5_simplifiers[i]);
        CHECK_B(entry_descr != NULL && entry_descr[0] != '\0', 1,
                "enumerated simplifier has description");
    }

#ifndef AY_TWIN_USE_Z3
    // ---- AY-only honesty checks (libz3 diverges/aborts on these) ----
    // get_descr(unknown) -> NULL + Z3_INVALID_ARG (libz3 returns "" + error).
    Z3_string du = Z3_simplifier_get_descr(C, "not-a-real-simplifier");
    CHECK_B(du == NULL, 1, "descr(unknown)=NULL (ay honest)");
    CHECK_I(Z3_get_error_code(C), Z3_INVALID_ARG, "descr(unknown) sets INVALID_ARG");

    // elim-and / nnf are tactics, not Z3 5.0.0 simplifiers. The old AY-only
    // registry extras must now be rejected.
    for (int i = 0; i < 2; i++) {
        const char *nm = (i == 0) ? "elim-and" : "nnf";
        Z3_simplifier old_extra = Z3_mk_simplifier(C, nm);
        CHECK_B(old_extra == NULL, 1, "old AY-only simplifier is rejected");
        CHECK_I(Z3_get_error_code(C), Z3_INVALID_ARG,
                "old AY-only simplifier sets INVALID_ARG");
        Z3_string d = Z3_simplifier_get_descr(C, nm);
        CHECK_B(d == NULL, 1, "old AY-only simplifier has no description");
    }

    // Tactic-only control names are NOT simplifiers: honest NULL + error.
    const char *notsimp[] = {"skip", "fail", "split-clause", "cnf"};
    for (int i = 0; i < 4; i++) {
        Z3_simplifier s = Z3_mk_simplifier(C, notsimp[i]);
        CHECK_B(s == NULL, 1, "tactic-only name is not a simplifier");
        CHECK_I(Z3_get_error_code(C), Z3_INVALID_ARG, "tactic-only name INVALID_ARG");
    }

    // get_param_descrs: honest-empty (a REAL size-0 descriptor set, never a fake).
    Z3_param_descrs pd = Z3_simplifier_get_param_descrs(C, comp);
    CHECK_B(pd != NULL, 1, "get_param_descrs non-null");
    if (pd != NULL) {
        Z3_param_descrs_inc_ref(C, pd);
        CHECK_I(Z3_param_descrs_size(C, pd), 0, "param_descrs honest-empty size 0");
        Z3_param_descrs_dec_ref(C, pd);
    }

    // Null operands are honest NULL + Z3_INVALID_ARG (libz3 aborts).
    CHECK_B(Z3_simplifier_and_then(C, comp, NULL) == NULL, 1, "and_then(null)=NULL");
    CHECK_B(Z3_simplifier_using_params(C, NULL, pr) == NULL, 1, "using_params(null)=NULL");
    CHECK_B(Z3_solver_add_simplifier(C, NULL, comp) == NULL, 1, "add_simplifier(null solver)=NULL");
    CHECK_B(Z3_simplifier_get_help(C, NULL) == NULL, 1, "get_help(null)=NULL");
    CHECK_B(Z3_simplifier_get_param_descrs(C, NULL) == NULL, 1, "get_param_descrs(null)=NULL");
    CHECK_B(Z3_mk_simplifier(C, NULL) == NULL, 1, "mk(null name)=NULL");
#endif

    if (g_fail == 0) {
        printf("All %d simplifier C consumer checks passed\n", g_pass);
        return 0;
    }
    printf("%d checks passed, %d FAILED\n", g_pass, g_fail);
    return 1;
}
