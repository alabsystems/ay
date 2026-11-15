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
// runs it before each check-sat. Registry checks validate actual enumeration
// and constructibility without freezing an older release's size or order.
// The core semantic check builds a simplifier
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
#include <stdlib.h>
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
    Z3_ast_vector original = Z3_solver_get_assertions(C, s);
    Z3_ast_vector_inc_ref(C, original);
    int r = Z3_solver_check(C, s);
    if (r == Z3_L_TRUE) {
        Z3_model model = Z3_solver_get_model(C, s);
        CHECK_B(model != NULL, 1, "attached simplifier returns a model");
        if (model) {
            Z3_model_inc_ref(C, model);
            for (unsigned i = 0; i < Z3_ast_vector_size(C, original); ++i) {
                Z3_ast value = NULL;
                int evaluated = Z3_model_eval(C, model,
                    Z3_ast_vector_get(C, original, i), 1, &value);
                CHECK_B(evaluated, 1, "original LIA assertion evaluates");
                if (evaluated)
                    CHECK_I(Z3_get_bool_value(C, value), Z3_L_TRUE,
                            "simplifier model satisfies original LIA input");
            }
            Z3_model_dec_ref(C, model);
        }
    }
    Z3_ast_vector_dec_ref(C, original);
    return r;
}

// Public symbol spelling is DATA, even when it resembles an internal binder.
// A converted model must both evaluate the source constant and print its name.
static void converted_scalar_public_spelling(Z3_simplifier comp) {
    Z3_solver base = Z3_mk_solver(C);
    Z3_solver_inc_ref(C, base);
    Z3_solver s = Z3_solver_add_simplifier(C, base, comp);
    CHECK_B(s != NULL, 1, "public-name converted solver");
    if (!s) return;
    Z3_solver_inc_ref(C, s);
    Z3_sort ints = Z3_mk_int_sort(C);
    Z3_ast x = Z3_mk_const(C, Z3_mk_string_symbol(C, "__db0"), ints);
    Z3_ast three = Z3_mk_int(C, 3, ints);
    Z3_solver_assert(C, s, Z3_mk_eq(C, x, three));
    CHECK_I(Z3_solver_check(C, s), Z3_L_TRUE, "public-name converted SAT");
    Z3_model model = Z3_solver_get_model(C, s);
    CHECK_B(model != NULL, 1, "public-name reconstructed model");
    if (model) {
        Z3_model_inc_ref(C, model);
        Z3_ast value = NULL;
        CHECK_B(Z3_model_eval(C, model, x, 0, &value), 1, "public-name source value");
        if (value) CHECK_B(Z3_is_eq_ast(C, value, three), 1, "public-name value is three");
        const char *text = Z3_model_to_string(C, model);
        CHECK_B(text && strstr(text, "__db0"), 1, "model preserves authored public name");
        CHECK_B(text && !strstr(text, "(:var "), 1, "free name is not a bound-variable term");
        Z3_model_dec_ref(C, model);
    }
    Z3_solver_dec_ref(C, s);
    Z3_solver_dec_ref(C, base);
}

// Solver adapters must consume real reconstructed models. ff2bv exercises
// exact auxiliary adoption; ff-sat exercises the independently checked witness.
static void converted_field_solver_witnesses(void) {
    const char *tactics[] = {"ff2bv", "ff-sat"};
    const char *inputs[] = {
        "(declare-const by_bv (_ FiniteField 7)) (assert (= by_bv #f3m7))",
        "(declare-const by_sat (_ FiniteField 7)) (assert (= by_sat #f3m7))"
    };
    for (unsigned i = 0; i < 2; ++i) {
        Z3_tactic tactic = Z3_mk_tactic(C, tactics[i]);
        CHECK_B(tactic != NULL, 1, "field tactic exists");
        if (!tactic) continue;
        Z3_tactic_inc_ref(C, tactic);
        Z3_solver s = Z3_mk_solver_from_tactic(C, tactic);
        CHECK_B(s != NULL, 1, "field tactic creates solver");
        if (!s) { Z3_tactic_dec_ref(C, tactic); continue; }
        Z3_solver_inc_ref(C, s);
        Z3_solver_from_string(C, s, inputs[i]);
        CHECK_I(Z3_get_error_code(C), Z3_OK, "field source parsed");
        Z3_ast_vector roots = Z3_solver_get_assertions(C, s);
        Z3_ast_vector_inc_ref(C, roots);
        CHECK_I(Z3_solver_check(C, s), Z3_L_TRUE, "field wrapper SAT");
        Z3_model model = Z3_solver_get_model(C, s);
        CHECK_B(model != NULL, 1, "field wrapper reconstructed model");
        if (model) {
            Z3_model_inc_ref(C, model);
            CHECK_I(Z3_model_get_num_consts(C, model), 1,
                    "generated representatives do not leak into source model");
            for (unsigned j = 0; j < Z3_ast_vector_size(C, roots); ++j) {
                Z3_ast value = NULL;
                CHECK_B(Z3_model_eval(C, model, Z3_ast_vector_get(C, roots, j), 0, &value),
                        1, "field original root evaluated");
                if (value) CHECK_I(Z3_get_bool_value(C, value), Z3_L_TRUE,
                                   "field model satisfies actual source root");
            }
            if (Z3_model_get_num_consts(C, model) == 1) {
                Z3_func_decl decl = Z3_model_get_const_decl(C, model, 0);
                Z3_ast member = Z3_mk_app(C, decl, 0, NULL);
                Z3_ast expected = Z3_mk_numeral(C, "3", Z3_get_range(C, decl));
                Z3_ast value = NULL;
                CHECK_B(Z3_model_eval(C, model, member, 0, &value), 1, "source field member read");
                if (value) CHECK_B(Z3_is_eq_ast(C, value, expected), 1,
                                   "source member is actual residue three");
            }
            Z3_model_dec_ref(C, model);
        }
        Z3_ast_vector_dec_ref(C, roots);
        Z3_solver_dec_ref(C, s);
        Z3_tactic_dec_ref(C, tactic);
    }
}

static unsigned occurrences(Z3_ast root, Z3_ast variable) {
    if (Z3_is_eq_ast(C, root, variable)) return 1;
    if (Z3_get_ast_kind(C, root) != Z3_APP_AST) return 0;
    Z3_app app = Z3_to_app(C, root);
    unsigned result = 0;
    for (unsigned i = 0; i < Z3_get_app_num_args(C, app); ++i)
        result += occurrences(Z3_get_app_arg(C, app, i), variable);
    return result;
}

static void field_simplifier_semantics(void) {
    Z3_simplifier simp = S(Z3_mk_simplifier(C, "ff-simplify"));
    CHECK_B(simp != NULL, 1, "native field simplifier exists");
    if (!simp) return;
    Z3_solver base = Z3_mk_solver(C);
    Z3_solver_inc_ref(C, base);
    Z3_solver solver = Z3_solver_add_simplifier(C, base, simp);
    CHECK_B(solver != NULL, 1, "field simplifier attaches");
    if (!solver) return;
    Z3_solver_inc_ref(C, solver);
    Z3_sort field = Z3_mk_finite_field_sort(C, "7");
    Z3_ast x = Z3_mk_const(C, Z3_mk_string_symbol(C, "simp_field_x"), field);
    Z3_ast y = Z3_mk_const(C, Z3_mk_string_symbol(C, "simp_field_y"), field);
    Z3_ast three = Z3_mk_numeral(C, "3", field);
    Z3_ast two = Z3_mk_numeral(C, "2", field);
    Z3_ast six = Z3_mk_numeral(C, "6", field);
    Z3_ast args[2] = {x, y};
    Z3_ast original[2] = {Z3_mk_eq(C, x, three),
        Z3_mk_eq(C, Z3_mk_ff_add(C, 2, args), two)};
    Z3_solver_assert(C, solver, original[0]);
    Z3_solver_assert(C, solver, original[1]);
    CHECK_I(Z3_solver_check(C, solver), Z3_L_TRUE, "field simplifier SAT");
    Z3_ast_vector assertions = Z3_solver_get_assertions(C, solver);
    unsigned uses = 0;
    for (unsigned i = 0; i < Z3_ast_vector_size(C, assertions); ++i)
        uses += occurrences(Z3_ast_vector_get(C, assertions, i), x);
    // Propagation must do real work, but its output order and exact normal
    // form are deliberately unrestricted. Retaining x=3 is valid; upstream
    // may instead eliminate it and reconstruct x in the model.
    CHECK_B(uses < occurrences(original[0], x) + occurrences(original[1], x),
            1, "field definition propagated into arithmetic");
    Z3_model model = Z3_solver_get_model(C, solver);
    CHECK_B(model != NULL, 1, "field simplifier model exists");
    if (model) {
        Z3_model_inc_ref(C, model);
        for (unsigned i = 0; i < 2; ++i) {
            Z3_ast value = NULL;
            int evaluated = Z3_model_eval(C, model, original[i], 1, &value);
            CHECK_B(evaluated, 1, "original field assertion evaluates");
            if (evaluated)
                CHECK_I(Z3_get_bool_value(C, value), Z3_L_TRUE,
                        "returned model satisfies original assertion");
        }
        Z3_model_dec_ref(C, model);
    }
    Z3_solver_push(C, solver);
    Z3_solver_assert(C, solver, Z3_mk_not(C, Z3_mk_eq(C, y, six)));
    CHECK_I(Z3_solver_check(C, solver), Z3_L_FALSE, "field push contradiction");
    Z3_solver_pop(C, solver, 1);
    CHECK_I(Z3_solver_check(C, solver), Z3_L_TRUE, "field pop restores SAT");
    CHECK_I(Z3_ast_vector_size(C, Z3_solver_get_assertions(C, base)), 0,
            "attachment leaves source solver empty");
    Z3_solver_dec_ref(C, solver);
    Z3_solver_dec_ref(C, base);
}

static void attachment_source_contract(Z3_simplifier simp) {
    Z3_solver source = Z3_mk_solver(C);
    Z3_solver_inc_ref(C, source);
    Z3_ast p = Z3_mk_const(C, Z3_mk_string_symbol(C, "attachment_p"),
                          Z3_mk_bool_sort(C));
    Z3_solver_assert(C, source, p);
    CHECK_B(Z3_solver_add_simplifier(C, source, simp) == NULL, 1,
            "populated source rejects attachment");
    CHECK_I(Z3_get_error_code(C), Z3_INVALID_ARG, "populated source error");
    CHECK_I(Z3_solver_check(C, source), Z3_L_TRUE,
            "rejected attachment preserves source");
    Z3_solver_dec_ref(C, source);

    source = Z3_mk_solver(C);
    Z3_solver_inc_ref(C, source);
    Z3_solver_push(C, source);
    Z3_solver attached = Z3_solver_add_simplifier(C, source, simp);
    CHECK_B(attached != NULL, 1, "empty scoped source can be copied");
    if (attached) {
        Z3_solver_inc_ref(C, attached);
        CHECK_I(Z3_solver_get_num_scopes(C, attached), 0,
                "new simplifier solver starts without scopes");
        Z3_solver_dec_ref(C, attached);
    }
    CHECK_I(Z3_solver_get_num_scopes(C, source), 1,
            "attachment preserves source scope");
    Z3_solver_pop(C, source, 1);
    Z3_solver_dec_ref(C, source);
}

int main(void) {
    setbuf(stdout, NULL);
    printf("simplifier consumer library: %s\n", Z3_get_full_version());
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
    converted_scalar_public_spelling(comp);
    converted_field_solver_witnesses();
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

    field_simplifier_semantics();
    attachment_source_contract(simp);

    // ---- Actual registry: unique, described and constructible entries ----
    unsigned int num_simplifiers = Z3_get_num_simplifiers(C);
    CHECK_B(num_simplifiers > 0, 1, "simplifier enumeration is nonempty");
    for (unsigned int i = 0; i < num_simplifiers; i++) {
        Z3_string got = Z3_get_simplifier_name(C, i);
        CHECK_B(got != NULL, 1, "enumerated simplifier name non-null");
        if (got == NULL) break;
        // Z3 may reuse its returned string buffer on the next API call.
        // Retain the observed name before querying other entries or metadata.
        char *name = malloc(strlen(got) + 1);
        CHECK_B(name != NULL, 1, "enumerated name retained");
        if (name == NULL) break;
        strcpy(name, got);
        for (unsigned int j = 0; j < i; ++j)
            CHECK_B(strcmp(name, Z3_get_simplifier_name(C, j)) != 0, 1,
                    "enumerated simplifier names are unique");
        Z3_simplifier entry = Z3_mk_simplifier(C, name);
        CHECK_B(entry != NULL, 1, "enumerated simplifier builds");
        Z3_string entry_descr = Z3_simplifier_get_descr(C, name);
        CHECK_B(entry_descr != NULL && entry_descr[0] != '\0', 1,
                "enumerated simplifier has description");
        free(name);
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
