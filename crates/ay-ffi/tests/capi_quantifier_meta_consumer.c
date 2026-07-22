// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C consumer for Group B introspection: quantifier metadata + pattern getters
// + AST depth + tactic/simplifier registry enumerators + as-array:
//
//   Z3_get_quantifier_id / Z3_get_quantifier_skolem_id
//   Z3_get_pattern_num_terms / Z3_get_pattern
//   Z3_get_depth
//   Z3_get_num_tactics / Z3_get_tactic_name
//   Z3_get_num_simplifiers / Z3_get_simplifier_name
//   Z3_is_as_array / Z3_get_as_array_func_decl
//
// The SAME source compiles and runs against BOTH ay-ffi (default) and libz3
// (-DAY_TWIN_USE_Z3 -lz3). Shared assertions (both must pass): pattern
// round-trip of a ForAll-with-pattern (num_patterns / num_terms / the term
// itself via Z3_is_eq_ast), exact Z3_get_depth values on nested ground terms,
// the registry enumerators listing real names including the shared subset
// ("simplify", "nnf", "ctx-solver-simplify" tactics; "solve-eqs",
// "propagate-values" simplifiers) with every enumerated name buildable, and
// Z3_is_as_array(plain const) == false. AY's registry is a documented SUBSET
// of z3's, so counts are NOT compared — only that shared names appear and all
// names are real. AY-only assertions: qid/skolem-id are the HONEST empty
// symbol (AY does not track :qid/:skolemid), and Z3_get_as_array_func_decl is
// an honest NULL + Z3_INVALID_ARG (AY models never emit as-array terms).

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

#define CHECK_B(actual, expected, what) CHECK_I((actual) ? 1 : 0, (expected) ? 1 : 0, what)

#ifdef AY_TWIN_USE_Z3
static void err_handler(Z3_context c, Z3_error_code e) { (void)c; (void)e; }
#else
static void err_handler(Z3_context c, unsigned int e) { (void)c; (void)e; }
#endif

static Z3_context C;

// Does name appear among the first n tactic-registry entries?
static int has_tactic_name(unsigned int n, const char *name) {
    for (unsigned int i = 0; i < n; i++) {
        Z3_string s = Z3_get_tactic_name(C, i);
        if (s != NULL && strcmp(s, name) == 0) return 1;
    }
    return 0;
}

static int has_simplifier_name(unsigned int n, const char *name) {
    for (unsigned int i = 0; i < n; i++) {
        Z3_string s = Z3_get_simplifier_name(C, i);
        if (s != NULL && strcmp(s, name) == 0) return 1;
    }
    return 0;
}

int main(void) {
    setbuf(stdout, NULL);
    Z3_config cfg = Z3_mk_config();
    C = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_set_error_handler(C, err_handler);

    Z3_sort I = Z3_mk_int_sort(C);

    // ---- ForAll x . f(x) = x, with pattern {f(x)} ----
    Z3_func_decl f = Z3_mk_func_decl(C, Z3_mk_string_symbol(C, "f"), 1, &I, I);
    Z3_ast x = Z3_mk_const(C, Z3_mk_string_symbol(C, "x"), I);
    Z3_ast fx = Z3_mk_app(C, f, 1, &x);
    Z3_pattern pat = Z3_mk_pattern(C, 1, &fx);
    CHECK_B(pat != NULL, 1, "mk_pattern non-null");
    Z3_ast body = Z3_mk_eq(C, fx, x);
#ifdef AY_TWIN_USE_Z3
    Z3_app bound[1];
    bound[0] = Z3_to_app(C, x);
#else
    Z3_ast bound[1];
    bound[0] = x;
#endif
    Z3_ast q = Z3_mk_forall_const(C, 0, 1, bound, 1, &pat, body);
    CHECK_B(q != 0, 1, "forall_const built");

    // qid / skolem id: this quantifier was built WITHOUT :qid/:skolemid, so
    // the honest answer is the null symbol — libz3 returns exactly that, and
    // AY (which does not track qid annotations at all) matches byte-for-byte.
    CHECK_B(Z3_get_quantifier_id(C, q) == NULL, 1, "unset qid -> null symbol (== libz3)");
    CHECK_B(Z3_get_quantifier_skolem_id(C, q) == NULL, 1,
            "unset skolem id -> null symbol (== libz3)");

    // Pattern round-trip: 1 pattern, 1 term, and the term IS f(x).
    CHECK_I(Z3_get_quantifier_num_patterns(C, q), 1, "num_patterns == 1");
    Z3_pattern p0 = Z3_get_quantifier_pattern_ast(C, q, 0);
    CHECK_B(p0 != NULL, 1, "pattern_ast(0) non-null");
    CHECK_I(Z3_get_pattern_num_terms(C, p0), 1, "pattern_num_terms == 1");
    Z3_ast pt0 = Z3_get_pattern(C, p0, 0);
    CHECK_B(pt0 != 0, 1, "get_pattern(0) non-null");
#ifdef AY_TWIN_USE_Z3
    // z3's quantifier body/patterns are de-Bruijn-rewritten, so the pattern
    // term is f((:var 0)), not literally f(x); assert it is a unary f-app.
    CHECK_B(Z3_get_app_decl(C, Z3_to_app(C, pt0)) == f, 1, "pattern term head is f");
    CHECK_I(Z3_get_app_num_args(C, Z3_to_app(C, pt0)), 1, "pattern term arity 1");
#else
    CHECK_B(Z3_is_eq_ast(C, pt0, fx), 1, "pattern term == f(x)");
    // Out-of-range pattern term is an honest null AST.
    CHECK_B(Z3_get_pattern(C, p0, 7) == 0, 1, "get_pattern OOB -> 0");
#endif

    // ---- A declared constant is a NULLARY APPLICATION, not a bound variable ----
    // z3 exposes `Z3_mk_const(x)` as Z3_APP_AST with a 0-arity decl; stock z3py
    // depends on this for m[x], x.decl(), children(), ForAll/Exists over consts.
    // AY once reported Z3_VAR_AST and returned NULL from Z3_to_app. Shared check.
    CHECK_I(Z3_get_ast_kind(C, x), Z3_APP_AST, "declared const is Z3_APP_AST");
    CHECK_B(Z3_is_app(C, x), 1, "declared const is_app");
    Z3_app xa = Z3_to_app(C, x);
    CHECK_B(xa != 0, 1, "to_app(const) is non-null");
    CHECK_I(Z3_get_app_num_args(C, xa), 0, "declared const has 0 args");
    Z3_func_decl xd = Z3_get_app_decl(C, xa);
    CHECK_B(xd != 0, 1, "declared const has a decl");
    CHECK_I(Z3_get_arity(C, xd), 0, "declared const decl arity 0");
    // A genuine de-Bruijn bound variable stays Z3_VAR_AST.
    Z3_ast dbvar = Z3_mk_bound(C, 0, I);
    CHECK_I(Z3_get_ast_kind(C, dbvar), Z3_VAR_AST, "bound var is Z3_VAR_AST");

    // ---- Z3_get_depth: exact values, cross-checked on ground terms ----
    Z3_ast y = Z3_mk_const(C, Z3_mk_string_symbol(C, "y"), I);
    Z3_ast two = Z3_mk_int(C, 2, I);
    CHECK_I(Z3_get_depth(C, x), 1, "depth(x) == 1");
    CHECK_I(Z3_get_depth(C, two), 1, "depth(2) == 1");
    Z3_ast mul_args[2] = {two, y};
    Z3_ast two_y = Z3_mk_mul(C, 2, mul_args);      // (* 2 y)         depth 2
    Z3_ast add_args[2] = {x, two_y};
    Z3_ast sum = Z3_mk_add(C, 2, add_args);        // (+ x (* 2 y))   depth 3
    CHECK_I(Z3_get_depth(C, two_y), 2, "depth(2*y) == 2");
    CHECK_I(Z3_get_depth(C, sum), 3, "depth(x + 2*y) == 3");
    Z3_ast nested = Z3_mk_eq(C, sum, fx);          // (= (+ x (* 2 y)) (f x)) depth 4
    CHECK_I(Z3_get_depth(C, nested), 4, "depth(sum = f(x)) == 4");
    CHECK_B(Z3_get_depth(C, q) >= 2, 1, "depth(forall) >= 2");

    // ---- Tactic registry enumeration ----
    unsigned int nt = Z3_get_num_tactics(C);
    CHECK_B(nt > 0, 1, "num_tactics > 0");
    CHECK_B(has_tactic_name(nt, "simplify"), 1, "tactic list has simplify");
    CHECK_B(has_tactic_name(nt, "nnf"), 1, "tactic list has nnf");
    CHECK_B(has_tactic_name(nt, "ctx-solver-simplify"), 1, "tactic list has ctx-solver-simplify");
    CHECK_B(has_tactic_name(nt, "bit-blast"), 1, "tactic list has bit-blast");
    // Every enumerated name is REAL: Z3_mk_tactic accepts it.
    for (unsigned int i = 0; i < nt; i++) {
        Z3_string name = Z3_get_tactic_name(C, i);
        CHECK_B(name != NULL && strlen(name) > 0, 1, "tactic name non-empty");
        if (name != NULL) {
            Z3_tactic t = Z3_mk_tactic(C, name);
            CHECK_B(t != NULL, 1, "enumerated tactic buildable");
            if (t != NULL) Z3_tactic_inc_ref(C, t);
        }
    }
#ifndef AY_TWIN_USE_Z3
    // AY_EXPECTED_TACTICS is injected by the Rust link test straight from
    // ay_frontend::SUPPORTED_TACTIC_NAMES.len(), so this pins "the registry is
    // exactly the shared name list" without a magic number that rots when the
    // list grows (it was hard-coded to 13 and silently drifted to 17).
    CHECK_I(nt, AY_EXPECTED_TACTICS, "AY registry is exactly SUPPORTED_TACTIC_NAMES");
    CHECK_B(Z3_get_tactic_name(C, nt) == NULL, 1, "tactic_name OOB -> NULL");
    CHECK_I(Z3_get_error_code(C), Z3_INVALID_ARG, "tactic_name OOB sets INVALID_ARG");
#endif

    // ---- Simplifier registry enumeration ----
    unsigned int ns = Z3_get_num_simplifiers(C);
    CHECK_B(ns > 0, 1, "num_simplifiers > 0");
    CHECK_B(has_simplifier_name(ns, "solve-eqs"), 1, "simplifier list has solve-eqs");
    CHECK_B(has_simplifier_name(ns, "propagate-values"), 1, "simplifier list has propagate-values");
    for (unsigned int i = 0; i < ns; i++) {
        Z3_string name = Z3_get_simplifier_name(C, i);
        CHECK_B(name != NULL && strlen(name) > 0, 1, "simplifier name non-empty");
        if (name != NULL) {
            Z3_simplifier s = Z3_mk_simplifier(C, name);
            CHECK_B(s != NULL, 1, "enumerated simplifier buildable");
            if (s != NULL) Z3_simplifier_inc_ref(C, s);
        }
    }
#ifndef AY_TWIN_USE_Z3
    // Injected from ay_ffi::z3_compat::SUPPORTED_SIMPLIFIER_NAMES.len(), same
    // anti-drift reason as AY_EXPECTED_TACTICS above.
    CHECK_I(ns, AY_EXPECTED_SIMPLIFIERS,
            "AY registry is exactly SUPPORTED_SIMPLIFIER_NAMES");
    CHECK_B(Z3_get_simplifier_name(C, ns) == NULL, 1, "simplifier_name OOB -> NULL");
    CHECK_I(Z3_get_error_code(C), Z3_INVALID_ARG, "simplifier_name OOB sets INVALID_ARG");
#endif

    // ---- as-array ----
    CHECK_B(Z3_is_as_array(C, x), 0, "plain const is not as-array");
    CHECK_B(Z3_is_as_array(C, sum), 0, "app is not as-array");
#ifndef AY_TWIN_USE_Z3
    // AY never emits as-array model terms; the getter is an honest rejection.
    CHECK_B(Z3_get_as_array_func_decl(C, x) == NULL, 1, "as_array_func_decl honest NULL");
    CHECK_I(Z3_get_error_code(C), Z3_INVALID_ARG, "as_array_func_decl sets INVALID_ARG");
#endif

    Z3_del_context(C);

    if (g_fail == 0) {
        printf("All %d quantifier-meta C consumer checks passed\n", g_pass);
        return 0;
    }
    printf("%d checks passed, %d FAILED\n", g_pass, g_fail);
    return 1;
}
