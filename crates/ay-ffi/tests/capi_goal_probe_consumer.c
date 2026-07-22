// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C consumer for the Z3-compatible Goal + Probe C API (Z3_goal_* / Z3_probe_*).
//
// Builds real goals, reads them back (size/formula/num_exprs/precision/depth/
// is_decided_*/to_string), and applies probes (num-consts, is-qflia, is-qfbv,
// is-propositional, the combinators, ...). Every expected value is the value
// libz3 4.15.4 returns for the SAME goal — so this single source compiles and
// runs against BOTH ay-ffi (default) and libz3 (`-DAY_TWIN_USE_Z3`), and both
// must pass the identical assertions. That is the cross-check: ay's observable
// behavior == libz3's on the supported Goal/Probe surface.
//
// Formulas are chosen so their s-expression rendering is identical in ay and
// libz3 (ay canonicalizes `a > b` to `b < a` and orders `=` operands, both
// semantically identical); goal_to_string is therefore byte-compared only on
// `<`/`+`/`or`/bool/empty/false goals where the two agree exactly.

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

#define CHECK_D(actual, expected, what)                                        \
    do {                                                                       \
        double a_ = (actual);                                                  \
        double e_ = (expected);                                                \
        if (a_ == e_) {                                                        \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s: got %.4f want %.4f\n", (what), a_, e_);           \
        }                                                                      \
    } while (0)

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

#define CHECK_STR(actual, expected, what)                                      \
    do {                                                                       \
        const char *a_ = (actual);                                             \
        const char *e_ = (expected);                                           \
        if (a_ != NULL && strcmp(a_, e_) == 0) {                               \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s:\n  got [%s]\n  want[%s]\n", (what),               \
                   a_ ? a_ : "(null)", e_);                                    \
        }                                                                      \
    } while (0)

static Z3_ast int_var(Z3_context c, const char *n) {
    return Z3_mk_const(c, Z3_mk_string_symbol(c, n), Z3_mk_int_sort(c));
}
static Z3_ast bool_var(Z3_context c, const char *n) {
    return Z3_mk_const(c, Z3_mk_string_symbol(c, n), Z3_mk_bool_sort(c));
}
static Z3_ast bv_var(Z3_context c, const char *n, unsigned w) {
    return Z3_mk_const(c, Z3_mk_string_symbol(c, n), Z3_mk_bv_sort(c, w));
}

// Apply a named probe to a goal, returning its double value.
static double probe(Z3_context c, const char *name, Z3_goal g) {
    Z3_probe p = Z3_mk_probe(c, name);
    Z3_probe_inc_ref(c, p);
    double v = Z3_probe_apply(c, p, g);
    Z3_probe_dec_ref(c, p);
    return v;
}

int main(void) {
    setbuf(stdout, NULL);
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_sort I = Z3_mk_int_sort(c);

    // ---- QF_LIA goal: (< 0 x), (< y 10), (< z (+ x y)) ; 3 int vars ----
    Z3_ast x = int_var(c, "x");
    Z3_ast y = int_var(c, "y");
    Z3_ast z = int_var(c, "z");
    Z3_ast sum_args[2] = {x, y};
    Z3_ast f1 = Z3_mk_lt(c, Z3_mk_int(c, 0, I), x);
    Z3_ast f2 = Z3_mk_lt(c, y, Z3_mk_int(c, 10, I));
    Z3_ast f3 = Z3_mk_lt(c, z, Z3_mk_add(c, 2, sum_args));

    Z3_goal g = Z3_mk_goal(c, false, false, false);
    Z3_goal_inc_ref(c, g);
    Z3_goal_assert(c, g, f1);
    Z3_goal_assert(c, g, f2);
    Z3_goal_assert(c, g, f3);

    // Goal readback.
    CHECK_U(Z3_goal_size(c, g), 3, "lia goal_size");
    CHECK_U(Z3_goal_num_exprs(c, g), 9, "lia goal_num_exprs");
    CHECK_U(Z3_goal_depth(c, g), 0, "lia goal_depth");
    CHECK_U(Z3_goal_precision(c, g), Z3_GOAL_PRECISE, "lia goal_precision");
    CHECK_B(Z3_goal_is_decided_sat(c, g), 0, "lia is_decided_sat");
    CHECK_B(Z3_goal_is_decided_unsat(c, g), 0, "lia is_decided_unsat");
    CHECK_B(Z3_goal_inconsistent(c, g), 0, "lia inconsistent");
    // goal_formula handles are non-null and index the asserted formulas.
    CHECK_B(Z3_goal_formula(c, g, 0) != 0, 1, "lia goal_formula[0] non-null");
    CHECK_B(Z3_goal_formula(c, g, 2) != 0, 1, "lia goal_formula[2] non-null");
    CHECK_STR(Z3_goal_to_string(c, g),
              "(goal\n  (< 0 x)\n  (< y 10)\n  (< z (+ x y)))",
              "lia goal_to_string");

    // Probes over the LIA goal (structural).
    CHECK_D(probe(c, "num-consts", g), 3.0, "lia num-consts");
    CHECK_D(probe(c, "num-exprs", g), 9.0, "lia num-exprs");
    CHECK_D(probe(c, "size", g), 3.0, "lia size");
    CHECK_D(probe(c, "depth", g), 0.0, "lia depth");
    CHECK_D(probe(c, "num-arith-consts", g), 3.0, "lia num-arith-consts");
    CHECK_D(probe(c, "num-bool-consts", g), 0.0, "lia num-bool-consts");
    CHECK_D(probe(c, "num-bv-consts", g), 0.0, "lia num-bv-consts");
    CHECK_D(probe(c, "has-quantifiers", g), 0.0, "lia has-quantifiers");
    // Probes over the LIA goal (fragment classification).
    CHECK_D(probe(c, "is-qflia", g), 1.0, "lia is-qflia");
    CHECK_D(probe(c, "is-qflira", g), 1.0, "lia is-qflira");
    CHECK_D(probe(c, "is-lia", g), 1.0, "lia is-lia");
    CHECK_D(probe(c, "is-qfbv", g), 0.0, "lia is-qfbv");
    CHECK_D(probe(c, "is-qflra", g), 0.0, "lia is-qflra");
    CHECK_D(probe(c, "is-propositional", g), 0.0, "lia is-propositional");
    CHECK_D(probe(c, "is-qfnia", g), 0.0, "lia is-qfnia");
    CHECK_D(probe(c, "is-nia", g), 0.0, "lia is-nia");

    // Probe combinators over the LIA goal.
    Z3_probe pc = Z3_mk_probe(c, "num-consts");
    Z3_probe_inc_ref(c, pc);
    Z3_probe three = Z3_probe_const(c, 3.0);
    Z3_probe_inc_ref(c, three);
    Z3_probe eq = Z3_probe_eq(c, pc, three);
    Z3_probe_inc_ref(c, eq);
    Z3_probe gt = Z3_probe_gt(c, pc, three);
    Z3_probe_inc_ref(c, gt);
    Z3_probe le = Z3_probe_le(c, pc, three);
    Z3_probe_inc_ref(c, le);
    Z3_probe qflia = Z3_mk_probe(c, "is-qflia");
    Z3_probe_inc_ref(c, qflia);
    Z3_probe both = Z3_probe_and(c, eq, qflia);
    Z3_probe_inc_ref(c, both);
    Z3_probe notq = Z3_probe_not(c, qflia);
    Z3_probe_inc_ref(c, notq);
    Z3_probe either = Z3_probe_or(c, gt, qflia);
    Z3_probe_inc_ref(c, either);
    CHECK_D(Z3_probe_apply(c, eq, g), 1.0, "num-consts == 3");
    CHECK_D(Z3_probe_apply(c, gt, g), 0.0, "num-consts > 3");
    CHECK_D(Z3_probe_apply(c, le, g), 1.0, "num-consts <= 3");
    CHECK_D(Z3_probe_apply(c, both, g), 1.0, "(num-consts==3) and is-qflia");
    CHECK_D(Z3_probe_apply(c, notq, g), 0.0, "not is-qflia");
    CHECK_D(Z3_probe_apply(c, either, g), 1.0, "(num-consts>3) or is-qflia");
    CHECK_D(Z3_probe_apply(c, three, g), 3.0, "const 3");

    // ---- Bool (propositional) goal: (or a b), a ----
    Z3_ast a = bool_var(c, "a");
    Z3_ast b = bool_var(c, "b");
    Z3_ast or_args[2] = {a, b};
    Z3_goal gb = Z3_mk_goal(c, false, false, false);
    Z3_goal_inc_ref(c, gb);
    Z3_goal_assert(c, gb, Z3_mk_or(c, 2, or_args));
    Z3_goal_assert(c, gb, a);
    CHECK_U(Z3_goal_size(c, gb), 2, "bool goal_size");
    CHECK_U(Z3_goal_num_exprs(c, gb), 3, "bool goal_num_exprs");
    CHECK_D(probe(c, "num-consts", gb), 0.0, "bool num-consts");
    CHECK_D(probe(c, "num-bool-consts", gb), 2.0, "bool num-bool-consts");
    CHECK_D(probe(c, "is-propositional", gb), 1.0, "bool is-propositional");
    CHECK_D(probe(c, "is-qflia", gb), 1.0, "bool is-qflia (prop subset)");
    CHECK_D(probe(c, "is-qfbv", gb), 1.0, "bool is-qfbv (prop subset)");
    CHECK_STR(Z3_goal_to_string(c, gb), "(goal\n  (or a b)\n  a)",
              "bool goal_to_string");

    // ---- Empty goal ----
    Z3_goal ge = Z3_mk_goal(c, false, false, false);
    Z3_goal_inc_ref(c, ge);
    CHECK_U(Z3_goal_size(c, ge), 0, "empty goal_size");
    CHECK_U(Z3_goal_num_exprs(c, ge), 0, "empty goal_num_exprs");
    CHECK_B(Z3_goal_is_decided_sat(c, ge), 1, "empty is_decided_sat");
    CHECK_B(Z3_goal_is_decided_unsat(c, ge), 0, "empty is_decided_unsat");
    CHECK_STR(Z3_goal_to_string(c, ge), "(goal)", "empty goal_to_string");

    // ---- False goal ----
    Z3_goal gf = Z3_mk_goal(c, false, false, false);
    Z3_goal_inc_ref(c, gf);
    Z3_goal_assert(c, gf, Z3_mk_false(c));
    CHECK_U(Z3_goal_size(c, gf), 1, "false goal_size");
    CHECK_B(Z3_goal_inconsistent(c, gf), 1, "false inconsistent");
    CHECK_B(Z3_goal_is_decided_unsat(c, gf), 1, "false is_decided_unsat");
    CHECK_B(Z3_goal_is_decided_sat(c, gf), 0, "false is_decided_sat");
    CHECK_STR(Z3_goal_to_string(c, gf), "(goal\n  false)", "false goal_to_string");

    // ---- QF_BV goal: (= (bvadd x8 y8) 3) ----
    Z3_ast bx = bv_var(c, "bx", 8);
    Z3_ast by = bv_var(c, "by", 8);
    Z3_ast bthree = Z3_mk_unsigned_int(c, 3, Z3_mk_bv_sort(c, 8));
    Z3_goal gbv = Z3_mk_goal(c, false, false, false);
    Z3_goal_inc_ref(c, gbv);
    Z3_goal_assert(c, gbv, Z3_mk_eq(c, Z3_mk_bvadd(c, bx, by), bthree));
    CHECK_D(probe(c, "is-qfbv", gbv), 1.0, "bv is-qfbv");
    CHECK_D(probe(c, "is-qflia", gbv), 0.0, "bv is-qflia");
    CHECK_D(probe(c, "num-bv-consts", gbv), 2.0, "bv num-bv-consts");
    CHECK_D(probe(c, "num-consts", gbv), 2.0, "bv num-consts");
    CHECK_D(probe(c, "num-arith-consts", gbv), 0.0, "bv num-arith-consts");

    // ---- QF_NIA goal: (< 0 (* x y)) ----
    Z3_ast mul_args[2] = {x, y};
    Z3_goal gnl = Z3_mk_goal(c, false, false, false);
    Z3_goal_inc_ref(c, gnl);
    Z3_goal_assert(c, gnl, Z3_mk_lt(c, Z3_mk_int(c, 0, I), Z3_mk_mul(c, 2, mul_args)));
    CHECK_D(probe(c, "is-qfnia", gnl), 1.0, "nl is-qfnia");
    CHECK_D(probe(c, "is-nia", gnl), 1.0, "nl is-nia");
    CHECK_D(probe(c, "is-qflia", gnl), 0.0, "nl is-qflia");
    CHECK_D(probe(c, "is-qfnra", gnl), 0.0, "nl is-qfnra");

    // ---- Probe introspection + honest unsupported-name handling ----
    // Cross-checkable in both engines: a real probe name has a description and a
    // non-null name at index 0.
    CHECK_B(Z3_get_probe_name(c, 0) != NULL, 1, "get_probe_name[0] non-null");
    CHECK_B(Z3_probe_get_descr(c, "is-qflia") != NULL, 1, "descr(is-qflia)");
#ifndef AY_TWIN_USE_Z3
    // AY-specific: it implements the full 42-probe z3 4.15.4 registry and
    // HONESTLY returns NULL for an unknown probe name (never a fake probe;
    // libz3 aborts via its default error handler instead — so these are
    // exercised only in ay).
    CHECK_U(Z3_get_num_probes(c), 42, "get_num_probes (full z3 registry)");
    CHECK_B(Z3_mk_probe(c, "arith-max-deg") != NULL, 1,
            "arith-max-deg probe implemented");
    CHECK_B(Z3_mk_probe(c, "not-a-probe") == NULL, 1, "bogus probe -> NULL");
#endif

    // ---- Z3_goal_translate (cross-context): deep-copy g from c into c2 ----
    Z3_config cfg2 = Z3_mk_config();
    Z3_context c2 = Z3_mk_context(cfg2);
    Z3_del_config(cfg2);
    Z3_goal gt2 = Z3_goal_translate(c, g, c2);
    CHECK_B(gt2 != NULL, 1, "translate non-null");
    CHECK_U(Z3_goal_size(c2, gt2), 3, "translate goal_size");
    CHECK_STR(Z3_goal_to_string(c2, gt2),
              "(goal\n  (< 0 x)\n  (< y 10)\n  (< z (+ x y)))",
              "translate goal_to_string");
#ifndef AY_TWIN_USE_Z3
    // AY evaluates probes over a cross-context-translated goal correctly. (libz3
    // 4.15.4 crashes applying a probe to a translated goal, so this is exercised
    // only in ay — a case where ay is strictly more robust than libz3.)
    CHECK_D(probe(c2, "num-consts", gt2), 3.0, "translate num-consts");
    CHECK_D(probe(c2, "is-qflia", gt2), 1.0, "translate is-qflia");
#endif

    // ---- Z3_goal_convert_model: identity conversion returns a real model ----
    // AY-only: a goal built via Z3_mk_goal carries the IDENTITY model converter,
    // so converting a model of its formulas returns that real model. (libz3
    // 4.15.4 dereferences a null converter and crashes on a plain goal, so this
    // is exercised only in ay.)
#ifndef AY_TWIN_USE_Z3
    Z3_solver solver = Z3_mk_solver(c);
    Z3_solver_assert(c, solver, f1);
    Z3_solver_assert(c, solver, f2);
    if (Z3_solver_check(c, solver) == Z3_L_TRUE) {
        Z3_model m = Z3_solver_get_model(c, solver);
        Z3_model cm = Z3_goal_convert_model(c, g, m);
        CHECK_B(cm != NULL, 1, "convert_model non-null");
        CHECK_B(Z3_model_to_string(c, cm) != NULL, 1, "convert_model to_string");
    } else {
        g_fail++;
        printf("FAIL convert_model: goal unexpectedly not SAT\n");
    }
#endif

    if (g_fail == 0) {
        printf("All %d goal/probe C consumer checks passed\n", g_pass);
        return 0;
    }
    printf("%d checks passed, %d FAILED\n", g_pass, g_fail);
    return 1;
}
