// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C consumer for the Z3-compatible solver-completion C API (wave 2):
//   Z3_solver_assert_and_track, Z3_solver_get_unsat_core (tracked cores),
//   Z3_solver_from_string / Z3_solver_from_file, Z3_solver_translate,
//   Z3_solver_get_consequences, Z3_solver_get_units / _non_units / _trail,
//   Z3_solver_get_help, Z3_solver_congruence_root / _next,
//   Z3_solver_to_dimacs_string.
//
// This single source compiles and runs against BOTH ay-ffi (default) and libz3
// 4.15.4 (`-DAY_TWIN_USE_Z3`). Every non-guarded assertion is a value that libz3
// itself returns for the SAME input (verified out-of-band), so passing on both
// engines is the cross-check: ay's observable behavior == libz3's on the
// supported surface. Blocks guarded by `#ifndef AY_TWIN_USE_Z3` are AY-specific
// (documented honest divergences: consequence terms are pre-simplified, the
// congruence ring is a singleton, DIMACS is the propositional skeleton, and the
// trail is the level-0 portion — each SOUND and never fabricated).

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

static Z3_ast bool_var(Z3_context c, const char *n) {
    return Z3_mk_const(c, Z3_mk_string_symbol(c, n), Z3_mk_bool_sort(c));
}
static Z3_ast int_var(Z3_context c, const char *n) {
    return Z3_mk_const(c, Z3_mk_string_symbol(c, n), Z3_mk_int_sort(c));
}

// Whether an ast_vector contains an element whose to_string equals `needle`.
static int vec_contains_str(Z3_context c, Z3_ast_vector v, const char *needle) {
    unsigned n = Z3_ast_vector_size(c, v);
    for (unsigned i = 0; i < n; i++) {
        const char *s = Z3_ast_to_string(c, Z3_ast_vector_get(c, v, i));
        if (s && strcmp(s, needle) == 0) {
            return 1;
        }
    }
    return 0;
}

// Whether the concatenation of an ast_vector's element strings contains `needle`.
static int vec_any_substr(Z3_context c, Z3_ast_vector v, const char *needle) {
    unsigned n = Z3_ast_vector_size(c, v);
    for (unsigned i = 0; i < n; i++) {
        const char *s = Z3_ast_to_string(c, Z3_ast_vector_get(c, v, i));
        if (s && strstr(s, needle) != NULL) {
            return 1;
        }
    }
    return 0;
}

int main(void) {
    setbuf(stdout, NULL);
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // ---- 1. assert_and_track: build an UNSAT core from tracking literals ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast a = bool_var(c, "a");
        Z3_ast p1 = bool_var(c, "p1");
        Z3_ast p2 = bool_var(c, "p2");
        Z3_solver_assert_and_track(c, s, a, p1);              // track a  by p1
        Z3_solver_assert_and_track(c, s, Z3_mk_not(c, a), p2); // track !a by p2
        CHECK_U(Z3_solver_check(c, s), (unsigned)Z3_L_FALSE, "track: check UNSAT");
        Z3_ast_vector core = Z3_solver_get_unsat_core(c, s);
        Z3_ast_vector_inc_ref(c, core);
        CHECK_U(Z3_ast_vector_size(c, core), 2, "track: core size");
        CHECK_B(vec_contains_str(c, core, "p1"), 1, "track: core has p1");
        CHECK_B(vec_contains_str(c, core, "p2"), 1, "track: core has p2");
        Z3_ast_vector_dec_ref(c, core);
        Z3_solver_dec_ref(c, s);
    }

    // ---- 2. from_string: parse+append, then solve ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast x = int_var(c, "x");
        Z3_solver_assert(c, s, Z3_mk_eq(c, x, Z3_mk_int(c, 5, Z3_mk_int_sort(c))));
        Z3_solver_from_string(c, s, "(declare-const y Int)(assert (= y 7))");
        Z3_ast_vector av = Z3_solver_get_assertions(c, s);
        Z3_ast_vector_inc_ref(c, av);
        CHECK_U(Z3_ast_vector_size(c, av), 2, "from_string: appended assertions");
        CHECK_U(Z3_solver_check(c, s), (unsigned)Z3_L_TRUE, "from_string: SAT");
        Z3_ast_vector_dec_ref(c, av);
        Z3_solver_dec_ref(c, s);
    }

    // ---- 2b. from_string that is UNSAT ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_from_string(
            c, s, "(declare-const z Int)(assert (> z 10))(assert (< z 3))");
        CHECK_U(Z3_solver_check(c, s), (unsigned)Z3_L_FALSE, "from_string: UNSAT");
        Z3_solver_dec_ref(c, s);
    }

    // ---- 3. from_file: write a temp SMT-LIB2 file, load it, solve ----
    {
        const char *path = "/tmp/ay_capi_solver_completion.smt2";
        FILE *f = fopen(path, "w");
        if (f) {
            fputs("(declare-const w Int)\n(assert (= w 42))\n", f);
            fclose(f);
            Z3_solver s = Z3_mk_solver(c);
            Z3_solver_inc_ref(c, s);
            Z3_solver_from_file(c, s, path);
            Z3_ast_vector av = Z3_solver_get_assertions(c, s);
            Z3_ast_vector_inc_ref(c, av);
            CHECK_U(Z3_ast_vector_size(c, av), 1, "from_file: one assertion");
            CHECK_U(Z3_solver_check(c, s), (unsigned)Z3_L_TRUE, "from_file: SAT");
            Z3_ast_vector_dec_ref(c, av);
            Z3_solver_dec_ref(c, s);
        } else {
            g_fail++;
            printf("FAIL from_file: could not create temp file\n");
        }
    }

    // ---- 4. translate: copy a solver into a fresh context and re-solve ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast x = int_var(c, "tx");
        Z3_solver_assert(c, s, Z3_mk_gt(c, x, Z3_mk_int(c, 0, Z3_mk_int_sort(c))));
        Z3_solver_assert(c, s, Z3_mk_lt(c, x, Z3_mk_int(c, 5, Z3_mk_int_sort(c))));

        Z3_config cfg2 = Z3_mk_config();
        Z3_context c2 = Z3_mk_context(cfg2);
        Z3_del_config(cfg2);
        Z3_solver s2 = Z3_solver_translate(c, s, c2);
        CHECK_B(s2 != NULL, 1, "translate: non-null handle");
        Z3_solver_inc_ref(c2, s2);
        Z3_ast_vector av2 = Z3_solver_get_assertions(c2, s2);
        Z3_ast_vector_inc_ref(c2, av2);
        CHECK_U(Z3_ast_vector_size(c2, av2), 2, "translate: copied assertions");
        CHECK_U(Z3_solver_check(c2, s2), (unsigned)Z3_L_TRUE, "translate: re-solve SAT");
        Z3_ast_vector_dec_ref(c2, av2);
        Z3_solver_dec_ref(c2, s2);
        Z3_solver_dec_ref(c, s);
        Z3_del_context(c2);
    }

    // ---- 5. get_consequences: va asserted true, va=>vb; vd free ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast va = bool_var(c, "va");
        Z3_ast vb = bool_var(c, "vb");
        Z3_ast vd = bool_var(c, "vd");
        Z3_solver_assert(c, s, va);
        Z3_solver_assert(c, s, Z3_mk_implies(c, va, vb));
        Z3_ast_vector assumptions = Z3_mk_ast_vector(c);
        Z3_ast_vector_inc_ref(c, assumptions);
        Z3_ast_vector vars = Z3_mk_ast_vector(c);
        Z3_ast_vector_inc_ref(c, vars);
        Z3_ast_vector_push(c, vars, va);
        Z3_ast_vector_push(c, vars, vb);
        Z3_ast_vector_push(c, vars, vd);
        Z3_ast_vector cons = Z3_mk_ast_vector(c);
        Z3_ast_vector_inc_ref(c, cons);
        CHECK_U(Z3_solver_get_consequences(c, s, assumptions, vars, cons),
                (unsigned)Z3_L_TRUE, "consequences: L_TRUE");
        CHECK_U(Z3_ast_vector_size(c, cons), 2, "consequences: two forced vars");
        // va and vb are the forced consequents (vd stays free). Both engines
        // mention them; libz3 renders "(=> true va)", ay pre-simplifies to "va".
        CHECK_B(vec_any_substr(c, cons, "va"), 1, "consequences: mentions va");
        CHECK_B(vec_any_substr(c, cons, "vb"), 1, "consequences: mentions vb");
        CHECK_B(vec_any_substr(c, cons, "vd"), 0, "consequences: vd not forced");
        Z3_ast_vector_dec_ref(c, cons);
        Z3_ast_vector_dec_ref(c, vars);
        Z3_ast_vector_dec_ref(c, assumptions);
        Z3_solver_dec_ref(c, s);
    }

    // ---- 5b. get_consequences under a contradictory assumption -> L_FALSE ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast ca = bool_var(c, "ca");
        Z3_solver_assert(c, s, ca);
        Z3_ast_vector assumptions = Z3_mk_ast_vector(c);
        Z3_ast_vector_inc_ref(c, assumptions);
        Z3_ast_vector_push(c, assumptions, Z3_mk_not(c, ca)); // contradicts ca
        Z3_ast_vector vars = Z3_mk_ast_vector(c);
        Z3_ast_vector_inc_ref(c, vars);
        Z3_ast_vector_push(c, vars, ca);
        Z3_ast_vector cons = Z3_mk_ast_vector(c);
        Z3_ast_vector_inc_ref(c, cons);
        CHECK_U(Z3_solver_get_consequences(c, s, assumptions, vars, cons),
                (unsigned)Z3_L_FALSE, "consequences: UNSAT -> L_FALSE");
        Z3_ast_vector_dec_ref(c, cons);
        Z3_ast_vector_dec_ref(c, vars);
        Z3_ast_vector_dec_ref(c, assumptions);
        Z3_solver_dec_ref(c, s);
    }

    // ---- 6. units / non_units: literals vs compound ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast pp = bool_var(c, "pp");
        Z3_ast qq = bool_var(c, "qq");
        Z3_ast rr = bool_var(c, "rr");
        Z3_ast oq[2] = {qq, rr};
        Z3_solver_assert(c, s, pp);                  // unit
        Z3_solver_assert(c, s, Z3_mk_not(c, qq));    // unit (negated atom)
        Z3_solver_assert(c, s, Z3_mk_or(c, 2, oq));  // non-unit (or)
        Z3_ast_vector u = Z3_solver_get_units(c, s);
        Z3_ast_vector_inc_ref(c, u);
        Z3_ast_vector nu = Z3_solver_get_non_units(c, s);
        Z3_ast_vector_inc_ref(c, nu);
        CHECK_U(Z3_ast_vector_size(c, u), 2, "units: size");
        CHECK_U(Z3_ast_vector_size(c, nu), 1, "non_units: size");
        CHECK_B(vec_contains_str(c, u, "pp"), 1, "units: has pp");
        CHECK_B(vec_contains_str(c, u, "(not qq)"), 1, "units: has (not qq)");
        Z3_ast_vector_dec_ref(c, nu);
        Z3_ast_vector_dec_ref(c, u);

#ifndef AY_TWIN_USE_Z3
        // AY-only: get_trail exposes the level-0 trail (= the input units).
        // (libz3's get_trail after inprocessing/checks is a superset that
        // depends on solver internals, so it is not byte-comparable here.)
        Z3_ast_vector tr = Z3_solver_get_trail(c, s);
        Z3_ast_vector_inc_ref(c, tr);
        CHECK_U(Z3_ast_vector_size(c, tr), 2, "trail: level-0 units");
        Z3_ast_vector_dec_ref(c, tr);
#endif
        Z3_solver_dec_ref(c, s);
    }

    // ---- 7. get_help: real, non-empty parameter description ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_string help = Z3_solver_get_help(c, s);
        CHECK_B(help != NULL && help[0] != '\0', 1, "help: non-empty");
        Z3_solver_dec_ref(c, s);
    }

#ifndef AY_TWIN_USE_Z3
    // ---- 8. congruence (AY honest singleton class) ----
    // AY models each term as its own congruence class, so root(a)==a and
    // next(a)==a (a one-element cyclic list). SOUND: it never claims two
    // distinct terms are congruent when they are not. (libz3's congruence ring
    // exposes real e-graph representatives that depend on the completed search
    // state, so this is verified only in ay.)
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast g = bool_var(c, "g");
        Z3_solver_assert(c, s, g);
        Z3_solver_check(c, s);
        CHECK_B(Z3_solver_congruence_root(c, s, g) == g, 1, "congruence: root(g)==g");
        CHECK_B(Z3_solver_congruence_next(c, s, g) == g, 1, "congruence: next(g)==g");
        Z3_solver_dec_ref(c, s);
    }

    // ---- 9. to_dimacs_string (AY propositional skeleton) ----
    // Assert two unit literals `da` and `(not db)`. da -> var 1, db -> var 2.
    // The Tseitin CNF is exactly two unit clauses. (libz3 bit-blasts and uses a
    // different numbering, so the exact string is verified only in ay.)
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast da = bool_var(c, "da");
        Z3_ast db = bool_var(c, "db");
        Z3_solver_assert(c, s, da);
        Z3_solver_assert(c, s, Z3_mk_not(c, db));
        Z3_string d = Z3_solver_to_dimacs_string(c, s, false);
        CHECK_B(d != NULL, 1, "dimacs: non-null");
        CHECK_B(strstr(d, "p cnf 2 2") != NULL, 1, "dimacs: header p cnf 2 2");
        CHECK_B(strstr(d, "1 0") != NULL, 1, "dimacs: unit clause 1 0");
        CHECK_B(strstr(d, "-2 0") != NULL, 1, "dimacs: unit clause -2 0");
        // include_names emits a mapping comment naming the atoms.
        Z3_string dn = Z3_solver_to_dimacs_string(c, s, true);
        CHECK_B(dn != NULL && strstr(dn, "da") != NULL, 1, "dimacs: names da");
        Z3_solver_dec_ref(c, s);
    }
#endif

    Z3_del_context(c);

    if (g_fail == 0) {
        printf("All %d solver-completion consumer tests passed\n", g_pass);
        return 0;
    }
    printf("%d checks passed, %d FAILED\n", g_pass, g_fail);
    return 1;
}
