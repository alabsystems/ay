// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C consumer for the Z3-compatible incremental parser context
// (Z3_mk_parser_context + Z3_parser_context_*) and the curated datatype /
// decl-parameter getters (Z3_get_datatype_sort_num_constructors /
// _constructor / _recognizer / _constructor_accessor, Z3_get_decl_parameter_kind).
//
// Every expected value is the value libz3 4.15.4 returns for the SAME input, so
// this single source compiles and runs against BOTH ay-ffi (default) and libz3
// (`-DAY_TWIN_USE_Z3`), and both must pass the identical assertions. That is the
// cross-check: ay's observable behavior == libz3's on this surface.
//
// Documented divergences (deliberately not byte-compared across the twin):
//   * The datatype RECOGNIZER decl name is `is-<ctor>` in AY (its canonical
//     SMT-LIB form) vs `is` in libz3. Both are arity-1 DT->Bool recognizers, so
//     the shared cross-check verifies arity+range and only that the name starts
//     with "is"; AY's exact `is-<ctor>` spelling is checked ay-only.
//   * Parse-ERROR paths are exercised ay-only: libz3's default error handler on
//     a bad parse is not a portable, assertion-friendly path.

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

// Copy a func_decl's name into `buf` immediately (libz3's Z3_get_symbol_string
// returns a reused buffer; copying keeps two names live at once).
static void decl_name(Z3_context c, Z3_func_decl d, char *buf, size_t n) {
    const char *s = Z3_get_symbol_string(c, Z3_get_decl_name(c, d));
    snprintf(buf, n, "%s", s ? s : "");
}

// --- Datatype introspection: enum Color = red | green | blue --------------
static void test_enum(Z3_context c) {
    const char *names[3] = {"red", "green", "blue"};
    Z3_constructor ctors[3];
    for (int i = 0; i < 3; i++) {
        ctors[i] = Z3_mk_constructor(c, Z3_mk_string_symbol(c, names[i]),
                                     Z3_mk_string_symbol(c, "r"), 0, NULL, NULL,
                                     NULL);
    }
    Z3_sort color = Z3_mk_datatype(c, Z3_mk_string_symbol(c, "Color"), 3, ctors);

    CHECK_U(Z3_get_sort_kind(c, color), Z3_DATATYPE_SORT, "Color sort_kind");
    CHECK_U(Z3_get_datatype_sort_num_constructors(c, color), 3, "Color num_ctors");
    for (unsigned i = 0; i < 3; i++) {
        Z3_func_decl cd = Z3_get_datatype_sort_constructor(c, color, i);
        Z3_func_decl rd = Z3_get_datatype_sort_recognizer(c, color, i);
        char cn[64];
        char rn[64];
        decl_name(c, cd, cn, sizeof cn);
        decl_name(c, rd, rn, sizeof rn);
        CHECK_STR(cn, names[i], "Color ctor name");
        CHECK_U(Z3_get_arity(c, cd), 0, "Color ctor arity");
        CHECK_U(Z3_get_sort_kind(c, Z3_get_range(c, cd)), Z3_DATATYPE_SORT,
                "Color ctor range kind");
        CHECK_U(Z3_get_arity(c, rd), 1, "Color recognizer arity");
        CHECK_U(Z3_get_sort_kind(c, Z3_get_range(c, rd)), Z3_BOOL_SORT,
                "Color recognizer range Bool");
        // Shared cross-check: both AY ("is-red") and libz3 ("is") begin "is".
        CHECK_B(strncmp(rn, "is", 2) == 0, 1, "recognizer name begins is");
#ifndef AY_TWIN_USE_Z3
        // AY-only: exact canonical recognizer spelling.
        char want[64];
        snprintf(want, sizeof want, "is-%s", names[i]);
        CHECK_STR(rn, want, "AY recognizer name is-<ctor>");
#endif
    }

    // The constructor/recognizer func_decls are REAL: build (is-red red) and
    // check it is satisfiable (a genuine datatype term).
    Z3_func_decl red_ctor = Z3_get_datatype_sort_constructor(c, color, 0);
    Z3_func_decl is_red = Z3_get_datatype_sort_recognizer(c, color, 0);
    Z3_ast red_term = Z3_mk_app(c, red_ctor, 0, NULL);
    Z3_ast is_red_app = Z3_mk_app(c, is_red, 1, &red_term);
    Z3_solver s = Z3_mk_solver(c);
    Z3_solver_inc_ref(c, s);
    Z3_solver_assert(c, s, is_red_app);
    CHECK_U(Z3_solver_check(c, s), Z3_L_TRUE, "(is-red red) SAT");
    Z3_solver_dec_ref(c, s);
}

// --- Datatype introspection: struct IntPair = mk(fst:Int, snd:Int) --------
static void test_struct(Z3_context c) {
    Z3_sort I = Z3_mk_int_sort(c);
    Z3_symbol fnames[2] = {Z3_mk_string_symbol(c, "fst"),
                           Z3_mk_string_symbol(c, "snd")};
    Z3_sort fsorts[2] = {I, I};
    unsigned srefs[2] = {0, 0};
    Z3_constructor mk = Z3_mk_constructor(c, Z3_mk_string_symbol(c, "mk"),
                                          Z3_mk_string_symbol(c, "is_mk"), 2,
                                          fnames, fsorts, srefs);
    Z3_constructor arr[1] = {mk};
    Z3_sort pair = Z3_mk_datatype(c, Z3_mk_string_symbol(c, "IntPair"), 1, arr);

    CHECK_U(Z3_get_datatype_sort_num_constructors(c, pair), 1, "IntPair num_ctors");
    Z3_func_decl cd = Z3_get_datatype_sort_constructor(c, pair, 0);
    char cn[64];
    decl_name(c, cd, cn, sizeof cn);
    CHECK_STR(cn, "mk", "IntPair ctor name");
    CHECK_U(Z3_get_arity(c, cd), 2, "IntPair ctor arity");
    CHECK_U(Z3_get_domain_size(c, cd), 2, "IntPair ctor domain size");

    Z3_func_decl a0 = Z3_get_datatype_sort_constructor_accessor(c, pair, 0, 0);
    Z3_func_decl a1 = Z3_get_datatype_sort_constructor_accessor(c, pair, 0, 1);
    char n0[64];
    char n1[64];
    decl_name(c, a0, n0, sizeof n0);
    decl_name(c, a1, n1, sizeof n1);
    CHECK_STR(n0, "fst", "IntPair accessor0 name");
    CHECK_STR(n1, "snd", "IntPair accessor1 name");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_range(c, a0)), Z3_INT_SORT,
            "IntPair accessor0 range Int");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_range(c, a1)), Z3_INT_SORT,
            "IntPair accessor1 range Int");

#ifndef AY_TWIN_USE_Z3
    // AY-only: honest 0 / null on degenerate inputs (never fabricated). These
    // violate libz3's documented preconditions (idx < num_constructors,
    // idx_a < domain_size, t is a datatype), where libz3 raises an error rather
    // than returning a value, so they are not a portable twin assertion target.
    CHECK_U(Z3_get_datatype_sort_num_constructors(c, I), 0, "Int num_ctors 0");
    CHECK_B(Z3_get_datatype_sort_constructor(c, pair, 9) == NULL, 1,
            "OOB constructor null");
    CHECK_B(Z3_get_datatype_sort_constructor_accessor(c, pair, 0, 9) == NULL, 1,
            "OOB accessor null");
#endif
}

// --- Decl parameter kind: (_ extract 5 2) ---------------------------------
static void test_decl_parameter_kind(Z3_context c) {
    Z3_sort bv8 = Z3_mk_bv_sort(c, 8);
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "bx"), bv8);
    Z3_ast ext = Z3_mk_extract(c, 5, 2, x);
    Z3_func_decl d = Z3_get_app_decl(c, Z3_to_app(c, ext));

    CHECK_U(Z3_get_decl_num_parameters(c, d), 2, "extract num_parameters");
    CHECK_U(Z3_get_decl_parameter_kind(c, d, 0), Z3_PARAMETER_INT,
            "extract param0 kind INT");
    CHECK_U(Z3_get_decl_parameter_kind(c, d, 1), Z3_PARAMETER_INT,
            "extract param1 kind INT");
    CHECK_U(Z3_get_decl_int_parameter(c, d, 0), 5, "extract param0 == 5");
    CHECK_U(Z3_get_decl_int_parameter(c, d, 1), 2, "extract param1 == 2");
}

// --- Incremental parser context -------------------------------------------
static void test_parser_context(Z3_context c) {
    Z3_parser_context pc = Z3_mk_parser_context(c);
    Z3_parser_context_inc_ref(c, pc);

    // Inject an uninterpreted sort U and a function f: Int -> Int.
    Z3_sort U = Z3_mk_uninterpreted_sort(c, Z3_mk_string_symbol(c, "U"));
    Z3_parser_context_add_sort(c, pc, U);
    Z3_sort I = Z3_mk_int_sort(c);
    Z3_sort dom[1] = {I};
    Z3_func_decl f =
        Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "f"), 1, dom, I);
    Z3_parser_context_add_decl(c, pc, f);

    // First parse: declares a,b : U ; uses U (via add_sort) and f (via add_decl).
    Z3_ast_vector v1 = Z3_parser_context_from_string(
        c, pc,
        "(declare-const a U)(declare-const b U)"
        "(assert (distinct a b))(assert (= (f 0) 5))");
    Z3_ast_vector_inc_ref(c, v1);
    CHECK_U(Z3_get_error_code(c), Z3_OK, "parse1 ok");
    CHECK_U(Z3_ast_vector_size(c, v1), 2, "parse1 -> 2 assertions");
    // The returned assertion is a real, inspectable APP term in this context.
    CHECK_B(Z3_ast_vector_get(c, v1, 0) != 0, 1, "parse1 assertion non-null");
    CHECK_U(Z3_get_ast_kind(c, Z3_ast_vector_get(c, v1, 0)), Z3_APP_AST,
            "parse1 assertion is app");

    // Second parse: references a,b DECLARED BY THE FIRST parse (incremental
    // symbol table). Declares its own new symbol cc.
    Z3_ast_vector v2 = Z3_parser_context_from_string(
        c, pc, "(declare-const cc U)(assert (or (= cc a) (= cc b)))");
    Z3_ast_vector_inc_ref(c, v2);
    CHECK_U(Z3_get_error_code(c), Z3_OK, "parse2 resolves a,b from parse1");
    CHECK_U(Z3_ast_vector_size(c, v2), 1, "parse2 -> 1 assertion");

    // All collected assertions are jointly satisfiable.
    Z3_solver s = Z3_mk_solver(c);
    Z3_solver_inc_ref(c, s);
    for (unsigned i = 0; i < Z3_ast_vector_size(c, v1); i++)
        Z3_solver_assert(c, s, Z3_ast_vector_get(c, v1, i));
    for (unsigned i = 0; i < Z3_ast_vector_size(c, v2); i++)
        Z3_solver_assert(c, s, Z3_ast_vector_get(c, v2, i));
    CHECK_U(Z3_solver_check(c, s), Z3_L_TRUE, "collected assertions SAT");

    Z3_solver_dec_ref(c, s);
    Z3_ast_vector_dec_ref(c, v1);
    Z3_ast_vector_dec_ref(c, v2);
    Z3_parser_context_dec_ref(c, pc);

#ifndef AY_TWIN_USE_Z3
    // AY-only: honest handling of a malformed parse (empty vector + error), and
    // a null input string. libz3's default parse-error path is not a portable
    // assertion target, so these are checked against ay only.
    Z3_parser_context pc2 = Z3_mk_parser_context(c);
    Z3_ast_vector bad = Z3_parser_context_from_string(c, pc2, NULL);
    CHECK_U(Z3_get_error_code(c), Z3_INVALID_ARG, "null input -> INVALID_ARG");
    CHECK_U(Z3_ast_vector_size(c, bad), 0, "null input -> empty vector");
    Z3_ast_vector bad2 =
        Z3_parser_context_from_string(c, pc2, "(assert (and true false");
    CHECK_B(Z3_get_error_code(c) != Z3_OK, 1, "malformed input -> error");
    CHECK_U(Z3_ast_vector_size(c, bad2), 0, "malformed input -> empty vector");
#endif
}

int main(void) {
    setbuf(stdout, NULL);
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    test_enum(c);
    test_struct(c);
    test_decl_parameter_kind(c);
    test_parser_context(c);

    Z3_del_context(c);

    printf("checks: %d passed, %d failed\n", g_pass, g_fail);
    if (g_fail == 0) {
        printf("parser-context C consumer checks passed\n");
        return 0;
    }
    return 1;
}
