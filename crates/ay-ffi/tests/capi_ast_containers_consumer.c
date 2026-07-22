// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C consumer for the Z3-compatible AST-container C API: the Z3_ast_map_* family
// plus the Z3_ast_vector_to_string / Z3_ast_vector_translate completions.
//
// Builds a real ast_map (insert 3 key->value pairs; check contains/find/size/
// keys; erase one; reset), renders map + vector to_string, and translates a
// vector into a fresh context. Every expected value/string is what libz3 4.15.4
// returns for the SAME container, so this single source compiles and runs
// against BOTH ay-ffi (default) and libz3 (`-DAY_TWIN_USE_Z3`), and both must
// pass the identical assertions. That is the cross-check: ay's observable
// behavior == libz3's on the supported AST-container surface.
//
// Order-sensitive surfaces are cross-checked robustly: a *vector*'s element
// order is deterministic (push order) in both engines, so its to_string is
// byte-compared. A *map*'s key iteration order is hash-table-dependent (and thus
// unspecified) in libz3, so multi-entry maps are checked by size + membership +
// find + to_string *shape*, while a single-entry map (order-irrelevant) is
// byte-compared exactly.

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

static Z3_ast int_var(Z3_context c, const char *n) {
    return Z3_mk_const(c, Z3_mk_string_symbol(c, n), Z3_mk_int_sort(c));
}

// Return 1 iff the AST vector contains handle `k` (order-independent).
static int vec_contains(Z3_context c, Z3_ast_vector v, Z3_ast k) {
    unsigned n = Z3_ast_vector_size(c, v);
    for (unsigned i = 0; i < n; i++) {
        if (Z3_ast_vector_get(c, v, i) == k) {
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
    Z3_sort I = Z3_mk_int_sort(c);

    Z3_ast x = int_var(c, "x");
    Z3_ast y = int_var(c, "y");
    Z3_ast z = int_var(c, "z");
    Z3_ast w = int_var(c, "w"); // never inserted
    Z3_ast one = Z3_mk_int(c, 1, I);
    Z3_ast two = Z3_mk_int(c, 2, I);
    Z3_ast three = Z3_mk_int(c, 3, I);

    // ---- AST map: build, read, erase, reset ----
    Z3_ast_map m = Z3_mk_ast_map(c);
    Z3_ast_map_inc_ref(c, m);
    CHECK_B(m != NULL, 1, "mk_ast_map non-null");
    CHECK_U(Z3_ast_map_size(c, m), 0, "fresh map size 0");
    CHECK_STR(Z3_ast_map_to_string(c, m), "(ast-map)", "empty map to_string");

    // Insert 3 key -> value pairs.
    Z3_ast_map_insert(c, m, x, one);
    Z3_ast_map_insert(c, m, y, two);
    Z3_ast_map_insert(c, m, z, three);
    CHECK_U(Z3_ast_map_size(c, m), 3, "size after 3 inserts");

    // contains / find return the REAL stored values.
    CHECK_B(Z3_ast_map_contains(c, m, x), 1, "contains x");
    CHECK_B(Z3_ast_map_contains(c, m, y), 1, "contains y");
    CHECK_B(Z3_ast_map_contains(c, m, z), 1, "contains z");
    CHECK_B(Z3_ast_map_contains(c, m, w), 0, "contains w (never inserted)");
    CHECK_B(Z3_ast_map_find(c, m, x) == one, 1, "find x == 1");
    CHECK_B(Z3_ast_map_find(c, m, y) == two, 1, "find y == 2");
    CHECK_B(Z3_ast_map_find(c, m, z) == three, 1, "find z == 3");

    // Re-insert an existing key replaces the value and keeps size.
    Z3_ast_map_insert(c, m, x, three);
    CHECK_U(Z3_ast_map_size(c, m), 3, "re-insert keeps size");
    CHECK_B(Z3_ast_map_find(c, m, x) == three, 1, "re-insert replaces value");

    // keys() is a real vector containing exactly the 3 keys (order unspecified
    // in libz3, so check membership + size, not index).
    Z3_ast_vector keys = Z3_ast_map_keys(c, m);
    Z3_ast_vector_inc_ref(c, keys);
    CHECK_U(Z3_ast_vector_size(c, keys), 3, "keys size");
    CHECK_B(vec_contains(c, keys, x), 1, "keys contains x");
    CHECK_B(vec_contains(c, keys, y), 1, "keys contains y");
    CHECK_B(vec_contains(c, keys, z), 1, "keys contains z");
    CHECK_B(vec_contains(c, keys, w), 0, "keys excludes w");

    // Multi-entry to_string: shape only (starts with "(ast-map"); the exact
    // per-line order is hash-dependent in libz3.
    const char *ms = Z3_ast_map_to_string(c, m);
    CHECK_B(ms != NULL && strncmp(ms, "(ast-map", 8) == 0, 1, "map to_string shape");

    // Erase one key: size drops, contains=false, others survive.
    Z3_ast_map_erase(c, m, y);
    CHECK_U(Z3_ast_map_size(c, m), 2, "size after erase");
    CHECK_B(Z3_ast_map_contains(c, m, y), 0, "erased key absent");
    CHECK_B(Z3_ast_map_contains(c, m, x), 1, "x survives erase");
    CHECK_B(Z3_ast_map_contains(c, m, z), 1, "z survives erase");

    // Reset: empty again.
    Z3_ast_map_reset(c, m);
    CHECK_U(Z3_ast_map_size(c, m), 0, "size after reset");
    CHECK_B(Z3_ast_map_contains(c, m, x), 0, "no keys after reset");

    // Single-entry map: byte-exact to_string (order-irrelevant, both engines).
    Z3_ast_map sm = Z3_mk_ast_map(c);
    Z3_ast_map_inc_ref(c, sm);
    Z3_ast_map_insert(c, sm, x, three);
    CHECK_STR(Z3_ast_map_to_string(c, sm), "(ast-map\n  (x\n   3))",
              "single-entry map to_string");

    // ---- AST vector: to_string (deterministic push order) ----
    Z3_ast_vector ev = Z3_mk_ast_vector(c);
    Z3_ast_vector_inc_ref(c, ev);
    CHECK_STR(Z3_ast_vector_to_string(c, ev), "(ast-vector)",
              "empty vector to_string");

    Z3_ast_vector v = Z3_mk_ast_vector(c);
    Z3_ast_vector_inc_ref(c, v);
    Z3_ast_vector_push(c, v, x);
    Z3_ast_vector_push(c, v, y);
    Z3_ast_vector_push(c, v, Z3_mk_lt(c, x, y));
    CHECK_U(Z3_ast_vector_size(c, v), 3, "vector size 3");
    CHECK_STR(Z3_ast_vector_to_string(c, v), "(ast-vector\n  x\n  y\n  (< x y))",
              "vector to_string");

    // ---- Z3_ast_vector_translate: same context is a real copy ----
    Z3_ast_vector vc = Z3_ast_vector_translate(c, v, c);
    Z3_ast_vector_inc_ref(c, vc);
    CHECK_B(vc != NULL, 1, "same-ctx translate non-null");
    CHECK_U(Z3_ast_vector_size(c, vc), 3, "same-ctx translate size");
    CHECK_B(Z3_ast_vector_get(c, vc, 0) == x, 1, "same-ctx translate[0]==x");
    CHECK_B(Z3_ast_vector_get(c, vc, 1) == y, 1, "same-ctx translate[1]==y");

    // ---- Z3_ast_vector_translate: cross context deep-copies the DAG ----
    Z3_config cfg2 = Z3_mk_config();
    Z3_context c2 = Z3_mk_context(cfg2);
    Z3_del_config(cfg2);
    Z3_ast_vector tv = Z3_ast_vector_translate(c, v, c2);
    Z3_ast_vector_inc_ref(c2, tv);
    CHECK_B(tv != NULL, 1, "cross-ctx translate non-null");
    CHECK_U(Z3_ast_vector_size(c2, tv), 3, "cross-ctx translate size");
    // Translated elements are re-readable in c2 and render identically.
    CHECK_STR(Z3_ast_to_string(c2, Z3_ast_vector_get(c2, tv, 0)), "x",
              "translated[0] renders x");
    CHECK_STR(Z3_ast_to_string(c2, Z3_ast_vector_get(c2, tv, 2)), "(< x y)",
              "translated[2] renders (< x y)");
    CHECK_STR(Z3_ast_vector_to_string(c2, tv),
              "(ast-vector\n  x\n  y\n  (< x y))",
              "translated vector to_string");

#ifndef AY_TWIN_USE_Z3
    // AY-only: find on an ABSENT key returns the null AST 0 and records
    // Z3_INVALID_ARG (honest — never a fabricated value). libz3's default error
    // handler ABORTS the process on this case, so it is exercised only in ay
    // (where ay is strictly more robust than libz3).
    Z3_ast_map am = Z3_mk_ast_map(c);
    Z3_ast_map_inc_ref(c, am);
    Z3_ast_map_insert(c, am, x, one);
    CHECK_B(Z3_ast_map_find(c, am, y) == 0, 1, "find absent key -> 0");
    CHECK_U(Z3_get_error_code(c), Z3_INVALID_ARG, "absent find sets INVALID_ARG");
#endif

    if (g_fail == 0) {
        printf("All %d ast-containers C consumer checks passed\n", g_pass);
        return 0;
    }
    printf("%d checks passed, %d FAILED\n", g_pass, g_fail);
    return 1;
}
