// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C consumer for the Z3_func_interp_*/Z3_func_entry_* family and the
// model-facing Z3_model_* completion (func_decl / func_interp / translate /
// uninterpreted-sort universes) over ay's REAL models.
//
// Compile against ay:    cc -DUSE_AY   ... -I<ay include> capi_func_interp_consumer.c libay_ffi.a
// Compile against libz3: cc -DUSE_LIBZ3 ... -I/opt/homebrew/include ... -lz3
//
// The SAME calls run against both libraries so the observable behavior can be
// diffed. Function graphs are compared modulo canonicalization: ay and libz3
// pick different (entries, else) encodings of the same finite map, so the
// consumer reconstructs f(x) = <matching entry value, else default> and asserts
// the CONSTRAINED points, never a specific else/entry split.

#ifdef USE_LIBZ3
#include <z3.h>
#else
#include "ay.h"
#include "ay_z3_compat.h"
#endif

#include <assert.h>
#include <stdio.h>
#include <string.h>

// Reconstruct f(arg) for an arity-1 integer function interpretation: scan the
// finite map for a matching entry, else fall to the interpretation's else
// value. This is exactly how a Z3 func_interp encodes a total function.
static int interp_at_1(Z3_context c, Z3_func_interp fi, int arg) {
    unsigned ne = Z3_func_interp_get_num_entries(c, fi);
    for (unsigned i = 0; i < ne; i++) {
        Z3_func_entry e = Z3_func_interp_get_entry(c, fi, i);
        assert(e != NULL);
        Z3_func_entry_inc_ref(c, e);
        assert(Z3_func_entry_get_num_args(c, e) == 1);
        int a = 0;
        int got_a = Z3_get_numeral_int(c, Z3_func_entry_get_arg(c, e, 0), &a);
        if (got_a && a == arg) {
            int v = 0;
            int got_v = Z3_get_numeral_int(c, Z3_func_entry_get_value(c, e), &v);
            assert(got_v);
            Z3_func_entry_dec_ref(c, e);
            return v;
        }
        Z3_func_entry_dec_ref(c, e);
    }
    Z3_ast els = Z3_func_interp_get_else(c, fi);
    assert(els != 0 && "func_interp must carry an else value");
    int ev = 0;
    int got = Z3_get_numeral_int(c, els, &ev);
    assert(got && "else value must be an integer numeral");
    return ev;
}

// (assert (= (f 1) 5)) (assert (= (f 2) 7)) — read f's func_interp and verify
// the committed graph maps 1 -> 5 and 2 -> 7.
static void test_func_interp_graph(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort I = Z3_mk_int_sort(c);
    Z3_symbol fs = Z3_mk_string_symbol(c, "f");
    Z3_sort dom[1] = {I};
    Z3_func_decl f = Z3_mk_func_decl(c, fs, 1, dom, I);

    Z3_ast one = Z3_mk_int(c, 1, I), two = Z3_mk_int(c, 2, I);
    Z3_ast five = Z3_mk_int(c, 5, I), seven = Z3_mk_int(c, 7, I);
    Z3_ast a1[1] = {one}, a2[1] = {two};
    Z3_ast f1 = Z3_mk_app(c, f, 1, a1);
    Z3_ast f2 = Z3_mk_app(c, f, 1, a2);

    Z3_solver s = Z3_mk_solver(c);
    Z3_solver_inc_ref(c, s);
    Z3_solver_assert(c, s, Z3_mk_eq(c, f1, five));
    Z3_solver_assert(c, s, Z3_mk_eq(c, f2, seven));
    assert(Z3_solver_check(c, s) == Z3_L_TRUE);

    Z3_model m = Z3_solver_get_model(c, s);
    assert(m != NULL);
    Z3_model_inc_ref(c, m);

    // The model interprets at least the one constrained function f. (libz3's C
    // model omits declared-but-unconstrained functions; ay's may include them
    // with a default interpretation — an honest model-inclusion difference. So
    // find f by name rather than assert an exact count.)
    unsigned nf = Z3_model_get_num_funcs(c, m);
    assert(nf >= 1);
    Z3_func_decl fd_f = NULL;
    for (unsigned i = 0; i < nf; i++) {
        Z3_func_decl fd = Z3_model_get_func_decl(c, m, i);
        assert(fd != NULL);
        if (strcmp(Z3_get_symbol_string(c, Z3_get_decl_name(c, fd)), "f") == 0) {
            fd_f = fd;
            assert(Z3_get_arity(c, fd) == 1);
        }
    }
    assert(fd_f != NULL && "model must enumerate a func_decl named f");

    Z3_func_interp fi = Z3_model_get_func_interp(c, m, f);
    assert(fi != NULL);
    Z3_func_interp_inc_ref(c, fi);
    assert(Z3_func_interp_get_arity(c, fi) == 1);
    assert(Z3_func_interp_get_num_entries(c, fi) >= 1);

    // The committed graph: 1 -> 5, 2 -> 7 (via entry or else, identical for
    // both libraries despite different canonicalization).
    assert(interp_at_1(c, fi, 1) == 5);
    assert(interp_at_1(c, fi, 2) == 7);

    // A function the model does NOT interpret has no interpretation ("does not
    // matter"). Declared AFTER the model snapshot, so it is absent from both
    // libraries' committed models.
    Z3_func_decl h = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "h_never"), 1, dom, I);
    Z3_func_interp hi = Z3_model_get_func_interp(c, m, h);
    assert(hi == NULL);

    printf("  [func_interp] num_funcs=%u arity=%u num_entries=%u f(1)=%d f(2)=%d else=%d\n",
           nf, Z3_func_interp_get_arity(c, fi), Z3_func_interp_get_num_entries(c, fi),
           interp_at_1(c, fi, 1), interp_at_1(c, fi, 2), interp_at_1(c, fi, 99));

    Z3_func_interp_dec_ref(c, fi);
    Z3_model_dec_ref(c, m);
    Z3_solver_dec_ref(c, s);
    Z3_del_context(c);
}

// Z3_model_translate: cloning the model into a fresh context preserves the
// function graph.
static void test_model_translate(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_config cfg2 = Z3_mk_config();
    Z3_context dst = Z3_mk_context(cfg2);
    Z3_del_config(cfg2);

    Z3_sort I = Z3_mk_int_sort(c);
    Z3_symbol fs = Z3_mk_string_symbol(c, "f");
    Z3_sort dom[1] = {I};
    Z3_func_decl f = Z3_mk_func_decl(c, fs, 1, dom, I);
    Z3_ast one = Z3_mk_int(c, 1, I), two = Z3_mk_int(c, 2, I);
    Z3_ast a1[1] = {one}, a2[1] = {two};
    Z3_solver s = Z3_mk_solver(c);
    Z3_solver_inc_ref(c, s);
    Z3_solver_assert(c, s, Z3_mk_eq(c, Z3_mk_app(c, f, 1, a1), Z3_mk_int(c, 5, I)));
    Z3_solver_assert(c, s, Z3_mk_eq(c, Z3_mk_app(c, f, 1, a2), Z3_mk_int(c, 7, I)));
    assert(Z3_solver_check(c, s) == Z3_L_TRUE);
    Z3_model m = Z3_solver_get_model(c, s);
    Z3_model_inc_ref(c, m);

    Z3_model tm = Z3_model_translate(c, m, dst);
    assert(tm != NULL);
    Z3_model_inc_ref(c, tm);

    // The translated model carries the same function count and graph, queried
    // through the destination context.
    assert(Z3_model_get_num_funcs(dst, tm) == 1);
    Z3_sort I2 = Z3_mk_int_sort(dst);
    Z3_symbol fs2 = Z3_mk_string_symbol(dst, "f");
    Z3_sort dom2[1] = {I2};
    Z3_func_decl f2 = Z3_mk_func_decl(dst, fs2, 1, dom2, I2);
    Z3_func_interp fi = Z3_model_get_func_interp(dst, tm, f2);
    assert(fi != NULL);
    Z3_func_interp_inc_ref(dst, fi);
    assert(interp_at_1(dst, fi, 1) == 5);
    assert(interp_at_1(dst, fi, 2) == 7);
    printf("  [translate] translated f(1)=%d f(2)=%d (dst context)\n",
           interp_at_1(dst, fi, 1), interp_at_1(dst, fi, 2));

    Z3_func_interp_dec_ref(dst, fi);
    Z3_model_dec_ref(dst, tm);
    Z3_model_dec_ref(c, m);
    Z3_solver_dec_ref(c, s);
    Z3_del_context(dst);
    Z3_del_context(c);
}

// Uninterpreted-sort universes: (declare-sort S) with two distinct S-consts.
static void test_sort_universe(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_symbol ss = Z3_mk_string_symbol(c, "S");
    Z3_sort S = Z3_mk_uninterpreted_sort(c, ss);
    Z3_ast a = Z3_mk_const(c, Z3_mk_string_symbol(c, "a"), S);
    Z3_ast b = Z3_mk_const(c, Z3_mk_string_symbol(c, "b"), S);
    Z3_ast ab[2] = {a, b};
    Z3_solver s = Z3_mk_solver(c);
    Z3_solver_inc_ref(c, s);
    Z3_solver_assert(c, s, Z3_mk_distinct(c, 2, ab));
    assert(Z3_solver_check(c, s) == Z3_L_TRUE);
    Z3_model m = Z3_solver_get_model(c, s);
    Z3_model_inc_ref(c, m);

    unsigned nsorts = Z3_model_get_num_sorts(c, m);
    assert(nsorts >= 1);
    // Find the universe for S and confirm it holds two distinct elements
    // (a != b forces cardinality >= 2).
    int found_two = 0;
    for (unsigned i = 0; i < nsorts; i++) {
        Z3_sort si = Z3_model_get_sort(c, m, i);
        assert(si != NULL);
        Z3_ast_vector u = Z3_model_get_sort_universe(c, m, si);
        assert(u != NULL);
        unsigned usz = Z3_ast_vector_size(c, u);
        printf("  [sort_universe] sort[%u] universe_size=%u\n", i, usz);
        if (usz == 2) {
            Z3_ast e0 = Z3_ast_vector_get(c, u, 0);
            Z3_ast e1 = Z3_ast_vector_get(c, u, 1);
            assert(e0 != 0 && e1 != 0);
            found_two = 1;
        }
    }
    assert(found_two && "S's universe must contain two distinct elements");
    // NOTE: probing a NON-model sort (e.g. Int) is intentionally NOT done here:
    // libz3 raises "invalid argument" for that, whereas ay honestly returns an
    // empty vector. The ay-specific lenient behavior is asserted in the
    // Rust-side test (test_model_sort_universe_unknown_sort_empty), not in this
    // shared cross-checked consumer.

    Z3_model_dec_ref(c, m);
    Z3_solver_dec_ref(c, s);
    Z3_del_context(c);
}

int main(void) {
    test_func_interp_graph();
    test_model_translate();
    test_sort_universe();
    printf("All 3 func_interp consumer tests passed\n");
    return 0;
}
