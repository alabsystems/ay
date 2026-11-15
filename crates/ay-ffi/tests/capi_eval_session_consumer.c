// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#include <z3.h>
#include <assert.h>
#include <stdio.h>
#include <string.h>

static void ignore_error(Z3_context c, Z3_error_code error) { (void)c; (void)error; }

static void expect(Z3_context c, const char *input, const char *expected) {
    const char *output = Z3_eval_smtlib2_string(c, input);
    assert(output);
    if (strcmp(output, expected)) {
        fprintf(stderr, "input=%s\nexpected=%s\nactual=%s\n", input, expected, output);
        assert(0);
    }
    assert(Z3_get_error_code(c) == Z3_OK);
}

int main(void) {
    Z3_config config = Z3_mk_config();
    Z3_context c = Z3_mk_context(config);
    Z3_context other = Z3_mk_context(config);
    Z3_del_config(config);
    Z3_set_error_handler(c, ignore_error);
    Z3_set_error_handler(other, ignore_error);
    expect(c, "(declare-const x Int) (assert (> x 0))", "");
    expect(c, "(check-sat)", "sat\n");
    expect(c, "(push 1) (assert (< x 0)) (check-sat)", "unsat\n");
    expect(c, "(pop 1) (check-sat)", "sat\n");
    expect(c, "(reset-assertions) (assert (= x 0)) (check-sat)", "sat\n");
    const char *output = Z3_eval_smtlib2_string(c,
        "(declare-const y Int) (assert) (assert (= y 7)) (check-sat)");
    assert(output && strstr(output, "error") && strstr(output, "sat\n"));
    assert(Z3_get_error_code(c) == Z3_PARSER_ERROR);
    expect(c, "(assert (= y 8)) (check-sat)", "unsat\n");
    output = Z3_eval_smtlib2_string(other, "(assert (= y 7)) (check-sat)");
    assert(output && strstr(output, "error"));
    assert(Z3_get_error_code(other) == Z3_PARSER_ERROR);
    expect(other, "(set-option :print-success true)", "success\n");
    expect(other, "(declare-const p Bool)", "success\n");
    expect(other, "(assert p) (check-sat)", "success\nsat\n");
    expect(other, "(exit) (assert false) (check-sat)", "success\n");
    expect(other, "(check-sat)", "sat\n");
    Z3_solver solver = Z3_mk_solver(c);
    Z3_solver_inc_ref(c, solver);
    Z3_solver_assert(c, solver, Z3_mk_false(c));
    assert(Z3_solver_check(c, solver) == Z3_L_FALSE);
    expect(c, "(reset-assertions) (check-sat)", "sat\n");
    assert(Z3_solver_check(c, solver) == Z3_L_FALSE);
    expect(c, "(reset) (declare-const x Bool) (assert x) (check-sat)", "sat\n");
    expect(c, "(exit) (assert false) (check-sat)", "");
    expect(c, "(check-sat)", "sat\n");
    Z3_solver_dec_ref(c, solver);
    Z3_del_context(other);
    Z3_del_context(c);
    puts("Persistent SMT-LIB command sessions passed");
    return 0;
}
