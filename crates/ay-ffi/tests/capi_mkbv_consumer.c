// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#ifdef AY_TWIN_USE_Z3
#include <z3.h>
#else
#include "ay_z3_compat.h"
#endif
#include <assert.h>
#include <stdio.h>

int main(void) {
    Z3_config config = Z3_mk_config();
    Z3_context c = Z3_mk_context(config);
    Z3_del_config(config);

    Z3_ast_vector assertions = Z3_parse_smtlib2_string(
        c, "(declare-const a Bool)(assert a)"
           "(assert (= (mkbv a false false) #b001))"
           "(assert (= (mkbv a false false) #b100))",
        0, 0, 0, 0, 0, 0);
    assert(assertions);
    Z3_ast_vector_inc_ref(c, assertions);
    assert(Z3_ast_vector_size(c, assertions) == 3);

    Z3_app equality = Z3_to_app(c, Z3_ast_vector_get(c, assertions, 1));
    Z3_ast term = Z3_get_app_arg(c, equality, 0);
    Z3_app bits = Z3_to_app(c, term);
    assert(Z3_get_decl_kind(c, Z3_get_app_decl(c, bits)) == Z3_OP_MKBV);
    assert(Z3_get_app_num_args(c, bits) == 3);
    assert(Z3_get_bv_sort_size(c, Z3_get_sort(c, term)) == 3);
    assert(Z3_is_eq_ast(c, Z3_get_app_arg(c, bits, 0),
                        Z3_ast_vector_get(c, assertions, 0)));

    Z3_solver solver = Z3_mk_solver(c);
    Z3_solver_inc_ref(c, solver);
    Z3_solver_assert(c, solver, Z3_ast_vector_get(c, assertions, 0));
    Z3_solver_assert(c, solver, Z3_ast_vector_get(c, assertions, 1));
    assert(Z3_solver_check(c, solver) == Z3_L_TRUE);
    Z3_solver_assert(c, solver, Z3_ast_vector_get(c, assertions, 2));
    assert(Z3_solver_check(c, solver) == Z3_L_FALSE);

    Z3_solver_dec_ref(c, solver);
    Z3_ast_vector_dec_ref(c, assertions);
    Z3_del_context(c);
    puts("mkbv AST and bit order passed");
    return 0;
}
