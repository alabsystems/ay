// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("solver.context-created", c != NULL);
    Z3_sort boolean = Z3_mk_bool_sort(c); HOLD_SORT(c, boolean);
    Z3_ast p = Z3_mk_const(c, Z3_mk_string_symbol(c, "contract_p"), boolean); HOLD(c, p);
    Z3_ast not_p = Z3_mk_not(c, p); HOLD(c, not_p);
    Z3_solver a = Z3_mk_solver(c); if (a) Z3_solver_inc_ref(c, a);
    Z3_solver b = Z3_mk_solver(c); if (b) Z3_solver_inc_ref(c, b);
    CHECK("solver.fresh-state", p && not_p && a && b &&
          Z3_solver_get_num_scopes(c, a) == 0 && Z3_solver_get_num_scopes(c, b) == 0);
    Z3_solver_assert(c, a, p);
    Z3_solver_assert(c, b, not_p);
    CHECK("solver.independent-instances", Z3_solver_check(c, a) == Z3_L_TRUE &&
          Z3_solver_check(c, b) == Z3_L_TRUE);
    Z3_solver_push(c, a);
    Z3_solver_assert(c, a, not_p);
    CHECK("solver.push-isolated-contradiction", Z3_solver_get_num_scopes(c, a) == 1 &&
          Z3_solver_get_num_scopes(c, b) == 0 && Z3_solver_check(c, a) == Z3_L_FALSE &&
          Z3_solver_check(c, b) == Z3_L_TRUE);
    Z3_ast_vector snapshot = Z3_solver_get_assertions(c, a);
    if (snapshot) Z3_ast_vector_inc_ref(c, snapshot);
    CHECK("solver.assertion-snapshot", snapshot && Z3_ast_vector_size(c, snapshot) == 2 &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, snapshot, 0), p) &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, snapshot, 1), not_p));
    Z3_solver_pop(c, a, 1);
    CHECK("solver.pop-restores-scope", Z3_solver_get_num_scopes(c, a) == 0 &&
          Z3_solver_check(c, a) == Z3_L_TRUE && Z3_solver_check(c, b) == Z3_L_TRUE);
    Z3_ast assumptions[1] = {not_p};
    CHECK("solver.assumption-contradiction", Z3_solver_check_assumptions(c, a, 1, assumptions) == Z3_L_FALSE);
    Z3_ast_vector core = Z3_solver_get_unsat_core(c, a);
    if (core) Z3_ast_vector_inc_ref(c, core);
    CHECK("solver.assumption-core", core && Z3_ast_vector_size(c, core) == 1 &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, core, 0), not_p));
    CHECK("solver.assumptions-do-not-persist", Z3_solver_check(c, a) == Z3_L_TRUE);
    Z3_solver_reset(c, a);
    Z3_ast_vector empty = Z3_solver_get_assertions(c, a);
    if (empty) Z3_ast_vector_inc_ref(c, empty);
    CHECK("solver.reset-and-retained-snapshots", empty && Z3_ast_vector_size(c, empty) == 0 &&
          Z3_solver_get_num_scopes(c, a) == 0 && Z3_solver_check(c, a) == Z3_L_TRUE &&
          Z3_ast_vector_size(c, snapshot) == 2 && Z3_ast_vector_size(c, core) == 1 &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, core, 0), not_p));
    Z3_ast_vector_dec_ref(c, empty);
    Z3_ast_vector_dec_ref(c, core);
    Z3_ast_vector_dec_ref(c, snapshot);
    Z3_solver_dec_ref(c, b);
    Z3_solver_dec_ref(c, a);
    Z3_dec_ref(c, not_p);
    Z3_dec_ref(c, p);
    Z3_dec_ref(c, Z3_sort_to_ast(c, boolean));
    Z3_del_context(c);
    return 0;
}
