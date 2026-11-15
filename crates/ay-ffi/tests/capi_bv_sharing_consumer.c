// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#ifdef AY_TWIN_USE_Z3
#include <z3.h>
#else
#include "ay_z3_compat.h"
#endif
#include <assert.h>
#include <stdio.h>

typedef Z3_ast (*binary_op)(Z3_context, Z3_ast, Z3_ast);

static void check_sharing(Z3_context c, binary_op op) {
    Z3_sort bv = Z3_mk_bv_sort(c, 8);
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "x"), bv);
    Z3_ast y = Z3_mk_const(c, Z3_mk_string_symbol(c, "y"), bv);
    Z3_ast z = Z3_mk_const(c, Z3_mk_string_symbol(c, "z"), bv);
    Z3_func_decl p = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "p"), 1, &bv, Z3_mk_bool_sort(c));
    Z3_ast xy = op(c, x, y), yz = op(c, y, z), xyz = op(c, x, yz);
    Z3_ast first = Z3_mk_app(c, p, 1, &xy), second = Z3_mk_app(c, p, 1, &xyz);
    Z3_goal input = Z3_mk_goal(c, false, false, false);
    Z3_goal_inc_ref(c, input);
    Z3_goal_assert(c, input, first);
    Z3_goal_assert(c, input, second);
    Z3_tactic tactic = Z3_mk_tactic(c, "max-bv-sharing");
    assert(tactic);
    Z3_tactic_inc_ref(c, tactic);
    Z3_apply_result result = Z3_tactic_apply(c, tactic, input);
    assert(result && Z3_get_error_code(c) == Z3_OK);
    Z3_apply_result_inc_ref(c, result);
    assert(Z3_apply_result_get_num_subgoals(c, result) == 1);
    Z3_goal output = Z3_apply_result_get_subgoal(c, result, 0);
    assert(Z3_goal_size(c, output) == 2);
    assert(Z3_is_eq_ast(c, Z3_goal_formula(c, output, 0), first));
    Z3_ast formula = Z3_goal_formula(c, output, 1);
    Z3_ast sum = Z3_get_app_arg(c, Z3_to_app(c, formula), 0);
    Z3_app app = Z3_to_app(c, sum);
    assert(Z3_get_app_num_args(c, app) == 2);
    Z3_ast a = Z3_get_app_arg(c, app, 0), b = Z3_get_app_arg(c, app, 1);
    assert((Z3_is_eq_ast(c, a, xy) && Z3_is_eq_ast(c, b, z)) ||
           (Z3_is_eq_ast(c, b, xy) && Z3_is_eq_ast(c, a, z)));
    assert(Z3_is_eq_ast(c, Z3_goal_formula(c, input, 1), second));
    Z3_apply_result again = Z3_tactic_apply(c, tactic, output);
    assert(again);
    Z3_apply_result_inc_ref(c, again);
    Z3_goal stable = Z3_apply_result_get_subgoal(c, again, 0);
    assert(Z3_is_eq_ast(c, Z3_goal_formula(c, stable, 1), formula));
    Z3_apply_result_dec_ref(c, again);
    Z3_apply_result_dec_ref(c, result);
    Z3_tactic_dec_ref(c, tactic);
    Z3_goal_dec_ref(c, input);
}

int main(void) {
    Z3_config config = Z3_mk_config();
    Z3_context c = Z3_mk_context(config);
    Z3_del_config(config);
    for (unsigned i = 0; i < 4; ++i) {
        binary_op ops[] = {Z3_mk_bvadd, Z3_mk_bvmul, Z3_mk_bvand, Z3_mk_bvor};
        check_sharing(c, ops[i]);
    }
    Z3_del_context(c);
    puts("BV sharing C tactic preserves input and reuses all four AC circuits");
    return 0;
}
