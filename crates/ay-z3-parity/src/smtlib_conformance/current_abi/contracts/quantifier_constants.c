// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static int quantifier_constant_decision(Z3_context c, Z3_solver solver, Z3_ast formula, Z3_lbool expected) {
    if (!formula) return 0;
    Z3_solver_reset(c, solver);
    Z3_solver_assert(c, solver, formula);
    return Z3_solver_check(c, solver) == expected && Z3_get_error_code(c) == Z3_OK;
}

static Z3_ast quantifier_constant_argument(Z3_context c, Z3_ast term, unsigned index) {
    if (!term || Z3_get_ast_kind(c, term) != Z3_APP_AST) return NULL;
    Z3_app app = Z3_to_app(c, term);
    if (!app || Z3_get_app_num_args(c, app) != 2 || index >= 2) return NULL;
    return quantifier_hold(c, Z3_get_app_arg(c, app, index));
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("quantifier.constants.context-created", c != NULL);
    Z3_sort integer = quantifier_hold_sort(c, Z3_mk_int_sort(c));
    CHECK("quantifier.constants.sort-created", integer != NULL);
    Z3_ast x = quantifier_hold(c, Z3_mk_const(c, Z3_mk_string_symbol(c, "abstract_x"), integer));
    Z3_ast free_value = quantifier_hold(c, Z3_mk_const(c, Z3_mk_string_symbol(c, "free_value"), integer));
    Z3_ast zero = quantifier_hold(c, Z3_mk_int(c, 0, integer));
    Z3_ast seven = quantifier_hold(c, Z3_mk_int(c, 7, integer));
    CHECK("quantifier.constants.terms-created",
          x && free_value && zero && seven && Z3_get_ast_kind(c, x) == Z3_APP_AST);
    Z3_app bound = Z3_to_app(c, x);
    Z3_ast body = quantifier_hold(c, Z3_mk_eq(c, x, free_value));
    CHECK("quantifier.constants.body-created", bound && body);
    Z3_ast all_equal = quantifier_hold(c, Z3_mk_forall_const(c, 0, 1, &bound, 0, NULL, body));
    Z3_ast some_equal = quantifier_hold(c, Z3_mk_exists_const(c, 0, 1, &bound, 0, NULL, body));
    CHECK("quantifier.constants.abstraction-constructors",
          all_equal && some_equal && Z3_get_ast_kind(c, all_equal) == Z3_QUANTIFIER_AST &&
          Z3_get_ast_kind(c, some_equal) == Z3_QUANTIFIER_AST &&
          Z3_is_quantifier_forall(c, all_equal) && Z3_is_quantifier_exists(c, some_equal));
    Z3_ast abstract_body = quantifier_hold(c, Z3_get_quantifier_body(c, some_equal));
    CHECK("quantifier.constants.abstract-body-created", abstract_body && Z3_get_ast_kind(c, abstract_body) == Z3_APP_AST);
    Z3_ast abstract_first = quantifier_constant_argument(c, abstract_body, 0);
    Z3_ast abstract_second = quantifier_constant_argument(c, abstract_body, 1);
    CHECK("quantifier.constants.free-constant-preserved",
          quantifier_bound_is(c, abstract_first, 0) &&
          quantifier_ast_is(c, abstract_second, free_value) &&
          Z3_get_quantifier_num_bound(c, some_equal) == 1 &&
          quantifier_symbol_is(c, Z3_get_quantifier_bound_name(c, some_equal, 0), "abstract_x") &&
          quantifier_sort_is(c, Z3_get_quantifier_bound_sort(c, some_equal, 0), integer));
    Z3_ast source_first = quantifier_constant_argument(c, body, 0);
    Z3_ast source_second = quantifier_constant_argument(c, body, 1);
    CHECK("quantifier.constants.source-body-unmodified",
          quantifier_ast_is(c, source_first, x) && quantifier_ast_is(c, source_second, free_value));
    Z3_solver solver = Z3_mk_solver(c);
    CHECK("quantifier.constants.solver-created", solver != NULL);
    Z3_solver_inc_ref(c, solver);
    CHECK("quantifier.constants.exists-free-value",
          quantifier_constant_decision(c, solver, some_equal, Z3_L_TRUE));
    Z3_ast not_some_equal = quantifier_hold(c, Z3_mk_not(c, some_equal));
    CHECK("quantifier.constants.exists-free-value-valid",
          not_some_equal && quantifier_constant_decision(c, solver, not_some_equal, Z3_L_FALSE));
    CHECK("quantifier.constants.forall-free-value-impossible",
          quantifier_constant_decision(c, solver, all_equal, Z3_L_FALSE));
    Z3_ast equal_seven = quantifier_hold(c, Z3_mk_eq(c, x, seven));
    CHECK("quantifier.constants.generic-body-created", equal_seven != NULL);
    Z3_ast generic_all = quantifier_hold(c, Z3_mk_quantifier_const(c, true, 0, 1, &bound, 0, NULL, equal_seven));
    Z3_ast generic_some = quantifier_hold(c, Z3_mk_quantifier_const(c, false, 0, 1, &bound, 0, NULL, equal_seven));
    CHECK("quantifier.constants.generic-polarity",
          generic_all && generic_some &&
          quantifier_constant_decision(c, solver, generic_all, Z3_L_FALSE) &&
          quantifier_constant_decision(c, solver, generic_some, Z3_L_TRUE));
    Z3_sort domain[2] = { integer, integer };
    Z3_func_decl f = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "abstract_f"), 2, domain, integer);
    CHECK("quantifier.constants.pattern-declaration",
          f && quantifier_hold(c, Z3_func_decl_to_ast(c, f)));
    Z3_ast arguments[2] = { x, free_value };
    Z3_ast application = quantifier_hold(c, Z3_mk_app(c, f, 2, arguments));
    CHECK("quantifier.constants.pattern-application", application != NULL);
    Z3_pattern pattern = Z3_mk_pattern(c, 1, &application);
    CHECK("quantifier.constants.pattern-created",
          pattern && quantifier_hold(c, Z3_pattern_to_ast(c, pattern)));
    Z3_ast identity_body = quantifier_hold(c, Z3_mk_eq(c, application, x));
    CHECK("quantifier.constants.identity-body", identity_body != NULL);
    Z3_ast with_pattern = quantifier_hold(c, Z3_mk_quantifier_const_ex(
        c, true, 11, Z3_mk_string_symbol(c, "const-qid"), Z3_mk_string_symbol(c, "const-skid"),
        1, &bound, 1, &pattern, 0, NULL, identity_body));
    CHECK("quantifier.constants.extended-pattern-created",
          with_pattern && Z3_get_ast_kind(c, with_pattern) == Z3_QUANTIFIER_AST &&
          Z3_get_quantifier_num_patterns(c, with_pattern) == 1 &&
          Z3_get_quantifier_num_no_patterns(c, with_pattern) == 0);
    Z3_pattern abstract_pattern = Z3_get_quantifier_pattern_ast(c, with_pattern, 0);
    CHECK("quantifier.constants.abstract-pattern-created",
          abstract_pattern && quantifier_hold(c, Z3_pattern_to_ast(c, abstract_pattern)) &&
          Z3_get_pattern_num_terms(c, abstract_pattern) == 1);
    Z3_ast abstract_term = quantifier_hold(c, Z3_get_pattern(c, abstract_pattern, 0));
    Z3_ast pattern_first = quantifier_constant_argument(c, abstract_term, 0);
    Z3_ast pattern_second = quantifier_constant_argument(c, abstract_term, 1);
    CHECK("quantifier.constants.pattern-abstracts-only-bound",
          quantifier_bound_is(c, pattern_first, 0) &&
          quantifier_ast_is(c, pattern_second, free_value) &&
          Z3_get_quantifier_weight(c, with_pattern) == 11 &&
          quantifier_symbol_is(c, Z3_get_quantifier_id(c, with_pattern), "const-qid") &&
          quantifier_symbol_is(c, Z3_get_quantifier_skolem_id(c, with_pattern), "const-skid"));
    Z3_ast without_pattern = quantifier_hold(c, Z3_mk_quantifier_const_ex(
        c, true, 13, Z3_mk_string_symbol(c, "const-no-qid"), Z3_mk_string_symbol(c, "const-no-skid"),
        1, &bound, 0, NULL, 1, &application, identity_body));
    CHECK("quantifier.constants.extended-no-pattern-created",
          without_pattern && Z3_get_ast_kind(c, without_pattern) == Z3_QUANTIFIER_AST &&
          Z3_get_quantifier_num_patterns(c, without_pattern) == 0 &&
          Z3_get_quantifier_num_no_patterns(c, without_pattern) == 1);
    Z3_ast excluded = quantifier_hold(c, Z3_get_quantifier_no_pattern_ast(c, without_pattern, 0));
    CHECK("quantifier.constants.no-pattern-abstracted",
          quantifier_ast_is(c, excluded, abstract_term) &&
          quantifier_ast_is(c, Z3_get_quantifier_body(c, without_pattern), Z3_get_quantifier_body(c, with_pattern)));
    Z3_ast zero_arguments[2] = { zero, free_value };
    Z3_ast fzero = quantifier_hold(c, Z3_mk_app(c, f, 2, zero_arguments));
    CHECK("quantifier.constants.ground-application", fzero != NULL);
    Z3_ast fzero_is_zero = quantifier_hold(c, Z3_mk_eq(c, fzero, zero));
    CHECK("quantifier.constants.ground-equality", fzero_is_zero != NULL);
    Z3_ast counterexample = quantifier_hold(c, Z3_mk_not(c, fzero_is_zero));
    CHECK("quantifier.constants.ground-counterexample-created", counterexample != NULL);
    CHECK("quantifier.constants.counterexample-without-quantifier",
          quantifier_constant_decision(c, solver, counterexample, Z3_L_TRUE));
    Z3_solver_push(c, solver);
    Z3_solver_assert(c, solver, with_pattern);
    CHECK("quantifier.constants.pattern-quantifier-refutes-counterexample",
          Z3_solver_check(c, solver) == Z3_L_FALSE);
    Z3_solver_pop(c, solver, 1);
    CHECK("quantifier.constants.counterexample-scope-restored", Z3_solver_check(c, solver) == Z3_L_TRUE);
    Z3_solver_assert(c, solver, without_pattern);
    CHECK("quantifier.constants.no-pattern-quantifier-refutes-counterexample",
          Z3_solver_check(c, solver) == Z3_L_FALSE);
    Z3_solver_dec_ref(c, solver);
    for (int i = 0; i < 256; ++i) {
        Z3_ast temporary = Z3_mk_int(c, i, integer);
        if (!temporary) return 2;
        Z3_inc_ref(c, temporary);
        Z3_dec_ref(c, temporary);
    }
    CHECK("quantifier.constants.retained-after-solver-release",
          Z3_get_quantifier_num_patterns(c, with_pattern) == 1 &&
          Z3_get_pattern_num_terms(c, abstract_pattern) == 1 &&
          quantifier_ast_is(c, Z3_get_pattern(c, abstract_pattern, 0), abstract_term) &&
          quantifier_ast_is(c, Z3_get_quantifier_no_pattern_ast(c, without_pattern, 0), excluded) &&
          quantifier_ast_is(c, Z3_get_quantifier_body(c, some_equal), abstract_body) &&
          Z3_get_error_code(c) == Z3_OK);
    quantifier_release(c);
    Z3_del_context(c);
    return 0;
}
