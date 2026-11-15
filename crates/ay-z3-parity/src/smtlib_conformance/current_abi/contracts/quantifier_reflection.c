// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

/* Pinned z3_api.h specifies reversed declaration-to-de-Bruijn order;
   api_quant.cpp preserves supplied patterns, no-patterns, weight and IDs.
   Patterns and no-patterns are intentionally used in DIFFERENT quantifiers. */
int main(void) {
    Z3_context c = contract_context();
    CHECK("quantifier.reflection.context-created", c != NULL);
    Z3_sort integer = quantifier_hold_sort(c, Z3_mk_int_sort(c));
    Z3_sort boolean = quantifier_hold_sort(c, Z3_mk_bool_sort(c));
    CHECK("quantifier.reflection.sorts", integer && boolean);
    Z3_ast outer = quantifier_hold(c, Z3_mk_bound(c, 1, integer));
    Z3_ast inner = quantifier_hold(c, Z3_mk_bound(c, 0, boolean));
    CHECK("quantifier.reflection.debruijn-indices",
          quantifier_bound_is(c, outer, 1) && quantifier_bound_is(c, inner, 0) &&
          quantifier_sort_is(c, Z3_get_sort(c, outer), integer) &&
          quantifier_sort_is(c, Z3_get_sort(c, inner), boolean));
    Z3_sort domain[2] = { integer, boolean };
    Z3_func_decl f = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "qf"), 2, domain, integer);
    CHECK("quantifier.reflection.first-declaration",
          f && quantifier_hold(c, Z3_func_decl_to_ast(c, f)));
    Z3_func_decl g = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "qg"), 2, domain, integer);
    CHECK("quantifier.reflection.second-declaration",
          g && quantifier_hold(c, Z3_func_decl_to_ast(c, g)));
    Z3_ast arguments[2] = { outer, inner };
    Z3_ast ft = quantifier_hold(c, Z3_mk_app(c, f, 2, arguments));
    Z3_ast gt = quantifier_hold(c, Z3_mk_app(c, g, 2, arguments));
    CHECK("quantifier.reflection.pattern-terms-created", ft && gt);
    Z3_ast terms[2] = { ft, gt };
    Z3_pattern pattern = Z3_mk_pattern(c, 2, terms);
    CHECK("quantifier.reflection.multi-pattern",
          pattern && quantifier_hold(c, Z3_pattern_to_ast(c, pattern)) &&
          Z3_get_pattern_num_terms(c, pattern) == 2 &&
          quantifier_ast_is(c, Z3_get_pattern(c, pattern, 0), ft) &&
          quantifier_ast_is(c, Z3_get_pattern(c, pattern, 1), gt));
    Z3_ast body = quantifier_hold(c, Z3_mk_eq(c, ft, gt));
    CHECK("quantifier.reflection.body-created", body != NULL);
    Z3_symbol names[2] = { Z3_mk_string_symbol(c, "outer_i"), Z3_mk_string_symbol(c, "inner_b") };
    Z3_symbol qid = Z3_mk_string_symbol(c, "reflection-qid");
    Z3_symbol skid = Z3_mk_string_symbol(c, "reflection-skid");
    Z3_ast universal = quantifier_hold(c, Z3_mk_quantifier_ex(
        c, true, 7, qid, skid, 1, &pattern, 0, NULL, 2, domain, names, body));
    CHECK("quantifier.reflection.forall-kind",
          universal && Z3_get_ast_kind(c, universal) == Z3_QUANTIFIER_AST &&
          Z3_is_quantifier_forall(c, universal) && !Z3_is_quantifier_exists(c, universal));
    Z3_symbol integer_name = Z3_mk_int_symbol(c, 17);
    CHECK("quantifier.reflection.declaration-order",
          Z3_get_quantifier_num_bound(c, universal) == 2 &&
          integer_name && Z3_get_symbol_kind(c, integer_name) == Z3_INT_SYMBOL &&
          !quantifier_symbol_is(c, NULL, "outer_i") &&
          !quantifier_symbol_is(c, integer_name, "outer_i") &&
          quantifier_symbol_is(c, Z3_get_quantifier_bound_name(c, universal, 0), "outer_i") &&
          quantifier_symbol_is(c, Z3_get_quantifier_bound_name(c, universal, 1), "inner_b") &&
          quantifier_sort_is(c, Z3_get_quantifier_bound_sort(c, universal, 0), integer) &&
          quantifier_sort_is(c, Z3_get_quantifier_bound_sort(c, universal, 1), boolean));
    Z3_ast reflected_body = quantifier_hold(c, Z3_get_quantifier_body(c, universal));
    CHECK("quantifier.reflection.body-preserved", quantifier_ast_is(c, reflected_body, body));
    CHECK("quantifier.reflection.explicit-attributes",
          Z3_get_quantifier_weight(c, universal) == 7 &&
          quantifier_symbol_is(c, Z3_get_quantifier_id(c, universal), "reflection-qid") &&
          quantifier_symbol_is(c, Z3_get_quantifier_skolem_id(c, universal), "reflection-skid"));
    CHECK("quantifier.reflection.pattern-counts",
          Z3_get_quantifier_num_patterns(c, universal) == 1 &&
          Z3_get_quantifier_num_no_patterns(c, universal) == 0);
    Z3_pattern reflected_pattern = Z3_get_quantifier_pattern_ast(c, universal, 0);
    CHECK("quantifier.reflection.reflected-pattern",
          reflected_pattern && quantifier_hold(c, Z3_pattern_to_ast(c, reflected_pattern)) &&
          Z3_get_pattern_num_terms(c, reflected_pattern) == 2 &&
          quantifier_ast_is(c, Z3_get_pattern(c, reflected_pattern, 0), ft) &&
          quantifier_ast_is(c, Z3_get_pattern(c, reflected_pattern, 1), gt));
    Z3_ast existential = quantifier_hold(c, Z3_mk_quantifier_ex(
        c, false, 3, Z3_mk_string_symbol(c, "no-pattern-qid"),
        Z3_mk_string_symbol(c, "no-pattern-skid"), 0, NULL, 1, &gt, 2, domain, names, body));
    CHECK("quantifier.reflection.exists-no-pattern",
          existential && Z3_is_quantifier_exists(c, existential) &&
          !Z3_is_quantifier_forall(c, existential) &&
          Z3_get_quantifier_num_patterns(c, existential) == 0 &&
          Z3_get_quantifier_num_no_patterns(c, existential) == 1);
    Z3_ast excluded = quantifier_hold(c, Z3_get_quantifier_no_pattern_ast(c, existential, 0));
    CHECK("quantifier.reflection.no-pattern-content",
          quantifier_ast_is(c, excluded, gt) &&
          quantifier_ast_is(c, Z3_get_quantifier_body(c, existential), body) &&
          Z3_get_quantifier_weight(c, existential) == 3 &&
          quantifier_symbol_is(c, Z3_get_quantifier_id(c, existential), "no-pattern-qid") &&
          quantifier_symbol_is(c, Z3_get_quantifier_skolem_id(c, existential), "no-pattern-skid") &&
          Z3_get_error_code(c) == Z3_OK);
    quantifier_release(c);
    Z3_del_context(c);
    return 0;
}
