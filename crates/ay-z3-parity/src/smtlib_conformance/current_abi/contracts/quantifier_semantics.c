// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static int quantifier_decision(Z3_context c, Z3_solver solver, Z3_ast formula, Z3_lbool expected) {
    if (!formula) return 0;
    Z3_solver_reset(c, solver);
    Z3_solver_assert(c, solver, formula);
    return Z3_solver_check(c, solver) == expected && Z3_get_error_code(c) == Z3_OK;
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("quantifier.semantics.context-created", c != NULL);
    Z3_sort integer = quantifier_hold_sort(c, Z3_mk_int_sort(c));
    Z3_sort boolean = quantifier_hold_sort(c, Z3_mk_bool_sort(c));
    CHECK("quantifier.semantics.sorts", integer && boolean);
    Z3_ast x = quantifier_hold(c, Z3_mk_bound(c, 0, integer));
    Z3_ast zero = quantifier_hold(c, Z3_mk_int(c, 0, integer));
    Z3_ast one = quantifier_hold(c, Z3_mk_int(c, 1, integer));
    CHECK("quantifier.semantics.terms",
          quantifier_bound_is(c, x, 0) && zero && one &&
          quantifier_sort_is(c, Z3_get_sort(c, x), integer));
    Z3_symbol name = Z3_mk_string_symbol(c, "integer_x");
    Z3_ast nonnegative = quantifier_hold(c, Z3_mk_ge(c, x, zero));
    Z3_ast negative = quantifier_hold(c, Z3_mk_lt(c, x, zero));
    CHECK("quantifier.semantics.bodies", nonnegative && negative);
    Z3_ast all_nonnegative = quantifier_hold(c, Z3_mk_forall(c, 0, 0, NULL, 1, &integer, &name, nonnegative));
    Z3_ast some_negative = quantifier_hold(c, Z3_mk_exists(c, 0, 0, NULL, 1, &integer, &name, negative));
    CHECK("quantifier.semantics.bound-constructors",
          all_nonnegative && some_negative && Z3_is_quantifier_forall(c, all_nonnegative) &&
          Z3_is_quantifier_exists(c, some_negative) &&
          Z3_get_quantifier_num_bound(c, all_nonnegative) == 1 &&
          quantifier_symbol_is(c, Z3_get_quantifier_bound_name(c, all_nonnegative, 0), "integer_x") &&
          quantifier_ast_is(c, Z3_get_quantifier_body(c, all_nonnegative), nonnegative));
    Z3_solver solver = Z3_mk_solver(c);
    CHECK("quantifier.semantics.solver-created", solver != NULL);
    Z3_solver_inc_ref(c, solver);
    CHECK("quantifier.semantics.forall-negative-control",
          quantifier_decision(c, solver, all_nonnegative, Z3_L_FALSE));
    CHECK("quantifier.semantics.exists-negative-witness",
          quantifier_decision(c, solver, some_negative, Z3_L_TRUE));
    Z3_ast add_arguments[2] = { x, one };
    Z3_ast next = quantifier_hold(c, Z3_mk_add(c, 2, add_arguments));
    CHECK("quantifier.semantics.successor-created", next != NULL);
    Z3_ast impossible_body = quantifier_hold(c, Z3_mk_eq(c, next, x));
    CHECK("quantifier.semantics.impossible-body-created", impossible_body != NULL);
    Z3_ast impossible_exists = quantifier_hold(c, Z3_mk_exists(c, 0, 0, NULL, 1, &integer, &name, impossible_body));
    CHECK("quantifier.semantics.exists-impossible",
          impossible_exists && quantifier_decision(c, solver, impossible_exists, Z3_L_FALSE));
    Z3_ast equal_zero = quantifier_hold(c, Z3_mk_eq(c, x, zero));
    CHECK("quantifier.semantics.generic-body-created", equal_zero != NULL);
    Z3_ast generic_forall = quantifier_hold(c, Z3_mk_quantifier(c, true, 0, 0, NULL, 1, &integer, &name, equal_zero));
    Z3_ast generic_exists = quantifier_hold(c, Z3_mk_quantifier(c, false, 0, 0, NULL, 1, &integer, &name, equal_zero));
    CHECK("quantifier.semantics.generic-polarity",
          generic_forall && generic_exists &&
          quantifier_decision(c, solver, generic_forall, Z3_L_FALSE) &&
          quantifier_decision(c, solver, generic_exists, Z3_L_TRUE));
    /* Two-element Bool domain gives a complete finite nested scope control:
       forall p exists q. q=p is true; exists p forall q. q=p is false. */
    Z3_ast p = quantifier_hold(c, Z3_mk_bound(c, 1, boolean));
    Z3_ast q = quantifier_hold(c, Z3_mk_bound(c, 0, boolean));
    CHECK("quantifier.semantics.nested-variables", p && q);
    Z3_ast same = quantifier_hold(c, Z3_mk_eq(c, q, p));
    CHECK("quantifier.semantics.nested-body-created", same != NULL);
    Z3_symbol pn = Z3_mk_string_symbol(c, "outer_p");
    Z3_symbol qn = Z3_mk_string_symbol(c, "inner_q");
    Z3_ast inner_exists = quantifier_hold(c, Z3_mk_exists(c, 0, 0, NULL, 1, &boolean, &qn, same));
    Z3_ast inner_forall = quantifier_hold(c, Z3_mk_forall(c, 0, 0, NULL, 1, &boolean, &qn, same));
    CHECK("quantifier.semantics.inner-scopes", inner_exists && inner_forall);
    Z3_ast all_some = quantifier_hold(c, Z3_mk_forall(c, 0, 0, NULL, 1, &boolean, &pn, inner_exists));
    Z3_ast some_all = quantifier_hold(c, Z3_mk_exists(c, 0, 0, NULL, 1, &boolean, &pn, inner_forall));
    CHECK("quantifier.semantics.outer-scopes", all_some && some_all);
    CHECK("quantifier.semantics.forall-exists-finite",
          quantifier_decision(c, solver, all_some, Z3_L_TRUE));
    Z3_ast not_all_some = quantifier_hold(c, Z3_mk_not(c, all_some));
    CHECK("quantifier.semantics.forall-exists-negation",
          not_all_some && quantifier_decision(c, solver, not_all_some, Z3_L_FALSE));
    CHECK("quantifier.semantics.exists-forall-finite",
          quantifier_decision(c, solver, some_all, Z3_L_FALSE));
    Z3_solver_dec_ref(c, solver);
    quantifier_release(c);
    Z3_del_context(c);
    return 0;
}
