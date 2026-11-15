// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static Z3_fixedpoint retained_fixedpoint(Z3_context c, const char *engine) {
    Z3_fixedpoint fp = Z3_mk_fixedpoint(c);
    if (!fp) return NULL;
    Z3_fixedpoint_inc_ref(c, fp);
    Z3_params params = Z3_mk_params(c);
    if (!params) return NULL;
    Z3_params_inc_ref(c, params);
    Z3_params_set_symbol(c, params, Z3_mk_string_symbol(c, "engine"),
                         Z3_mk_string_symbol(c, engine));
    Z3_fixedpoint_set_params(c, fp, params);
    Z3_params_dec_ref(c, params);
    return fp;
}

static int fixedpoint_relation_name(Z3_context c, Z3_func_decl relation, const char *expected) {
    if (!relation) return 0;
    Z3_symbol name = Z3_get_decl_name(c, relation);
    if (Z3_get_symbol_kind(c, name) != Z3_STRING_SYMBOL) return 0;
    const char *actual = Z3_get_symbol_string(c, name);
    return actual && strcmp(actual, expected) == 0;
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("fixedpoint.context-created", c != NULL);
    Z3_fixedpoint a = retained_fixedpoint(c, "datalog");
    Z3_fixedpoint b = retained_fixedpoint(c, "datalog");
    CHECK("fixedpoint.independent-objects-created", a && b && a != b && Z3_get_error_code(c) == Z3_OK);
    Z3_fixedpoint_inc_ref(c, a);
    Z3_fixedpoint_dec_ref(c, a);
    Z3_sort bv = Z3_mk_bv_sort(c, 4); HOLD_SORT(c, bv);
    Z3_sort boolean = Z3_mk_bool_sort(c); HOLD_SORT(c, boolean);
    Z3_sort domain[1] = {bv};
    Z3_func_decl p = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "contract_fp_p"), 1, domain, boolean);
    if (p) HOLD(c, Z3_func_decl_to_ast(c, p));
    Z3_func_decl q = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "contract_fp_q"), 1, domain, boolean);
    if (q) HOLD(c, Z3_func_decl_to_ast(c, q));
    Z3_ast one = Z3_mk_unsigned_int(c, 1, bv); HOLD(c, one);
    Z3_ast two = Z3_mk_unsigned_int(c, 2, bv); HOLD(c, two);
    CHECK("fixedpoint.typed-relations-created", bv && boolean && p && q && p != q && one && two &&
          fixedpoint_relation_name(c, p, "contract_fp_p") && fixedpoint_relation_name(c, q, "contract_fp_q"));
    Z3_fixedpoint_register_relation(c, a, p);
    Z3_fixedpoint_register_relation(c, a, q);
    Z3_fixedpoint_register_relation(c, b, p);
    Z3_ast p1 = Z3_mk_app(c, p, 1, &one); HOLD(c, p1);
    Z3_ast p2 = Z3_mk_app(c, p, 1, &two); HOLD(c, p2);
    Z3_ast q1 = Z3_mk_app(c, q, 1, &one); HOLD(c, q1);
    Z3_ast q2 = Z3_mk_app(c, q, 1, &two); HOLD(c, q2);
    CHECK("fixedpoint.empty-relation-is-unreachable", p1 && p2 && q1 && q2 &&
          Z3_fixedpoint_query(c, a, p1) == Z3_L_FALSE && Z3_get_error_code(c) == Z3_OK);
    unsigned fact[1] = {1};
    Z3_fixedpoint_add_fact(c, a, p, 1, fact);
    CHECK("fixedpoint.fact-membership", Z3_fixedpoint_query(c, a, p1) == Z3_L_TRUE &&
          Z3_fixedpoint_query(c, a, p2) == Z3_L_FALSE && Z3_get_error_code(c) == Z3_OK);
    CHECK("fixedpoint.ground-query-satisfiable", Z3_fixedpoint_query(c, a, p1) == Z3_L_TRUE);
    Z3_ast answer = Z3_fixedpoint_get_answer(c, a); HOLD(c, answer);
    CHECK("fixedpoint.ground-answer", answer && Z3_get_bool_value(c, answer) == Z3_L_TRUE);
    Z3_ast variable = Z3_mk_bound(c, 0, bv); HOLD(c, variable);
    Z3_ast px = Z3_mk_app(c, p, 1, &variable); HOLD(c, px);
    Z3_ast qx = Z3_mk_app(c, q, 1, &variable); HOLD(c, qx);
    Z3_ast implication = Z3_mk_implies(c, px, qx); HOLD(c, implication);
    Z3_symbol variable_name = Z3_mk_string_symbol(c, "contract_fp_x");
    Z3_ast rule = Z3_mk_forall(c, 0, 0, NULL, 1, domain, &variable_name, implication); HOLD(c, rule);
    CHECK("fixedpoint.bound-variable-rule", rule && Z3_is_quantifier_forall(c, rule) &&
          Z3_get_quantifier_num_bound(c, rule) == 1);
    Z3_fixedpoint_add_rule(c, a, rule, Z3_mk_string_symbol(c, "copy_rule"));
    CHECK("fixedpoint.rule-derives-only-matching-value", Z3_fixedpoint_query(c, a, q1) == Z3_L_TRUE &&
          Z3_fixedpoint_query(c, a, q2) == Z3_L_FALSE && Z3_get_error_code(c) == Z3_OK);
    Z3_func_decl queries[1] = {q};
    CHECK("fixedpoint.relation-query", Z3_fixedpoint_query_relations(c, a, 1, queries) == Z3_L_TRUE);
    unsigned other_fact[1] = {2};
    Z3_fixedpoint_add_fact(c, b, p, 1, other_fact);
    CHECK("fixedpoint.rule-and-fact-state-isolated", Z3_fixedpoint_query(c, b, p1) == Z3_L_FALSE &&
          Z3_fixedpoint_query(c, b, p2) == Z3_L_TRUE && Z3_fixedpoint_query(c, a, p2) == Z3_L_FALSE);
    Z3_ast_vector rules = Z3_fixedpoint_get_rules(c, a);
    if (rules) Z3_ast_vector_inc_ref(c, rules);
    /* add_fact inserts a database tuple, not an asserted rule. The snapshot
       contains only the quantified rule; reachability above checks the tuple. */
    CHECK("fixedpoint.rule-snapshot", rules && Z3_ast_vector_size(c, rules) == 1 &&
          Z3_is_quantifier_forall(c, Z3_ast_vector_get(c, rules, 0)));
    Z3_ast truth = Z3_mk_true(c); HOLD(c, truth);
    Z3_fixedpoint_assert(c, a, truth);
    Z3_ast_vector assertions = Z3_fixedpoint_get_assertions(c, a);
    if (assertions) Z3_ast_vector_inc_ref(c, assertions);
    CHECK("fixedpoint.background-assertion-snapshot", assertions &&
          Z3_ast_vector_size(c, assertions) == 1 &&
          Z3_get_bool_value(c, Z3_ast_vector_get(c, assertions, 0)) == Z3_L_TRUE);
    Z3_fixedpoint parsed = retained_fixedpoint(c, "datalog");
    Z3_fixedpoint isolated = retained_fixedpoint(c, "datalog");
    CHECK("fixedpoint.parser-objects-created", parsed && isolated);
    Z3_ast_vector parsed_queries = Z3_fixedpoint_from_string(c, parsed,
        "(declare-rel contract_fp_step ((_ BitVec 4))) (declare-var x (_ BitVec 4)) "
        "(rule (contract_fp_step #x1)) "
        "(rule (=> (and (contract_fp_step x) (bvult x #x3)) (contract_fp_step (bvadd x #x1)))) "
        "(query contract_fp_step)");
    if (parsed_queries) Z3_ast_vector_inc_ref(c, parsed_queries);
    Z3_ast_vector isolated_queries = Z3_fixedpoint_from_string(c, isolated,
        "(declare-rel contract_fp_step ((_ BitVec 4))) (rule (contract_fp_step #x0)) (query contract_fp_step)");
    if (isolated_queries) Z3_ast_vector_inc_ref(c, isolated_queries);
    Z3_func_decl step = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "contract_fp_step"), 1, domain, boolean);
    if (step) HOLD(c, Z3_func_decl_to_ast(c, step));
    Z3_ast three = Z3_mk_unsigned_int(c, 3, bv); HOLD(c, three);
    Z3_ast four = Z3_mk_unsigned_int(c, 4, bv); HOLD(c, four);
    Z3_ast step3 = Z3_mk_app(c, step, 1, &three); HOLD(c, step3);
    Z3_ast step4 = Z3_mk_app(c, step, 1, &four); HOLD(c, step4);
    CHECK("fixedpoint.parser-binds-rule-variables", parsed_queries && isolated_queries && step3 && step4 &&
          Z3_ast_vector_size(c, parsed_queries) == 1 && Z3_ast_vector_size(c, isolated_queries) == 1 &&
          Z3_fixedpoint_query(c, parsed, step3) == Z3_L_TRUE && Z3_fixedpoint_query(c, parsed, step4) == Z3_L_FALSE);
    CHECK("fixedpoint.parser-rule-state-isolated", Z3_fixedpoint_query(c, isolated, step3) == Z3_L_FALSE &&
          Z3_fixedpoint_query(c, parsed, step3) == Z3_L_TRUE && Z3_get_error_code(c) == Z3_OK);
    Z3_fixedpoint_dec_ref(c, isolated);
    Z3_fixedpoint_dec_ref(c, parsed);
    Z3_fixedpoint_dec_ref(c, b);
    Z3_fixedpoint_dec_ref(c, a);
    CHECK("fixedpoint.retained-results-survive-engine-release", Z3_get_bool_value(c, answer) == Z3_L_TRUE &&
          Z3_ast_vector_size(c, rules) == 1 && Z3_is_quantifier_forall(c, Z3_ast_vector_get(c, rules, 0)) &&
          Z3_ast_vector_size(c, assertions) == 1 && Z3_ast_vector_size(c, parsed_queries) == 1);
    Z3_ast_vector_dec_ref(c, isolated_queries);
    Z3_ast_vector_dec_ref(c, parsed_queries);
    Z3_ast_vector_dec_ref(c, assertions);
    Z3_ast_vector_dec_ref(c, rules);
    Z3_del_context(c);
    return 0;
}
