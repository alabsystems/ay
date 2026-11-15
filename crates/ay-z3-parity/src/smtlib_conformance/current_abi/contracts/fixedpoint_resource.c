// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("fixedpoint-resource.context-created", c != NULL);
    Z3_fixedpoint fp = Z3_mk_fixedpoint(c);
    if (fp) Z3_fixedpoint_inc_ref(c, fp);
    Z3_params params = Z3_mk_params(c);
    if (params) Z3_params_inc_ref(c, params);
    CHECK("fixedpoint-resource.objects-created", fp && params);
    Z3_params_set_symbol(c, params, Z3_mk_string_symbol(c, "engine"), Z3_mk_string_symbol(c, "spacer"));
    Z3_params_set_uint(c, params, Z3_mk_string_symbol(c, "rlimit"), 1);
    Z3_fixedpoint_set_params(c, fp, params);
    Z3_params_dec_ref(c, params);
    Z3_sort integer = Z3_mk_int_sort(c); HOLD_SORT(c, integer);
    Z3_sort boolean = Z3_mk_bool_sort(c); HOLD_SORT(c, boolean);
    Z3_sort domain[1] = {integer};
    Z3_func_decl relation = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "contract_fp_limited"), 1, domain, boolean);
    if (relation) HOLD(c, Z3_func_decl_to_ast(c, relation));
    Z3_ast zero = Z3_mk_int(c, 0, integer); HOLD(c, zero);
    Z3_ast query = Z3_mk_app(c, relation, 1, &zero); HOLD(c, query);
    CHECK("fixedpoint-resource.query-created", relation && query && Z3_get_error_code(c) == Z3_OK);
    Z3_fixedpoint_register_relation(c, fp, relation);
    Z3_fixedpoint_add_rule(c, fp, query, Z3_mk_string_symbol(c, "limited_fact"));
    contract_last_error = Z3_OK;
    Z3_lbool limited = Z3_fixedpoint_query(c, fp, query);
    Z3_error_code error = Z3_get_error_code(c);
    CHECK("fixedpoint-resource.budget-refuses-decision", limited == Z3_L_UNDEF &&
          error == Z3_EXCEPTION && contract_last_error == Z3_EXCEPTION);
    const char *message = Z3_get_error_msg(c, error);
    CHECK("fixedpoint-resource.cancellation-diagnostic", message && strcmp(message, "max. resource limit exceeded") == 0);
    const char *reason = Z3_fixedpoint_get_reason_unknown(c, fp);
    /* 5.3.3 records the thrown resource exception separately from the engine's
       last-status string, which remains "ok" for this exact cancellation. */
    CHECK("fixedpoint-resource.reason-after-exception", reason && strcmp(reason, "ok") == 0);
    params = Z3_mk_params(c);
    if (params) Z3_params_inc_ref(c, params);
    CHECK("fixedpoint-resource.recovery-params-created", params != NULL);
    Z3_params_set_uint(c, params, Z3_mk_string_symbol(c, "rlimit"), 0);
    Z3_fixedpoint_set_params(c, fp, params);
    Z3_params_dec_ref(c, params);
    CHECK("fixedpoint-resource.recovery-decision", Z3_fixedpoint_query(c, fp, query) == Z3_L_TRUE &&
          Z3_get_error_code(c) == Z3_OK);
    Z3_ast answer = Z3_fixedpoint_get_answer(c, fp); HOLD(c, answer);
    Z3_stats statistics = Z3_fixedpoint_get_statistics(c, fp);
    if (statistics) Z3_stats_inc_ref(c, statistics);
    CHECK("fixedpoint-resource.recovery-answer-and-statistics", answer && statistics &&
          Z3_get_ast_kind(c, answer) == Z3_APP_AST &&
          Z3_ast_to_string(c, answer) && strlen(Z3_ast_to_string(c, answer)) > 0 &&
          Z3_stats_size(c, statistics) > 0);
    unsigned answer_id = Z3_get_ast_id(c, answer);
    CHECK("fixedpoint-resource.repeated-query", Z3_fixedpoint_query(c, fp, query) == Z3_L_TRUE &&
          Z3_get_error_code(c) == Z3_OK && Z3_get_ast_id(c, answer) == answer_id);
    Z3_fixedpoint_dec_ref(c, fp);
    CHECK("fixedpoint-resource.retained-results-survive-engine-release",
          Z3_get_ast_kind(c, answer) == Z3_APP_AST && Z3_get_ast_id(c, answer) == answer_id &&
          Z3_ast_to_string(c, answer) && strlen(Z3_ast_to_string(c, answer)) > 0 &&
          Z3_stats_size(c, statistics) > 0 &&
          Z3_stats_get_key(c, statistics, 0) != NULL);
    Z3_stats_dec_ref(c, statistics);
    Z3_del_context(c);
    return 0;
}
