// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("arrays.context-created", c != NULL);
    Z3_sort integer = Z3_mk_int_sort(c); HOLD_SORT(c, integer);
    Z3_sort array = Z3_mk_array_sort(c, integer, integer); HOLD_SORT(c, array);
    CHECK("arrays.sort-reflection", integer && array &&
          Z3_get_sort_kind(c, array) == Z3_ARRAY_SORT &&
          Z3_is_eq_sort(c, Z3_get_array_sort_domain(c, array), integer) &&
          Z3_is_eq_sort(c, Z3_get_array_sort_range(c, array), integer));
    Z3_ast zero = Z3_mk_int(c, 0, integer); HOLD(c, zero);
    Z3_ast one = Z3_mk_int(c, 1, integer); HOLD(c, one);
    Z3_ast two = Z3_mk_int(c, 2, integer); HOLD(c, two);
    Z3_ast seven = Z3_mk_int(c, 7, integer); HOLD(c, seven);
    Z3_ast nine = Z3_mk_int(c, 9, integer); HOLD(c, nine);
    Z3_ast base = Z3_mk_const_array(c, integer, zero); HOLD(c, base);
    Z3_ast stored = Z3_mk_store(c, base, one, seven); HOLD(c, stored);
    Z3_ast base_at_two = Z3_mk_select(c, base, two); HOLD(c, base_at_two);
    Z3_ast stored_at_one = Z3_mk_select(c, stored, one); HOLD(c, stored_at_one);
    Z3_ast stored_at_two = Z3_mk_select(c, stored, two); HOLD(c, stored_at_two);
    CHECK("arrays.term-reflection", zero && one && two && seven && nine && base && stored &&
          base_at_two && stored_at_one && stored_at_two &&
          Z3_is_eq_sort(c, Z3_get_sort(c, base), array) &&
          Z3_is_eq_sort(c, Z3_get_sort(c, stored), array) &&
          Z3_is_eq_sort(c, Z3_get_sort(c, stored_at_one), integer) &&
          Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, base))) == Z3_OP_CONST_ARRAY &&
          Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, stored))) == Z3_OP_STORE &&
          Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, stored_at_one))) == Z3_OP_SELECT);
    CHECK("arrays.constant-array-value", ad_simplified_int(c, base_at_two, 0));
    CHECK("arrays.select-stored-value", ad_simplified_int(c, stored_at_one, 7));
    CHECK("arrays.store-preserves-other-index", ad_simplified_int(c, stored_at_two, 0));
    Z3_ast overwritten = Z3_mk_store(c, stored, one, nine); HOLD(c, overwritten);
    Z3_ast overwritten_at_one = Z3_mk_select(c, overwritten, one); HOLD(c, overwritten_at_one);
    CHECK("arrays.last-store-wins", ad_simplified_int(c, overwritten_at_one, 9));
    Z3_ast a = Z3_mk_const(c, Z3_mk_string_symbol(c, "contract_array_a"), array); HOLD(c, a);
    Z3_ast b = Z3_mk_const(c, Z3_mk_string_symbol(c, "contract_array_b"), array); HOLD(c, b);
    Z3_ast a_at_one = Z3_mk_select(c, a, one); HOLD(c, a_at_one);
    Z3_ast b_at_one = Z3_mk_select(c, b, one); HOLD(c, b_at_one);
    Z3_ast a_at_two = Z3_mk_select(c, a, two); HOLD(c, a_at_two);
    Z3_ast unchanged = Z3_mk_store(c, a, one, a_at_one); HOLD(c, unchanged);
    Z3_ast identity = Z3_mk_eq(c, a, unchanged); HOLD(c, identity);
    Z3_ast not_identity = Z3_mk_not(c, identity); HOLD(c, not_identity);
    Z3_solver solver = Z3_mk_solver(c); if (solver) Z3_solver_inc_ref(c, solver);
    CHECK("arrays.symbolic-terms-created", a && b && a_at_one && b_at_one && a_at_two &&
          unchanged && identity && not_identity && solver);
    CHECK("arrays.read-store-identity", ad_unsatisfiable(c, solver, not_identity));
    /* The pinned header defines array-ext by equal witness reads implying
       equal arrays. This checks that implication without a quantifier. */
    Z3_ast ext = Z3_mk_array_ext(c, a, b); HOLD(c, ext);
    Z3_ast a_at_ext = Z3_mk_select(c, a, ext); HOLD(c, a_at_ext);
    Z3_ast b_at_ext = Z3_mk_select(c, b, ext); HOLD(c, b_at_ext);
    Z3_ast equal_arrays = Z3_mk_eq(c, a, b); HOLD(c, equal_arrays);
    Z3_ast different_arrays = Z3_mk_not(c, equal_arrays); HOLD(c, different_arrays);
    Z3_ast equal_at_ext = Z3_mk_eq(c, a_at_ext, b_at_ext); HOLD(c, equal_at_ext);
    CHECK("arrays.extensional-witness-sort", ext && a_at_ext && b_at_ext && equal_at_ext &&
          different_arrays && Z3_is_eq_sort(c, Z3_get_sort(c, ext), integer));
    Z3_solver_reset(c, solver);
    Z3_solver_assert(c, solver, different_arrays);
    CHECK("arrays.distinct-arrays-satisfiable", Z3_solver_check(c, solver) == Z3_L_TRUE);
    Z3_solver_push(c, solver);
    Z3_solver_assert(c, solver, equal_at_ext);
    CHECK("arrays.extensional-witness-distinguishes", Z3_solver_check(c, solver) == Z3_L_FALSE &&
          Z3_get_error_code(c) == Z3_OK);
    Z3_solver_pop(c, solver, 1);
    CHECK("arrays.extensional-scope-restored", Z3_solver_check(c, solver) == Z3_L_TRUE);
    Z3_ast a_is_stored = Z3_mk_eq(c, a, stored); HOLD(c, a_is_stored);
    Z3_ast b_is_base = Z3_mk_eq(c, b, base); HOLD(c, b_is_base);
    Z3_ast a_is_base = Z3_mk_eq(c, a, base); HOLD(c, a_is_base);
    Z3_solver_reset(c, solver);
    Z3_solver_assert(c, solver, a_is_stored);
    Z3_solver_assert(c, solver, b_is_base);
    CHECK("arrays.concrete-model-satisfiable", Z3_solver_check(c, solver) == Z3_L_TRUE);
    Z3_model model = Z3_solver_get_model(c, solver); if (model) Z3_model_inc_ref(c, model);
    CHECK("arrays.model-select-values", model && ad_model_int(c, model, a_at_one, 7) &&
          ad_model_int(c, model, a_at_two, 0) && ad_model_int(c, model, b_at_one, 0) &&
          ad_model_bool(c, model, different_arrays, Z3_L_TRUE) &&
          ad_model_bool(c, model, equal_arrays, Z3_L_FALSE));
    Z3_solver_push(c, solver);
    Z3_solver_assert(c, solver, a_is_base);
    CHECK("arrays.retained-model-after-contradiction", Z3_solver_check(c, solver) == Z3_L_FALSE &&
          ad_model_int(c, model, a_at_one, 7));
    unsigned retained_id = Z3_get_ast_id(c, stored);
    Z3_solver_dec_ref(c, solver);
    CHECK("arrays.retained-model-after-solver-release", Z3_get_ast_id(c, stored) == retained_id &&
          ad_simplified_int(c, stored_at_one, 7) && ad_model_int(c, model, a_at_one, 7) &&
          ad_model_int(c, model, b_at_one, 0) && Z3_get_error_code(c) == Z3_OK &&
          contract_last_error == Z3_OK);
    Z3_model_dec_ref(c, model);
    Z3_del_context(c);
    return 0;
}
