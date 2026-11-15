// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("vector.context-created", c != NULL);
    Z3_sort integer = Z3_mk_int_sort(c); HOLD_SORT(c, integer);
    Z3_ast one = Z3_mk_int(c, 1, integer); HOLD(c, one);
    Z3_ast two = Z3_mk_int(c, 2, integer); HOLD(c, two);
    Z3_ast_vector vector = Z3_mk_ast_vector(c); if (vector) Z3_ast_vector_inc_ref(c, vector);
    CHECK("vector.initially-empty", integer && one && two && vector && Z3_ast_vector_size(c, vector) == 0);
    Z3_ast_vector_push(c, vector, one);
    Z3_ast_vector_push(c, vector, two);
    CHECK("vector.push-preserves-order", Z3_ast_vector_size(c, vector) == 2 &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, vector, 0), one) &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, vector, 1), two));
    Z3_ast_vector_set(c, vector, 0, two);
    CHECK("vector.set-preserves-other-elements", Z3_ast_vector_size(c, vector) == 2 &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, vector, 0), two) &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, vector, 1), two));
    Z3_ast_vector_resize(c, vector, 1);
    CHECK("vector.shrink-preserves-prefix", Z3_ast_vector_size(c, vector) == 1 &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, vector, 0), two));
    Z3_context destination = contract_context();
    CHECK("vector.destination-created", destination != NULL);
    Z3_ast_vector translated = Z3_ast_vector_translate(c, vector, destination);
    if (translated) Z3_ast_vector_inc_ref(destination, translated);
    CHECK("vector.translation-created", translated != NULL);
    Z3_ast_vector_dec_ref(c, vector);
    Z3_dec_ref(c, two); Z3_dec_ref(c, one);
    Z3_dec_ref(c, Z3_sort_to_ast(c, integer));
    Z3_del_context(c);
    int actual = 0;
    CHECK("vector.translation-survives-source-destruction", Z3_ast_vector_size(destination, translated) == 1 &&
          Z3_get_numeral_int(destination, Z3_ast_vector_get(destination, translated, 0), &actual) && actual == 2);
    Z3_ast_vector_dec_ref(destination, translated);
    Z3_del_context(destination);
    return 0;
}
