// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static inline Z3_ast sequence_integer(Z3_context c, Z3_sort sort, int value) {
    return sequence_hold(c, Z3_mk_int(c, value, sort));
}

static inline int sequence_integer_is(Z3_context c, Z3_ast term, int expected) {
    if (!term) return 0;
    Z3_ast value = sequence_hold(c, Z3_simplify(c, term));
    int integer = 0;
    return value && Z3_get_numeral_int(c, value, &integer) && integer == expected;
}

static inline int sequence_boolean_is(Z3_context c, Z3_ast term, Z3_lbool expected) {
    if (!term) return 0;
    Z3_ast value = sequence_hold(c, Z3_simplify(c, term));
    return value && Z3_get_bool_value(c, value) == expected;
}

static inline int sequence_equal_is(Z3_context c, Z3_ast left, Z3_ast right, Z3_lbool expected) {
    if (!left || !right) return 0;
    Z3_ast equality = sequence_hold(c, Z3_mk_eq(c, left, right));
    return sequence_boolean_is(c, equality, expected);
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("sequence.operations.context-created", c != NULL);
    Z3_sort integer = sequence_hold_sort(c, Z3_mk_int_sort(c));
    Z3_sort sequence = sequence_hold_sort(c, Z3_mk_seq_sort(c, integer));
    CHECK("sequence.operations.sort-basis", integer && sequence && Z3_is_seq_sort(c, sequence) &&
          !Z3_is_string_sort(c, sequence) && Z3_is_eq_sort(c, Z3_get_seq_sort_basis(c, sequence), integer));
    Z3_ast zero = sequence_integer(c, integer, 0), one = sequence_integer(c, integer, 1);
    Z3_ast two = sequence_integer(c, integer, 2), five = sequence_integer(c, integer, 5);
    Z3_ast seven = sequence_integer(c, integer, 7), nine = sequence_integer(c, integer, 9);
    Z3_ast empty = sequence_hold(c, Z3_mk_seq_empty(c, sequence));
    Z3_ast u7 = sequence_hold(c, Z3_mk_seq_unit(c, seven));
    Z3_ast u9 = sequence_hold(c, Z3_mk_seq_unit(c, nine));
    CHECK("sequence.operations.empty-and-unit", zero && one && two && five && seven && nine && empty && u7 && u9 &&
          Z3_is_eq_sort(c, Z3_get_sort(c, u7), sequence) && sequence_equal_is(c, u7, u9, Z3_L_FALSE));
    Z3_ast parts[4] = {u7, empty, u9, u7};
    Z3_ast word = sequence_hold(c, Z3_mk_seq_concat(c, 4, parts));
    Z3_ast length = sequence_hold(c, Z3_mk_seq_length(c, word));
    CHECK("sequence.operations.concat-length", word && sequence_integer_is(c, length, 3) && !sequence_integer_is(c, length, 2));
    Z3_ast part = sequence_hold(c, Z3_mk_seq_extract(c, word, one, one));
    Z3_ast tail = sequence_hold(c, Z3_mk_seq_extract(c, word, two, five));
    CHECK("sequence.operations.extract", sequence_equal_is(c, part, u9, Z3_L_TRUE) && sequence_equal_is(c, tail, u7, Z3_L_TRUE));
    Z3_ast at = sequence_hold(c, Z3_mk_seq_at(c, word, one));
    Z3_ast nth = sequence_hold(c, Z3_mk_seq_nth(c, word, one));
    CHECK("sequence.operations.at-and-nth", sequence_equal_is(c, at, u9, Z3_L_TRUE) && sequence_integer_is(c, nth, 9) && !sequence_integer_is(c, nth, 7));
    Z3_ast first = sequence_hold(c, Z3_mk_seq_index(c, word, u7, zero));
    Z3_ast next = sequence_hold(c, Z3_mk_seq_index(c, word, u7, one));
    Z3_ast last = sequence_hold(c, Z3_mk_seq_last_index(c, word, u7));
    CHECK("sequence.operations.index-offset", sequence_integer_is(c, first, 0) && sequence_integer_is(c, next, 2) && sequence_integer_is(c, last, 2));
    Z3_ast contains = sequence_hold(c, Z3_mk_seq_contains(c, word, u9));
    Z3_ast prefix = sequence_hold(c, Z3_mk_seq_prefix(c, u7, word));
    Z3_ast suffix = sequence_hold(c, Z3_mk_seq_suffix(c, u7, word));
    Z3_ast wrong = sequence_hold(c, Z3_mk_seq_prefix(c, u9, word));
    CHECK("sequence.operations.contains-prefix-suffix", sequence_boolean_is(c, contains, Z3_L_TRUE) && sequence_boolean_is(c, prefix, Z3_L_TRUE) && sequence_boolean_is(c, suffix, Z3_L_TRUE) && sequence_boolean_is(c, wrong, Z3_L_FALSE));
    Z3_ast beyond = sequence_hold(c, Z3_mk_seq_at(c, word, five));
    CHECK("sequence.operations.boundary-is-empty", sequence_equal_is(c, beyond, empty, Z3_L_TRUE));
    Z3_ast variable = sequence_hold(c, Z3_mk_const(c, Z3_mk_string_symbol(c, "sequence_value"), sequence));
    Z3_ast equality = sequence_hold(c, Z3_mk_eq(c, variable, word));
    Z3_solver solver = Z3_mk_solver(c);
    if (solver) Z3_solver_inc_ref(c, solver);
    CHECK("sequence.operations.solver-created", variable && equality && solver);
    Z3_solver_assert(c, solver, equality);
    CHECK("sequence.operations.solver-satisfiable", Z3_solver_check(c, solver) == Z3_L_TRUE);
    Z3_model model = Z3_solver_get_model(c, solver);
    if (model) Z3_model_inc_ref(c, model);
    Z3_ast value = NULL;
    int evaluated = model && Z3_model_eval(c, model, variable, false, &value);
    if (evaluated) value = sequence_hold(c, value);
    CHECK("sequence.operations.exact-model-value", evaluated && sequence_equal_is(c, value, word, Z3_L_TRUE));
    Z3_solver_dec_ref(c, solver);
    Z3_ast retained = NULL;
    evaluated = Z3_model_eval(c, model, variable, false, &retained);
    if (evaluated) retained = sequence_hold(c, retained);
    CHECK("sequence.operations.retained-after-solver-release", evaluated && sequence_equal_is(c, retained, word, Z3_L_TRUE));
    Z3_model_dec_ref(c, model);
    sequence_release(c);
    Z3_del_context(c);
    return 0;
}
