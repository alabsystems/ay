// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static inline Z3_ast sequence_string(Z3_context c, const char* text) {
    return sequence_hold(c, Z3_mk_string(c, text));
}

static inline int sequence_boolean_is(Z3_context c, Z3_ast term, Z3_lbool expected) {
    if (!term) return 0;
    Z3_ast value = sequence_hold(c, Z3_simplify(c, term));
    return value && Z3_get_bool_value(c, value) == expected;
}

static inline int sequence_membership_is(Z3_context c, Z3_ast word, Z3_ast regex, Z3_lbool expected) {
    if (!word || !regex) return 0;
    Z3_ast membership = sequence_hold(c, Z3_mk_seq_in_re(c, word, regex));
    return sequence_boolean_is(c, membership, expected);
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("regex.membership.context-created", c != NULL);
    Z3_sort string = sequence_hold_sort(c, Z3_mk_string_sort(c));
    Z3_sort regex = sequence_hold_sort(c, Z3_mk_re_sort(c, string));
    CHECK("regex.membership.sort-basis", string && regex && Z3_is_re_sort(c, regex) &&
          Z3_is_eq_sort(c, Z3_get_re_sort_basis(c, regex), string) && !Z3_is_seq_sort(c, regex));
    Z3_ast empty_word = sequence_string(c, ""), a = sequence_string(c, "a"), b = sequence_string(c, "b");
    Z3_ast ab = sequence_string(c, "ab"), ba = sequence_string(c, "ba"), xy = sequence_string(c, "xy");
    Z3_ast abab = sequence_string(c, "abab"), aba = sequence_string(c, "aba"), ababab = sequence_string(c, "ababab");
    Z3_ast literal = sequence_hold(c, Z3_mk_seq_to_re(c, ab));
    CHECK("regex.membership.literal-exact-language", sequence_membership_is(c, ab, literal, Z3_L_TRUE) && sequence_membership_is(c, ba, literal, Z3_L_FALSE) && sequence_membership_is(c, empty_word, literal, Z3_L_FALSE));
    Z3_ast other = sequence_hold(c, Z3_mk_seq_to_re(c, xy));
    Z3_ast union_parts[2] = {literal, other};
    Z3_ast either = sequence_hold(c, Z3_mk_re_union(c, 2, union_parts));
    CHECK("regex.membership.union", sequence_membership_is(c, ab, either, Z3_L_TRUE) && sequence_membership_is(c, xy, either, Z3_L_TRUE) && sequence_membership_is(c, ba, either, Z3_L_FALSE));
    Z3_ast ra = sequence_hold(c, Z3_mk_seq_to_re(c, a)), rb = sequence_hold(c, Z3_mk_seq_to_re(c, b));
    Z3_ast concat_parts[2] = {ra, rb};
    Z3_ast concatenated = sequence_hold(c, Z3_mk_re_concat(c, 2, concat_parts));
    CHECK("regex.membership.concat-order", sequence_membership_is(c, ab, concatenated, Z3_L_TRUE) && sequence_membership_is(c, ba, concatenated, Z3_L_FALSE));
    Z3_ast star = sequence_hold(c, Z3_mk_re_star(c, literal));
    Z3_ast plus = sequence_hold(c, Z3_mk_re_plus(c, literal));
    CHECK("regex.membership.star-versus-plus", sequence_membership_is(c, empty_word, star, Z3_L_TRUE) && sequence_membership_is(c, empty_word, plus, Z3_L_FALSE) && sequence_membership_is(c, abab, star, Z3_L_TRUE) && sequence_membership_is(c, abab, plus, Z3_L_TRUE) && sequence_membership_is(c, aba, star, Z3_L_FALSE));
    Z3_ast optional = sequence_hold(c, Z3_mk_re_option(c, literal));
    CHECK("regex.membership.optional", sequence_membership_is(c, empty_word, optional, Z3_L_TRUE) && sequence_membership_is(c, ab, optional, Z3_L_TRUE) && sequence_membership_is(c, abab, optional, Z3_L_FALSE));
    Z3_ast loop = sequence_hold(c, Z3_mk_re_loop(c, literal, 2, 3));
    CHECK("regex.membership.bounded-loop", sequence_membership_is(c, abab, loop, Z3_L_TRUE) && sequence_membership_is(c, ababab, loop, Z3_L_TRUE) && sequence_membership_is(c, ab, loop, Z3_L_FALSE) && sequence_membership_is(c, empty_word, loop, Z3_L_FALSE));
    Z3_ast c_text = sequence_string(c, "c"), d_text = sequence_string(c, "d");
    Z3_ast range = sequence_hold(c, Z3_mk_re_range(c, a, c_text));
    CHECK("regex.membership.character-range", sequence_membership_is(c, a, range, Z3_L_TRUE) && sequence_membership_is(c, b, range, Z3_L_TRUE) && sequence_membership_is(c, c_text, range, Z3_L_TRUE) && sequence_membership_is(c, d_text, range, Z3_L_FALSE) && sequence_membership_is(c, ab, range, Z3_L_FALSE));
    Z3_ast without_a = sequence_hold(c, Z3_mk_re_diff(c, range, ra));
    Z3_ast intersect_parts[2] = {range, rb};
    Z3_ast intersection = sequence_hold(c, Z3_mk_re_intersect(c, 2, intersect_parts));
    CHECK("regex.membership.difference-and-intersection", sequence_membership_is(c, b, without_a, Z3_L_TRUE) && sequence_membership_is(c, a, without_a, Z3_L_FALSE) && sequence_membership_is(c, b, intersection, Z3_L_TRUE) && sequence_membership_is(c, c_text, intersection, Z3_L_FALSE));
    Z3_ast complement = sequence_hold(c, Z3_mk_re_complement(c, literal));
    Z3_ast allchar = sequence_hold(c, Z3_mk_re_allchar(c, regex));
    CHECK("regex.membership.complement-and-allchar", sequence_membership_is(c, ab, complement, Z3_L_FALSE) && sequence_membership_is(c, ba, complement, Z3_L_TRUE) && sequence_membership_is(c, a, allchar, Z3_L_TRUE) && sequence_membership_is(c, ab, allchar, Z3_L_FALSE));
    Z3_ast none = sequence_hold(c, Z3_mk_re_empty(c, regex));
    Z3_ast all = sequence_hold(c, Z3_mk_re_full(c, regex));
    CHECK("regex.membership.empty-versus-full", sequence_membership_is(c, empty_word, none, Z3_L_FALSE) && sequence_membership_is(c, ab, none, Z3_L_FALSE) && sequence_membership_is(c, empty_word, all, Z3_L_TRUE) && sequence_membership_is(c, ab, all, Z3_L_TRUE));
    sequence_release(c);
    Z3_del_context(c);
    return 0;
}
