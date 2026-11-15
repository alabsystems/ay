// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("context.created-after-config-deletion", c != NULL);
    Z3_sort integer = Z3_mk_int_sort(c); HOLD_SORT(c, integer);
    Z3_sort boolean = Z3_mk_bool_sort(c); HOLD_SORT(c, boolean);
    CHECK("context.distinct-sorts", integer && boolean &&
          !Z3_is_eq_sort(c, integer, boolean) &&
          Z3_get_sort_kind(c, integer) == Z3_INT_SORT &&
          Z3_get_sort_kind(c, boolean) == Z3_BOOL_SORT);
    Z3_symbol name = Z3_mk_string_symbol(c, "contract_x");
    Z3_symbol numbered = Z3_mk_int_symbol(c, 17);
    CHECK("context.symbol-roundtrip", name && numbered &&
          Z3_get_symbol_kind(c, name) == Z3_STRING_SYMBOL &&
          strcmp(Z3_get_symbol_string(c, name), "contract_x") == 0 &&
          Z3_get_symbol_kind(c, numbered) == Z3_INT_SYMBOL &&
          Z3_get_symbol_int(c, numbered) == 17);
    Z3_ast x = Z3_mk_const(c, name, integer); HOLD(c, x);
    CHECK("context.ast-sort-and-kind", x && Z3_get_ast_kind(c, x) == Z3_APP_AST &&
          Z3_is_eq_sort(c, Z3_get_sort(c, x), integer));
    unsigned id = Z3_get_ast_id(c, x);
    unsigned hash = Z3_get_ast_hash(c, x);
    for (int i = 0; i < 4096; ++i) {
        Z3_ast temporary = Z3_mk_int(c, i, integer); HOLD(c, temporary);
        if (!temporary) return 3;
        Z3_dec_ref(c, temporary);
    }
    Z3_ast same_x = Z3_mk_const(c, name, integer); HOLD(c, same_x);
    CHECK("context.retained-ast-survives-churn", Z3_is_eq_ast(c, x, same_x) &&
          Z3_get_ast_id(c, x) == id && Z3_get_ast_hash(c, x) == hash &&
          strcmp(Z3_ast_to_string(c, x), "contract_x") == 0);
    Z3_context destination = contract_context();
    CHECK("context.destination-created", destination != NULL);
    Z3_ast translated = Z3_translate(c, x, destination); HOLD(destination, translated);
    CHECK("context.translation-created", translated != NULL);
    Z3_dec_ref(c, same_x);
    Z3_dec_ref(c, x);
    Z3_dec_ref(c, Z3_sort_to_ast(c, boolean));
    Z3_dec_ref(c, Z3_sort_to_ast(c, integer));
    Z3_del_context(c);
    Z3_sort destination_integer = Z3_mk_int_sort(destination); HOLD_SORT(destination, destination_integer);
    CHECK("context.translation-survives-source-destruction",
          Z3_is_eq_sort(destination, Z3_get_sort(destination, translated), destination_integer) &&
          strcmp(Z3_ast_to_string(destination, translated), "contract_x") == 0);
    Z3_dec_ref(destination, translated);
    Z3_dec_ref(destination, Z3_sort_to_ast(destination, destination_integer));
    Z3_del_context(destination);
    return 0;
}
