// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

/* Each fixture owns one RC context. Retain every returned AST before a later
   allocation, including sorts, declarations and pattern ASTs. Duplicate
   hash-consed results have one balanced release for every retained reference. */
static Z3_ast quantifier_roots[1024];
static unsigned quantifier_root_count = 0;

static inline Z3_ast quantifier_hold(Z3_context c, Z3_ast ast) {
    if (!ast || quantifier_root_count == 1024) return NULL;
    Z3_inc_ref(c, ast);
    quantifier_roots[quantifier_root_count++] = ast;
    return ast;
}

static inline Z3_sort quantifier_hold_sort(Z3_context c, Z3_sort sort) {
    if (!sort || !quantifier_hold(c, Z3_sort_to_ast(c, sort))) return NULL;
    return sort;
}

/* A wrong provider observation must fail CHECK before a C string operation or
   an API call whose argument is required to be a nonnull, correctly typed AST. */
static inline int quantifier_symbol_is(Z3_context c, Z3_symbol symbol, const char *expected) {
    if (!symbol || Z3_get_symbol_kind(c, symbol) != Z3_STRING_SYMBOL) return 0;
    const char *actual = Z3_get_symbol_string(c, symbol);
    return actual && strcmp(actual, expected) == 0;
}

static inline int quantifier_ast_is(Z3_context c, Z3_ast actual, Z3_ast expected) {
    return actual && expected && Z3_is_eq_ast(c, actual, expected);
}

static inline int quantifier_sort_is(Z3_context c, Z3_sort actual, Z3_sort expected) {
    return actual && expected && Z3_is_eq_sort(c, actual, expected);
}

static inline int quantifier_bound_is(Z3_context c, Z3_ast ast, unsigned index) {
    return ast && Z3_get_ast_kind(c, ast) == Z3_VAR_AST && Z3_get_index_value(c, ast) == index;
}

static inline void quantifier_release(Z3_context c) {
    while (quantifier_root_count) Z3_dec_ref(c, quantifier_roots[--quantifier_root_count]);
}
