// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

/* One context per fixture. Every returned AST is retained before another API
   call; cleanup balances each retain, including hash-consed duplicate ASTs. */
static Z3_ast sequence_roots[1024];
static unsigned sequence_root_count = 0;

static inline Z3_ast sequence_hold(Z3_context c, Z3_ast ast) {
    if (!ast || sequence_root_count == 1024) return NULL;
    Z3_inc_ref(c, ast);
    sequence_roots[sequence_root_count++] = ast;
    return ast;
}

static inline Z3_sort sequence_hold_sort(Z3_context c, Z3_sort sort) {
    if (!sort || !sequence_hold(c, Z3_sort_to_ast(c, sort))) return NULL;
    return sort;
}

static inline void sequence_release(Z3_context c) {
    while (sequence_root_count) Z3_dec_ref(c, sequence_roots[--sequence_root_count]);
}
