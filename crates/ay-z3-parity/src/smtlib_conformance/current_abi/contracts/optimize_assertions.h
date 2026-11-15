// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static inline Z3_ast_vector opt_assertions(Z3_context c, Z3_optimize o) {
    Z3_ast_vector result = Z3_optimize_get_assertions(c, o);
    if (result) Z3_ast_vector_inc_ref(c, result);
    return result;
}
