// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static inline int opt_model_bool_is(Z3_context c, Z3_model model, Z3_ast term, Z3_lbool expected) {
    Z3_ast value = NULL;
    if (!model || !term || !Z3_model_eval(c, model, term, false, &value) || !value) return 0;
    HOLD(c, value);
    int correct = Z3_get_bool_value(c, value) == expected;
    Z3_dec_ref(c, value);
    return correct;
}
