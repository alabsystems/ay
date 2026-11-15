// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static inline Z3_model opt_model(Z3_context c, Z3_optimize o) {
    Z3_model result = Z3_optimize_get_model(c, o);
    if (result) Z3_model_inc_ref(c, result);
    return result;
}

static inline int opt_model_rational_is(Z3_context c, Z3_model model, Z3_ast term,
                                 int64_t numerator, int64_t denominator) {
    Z3_ast value = NULL;
    if (!model || !term || !Z3_model_eval(c, model, term, false, &value) || !value) return 0;
    HOLD(c, value);
    int correct = opt_rational_is(c, value, numerator, denominator);
    Z3_dec_ref(c, value);
    return correct;
}
