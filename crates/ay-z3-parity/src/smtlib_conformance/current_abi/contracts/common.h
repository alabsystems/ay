// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

/* Executable current-release ABI contracts; compiled with authenticated z3.h. */
#include "z3.h"
#include <stdio.h>
#include <string.h>

static Z3_error_code contract_last_error = Z3_OK;
static void contract_error_handler(Z3_context c, Z3_error_code error) {
    (void)c;
    contract_last_error = error;
}

static Z3_context contract_context(void) {
    Z3_config config = Z3_mk_config();
    if (!config) return NULL;
    Z3_set_param_value(config, "model", "true");
    Z3_context context = Z3_mk_context_rc(config);
    Z3_del_config(config);
    if (context) Z3_set_error_handler(context, contract_error_handler);
    return context;
}

#ifdef AY_CONTRACT_NEGATIVE_CHECK
#define CONTRACT_CHECK_RESULT(id, condition) \
    (strcmp((id), AY_CONTRACT_NEGATIVE_CHECK) == 0 ? !(condition) : !!(condition))
#else
#define CONTRACT_CHECK_RESULT(id, condition) (!!(condition))
#endif

#define CHECK(id, condition) do { \
    if (!CONTRACT_CHECK_RESULT(id, condition)) { fprintf(stderr, "ABI_CONTRACT_FAILED:%s\n", id); return 2; } \
    puts(id); \
} while (0)
#define HOLD(context, ast) do { if (ast) Z3_inc_ref(context, ast); } while (0)
#define HOLD_SORT(context, sort) do { \
    if (sort) Z3_inc_ref(context, Z3_sort_to_ast(context, sort)); \
} while (0)
