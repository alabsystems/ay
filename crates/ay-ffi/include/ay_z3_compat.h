// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// AY compatibility include for the exact Z3 5.1.0 C surface.
//
// `z3.h` and every header it includes are byte-for-byte copies from Z3 commit
// 0b6cdcdbc65da25ef0f73ac9da210574d0f66cf8.  Existing AY users may keep this
// include name; stock Z3 C consumers can include `z3.h` directly.

#pragma once

#include "z3.h"

#define AY_Z3_COMPAT_REFERENCE_VERSION "5.1.0"
#define AY_Z3_COMPAT_REFERENCE_COMMIT \
    "0b6cdcdbc65da25ef0f73ac9da210574d0f66cf8"

// AY extensions. These names are deliberately outside the authenticated
// 805-declaration Z3 5.1.0 C inventory and are not evidence of Z3 parity.
#ifdef __cplusplus
extern "C" {
#endif

Z3_ast Z3_API Z3_mk_bvcomp(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_API Z3_mk_set_has_size(Z3_context c, Z3_ast set, Z3_ast k);
void Z3_API Z3_solver_set_proof_production(
    Z3_context c,
    Z3_solver s,
    bool enabled);
bool Z3_API Z3_solver_get_proof_production(Z3_context c, Z3_solver s);
Z3_string Z3_API Z3_solver_get_proof_string(Z3_context c, Z3_solver s);

#ifdef __cplusplus
}
#endif
