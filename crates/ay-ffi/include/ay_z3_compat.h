// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// AY compatibility include based on the historical Z3 5.1.0 C surface.
//
// The standard headers also expose implemented Z3 5.3 additions; their enum
// layout still requires reconciliation. Existing AY users may keep this
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
// AY alias for Z3_tactic_using_params; retains the same typed parameter semantics.
Z3_tactic Z3_API Z3_tactic_with(Z3_context c, Z3_tactic t, Z3_params p);
void Z3_API Z3_solver_set_proof_production(
    Z3_context c,
    Z3_solver s,
    bool enabled);
bool Z3_API Z3_solver_get_proof_production(Z3_context c, Z3_solver s);
// Z3_solver_get_proof exposes real asserted/unit-resolution application DAGs
// for the supported native fragment. Other rules retain opaque Alethe handles
// (UNKNOWN_AST). This named accessor always returns the Alethe artifact.
Z3_string Z3_API Z3_solver_get_proof_string(Z3_context c, Z3_solver s);

#ifdef __cplusplus
}
#endif
