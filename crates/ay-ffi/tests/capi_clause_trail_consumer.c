// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#include <assert.h>
#include <stdio.h>
#ifdef AY_TWIN_USE_Z3
#include <z3.h>
#else
#include "ay_z3_compat.h"
#endif

static void note_error(Z3_context context, Z3_error_code error) {
    (void)context;
    (void)error;
}

int main(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "proof", "true");
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_set_error_handler(c, note_error);
    Z3_tactic tactic = Z3_mk_tactic(c, "smt");
    Z3_tactic_inc_ref(c, tactic);
    Z3_solver solver = Z3_mk_solver_from_tactic(c, tactic);
    Z3_solver_inc_ref(c, solver);
    Z3_params params = Z3_mk_params(c);
    Z3_params_inc_ref(c, params);
    Z3_params_set_bool(c, params, Z3_mk_string_symbol(c, "clause_proof"), true);
    Z3_solver_set_params(c, solver, params);
    assert(Z3_get_error_code(c) == Z3_OK);
    Z3_solver_from_string(c, solver, "(declare-const a Int)(declare-const b Int)"
        "(declare-fun f (Int) Int)(assert (<= a b))(assert (<= b a))"
        "(assert (distinct (f a) (f b)))");
    assert(Z3_solver_check(c, solver) == Z3_L_FALSE);
    Z3_ast proof_ast = Z3_solver_get_proof(c, solver);
    if (!proof_ast) fprintf(stderr, "proof error %u: %s\n", Z3_get_error_code(c), Z3_get_error_msg(c, Z3_get_error_code(c)));
    assert(proof_ast);
    Z3_app proof = Z3_to_app(c, proof_ast);
    assert(Z3_get_decl_kind(c, Z3_get_app_decl(c, proof)) == Z3_OP_PR_CLAUSE_TRAIL);
    unsigned axiom = 0, lemma = 0;
    unsigned n = Z3_get_app_num_args(c, proof);
    assert(n > 1);
    for (unsigned i = 0; i + 1 < n; ++i) {
        Z3_app event = Z3_to_app(c, Z3_get_app_arg(c, proof, i));
        Z3_decl_kind kind = Z3_get_decl_kind(c, Z3_get_app_decl(c, event));
        if (kind == Z3_OP_PR_REDUNDANT_DEL) {
            assert(Z3_get_app_num_args(c, event) == 1);
            Z3_sort fact_sort = Z3_get_sort(c, Z3_get_app_arg(c, event, 0));
            assert(Z3_get_sort_kind(c, fact_sort) == Z3_BOOL_SORT);
        }
        if (kind == Z3_OP_PR_TH_ASSUMPTION_ADD || kind == Z3_OP_PR_TH_LEMMA_ADD) {
            unsigned arity = Z3_get_app_num_args(c, event);
            assert(arity == 1 || arity == 2);
            if (arity == 2) {
                Z3_ast justification = Z3_get_app_arg(c, event, 0);
                assert(Z3_get_ast_kind(c, justification) == Z3_APP_AST);
                assert(Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, justification))) != Z3_OP_UNINTERPRETED);
            }
            axiom += kind == Z3_OP_PR_TH_ASSUMPTION_ADD;
            lemma += kind == Z3_OP_PR_TH_LEMMA_ADD;
        }
    }
    assert(axiom && lemma);
    assert(Z3_get_bool_value(c, Z3_get_app_arg(c, proof, n - 1)) == Z3_L_FALSE);
    printf("clause-trail entries=%u theory-assumptions=%u theory-lemmas=%u\n", n - 1, axiom, lemma);
    Z3_solver other = Z3_mk_solver(c);
    Z3_solver_inc_ref(c, other);
    assert(Z3_solver_check(c, other) == Z3_L_TRUE);
    Z3_solver_assert(c, other, Z3_mk_false(c));
    assert(Z3_solver_check(c, other) == Z3_L_FALSE);
    Z3_ast ordinary = Z3_solver_get_proof(c, other);
    assert(ordinary);
    assert(Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, ordinary))) != Z3_OP_PR_CLAUSE_TRAIL);
    assert(Z3_get_app_num_args(c, proof) == n);
    Z3_solver_reset(c, solver);
    assert(Z3_solver_check(c, solver) == Z3_L_TRUE);
    assert(Z3_get_app_num_args(c, proof) == n);
    assert(Z3_solver_get_proof(c, solver) == 0);
    assert(Z3_get_error_code(c) == Z3_INVALID_USAGE);
    Z3_solver_dec_ref(c, other);
    Z3_params_dec_ref(c, params);
    Z3_solver_dec_ref(c, solver);
    Z3_tactic_dec_ref(c, tactic);
    Z3_del_context(c);
}
