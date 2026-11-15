// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C consumer for the Z3-compatible solver-completion C API (wave 2):
//   Z3_solver_assert_and_track, Z3_solver_get_unsat_core (tracked cores),
//   Z3_solver_from_string / Z3_solver_from_file, Z3_solver_translate,
//   Z3_solver_get_consequences, Z3_solver_get_units / _non_units / _trail,
//   Z3_solver_get_help, Z3_solver_congruence_root / _next,
//   Z3_solver_to_dimacs_string.
//
// This single source compiles and runs against BOTH ay-ffi (default) and libz3
// 4.15.4 (`-DAY_TWIN_USE_Z3`). Every non-guarded assertion is a value that libz3
// itself returns for the SAME input (verified out-of-band), so passing on both
// engines is the cross-check: ay's observable behavior == libz3's on the
// supported surface. Blocks guarded by `#ifndef AY_TWIN_USE_Z3` are AY-specific
// (documented honest divergences: consequence terms are pre-simplified, the
// congruence ring is a singleton, DIMACS is the propositional skeleton, and the
// trail is the level-0 portion — each SOUND and never fabricated).

#ifdef AY_TWIN_USE_Z3
#include <z3.h>
#else
#include "ay.h"
#include "ay_z3_compat.h"
#endif

#include <stdio.h>
#include <string.h>

static int g_pass = 0;
static int g_fail = 0;

#define CHECK_U(actual, expected, what)                                        \
    do {                                                                       \
        unsigned a_ = (unsigned)(actual);                                      \
        unsigned e_ = (unsigned)(expected);                                    \
        if (a_ == e_) {                                                        \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s: got %u want %u\n", (what), a_, e_);               \
        }                                                                      \
    } while (0)

#define CHECK_B(actual, expected, what)                                        \
    do {                                                                       \
        int a_ = (actual) ? 1 : 0;                                             \
        int e_ = (expected) ? 1 : 0;                                           \
        if (a_ == e_) {                                                        \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s: got %d want %d\n", (what), a_, e_);               \
        }                                                                      \
    } while (0)

static Z3_ast bool_var(Z3_context c, const char *n) {
    return Z3_mk_const(c, Z3_mk_string_symbol(c, n), Z3_mk_bool_sort(c));
}
static Z3_ast int_var(Z3_context c, const char *n) {
    return Z3_mk_const(c, Z3_mk_string_symbol(c, n), Z3_mk_int_sort(c));
}

// Whether an ast_vector contains an element whose to_string equals `needle`.
static int vec_contains_str(Z3_context c, Z3_ast_vector v, const char *needle) {
    unsigned n = Z3_ast_vector_size(c, v);
    for (unsigned i = 0; i < n; i++) {
        const char *s = Z3_ast_to_string(c, Z3_ast_vector_get(c, v, i));
        if (s && strcmp(s, needle) == 0) {
            return 1;
        }
    }
    return 0;
}

// Whether the concatenation of an ast_vector's element strings contains `needle`.
static int vec_any_substr(Z3_context c, Z3_ast_vector v, const char *needle) {
    unsigned n = Z3_ast_vector_size(c, v);
    for (unsigned i = 0; i < n; i++) {
        const char *s = Z3_ast_to_string(c, Z3_ast_vector_get(c, v, i));
        if (s && strstr(s, needle) != NULL) {
            return 1;
        }
    }
    return 0;
}

static void check_native_proof_applications(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "proof", "true");
    Z3_context c = Z3_mk_context_rc(cfg);
    Z3_del_config(cfg);
    Z3_set_error_handler(c, NULL);
    Z3_solver solver = Z3_mk_solver(c);
    Z3_solver_inc_ref(c, solver);
    Z3_ast falsity = Z3_mk_false(c);
    Z3_inc_ref(c, falsity);
    Z3_solver_assert(c, solver, falsity);
    CHECK_U(Z3_solver_check(c, solver), Z3_L_FALSE, "proof: genuine unsat");
    Z3_ast proof = Z3_solver_get_proof(c, solver);
    CHECK_B(proof != NULL, 1, "proof: available");
    if (!proof) { Z3_del_context(c); return; }
    Z3_inc_ref(c, proof);
    CHECK_U(Z3_get_ast_kind(c, proof), Z3_APP_AST, "proof: application kind");
    CHECK_B(Z3_is_app(c, proof), 1, "proof: is app");
    Z3_app app = Z3_to_app(c, proof);
    CHECK_B((Z3_ast)app == proof, 1, "proof: to-app identity");
    if (!app) { Z3_del_context(c); return; }
    CHECK_U(Z3_get_app_num_args(c, app), 1, "proof: asserted arity");
    CHECK_B(Z3_is_eq_ast(c, Z3_get_app_arg(c, app, 0), falsity), 1, "proof: real false argument");
    Z3_func_decl rule = Z3_get_app_decl(c, app);
    CHECK_U(Z3_get_decl_kind(c, rule), Z3_OP_PR_ASSERTED, "proof: actual asserted rule");
    CHECK_B(strcmp(Z3_get_symbol_string(c, Z3_get_decl_name(c, rule)), "asserted") == 0, 1, "proof: rule name");
    Z3_sort proof_sort = Z3_get_sort(c, proof);
    CHECK_U(Z3_get_sort_kind(c, proof_sort), Z3_UNKNOWN_SORT, "proof: native proof sort");
    CHECK_B(strcmp(Z3_sort_to_string(c, proof_sort), "Proof") == 0, 1, "proof: sort name");
    CHECK_B(Z3_is_eq_sort(c, proof_sort, Z3_get_range(c, rule)), 1, "proof: rule range");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_domain(c, rule, 0)), Z3_BOOL_SORT, "proof: asserted domain");
    CHECK_B(Z3_is_eq_ast(c, proof, Z3_solver_get_proof(c, solver)), 1, "proof: hash-consed retrieval");
    CHECK_B(strcmp(Z3_ast_to_string(c, proof), "(asserted false)") == 0, 1, "proof: structural rendering");
    Z3_solver_reset(c, solver);
    Z3_solver_assert(c, solver, Z3_mk_true(c));
    CHECK_U(Z3_solver_check(c, solver), Z3_L_TRUE, "proof: later sat");
    CHECK_U(Z3_get_app_num_args(c, app), 1, "proof: retained after solver reset");
    const char *eval = Z3_eval_smtlib2_string(c,
        "(set-option :produce-proofs true)(assert false)(check-sat)(get-proof)(reset)");
    CHECK_B(eval != NULL && strstr(eval, "unsat") != NULL, 1, "proof: real eval proof stays separate");
    CHECK_U(Z3_get_app_num_args(c, app), 1, "proof: retained after command reset");
    Z3_solver_reset(c, solver);
    Z3_ast atom = bool_var(c, "proof_atom");
    Z3_inc_ref(c, atom);
    Z3_ast negated = Z3_mk_not(c, atom);
    Z3_inc_ref(c, negated);
    Z3_solver_assert(c, solver, atom);
    Z3_solver_assert(c, solver, negated);
    CHECK_U(Z3_solver_check(c, solver), Z3_L_FALSE, "proof: contradictory literals unsat");
    Z3_ast resolution = Z3_solver_get_proof(c, solver);
    CHECK_B(resolution != NULL, 1, "proof: contradictory literals proof available");
    CHECK_U(Z3_get_ast_kind(c, resolution), Z3_APP_AST, "proof: unit resolution application");
    if (Z3_get_ast_kind(c, resolution) == Z3_APP_AST) {
        Z3_app root = Z3_to_app(c, resolution);
        CHECK_U(Z3_get_decl_kind(c, Z3_get_app_decl(c, root)), Z3_OP_PR_UNIT_RESOLUTION, "proof: unit resolution rule");
        CHECK_U(Z3_get_app_num_args(c, root), 3, "proof: two premises and conclusion");
        CHECK_B(Z3_is_eq_ast(c, Z3_get_app_arg(c, root, 2), falsity), 1, "proof: resolution concludes false");
        Z3_ast literals[2];
        for (unsigned i = 0; i < 2; i++) {
            Z3_app premise = Z3_to_app(c, Z3_get_app_arg(c, root, i));
            CHECK_U(Z3_get_decl_kind(c, Z3_get_app_decl(c, premise)), Z3_OP_PR_ASSERTED, "proof: genuine asserted premise");
            CHECK_U(Z3_get_app_num_args(c, premise), 1, "proof: asserted premise arity");
            literals[i] = Z3_get_app_arg(c, premise, 0);
        }
        CHECK_B((Z3_is_eq_ast(c, literals[0], atom) && Z3_is_eq_ast(c, literals[1], negated)) ||
                (Z3_is_eq_ast(c, literals[0], negated) && Z3_is_eq_ast(c, literals[1], atom)),
                1, "proof: both actual complementary assertions");
    }
    Z3_dec_ref(c, negated);
    Z3_dec_ref(c, atom);
#ifndef AY_TWIN_USE_Z3
    Z3_ast parent_integer = int_var(c, "bridge_atom");
    Z3_inc_ref(c, parent_integer);
    const char *bridged = Z3_eval_smtlib2_string(c,
        "(set-option :produce-proofs true)(declare-const bridge_atom Bool)"
        "(push 1)(assert bridge_atom)(check-sat-assuming ((not bridge_atom)))"
        "(get-proof)(pop 1)(check-sat)(reset)");
    CHECK_B(bridged != NULL && strstr(bridged, "(unit-resolution") != NULL,
            1, "proof: eval proof structurally imported");
    CHECK_B(bridged != NULL && strstr(bridged, "(asserted bridge_atom)") != NULL &&
            strstr(bridged, "(asserted (not bridge_atom))") != NULL,
            1, "proof: imported actual eval premises");
    CHECK_B(bridged != NULL && strncmp(bridged, "unsat\n", 6) == 0 &&
            strstr(bridged, "\nsat\n") != NULL, 1, "proof: scoped eval assumptions restored");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_sort(c, parent_integer)), Z3_INT_SORT,
            "proof: source reset preserves distinct parent arena");
    CHECK_U(Z3_get_app_num_args(c, app), 1, "proof: eval import preserves existing proof");
    Z3_dec_ref(c, parent_integer);
#endif
#ifndef AY_TWIN_USE_Z3
    Z3_ast forged = Z3_mk_app(c, rule, 1, &falsity);
    CHECK_B(forged == NULL, 1, "proof: cannot forge a derivation");
    CHECK_U(Z3_get_error_code(c), Z3_INVALID_USAGE, "proof: forgery rejected");
    CHECK_B(Z3_get_app_arg(c, app, 1) == NULL, 1, "proof: argument bounds");
    CHECK_U(Z3_get_error_code(c), Z3_IOB, "proof: argument bounds error");
    Z3_context foreign = Z3_mk_context(NULL);
    Z3_set_error_handler(foreign, NULL);
    CHECK_B(Z3_get_app_decl(foreign, (Z3_app)proof) == NULL, 1, "proof: foreign context rejected");
    CHECK_U(Z3_get_error_code(foreign), Z3_INVALID_ARG, "proof: foreign rejection error");
    Z3_del_context(foreign);
#endif
    Z3_dec_ref(c, proof);
    Z3_dec_ref(c, falsity);
    Z3_solver_dec_ref(c, solver);
    Z3_del_context(c);
}

#ifndef AY_TWIN_USE_Z3
struct proof_checker_state {
    unsigned calls;
    int tracked;
    int resolution;
    int null_report;
    int unregister;
    Z3_ast retained;
    Z3_ast_vector retained_inputs;
};

static Z3_string client_proof_checker(void *user, Z3_context c, Z3_ast proof, Z3_ast_vector inputs) {
    struct proof_checker_state *state = user;
    state->calls++;
    CHECK_U(Z3_get_ast_kind(c, proof), Z3_APP_AST, "callback: real proof application");
    Z3_app app = Z3_to_app(c, proof);
    Z3_func_decl rule = Z3_get_app_decl(c, app);
    CHECK_U(Z3_get_decl_kind(c, rule), state->tracked ? Z3_OP_PR_MODUS_PONENS :
            (state->resolution ? Z3_OP_PR_UNIT_RESOLUTION : Z3_OP_PR_ASSERTED),
            "callback: actual proof rule");
    CHECK_U(Z3_ast_vector_size(c, inputs), state->tracked || state->resolution ? 2 : 1, "callback: exact active input count");
    if (state->tracked) {
        Z3_ast guard = Z3_ast_vector_get(c, inputs, 0);
        Z3_ast label = Z3_ast_vector_get(c, inputs, 1);
        CHECK_U(Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, guard))), Z3_OP_IMPLIES,
                "callback: guarded tracked assertion");
        CHECK_U(Z3_get_app_num_args(c, Z3_to_app(c, guard)), 2, "callback: guard arity");
        CHECK_B(Z3_is_eq_ast(c, Z3_get_app_arg(c, Z3_to_app(c, guard), 0), label), 1,
                "callback: exact tracking literal identity");
        CHECK_U(Z3_get_bool_value(c, Z3_get_app_arg(c, Z3_to_app(c, guard), 1)), Z3_L_FALSE,
                "callback: original false assertion");
        const char *label_text = Z3_ast_to_string(c, label);
        CHECK_B(label_text != NULL && strcmp(label_text, "tracked_false") == 0, 1, "callback: tracking name");
        CHECK_U(Z3_get_app_num_args(c, app), 3, "callback: real modus ponens arity");
        for (unsigned i = 0; i < 2; i++) {
            Z3_app premise = Z3_to_app(c, Z3_get_app_arg(c, app, i));
            CHECK_U(Z3_get_decl_kind(c, Z3_get_app_decl(c, premise)), Z3_OP_PR_ASSERTED,
                    "callback: tracked asserted premise");
            CHECK_B(Z3_is_eq_ast(c, Z3_get_app_arg(c, premise, 0), i == 0 ? label : guard), 1,
                    "callback: premise is exact vector input");
        }
        CHECK_U(Z3_get_bool_value(c, Z3_get_app_arg(c, app, 2)), Z3_L_FALSE,
                "callback: tracked proof concludes false");
    }
    if (state->resolution) {
        CHECK_U(Z3_get_app_num_args(c, app), 3, "callback: actual assumption resolution");
        Z3_ast first = Z3_get_app_arg(c, Z3_to_app(c, Z3_get_app_arg(c, app, 0)), 0);
        Z3_ast second = Z3_get_app_arg(c, Z3_to_app(c, Z3_get_app_arg(c, app, 1)), 0);
        Z3_ast input0 = Z3_ast_vector_get(c, inputs, 0);
        Z3_ast input1 = Z3_ast_vector_get(c, inputs, 1);
        CHECK_B((Z3_is_eq_ast(c, first, input0) && Z3_is_eq_ast(c, second, input1)) ||
                (Z3_is_eq_ast(c, first, input1) && Z3_is_eq_ast(c, second, input0)),
                1, "callback: assertion and current check assumption bound");
        CHECK_U(Z3_get_bool_value(c, Z3_get_app_arg(c, app, 2)), Z3_L_FALSE,
                "callback: assumption proof concludes false");
    }
    // Reentrant ordinary AST construction/vector use must not alias a live
    // Rust context borrow in the evaluator.
    Z3_ast constructed = Z3_mk_not(c, Z3_mk_false(c));
    CHECK_U(Z3_get_bool_value(c, constructed), Z3_L_TRUE, "callback: construct AST in same context");
    if (!state->retained) {
        state->retained = proof;
        state->retained_inputs = inputs;
        Z3_inc_ref(c, proof);
        Z3_ast_vector_inc_ref(c, inputs);
    }
    if (state->unregister) { Z3_set_proof_check_callback(c, NULL, NULL); }
    return state->null_report ? NULL : "client checked";
}

static void check_eval_proof_callback(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "proof", "true");
    Z3_context c = Z3_mk_context_rc(cfg);
    Z3_del_config(cfg);
    Z3_set_error_handler(c, NULL);
    struct proof_checker_state state = {0};
    state.tracked = 1;
    state.unregister = 1;
    Z3_set_proof_check_callback(c, &state, client_proof_checker);
    Z3_solver solver = Z3_mk_solver(c);
    Z3_solver_assert(c, solver, Z3_mk_false(c));
    CHECK_U(Z3_solver_check(c, solver), Z3_L_FALSE, "callback: ordinary C unsat");
    CHECK_U(state.calls, 0, "callback: ordinary check does not invoke checker");
    const char *reply = Z3_eval_smtlib2_string(c,
        "(set-option :produce-unsat-cores true)(assert (! false :named tracked_false))"
        "(check-sat)(check-sat)(reset)");
    CHECK_U(state.calls, 1, "callback: self-unregister takes effect before next check");
    CHECK_B(reply != NULL && strstr(reply, "unsat\nclient checked\nunsat\n") != NULL,
            1, "callback: copied report and unchanged verdicts");
    CHECK_U(Z3_get_error_code(c), Z3_OK, "callback: successful evaluation");
    CHECK_U(Z3_get_ast_kind(c, state.retained), Z3_APP_AST, "callback: retained proof survives reset");
    CHECK_U(Z3_ast_vector_size(c, state.retained_inputs), 2, "callback: retained inputs survive reset");
    state.tracked = 0;
    state.unregister = 0;
    Z3_set_proof_check_callback(c, &state, client_proof_checker);
    reply = Z3_eval_smtlib2_string(c, "(reset)(set-option :produce-proofs true)(assert false)(check-sat-using smt)");
    CHECK_U(state.calls, 2, "callback: registration survives reset and tactic check");
    CHECK_B(reply != NULL && strstr(reply, "client checked") != NULL, 1, "callback: report after reset");
    state.resolution = 1;
    reply = Z3_eval_smtlib2_string(c,
        "(reset)(set-option :produce-proofs true)(declare-const callback_atom Bool)"
        "(assert callback_atom)(check-sat-assuming ((not callback_atom)))");
    CHECK_U(state.calls, 3, "callback: check-sat-assuming invokes checker");
    CHECK_B(reply != NULL && strstr(reply, "client checked") != NULL, 1, "callback: assumption report");
    state.resolution = 0;
    state.null_report = 1;
    reply = Z3_eval_smtlib2_string(c, "(reset)(set-option :produce-proofs true)(assert false)(check-sat)");
    CHECK_B(reply != NULL && strstr(reply, "unsat") != NULL && strstr(reply, "returned null") != NULL,
            1, "callback: null report is command error, retains verdict");
    CHECK_U(Z3_get_error_code(c), Z3_PARSER_ERROR, "callback: null report error code");
    Z3_set_proof_check_callback(c, NULL, NULL);
    Z3_dec_ref(c, state.retained);
    Z3_ast_vector_dec_ref(c, state.retained_inputs);
    Z3_del_context(c);

    c = Z3_mk_context(NULL);
    Z3_set_error_handler(c, NULL);
    memset(&state, 0, sizeof(state));
    Z3_set_proof_check_callback(c, &state, client_proof_checker);
    reply = Z3_eval_smtlib2_string(c, "(assert false)(set-option :produce-proofs true)(check-sat)");
    CHECK_U(state.calls, 0, "callback: cannot enable proofs after assertions");
    CHECK_B(reply != NULL && strstr(reply, "proof production before assertions") != NULL,
            1, "callback: unavailable proof data is command error");
    CHECK_U(Z3_get_error_code(c), Z3_PARSER_ERROR, "callback: unavailable proof error code");
    reply = Z3_eval_smtlib2_string(c,
        "(reset)(set-option :produce-proofs true)(set-option :produce-unsat-cores true)"
        "(assert (! (! false :named inner_label) :named outer_label))(check-sat)");
    CHECK_U(state.calls, 0, "callback: ambiguous named binding never invokes client");
    CHECK_B(reply != NULL && strstr(reply, "unsat") != NULL &&
            strstr(reply, "premise binding") != NULL,
            1, "callback: unsupported binding is explicit command error");
    CHECK_U(Z3_get_error_code(c), Z3_PARSER_ERROR, "callback: unsupported binding error code");
    Z3_del_context(c);
}
#endif

int main(int argc, char **argv) {
    setbuf(stdout, NULL);
    check_native_proof_applications();
#ifndef AY_TWIN_USE_Z3
    check_eval_proof_callback();
#endif
    if (argc == 2 && strcmp(argv[1], "proof-dag") == 0) {
        printf("native proof application checks: %d passed, %d failed\n", g_pass, g_fail);
        return g_fail ? 1 : 0;
    }
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // ---- 1. assert_and_track: build an UNSAT core from tracking literals ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast a = bool_var(c, "a");
        Z3_ast p1 = bool_var(c, "p1");
        Z3_ast p2 = bool_var(c, "p2");
        Z3_solver_assert_and_track(c, s, a, p1);              // track a  by p1
        Z3_solver_assert_and_track(c, s, Z3_mk_not(c, a), p2); // track !a by p2
        CHECK_U(Z3_solver_check(c, s), (unsigned)Z3_L_FALSE, "track: check UNSAT");
        Z3_ast_vector core = Z3_solver_get_unsat_core(c, s);
        Z3_ast_vector_inc_ref(c, core);
        CHECK_U(Z3_ast_vector_size(c, core), 2, "track: core size");
        CHECK_B(vec_contains_str(c, core, "p1"), 1, "track: core has p1");
        CHECK_B(vec_contains_str(c, core, "p2"), 1, "track: core has p2");
        Z3_ast_vector_dec_ref(c, core);
        Z3_solver_dec_ref(c, s);
    }

    // ---- 2. from_string: parse+append, then solve ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast x = int_var(c, "x");
        Z3_solver_assert(c, s, Z3_mk_eq(c, x, Z3_mk_int(c, 5, Z3_mk_int_sort(c))));
        Z3_solver_from_string(c, s, "(declare-const y Int)(assert (= y 7))");
        Z3_ast_vector av = Z3_solver_get_assertions(c, s);
        Z3_ast_vector_inc_ref(c, av);
        CHECK_U(Z3_ast_vector_size(c, av), 2, "from_string: appended assertions");
        CHECK_U(Z3_solver_check(c, s), (unsigned)Z3_L_TRUE, "from_string: SAT");
        Z3_ast_vector_dec_ref(c, av);
        Z3_solver_dec_ref(c, s);
    }

    // ---- 2b. from_string that is UNSAT ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_from_string(
            c, s, "(declare-const z Int)(assert (> z 10))(assert (< z 3))");
        CHECK_U(Z3_solver_check(c, s), (unsigned)Z3_L_FALSE, "from_string: UNSAT");
        Z3_solver_dec_ref(c, s);
    }

    // ---- 3. from_file: write a temp SMT-LIB2 file, load it, solve ----
    {
        const char *path = "/tmp/ay_capi_solver_completion.smt2";
        FILE *f = fopen(path, "w");
        if (f) {
            fputs("(declare-const w Int)\n(assert (= w 42))\n", f);
            fclose(f);
            Z3_solver s = Z3_mk_solver(c);
            Z3_solver_inc_ref(c, s);
            Z3_solver_from_file(c, s, path);
            Z3_ast_vector av = Z3_solver_get_assertions(c, s);
            Z3_ast_vector_inc_ref(c, av);
            CHECK_U(Z3_ast_vector_size(c, av), 1, "from_file: one assertion");
            CHECK_U(Z3_solver_check(c, s), (unsigned)Z3_L_TRUE, "from_file: SAT");
            Z3_ast_vector_dec_ref(c, av);
            Z3_solver_dec_ref(c, s);
        } else {
            g_fail++;
            printf("FAIL from_file: could not create temp file\n");
        }
    }

    // ---- 4. translate: copy a solver into a fresh context and re-solve ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast x = int_var(c, "tx");
        Z3_solver_assert(c, s, Z3_mk_gt(c, x, Z3_mk_int(c, 0, Z3_mk_int_sort(c))));
        Z3_solver_assert(c, s, Z3_mk_lt(c, x, Z3_mk_int(c, 5, Z3_mk_int_sort(c))));

        Z3_config cfg2 = Z3_mk_config();
        Z3_context c2 = Z3_mk_context(cfg2);
        Z3_del_config(cfg2);
        Z3_solver s2 = Z3_solver_translate(c, s, c2);
        CHECK_B(s2 != NULL, 1, "translate: non-null handle");
        Z3_solver_inc_ref(c2, s2);
        Z3_ast_vector av2 = Z3_solver_get_assertions(c2, s2);
        Z3_ast_vector_inc_ref(c2, av2);
        CHECK_U(Z3_ast_vector_size(c2, av2), 2, "translate: copied assertions");
        CHECK_U(Z3_solver_check(c2, s2), (unsigned)Z3_L_TRUE, "translate: re-solve SAT");
        Z3_ast_vector_dec_ref(c2, av2);
        Z3_solver_dec_ref(c2, s2);
        Z3_solver_dec_ref(c, s);
        Z3_del_context(c2);
    }

    // ---- 5. get_consequences: va asserted true, va=>vb; vd free ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast va = bool_var(c, "va");
        Z3_ast vb = bool_var(c, "vb");
        Z3_ast vd = bool_var(c, "vd");
        Z3_solver_assert(c, s, va);
        Z3_solver_assert(c, s, Z3_mk_implies(c, va, vb));
        Z3_ast_vector assumptions = Z3_mk_ast_vector(c);
        Z3_ast_vector_inc_ref(c, assumptions);
        Z3_ast_vector vars = Z3_mk_ast_vector(c);
        Z3_ast_vector_inc_ref(c, vars);
        Z3_ast_vector_push(c, vars, va);
        Z3_ast_vector_push(c, vars, vb);
        Z3_ast_vector_push(c, vars, vd);
        Z3_ast_vector cons = Z3_mk_ast_vector(c);
        Z3_ast_vector_inc_ref(c, cons);
        CHECK_U(Z3_solver_get_consequences(c, s, assumptions, vars, cons),
                (unsigned)Z3_L_TRUE, "consequences: L_TRUE");
        CHECK_U(Z3_ast_vector_size(c, cons), 2, "consequences: two forced vars");
        // va and vb are the forced consequents (vd stays free). Both engines
        // mention them; libz3 renders "(=> true va)", ay pre-simplifies to "va".
        CHECK_B(vec_any_substr(c, cons, "va"), 1, "consequences: mentions va");
        CHECK_B(vec_any_substr(c, cons, "vb"), 1, "consequences: mentions vb");
        CHECK_B(vec_any_substr(c, cons, "vd"), 0, "consequences: vd not forced");
        Z3_ast_vector_dec_ref(c, cons);
        Z3_ast_vector_dec_ref(c, vars);
        Z3_ast_vector_dec_ref(c, assumptions);
        Z3_solver_dec_ref(c, s);
    }

    // ---- 5b. get_consequences under a contradictory assumption -> L_FALSE ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast ca = bool_var(c, "ca");
        Z3_solver_assert(c, s, ca);
        Z3_ast_vector assumptions = Z3_mk_ast_vector(c);
        Z3_ast_vector_inc_ref(c, assumptions);
        Z3_ast_vector_push(c, assumptions, Z3_mk_not(c, ca)); // contradicts ca
        Z3_ast_vector vars = Z3_mk_ast_vector(c);
        Z3_ast_vector_inc_ref(c, vars);
        Z3_ast_vector_push(c, vars, ca);
        Z3_ast_vector cons = Z3_mk_ast_vector(c);
        Z3_ast_vector_inc_ref(c, cons);
        CHECK_U(Z3_solver_get_consequences(c, s, assumptions, vars, cons),
                (unsigned)Z3_L_FALSE, "consequences: UNSAT -> L_FALSE");
        Z3_ast_vector_dec_ref(c, cons);
        Z3_ast_vector_dec_ref(c, vars);
        Z3_ast_vector_dec_ref(c, assumptions);
        Z3_solver_dec_ref(c, s);
    }

    // ---- 6. units / non_units: literals vs compound ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast pp = bool_var(c, "pp");
        Z3_ast qq = bool_var(c, "qq");
        Z3_ast rr = bool_var(c, "rr");
        Z3_ast oq[2] = {qq, rr};
        Z3_solver_assert(c, s, pp);                  // unit
        Z3_solver_assert(c, s, Z3_mk_not(c, qq));    // unit (negated atom)
        Z3_solver_assert(c, s, Z3_mk_or(c, 2, oq));  // non-unit (or)
        Z3_ast_vector u = Z3_solver_get_units(c, s);
        Z3_ast_vector_inc_ref(c, u);
        Z3_ast_vector nu = Z3_solver_get_non_units(c, s);
        Z3_ast_vector_inc_ref(c, nu);
        CHECK_U(Z3_ast_vector_size(c, u), 2, "units: size");
        CHECK_U(Z3_ast_vector_size(c, nu), 1, "non_units: size");
        CHECK_B(vec_contains_str(c, u, "pp"), 1, "units: has pp");
        CHECK_B(vec_contains_str(c, u, "(not qq)"), 1, "units: has (not qq)");
        Z3_ast_vector_dec_ref(c, nu);
        Z3_ast_vector_dec_ref(c, u);

#ifndef AY_TWIN_USE_Z3
        // AY-only: get_trail exposes the level-0 trail (= the input units).
        // (libz3's get_trail after inprocessing/checks is a superset that
        // depends on solver internals, so it is not byte-comparable here.)
        Z3_ast_vector tr = Z3_solver_get_trail(c, s);
        Z3_ast_vector_inc_ref(c, tr);
        CHECK_U(Z3_ast_vector_size(c, tr), 2, "trail: level-0 units");
        Z3_ast_vector_dec_ref(c, tr);
#endif
        Z3_solver_dec_ref(c, s);
    }

    // ---- 7. get_help: real, non-empty parameter description ----
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_string help = Z3_solver_get_help(c, s);
        CHECK_B(help != NULL && help[0] != '\0', 1, "help: non-empty");
        Z3_solver_dec_ref(c, s);
    }

#ifndef AY_TWIN_USE_Z3
    // ---- 8. congruence (AY honest singleton class) ----
    // AY models each term as its own congruence class, so root(a)==a and
    // next(a)==a (a one-element cyclic list). SOUND: it never claims two
    // distinct terms are congruent when they are not. (libz3's congruence ring
    // exposes real e-graph representatives that depend on the completed search
    // state, so this is verified only in ay.)
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast g = bool_var(c, "g");
        Z3_solver_assert(c, s, g);
        Z3_solver_check(c, s);
        CHECK_B(Z3_solver_congruence_root(c, s, g) == g, 1, "congruence: root(g)==g");
        CHECK_B(Z3_solver_congruence_next(c, s, g) == g, 1, "congruence: next(g)==g");
        Z3_solver_dec_ref(c, s);
    }

    // ---- 9. to_dimacs_string (AY propositional skeleton) ----
    // Assert two unit literals `da` and `(not db)`. da -> var 1, db -> var 2.
    // The Tseitin CNF is exactly two unit clauses. (libz3 bit-blasts and uses a
    // different numbering, so the exact string is verified only in ay.)
    {
        Z3_solver s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_ast da = bool_var(c, "da");
        Z3_ast db = bool_var(c, "db");
        Z3_solver_assert(c, s, da);
        Z3_solver_assert(c, s, Z3_mk_not(c, db));
        Z3_string d = Z3_solver_to_dimacs_string(c, s, false);
        CHECK_B(d != NULL, 1, "dimacs: non-null");
        CHECK_B(strstr(d, "p cnf 2 2") != NULL, 1, "dimacs: header p cnf 2 2");
        CHECK_B(strstr(d, "1 0") != NULL, 1, "dimacs: unit clause 1 0");
        CHECK_B(strstr(d, "-2 0") != NULL, 1, "dimacs: unit clause -2 0");
        // include_names emits a mapping comment naming the atoms.
        Z3_string dn = Z3_solver_to_dimacs_string(c, s, true);
        CHECK_B(dn != NULL && strstr(dn, "da") != NULL, 1, "dimacs: names da");
        Z3_solver_dec_ref(c, s);
    }
#endif

    Z3_del_context(c);

    if (g_fail == 0) {
        printf("All %d solver-completion consumer tests passed\n", g_pass);
        return 0;
    }
    printf("%d checks passed, %d FAILED\n", g_pass, g_fail);
    return 1;
}
