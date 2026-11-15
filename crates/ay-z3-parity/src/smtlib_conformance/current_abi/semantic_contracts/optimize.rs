// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Selected finite Optimize state sequences. Every row remains a bounded
//! obligation, including when the exact pinned reference passes it.

use super::{Aspect, Claim, Family};

pub(super) const FAMILIES: &[Family] = &[
    Family {
        id: "contract-optimize-objectives",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/optimize_helpers.h"),
            include_str!("../contracts/optimize_assertions.h"),
            include_str!("../contracts/optimize_model.h"),
            include_str!("../contracts/optimize_boolean_model.h"),
            include_str!("../contracts/optimize_objectives.c")
        ),
        checks: &[
            "optimize.objectives.context-created",
            "optimize.objectives.setup",
            "optimize.objectives.distinct-handles",
            "optimize.objectives.finite-optimum",
            "optimize.objectives.exact-model",
            "optimize.objectives.normalized-objectives",
            "optimize.objectives.assertion-snapshot",
            "optimize.objectives.retained-after-owner-release",
            "optimize.objectives.recreated-owner-is-empty",
            "optimize.objectives.recreated-owner-independent",
        ],
    },
    Family {
        id: "contract-optimize-scopes",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/optimize_helpers.h"),
            include_str!("../contracts/optimize_assertions.h"),
            include_str!("../contracts/optimize_model.h"),
            include_str!("../contracts/optimize_scopes.c")
        ),
        checks: &[
            "optimize.scopes.context-created",
            "optimize.scopes.setup",
            "optimize.scopes.base-optimum",
            "optimize.scopes.scoped-objective-and-assertion",
            "optimize.scopes.assumption-contradiction",
            "optimize.scopes.exact-assumption-core",
            "optimize.scopes.assumptions-do-not-persist",
            "optimize.scopes.nested-contradiction",
            "optimize.scopes.inner-pop-restores-optimum",
            "optimize.scopes.outer-pop-removes-objective",
            "optimize.scopes.retained-snapshots",
        ],
    },
    Family {
        id: "contract-optimize-priorities",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/optimize_helpers.h"),
            include_str!("../contracts/optimize_model.h"),
            include_str!("../contracts/optimize_boolean_model.h"),
            include_str!("../contracts/optimize_priorities.c")
        ),
        checks: &[
            "optimize.priorities.context-created",
            "optimize.priorities.setup",
            "optimize.priorities.independent-owners",
            "optimize.priorities.lex-first-objective",
            "optimize.priorities.lex-reversed-objectives",
            "optimize.priorities.complete-finite-pareto-front",
            "optimize.priorities.pareto-exhaustion",
            "optimize.priorities.soft-setup",
            "optimize.priorities.soft-group-handles",
            "optimize.priorities.rational-soft-group-priority",
            "optimize.priorities.soft-model-and-objectives",
        ],
    },
    Family {
        id: "contract-optimize-errors",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/optimize_helpers.h"),
            include_str!("../contracts/optimize_assertions.h"),
            include_str!("../contracts/optimize_errors.c")
        ),
        checks: &[
            "optimize.errors.context-created",
            "optimize.errors.setup",
            "optimize.errors.empty-handles-refused",
            "optimize.errors.scoped-setup",
            "optimize.errors.valid-objective-after-error",
            "optimize.errors.out-of-range-handles-refused",
            "optimize.errors.null-weight-refused",
            "optimize.errors.valid-check-recovers",
            "optimize.errors.pop-all-is-empty",
            "optimize.errors.removed-handle-refused",
            "optimize.errors.replacement-setup",
            "optimize.errors.reused-index-has-new-value",
        ],
    },
];

pub(super) const CLAIMS: &[Claim] = &[
    Claim { family: "contract-optimize-objectives", check: "optimize.objectives.distinct-handles", aspect: Aspect::State, functions: &["Z3_mk_optimize", "Z3_optimize_inc_ref", "Z3_optimize_maximize", "Z3_optimize_minimize"], statement: "A retained optimizer assigns handles zero and one to independent bounded integer maximization and minimization objectives after a balanced extra retain/release." },
    Claim { family: "contract-optimize-objectives", check: "optimize.objectives.finite-optimum", aspect: Aspect::Output, functions: &["Z3_optimize_check", "Z3_optimize_get_lower", "Z3_optimize_get_upper", "Z3_optimize_get_lower_as_vector", "Z3_optimize_get_upper_as_vector", "Z3_get_numeral_rational_int64"], statement: "For 0<=x<=4 and 2<=y<=8, maximizing x then minimizing y yields attained exact bounds 4 and 2; both bound vectors are exactly [0, value, 0]." },
    Claim { family: "contract-optimize-objectives", check: "optimize.objectives.exact-model", aspect: Aspect::Output, functions: &["Z3_optimize_get_model", "Z3_model_eval"], statement: "The retained optimum model evaluates x to 4 and y to 2 without completion, and rejects the incorrect x=3 witness." },
    Claim { family: "contract-optimize-objectives", check: "optimize.objectives.normalized-objectives", aspect: Aspect::Output, functions: &["Z3_optimize_get_objectives"], statement: "The two exposed minimization-form objectives evaluate in the attained optimum model to -4 and 2 in handle order." },
    Claim { family: "contract-optimize-objectives", check: "optimize.objectives.assertion-snapshot", aspect: Aspect::Output, functions: &["Z3_optimize_get_assertions", "Z3_optimize_assert"], statement: "The exposed assertion vector contains four assertions, each true in the attained optimum model." },
    Claim { family: "contract-optimize-objectives", check: "optimize.objectives.retained-after-owner-release", aspect: Aspect::Lifetime, functions: &["Z3_optimize_dec_ref", "Z3_model_inc_ref", "Z3_model_dec_ref", "Z3_ast_vector_inc_ref", "Z3_ast_vector_dec_ref"], statement: "An explicitly retained model and explicitly retained objective/assertion snapshots remain readable after the owning optimizer's last reference is released." },
    Claim { family: "contract-optimize-objectives", check: "optimize.objectives.recreated-owner-is-empty", aspect: Aspect::State, functions: &["Z3_mk_optimize", "Z3_optimize_get_assertions", "Z3_optimize_get_objectives"], statement: "Recreating an optimizer in the same context starts with zero assertions and objectives and checks satisfiable; no nonexistent Optimize reset API is assumed." },
    Claim { family: "contract-optimize-objectives", check: "optimize.objectives.recreated-owner-independent", aspect: Aspect::Context, functions: &["Z3_optimize_assert", "Z3_optimize_minimize", "Z3_optimize_get_lower", "Z3_optimize_get_upper"], statement: "A recreated optimizer minimizes independently at x=1 while the prior retained model remains x=4." },
    Claim { family: "contract-optimize-scopes", check: "optimize.scopes.scoped-objective-and-assertion", aspect: Aspect::State, functions: &["Z3_optimize_push", "Z3_optimize_assert", "Z3_optimize_minimize", "Z3_optimize_get_objectives", "Z3_optimize_get_assertions"], statement: "A scope adds exactly one objective and x<=2 to a 0<=x<=5 maximizer, changing both objective optima to 2." },
    Claim { family: "contract-optimize-scopes", check: "optimize.scopes.assumption-contradiction", aspect: Aspect::State, functions: &["Z3_optimize_check"], statement: "The temporary x>=3 assumption makes the scoped x<=2 optimization problem unsatisfiable." },
    Claim { family: "contract-optimize-scopes", check: "optimize.scopes.exact-assumption-core", aspect: Aspect::Output, functions: &["Z3_optimize_get_unsat_core"], statement: "The sole contradictory assumption x>=3 is returned as the sole unsat-core entry." },
    Claim { family: "contract-optimize-scopes", check: "optimize.scopes.assumptions-do-not-persist", aspect: Aspect::State, functions: &["Z3_optimize_check"], statement: "A later check without assumptions restores optimum 2, and the retained earlier model is still evaluable." },
    Claim { family: "contract-optimize-scopes", check: "optimize.scopes.nested-contradiction", aspect: Aspect::State, functions: &["Z3_optimize_push", "Z3_optimize_assert"], statement: "An inner scope containing false makes the bounded optimization unsatisfiable." },
    Claim { family: "contract-optimize-scopes", check: "optimize.scopes.inner-pop-restores-optimum", aspect: Aspect::State, functions: &["Z3_optimize_pop"], statement: "Popping the inner contradiction restores the outer optimum 2." },
    Claim { family: "contract-optimize-scopes", check: "optimize.scopes.outer-pop-removes-objective", aspect: Aspect::State, functions: &["Z3_optimize_pop", "Z3_optimize_get_objectives", "Z3_optimize_get_assertions"], statement: "Popping the outer scope removes its objective and assertion, leaving exactly one objective, two assertions and original optimum 5." },
    Claim { family: "contract-optimize-scopes", check: "optimize.scopes.retained-snapshots", aspect: Aspect::Lifetime, functions: &["Z3_optimize_get_model", "Z3_optimize_get_assertions", "Z3_optimize_get_objectives", "Z3_optimize_get_unsat_core"], statement: "Explicitly retained scoped model, assertion vector, objective vector and assumption core preserve their values after both scopes are popped." },
    Claim { family: "contract-optimize-priorities", check: "optimize.priorities.independent-owners", aspect: Aspect::Context, functions: &["Z3_optimize_set_params", "Z3_mk_params", "Z3_params_inc_ref", "Z3_params_dec_ref", "Z3_params_set_symbol"], statement: "Three retained optimizers independently accept lex, lex and pareto priorities through a retained parameter object that is released before solving." },
    Claim { family: "contract-optimize-priorities", check: "optimize.priorities.lex-first-objective", aspect: Aspect::Output, functions: &["Z3_optimize_maximize", "Z3_optimize_check", "Z3_optimize_set_params"], statement: "Lex maximizing x then y over integer 0<=x,y<=2 and x+y<=2 yields (2,0)." },
    Claim { family: "contract-optimize-priorities", check: "optimize.priorities.lex-reversed-objectives", aspect: Aspect::State, functions: &["Z3_optimize_maximize", "Z3_optimize_check", "Z3_optimize_get_model"], statement: "Reversing the objective order in an independent optimizer yields (0,2), while the first retained model remains (2,0)." },
    Claim { family: "contract-optimize-priorities", check: "optimize.priorities.complete-finite-pareto-front", aspect: Aspect::Output, functions: &["Z3_optimize_set_params", "Z3_optimize_check", "Z3_optimize_get_model", "Z3_optimize_get_lower", "Z3_optimize_get_upper", "Z3_optimize_get_lower_as_vector", "Z3_optimize_get_upper_as_vector"], statement: "For integer 0<=x,y<=2 and x+y<=2, three Pareto checks enumerate exactly the distinct frontier (0,2),(1,1),(2,0) in any order; each model and bound API agrees on its point." },
    Claim { family: "contract-optimize-priorities", check: "optimize.priorities.pareto-exhaustion", aspect: Aspect::State, functions: &["Z3_optimize_check"], statement: "A fourth check after all three finite Pareto points returns unsatisfiable, rejecting repeated or invented frontier points." },
    Claim { family: "contract-optimize-priorities", check: "optimize.priorities.soft-group-handles", aspect: Aspect::State, functions: &["Z3_optimize_assert_soft"], statement: "Two rational-weight soft constraints with the same group share handle zero; a second named soft group has handle one." },
    Claim { family: "contract-optimize-priorities", check: "optimize.priorities.rational-soft-group-priority", aspect: Aspect::Output, functions: &["Z3_optimize_assert_soft", "Z3_optimize_get_lower", "Z3_optimize_get_upper", "Z3_optimize_get_lower_as_vector", "Z3_optimize_get_upper_as_vector"], statement: "Under hard xor(p,q), primary soft weights p:1/2 and q:3/2 followed by secondary p:2 produce lex costs exactly 1/2 and 2, distinguishing grouped lex optimization from flattening all weights." },
    Claim { family: "contract-optimize-priorities", check: "optimize.priorities.soft-model-and-objectives", aspect: Aspect::Output, functions: &["Z3_optimize_get_objectives", "Z3_optimize_get_model"], statement: "The soft optimum model assigns p=false and q=true; its two exposed objective expressions evaluate to 1/2 and 2." },
    Claim { family: "contract-optimize-errors", check: "optimize.errors.empty-handles-refused", aspect: Aspect::Errors, functions: &["Z3_optimize_get_lower", "Z3_optimize_get_upper", "Z3_optimize_get_lower_as_vector", "Z3_optimize_get_upper_as_vector", "Z3_get_error_code", "Z3_get_error_msg", "Z3_set_error_handler"], statement: "All four bound getters reject handles zero and UINT_MAX in an empty optimizer with null, handler/code Z3_EXCEPTION and pinned index-out-of-bounds diagnostic." },
    Claim { family: "contract-optimize-errors", check: "optimize.errors.valid-objective-after-error", aspect: Aspect::Errors, functions: &["Z3_optimize_maximize", "Z3_optimize_check"], statement: "A valid scoped bounded objective after invalid-handle errors checks satisfiable at 4 and clears the error code." },
    Claim { family: "contract-optimize-errors", check: "optimize.errors.out-of-range-handles-refused", aspect: Aspect::Errors, functions: &["Z3_optimize_get_lower", "Z3_optimize_get_upper", "Z3_optimize_get_lower_as_vector", "Z3_optimize_get_upper_as_vector"], statement: "All four getters reject the first out-of-range handle and UINT_MAX after an actual optimum has been computed." },
    Claim { family: "contract-optimize-errors", check: "optimize.errors.null-weight-refused", aspect: Aspect::Errors, functions: &["Z3_optimize_assert_soft"], statement: "A null soft-weight string is safely rejected through the handler and error-code API as Z3_INVALID_ARG." },
    Claim { family: "contract-optimize-errors", check: "optimize.errors.valid-check-recovers", aspect: Aspect::Errors, functions: &["Z3_optimize_check"], statement: "A valid check after a rejected null soft weight clears the error and preserves the existing optimum 4." },
    Claim { family: "contract-optimize-errors", check: "optimize.errors.removed-handle-refused", aspect: Aspect::Errors, functions: &["Z3_optimize_pop", "Z3_optimize_get_lower", "Z3_optimize_get_upper", "Z3_optimize_get_lower_as_vector", "Z3_optimize_get_upper_as_vector"], statement: "Popping the only objective and checking the now-empty optimizer invalidates the former handle for all four bound getters." },
    Claim { family: "contract-optimize-errors", check: "optimize.errors.reused-index-has-new-value", aspect: Aspect::State, functions: &["Z3_optimize_minimize", "Z3_optimize_get_lower", "Z3_optimize_get_upper", "Z3_optimize_get_lower_as_vector", "Z3_optimize_get_upper_as_vector"], statement: "After popping all objectives, a new minimum reuses index zero and all bound representations report its new optimum 0, not stale prior optimum 4." },
];
