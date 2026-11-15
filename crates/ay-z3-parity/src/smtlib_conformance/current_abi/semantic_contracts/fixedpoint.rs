// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite Fixedpoint contracts against the pinned Z3 5.3.3 C API.
//!
//! `z3_fixedpoint.h` requires explicit engine reference management and defines
//! query polarity as reachable=TRUE, unreachable=FALSE, interrupted=UNDEF.
//! `api_datalog.cpp` gives each from-string call a fresh command context and
//! catches resource exceptions at query, separately from get_reason_unknown.
//! Database facts added with add_fact affect reachability but are not entries
//! in the get_rules snapshot; that snapshot contains asserted rules only.
//! These witnesses do not cover arbitrary CHCs, all engines, callbacks,
//! concurrent interruption, cover queries, or a complete argument domain.

use super::*;

pub(super) const FAMILIES: &[Family] = &[
    Family {
        id: "contract-fixedpoint",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/fixedpoint.c")
        ),
        checks: &[
            "fixedpoint.context-created",
            "fixedpoint.independent-objects-created",
            "fixedpoint.typed-relations-created",
            "fixedpoint.empty-relation-is-unreachable",
            "fixedpoint.fact-membership",
            "fixedpoint.ground-query-satisfiable",
            "fixedpoint.ground-answer",
            "fixedpoint.bound-variable-rule",
            "fixedpoint.rule-derives-only-matching-value",
            "fixedpoint.relation-query",
            "fixedpoint.rule-and-fact-state-isolated",
            "fixedpoint.rule-snapshot",
            "fixedpoint.background-assertion-snapshot",
            "fixedpoint.parser-objects-created",
            "fixedpoint.parser-binds-rule-variables",
            "fixedpoint.parser-rule-state-isolated",
            "fixedpoint.retained-results-survive-engine-release",
        ],
    },
    Family {
        id: "contract-fixedpoint-resource",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/fixedpoint_resource.c")
        ),
        checks: &[
            "fixedpoint-resource.context-created",
            "fixedpoint-resource.objects-created",
            "fixedpoint-resource.query-created",
            "fixedpoint-resource.budget-refuses-decision",
            "fixedpoint-resource.cancellation-diagnostic",
            "fixedpoint-resource.reason-after-exception",
            "fixedpoint-resource.recovery-params-created",
            "fixedpoint-resource.recovery-decision",
            "fixedpoint-resource.recovery-answer-and-statistics",
            "fixedpoint-resource.repeated-query",
            "fixedpoint-resource.retained-results-survive-engine-release",
        ],
    },
];

pub(super) const CLAIMS: &[Claim] = &[
    Claim { family: "contract-fixedpoint", check: "fixedpoint.independent-objects-created", aspect: Aspect::Lifetime, functions: &["Z3_mk_fixedpoint", "Z3_fixedpoint_inc_ref", "Z3_fixedpoint_dec_ref", "Z3_fixedpoint_set_params", "Z3_mk_params", "Z3_params_inc_ref", "Z3_params_dec_ref", "Z3_params_set_symbol"], statement: "Two retained Datalog engines remain usable after their parameter objects are released and one balanced extra engine reference is released." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.typed-relations-created", aspect: Aspect::Output, functions: &["Z3_mk_func_decl", "Z3_get_decl_name"], statement: "The immediately retained p and q declarations remain distinct and retain their exact string names after subsequent AST allocations." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.empty-relation-is-unreachable", aspect: Aspect::State, functions: &["Z3_fixedpoint_register_relation", "Z3_fixedpoint_query"], statement: "A registered four-bit relation with no fact or defining rule is unreachable, reported as Z3_L_FALSE without an API error." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.fact-membership", aspect: Aspect::State, functions: &["Z3_fixedpoint_add_fact", "Z3_fixedpoint_query"], statement: "Adding the database fact p(1) makes exactly p(1), not p(2), reachable in the selected finite-domain relation." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.ground-answer", aspect: Aspect::Output, functions: &["Z3_fixedpoint_get_answer"], statement: "After a reachable ground Datalog query the answer is a true Boolean AST that can be retained independently." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.bound-variable-rule", aspect: Aspect::Output, functions: &["Z3_mk_bound", "Z3_mk_forall", "Z3_is_quantifier_forall", "Z3_get_quantifier_num_bound"], statement: "The universally quantified p(x) implies q(x) rule binds exactly one four-bit variable." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.rule-derives-only-matching-value", aspect: Aspect::State, functions: &["Z3_fixedpoint_add_rule", "Z3_fixedpoint_query"], statement: "The quantified copy rule derives q(1) from p(1) but does not derive q(2)." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.relation-query", aspect: Aspect::Output, functions: &["Z3_fixedpoint_query_relations"], statement: "Querying the single registered q relation returns reachable when q(1) is derivable." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.rule-and-fact-state-isolated", aspect: Aspect::State, functions: &["Z3_fixedpoint_add_fact", "Z3_fixedpoint_query"], statement: "A second engine sharing the same context and relation declarations has its own facts; p(2) there does not affect the first engine or create p(1)." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.rule-snapshot", aspect: Aspect::Output, functions: &["Z3_fixedpoint_get_rules"], statement: "The rule snapshot contains exactly the quantified copy rule and preserves its quantifier structure; the database fact added by add_fact is not an asserted rule." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.background-assertion-snapshot", aspect: Aspect::State, functions: &["Z3_fixedpoint_assert", "Z3_fixedpoint_get_assertions"], statement: "Asserting true is retained as exactly one true background assertion; this does not claim Datalog uses background axioms." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.parser-binds-rule-variables", aspect: Aspect::State, functions: &["Z3_fixedpoint_from_string"], statement: "Parsing declared finite-domain variables and a bounded successor rule reaches step(3) but not step(4), and returns exactly one query." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.parser-rule-state-isolated", aspect: Aspect::Context, functions: &["Z3_fixedpoint_from_string", "Z3_fixedpoint_query"], statement: "A second parse into another engine can reuse the relation name with a different rule set without inheriting the first engine's derivations." },
    Claim { family: "contract-fixedpoint", check: "fixedpoint.retained-results-survive-engine-release", aspect: Aspect::Lifetime, functions: &["Z3_fixedpoint_dec_ref", "Z3_fixedpoint_get_rules", "Z3_fixedpoint_get_assertions", "Z3_fixedpoint_get_answer"], statement: "Explicitly retained answer, rule, assertion and parsed-query ASTs remain readable after their engines are released, before context destruction." },
    Claim { family: "contract-fixedpoint-resource", check: "fixedpoint-resource.budget-refuses-decision", aspect: Aspect::Errors, functions: &["Z3_fixedpoint_set_params", "Z3_params_set_uint", "Z3_fixedpoint_query", "Z3_get_error_code", "Z3_set_error_handler"], statement: "The pinned Spacer ground-fact query with rlimit=1 returns Z3_L_UNDEF and reports Z3_EXCEPTION both to the callback and error-code API, rather than claiming a decided result." },
    Claim { family: "contract-fixedpoint-resource", check: "fixedpoint-resource.cancellation-diagnostic", aspect: Aspect::Errors, functions: &["Z3_get_error_msg"], statement: "The resource exception is identified by the pinned max. resource limit exceeded diagnostic." },
    Claim { family: "contract-fixedpoint-resource", check: "fixedpoint-resource.reason-after-exception", aspect: Aspect::Output, functions: &["Z3_fixedpoint_get_reason_unknown"], statement: "After this thrown resource exception the separate engine reason string is the pinned value ok; no stronger diagnostic behavior is assumed." },
    Claim { family: "contract-fixedpoint-resource", check: "fixedpoint-resource.recovery-decision", aspect: Aspect::State, functions: &["Z3_fixedpoint_set_params", "Z3_fixedpoint_query"], statement: "Replacing the exhausted rlimit with zero lets the same engine and query return reachable without an API error." },
    Claim { family: "contract-fixedpoint-resource", check: "fixedpoint-resource.recovery-answer-and-statistics", aspect: Aspect::Output, functions: &["Z3_fixedpoint_get_answer", "Z3_fixedpoint_get_statistics", "Z3_stats_inc_ref", "Z3_stats_size"], statement: "After successful recovery, Spacer returns a readable application AST and a retainable nonempty statistics object; proof shape, independent proof validity and timing counters remain outside this obligation." },
    Claim { family: "contract-fixedpoint-resource", check: "fixedpoint-resource.repeated-query", aspect: Aspect::State, functions: &["Z3_fixedpoint_query", "Z3_fixedpoint_get_answer"], statement: "Repeating the recovered ground-fact query remains reachable, and the previously retained answer keeps its AST identity." },
    Claim { family: "contract-fixedpoint-resource", check: "fixedpoint-resource.retained-results-survive-engine-release", aspect: Aspect::Lifetime, functions: &["Z3_fixedpoint_dec_ref", "Z3_stats_get_key", "Z3_stats_dec_ref"], statement: "The retained answer and nonempty statistics remain readable after the engine is released; the first statistic still has a key." },
];
