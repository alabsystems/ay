// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite parser, substitution and rewriting semantics for pinned Z3 5.3.3.
//!
//! Parser expectations follow `api_parsers.cpp`: each string parse uses a
//! fresh command context, keeps end-of-scope assertions and returns a vector
//! even on parser errors. `api_ast.cpp` specifies the tested refusal paths:
//! substitution sort mismatch returns null with SORT_ERROR, and update_term
//! wrong arity returns the original AST with IOB. Capture avoidance follows
//! `expr_safe_replace.cpp`; function-body Var(0) denotes the first argument,
//! while substitute_vars replaces free de Bruijn slot i with input i.
//! `poly_rewriter_params.hpp` documents the tested som Boolean parameter.
//! All observations are finite witnesses, including 25 independent integer
//! valuations and one solver rejection of a symbolic inequivalence. They do
//! not qualify all parser, binder, function-substitution or rewrite domains.

use super::{Aspect, Claim, Family};

pub(super) const REMAINING_SCOPE: &str = " Parser/substitution/rewrite witnesses cover only the listed string syntax, two external sort aliases, two declaration aliases, one push/pop scope, selected parser errors, one simultaneous and one compound substitution, two free de Bruijn slots, one quantifier-free function body, one capture-avoidance binder, one integer application update and one som polynomial parameter. File parsing, parser-context APIs, arbitrary SMT-LIB commands and theories, declaration conflicts, malformed map arrays, arbitrary binders/patterns, lambdas and function substitution beneath binders, cyclic or duplicate substitution maps, update_term on quantifiers, other simplifier parameters, resources, concurrency and all argument/lifetime sequences remain unqualified.";

pub(super) const FAMILIES: &[Family] = &[
    Family {
        id: "contract-parsing-maps",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/parsing_semantic_helpers.h"),
            include_str!("../contracts/parsing_maps.c")
        ),
        checks: &[
            "parsing.maps.context-created",
            "parsing.maps.sorts-created",
            "parsing.maps.declarations-created",
            "parsing.maps.external-terms-created",
            "parsing.maps.external-symbols-created",
            "parsing.maps.active-assertion-scope",
            "parsing.maps.declaration-alias-identity",
            "parsing.maps.function-and-sort-map",
            "parsing.maps.solver-created",
            "parsing.maps.mapped-assertions-satisfiable",
            "parsing.maps.model-uses-external-declaration",
            "parsing.maps.returned-assertions-have-semantic-force",
            "parsing.maps.complementary-assertion-refused",
            "parsing.maps.sort-error-refused",
            "parsing.maps.declarations-do-not-leak-between-calls",
            "parsing.maps.valid-parse-recovers",
            "parsing.maps.retained-vector-after-errors-and-solver-release",
        ],
    },
    Family {
        id: "contract-substitution-terms",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/parsing_semantic_helpers.h"),
            include_str!("../contracts/substitution_terms.c")
        ),
        checks: &[
            "substitution.terms.context-created",
            "substitution.terms.sort-created",
            "substitution.terms.atoms-created",
            "substitution.terms.setup",
            "substitution.terms.first-substitution-created",
            "substitution.terms.simultaneous-not-sequential",
            "substitution.terms.compound-created",
            "substitution.terms.repeated-compound-created",
            "substitution.terms.repeated-compound-subexpression",
            "substitution.terms.empty-map-preserves-term",
            "substitution.terms.boolean-replacement-created",
            "substitution.terms.sort-mismatch-refused",
            "substitution.terms.valid-map-recovers",
            "substitution.terms.variable-inputs-created",
            "substitution.terms.indexed-product-created",
            "substitution.terms.indexed-input-created",
            "substitution.terms.debruijn-index-order",
            "substitution.terms.function-created",
            "substitution.terms.function-inputs-created",
            "substitution.terms.function-body-created",
            "substitution.terms.function-substitution-created",
            "substitution.terms.function-argument-order",
            "substitution.terms.capture-fixture-created",
            "substitution.terms.capture-fixture-retains-binder",
            "substitution.terms.lifted-replacement-created",
            "substitution.terms.closed-inputs-created",
            "substitution.terms.zero-constraint-created",
            "substitution.terms.replacement-avoids-binder-capture",
            "substitution.terms.ignored-replacement-negative-control",
            "substitution.terms.bound-variables-are-not-free-slots",
        ],
    },
    Family {
        id: "contract-substitution-rewriting",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/parsing_semantic_helpers.h"),
            include_str!("../contracts/substitution_rewriting.c")
        ),
        checks: &[
            "substitution.rewriting.context-created",
            "substitution.rewriting.sort-created",
            "substitution.rewriting.atoms-created",
            "substitution.rewriting.setup",
            "substitution.rewriting.update-arguments-preserves-operator",
            "substitution.rewriting.original-term-unchanged",
            "substitution.rewriting.identical-update-preserves-identity",
            "substitution.rewriting.wrong-arity-refused",
            "substitution.rewriting.valid-update-recovers",
            "substitution.rewriting.factors-created",
            "substitution.rewriting.parameters-created",
            "substitution.rewriting.sum-of-monomials-parameter-effect",
            "substitution.rewriting.parameter-results-preserve-25-values",
            "substitution.rewriting.equivalence-created",
            "substitution.rewriting.symbolic-parameter-equivalence",
            "substitution.rewriting.ground-value-created",
            "substitution.rewriting.ground-equality-created",
            "substitution.rewriting.default-ground-simplification",
        ],
    },
];

pub(super) const CLAIMS: &[Claim] = &[
    Claim {
        family: "contract-parsing-maps",
        check: "parsing.maps.active-assertion-scope",
        aspect: Aspect::State,
        functions: &["Z3_parse_smtlib2_string", "Z3_ast_vector_size"],
        statement: "Parsing mapped declarations returns the three assertions active after a push, false assertion and matching pop; the popped false assertion is absent.",
    },
    Claim {
        family: "contract-parsing-maps",
        check: "parsing.maps.declaration-alias-identity",
        aspect: Aspect::Output,
        functions: &[
            "Z3_parse_smtlib2_string",
            "Z3_ast_vector_get",
            "Z3_is_eq_ast",
            "Z3_get_app_num_args",
        ],
        statement: "The supplied_x alias resolves to the pre-existing actual_x declaration: its parsed equality is AST-identical to the independently built actual_x=7, and the second assertion has two equality operands.",
    },
    Claim {
        family: "contract-parsing-maps",
        check: "parsing.maps.function-and-sort-map",
        aspect: Aspect::Output,
        functions: &[
            "Z3_parse_smtlib2_string",
            "Z3_get_app_arg",
            "Z3_get_app_decl",
            "Z3_is_eq_func_decl",
            "Z3_get_sort",
            "Z3_is_eq_sort",
        ],
        statement: "The supplied_f alias denotes the exact external Int-to-Int function on actual_x; AliasInt and AliasOpaque declarations have the supplied existing sorts.",
    },
    Claim {
        family: "contract-parsing-maps",
        check: "parsing.maps.model-uses-external-declaration",
        aspect: Aspect::Output,
        functions: &["Z3_solver_get_model", "Z3_model_eval", "Z3_get_numeral_int"],
        statement: "A model of all parsed assertions evaluates the external actual_x to seven without model completion and rejects the alternative eight.",
    },
    Claim {
        family: "contract-parsing-maps",
        check: "parsing.maps.complementary-assertion-refused",
        aspect: Aspect::State,
        functions: &["Z3_solver_assert", "Z3_solver_check"],
        statement: "All returned assertions are satisfiable, but additionally asserting the complement of the returned actual_x=7 assertion is unsatisfiable.",
    },
    Claim {
        family: "contract-parsing-maps",
        check: "parsing.maps.sort-error-refused",
        aspect: Aspect::Errors,
        functions: &[
            "Z3_parse_smtlib2_string",
            "Z3_get_error_code",
            "Z3_set_error_handler",
        ],
        statement: "Parsing an equality between integer one and Boolean true returns an empty nonnull AST vector and reports PARSER_ERROR both through the context code and callback.",
    },
    Claim {
        family: "contract-parsing-maps",
        check: "parsing.maps.declarations-do-not-leak-between-calls",
        aspect: Aspect::State,
        functions: &["Z3_parse_smtlib2_string"],
        statement: "A local declaration created by the first parse is not available to a subsequent independent string parse; the latter reports PARSER_ERROR.",
    },
    Claim {
        family: "contract-parsing-maps",
        check: "parsing.maps.valid-parse-recovers",
        aspect: Aspect::Errors,
        functions: &[
            "Z3_parse_smtlib2_string",
            "Z3_get_error_code",
            "Z3_get_bool_value",
        ],
        statement: "A valid assertion of true succeeds with OK and one true assertion after the two prior parser failures.",
    },
    Claim {
        family: "contract-parsing-maps",
        check: "parsing.maps.retained-vector-after-errors-and-solver-release",
        aspect: Aspect::Lifetime,
        functions: &[
            "Z3_ast_vector_inc_ref",
            "Z3_ast_vector_dec_ref",
            "Z3_ast_vector_get",
            "Z3_model_inc_ref",
            "Z3_model_dec_ref",
            "Z3_model_eval",
            "Z3_solver_dec_ref",
        ],
        statement: "The retained initial vector keeps its three assertions and external-declaration identity after later parses and solver release, while its separately retained model remains evaluable as actual_x=7.",
    },
    Claim {
        family: "contract-substitution-terms",
        check: "substitution.terms.simultaneous-not-sequential",
        aspect: Aspect::Output,
        functions: &["Z3_substitute", "Z3_simplify", "Z3_get_numeral_int"],
        statement: "Simultaneously replacing x by y and y by one in x-y, then closing y as seven, yields six rather than the zero produced by recursive sequential replacement.",
    },
    Claim {
        family: "contract-substitution-terms",
        check: "substitution.terms.repeated-compound-subexpression",
        aspect: Aspect::Output,
        functions: &["Z3_substitute"],
        statement: "Replacing the compound x+y by eleven in (x+y)*(x+y) replaces both occurrences and yields 121.",
    },
    Claim {
        family: "contract-substitution-terms",
        check: "substitution.terms.empty-map-preserves-term",
        aspect: Aspect::Output,
        functions: &["Z3_substitute", "Z3_is_eq_ast"],
        statement: "A zero-length substitution with null map arrays returns the original AST identity.",
    },
    Claim {
        family: "contract-substitution-terms",
        check: "substitution.terms.sort-mismatch-refused",
        aspect: Aspect::Errors,
        functions: &["Z3_substitute", "Z3_get_error_code", "Z3_set_error_handler"],
        statement: "Replacing an integer x by Boolean true is refused with null, SORT_ERROR and the error callback; no invalid pointer or malformed array is supplied.",
    },
    Claim {
        family: "contract-substitution-terms",
        check: "substitution.terms.valid-map-recovers",
        aspect: Aspect::Errors,
        functions: &["Z3_substitute", "Z3_get_error_code"],
        statement: "After the refused sort mismatch, the valid x=7,y=2 substitution succeeds with OK and yields five.",
    },
    Claim {
        family: "contract-substitution-terms",
        check: "substitution.terms.debruijn-index-order",
        aspect: Aspect::Output,
        functions: &["Z3_substitute_vars"],
        statement: "Replacing free de Bruijn slots zero and one by two and three in 10*Var(1)+Var(0) yields 32, rejecting reversed ordering 23.",
    },
    Claim {
        family: "contract-substitution-terms",
        check: "substitution.terms.function-argument-order",
        aspect: Aspect::Output,
        functions: &["Z3_substitute_funs"],
        statement: "Replacing a two-argument function by body 10*Var(0)+Var(1), then applying x=2,y=3, yields 23 rather than 32: Var(0) denotes the first function argument.",
    },
    Claim {
        family: "contract-substitution-terms",
        check: "substitution.terms.replacement-avoids-binder-capture",
        aspect: Aspect::Output,
        functions: &["Z3_substitute", "Z3_substitute_vars", "Z3_solver_check"],
        statement: "Replacing external x under one forall binder by free Var(0), then closing that free slot as seven, remains satisfiable with x=0; capture of the bound variable would instead make the quantified formula unsatisfiable.",
    },
    Claim {
        family: "contract-substitution-terms",
        check: "substitution.terms.ignored-replacement-negative-control",
        aspect: Aspect::Output,
        functions: &["Z3_substitute", "Z3_solver_check"],
        statement: "The unreplaced forall formula forces external x=7 and is unsatisfiable with x=0, distinguishing genuine capture-safe replacement from an ignored map.",
    },
    Claim {
        family: "contract-substitution-terms",
        check: "substitution.terms.bound-variables-are-not-free-slots",
        aspect: Aspect::Output,
        functions: &["Z3_substitute_vars", "Z3_is_eq_ast"],
        statement: "Replacing free slot zero in a formula whose only de Bruijn variable is locally bound leaves the quantified AST unchanged.",
    },
    Claim {
        family: "contract-substitution-rewriting",
        check: "substitution.rewriting.update-arguments-preserves-operator",
        aspect: Aspect::Output,
        functions: &["Z3_update_term", "Z3_get_decl_kind", "Z3_get_app_decl"],
        statement: "Updating the two children of x-y to seven and two preserves SUB and yields five, rejecting operand reversal.",
    },
    Claim {
        family: "contract-substitution-rewriting",
        check: "substitution.rewriting.original-term-unchanged",
        aspect: Aspect::State,
        functions: &["Z3_update_term", "Z3_get_app_arg", "Z3_is_eq_ast"],
        statement: "Updating an application produces the requested replacement without mutating the original x-y argument identities.",
    },
    Claim {
        family: "contract-substitution-rewriting",
        check: "substitution.rewriting.identical-update-preserves-identity",
        aspect: Aspect::Output,
        functions: &["Z3_update_term", "Z3_is_eq_ast"],
        statement: "Updating the integer application with its existing two argument ASTs preserves the original AST identity.",
    },
    Claim {
        family: "contract-substitution-rewriting",
        check: "substitution.rewriting.wrong-arity-refused",
        aspect: Aspect::Errors,
        functions: &[
            "Z3_update_term",
            "Z3_get_error_code",
            "Z3_set_error_handler",
        ],
        statement: "A one-argument update of a two-argument application returns the original term and reports IOB through context code and callback, matching the pinned explicit arity guard.",
    },
    Claim {
        family: "contract-substitution-rewriting",
        check: "substitution.rewriting.valid-update-recovers",
        aspect: Aspect::Errors,
        functions: &["Z3_update_term", "Z3_get_error_code"],
        statement: "After the arity refusal a valid two-argument update succeeds with OK and evaluates to five.",
    },
    Claim {
        family: "contract-substitution-rewriting",
        check: "substitution.rewriting.sum-of-monomials-parameter-effect",
        aspect: Aspect::State,
        functions: &[
            "Z3_mk_params",
            "Z3_params_inc_ref",
            "Z3_params_dec_ref",
            "Z3_params_set_bool",
            "Z3_simplify_ex",
            "Z3_get_decl_kind",
        ],
        statement: "The same polynomial (x+1)*(y+2) simplifies to a multiplication with som=false and an addition with som=true; both result ASTs survive parameter-object release and differ structurally.",
    },
    Claim {
        family: "contract-substitution-rewriting",
        check: "substitution.rewriting.parameter-results-preserve-25-values",
        aspect: Aspect::Output,
        functions: &["Z3_simplify_ex", "Z3_substitute", "Z3_simplify"],
        statement: "For all 25 integer pairs x,y from minus two through two, both parameterized results equal independent bounded C arithmetic (x+1)*(y+2).",
    },
    Claim {
        family: "contract-substitution-rewriting",
        check: "substitution.rewriting.symbolic-parameter-equivalence",
        aspect: Aspect::Output,
        functions: &["Z3_simplify_ex", "Z3_solver_check"],
        statement: "A solver rejects inequality between the factored and expanded simplifier results, beyond their structural parameter difference and finite evaluations.",
    },
    Claim {
        family: "contract-substitution-rewriting",
        check: "substitution.rewriting.default-ground-simplification",
        aspect: Aspect::Output,
        functions: &["Z3_simplify", "Z3_get_bool_value"],
        statement: "Default simplification of the equality between updated integer subtraction 7-2 and five produces literal Boolean true.",
    },
];
