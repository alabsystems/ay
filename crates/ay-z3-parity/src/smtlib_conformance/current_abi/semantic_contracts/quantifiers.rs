// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite binder, pattern and quantified-formula witnesses for Z3 5.3.3.
//!
//! The source contract is src/api/z3_api.h (Quantifiers / AST reflection) and
//! src/api/api_quant.cpp at 430d19e697e2ec9bad79ff210d41b4a7a5fcfa3e.
//! Declaration arrays are in source order, with their LAST entry at de-Bruijn
//! index zero. Extended constructors never receive patterns and no-patterns
//! together. IDs are checked only when explicitly supplied, and every indexed
//! getter is preceded by its exact count check. Constant constructors abstract
//! only uninterpreted nullary applications. No substitution API is exercised.
//!
//! Calibration mutants (one exact replacement in the named C fixture):
//! - reflection: `Z3_get_quantifier_weight(c, universal) == 7` -> `== 8`;
//!   exit 2, failed CHECK `quantifier.reflection.explicit-attributes`.
//! - semantics: `quantifier_decision(c, solver, all_nonnegative, Z3_L_FALSE)`
//!   -> same call with `Z3_L_TRUE`; exit 2, failed CHECK
//!   `quantifier.semantics.forall-negative-control`.
//! - constants: `quantifier_constant_decision(c, solver, some_equal, Z3_L_TRUE)`
//!   -> same call with `Z3_L_FALSE`; exit 2, failed CHECK
//!   `quantifier.constants.exists-free-value`.
//! All other expectations and inputs stay unchanged in each mutant.

use super::{Aspect, Claim, Family};

pub(super) const REMAINING_SCOPE: &str = "Quantifier checks cover two explicitly typed binders, supplied weight/IDs, one valid multi-pattern, one excluded subterm, ground integer existential/universal controls, two finite nested Bool formulas, and single-constant abstraction with a retained free constant. Arbitrary quantified theories, trigger inference or completeness, matching-loop behavior, qid/skolem naming defaults, zero-binder or invalid arguments, lambda/recursive/higher-order binders, generalized substitution and capture avoidance, cross-context translation, concurrent contexts, resource exhaustion and every other unlisted argument/state/lifetime domain remain unqualified.";

pub(super) const FAMILIES: &[Family] = &[
    Family {
        id: "contract-quantifier-reflection",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/quantifier_helpers.h"),
            include_str!("../contracts/quantifier_reflection.c")
        ),
        checks: &[
            "quantifier.reflection.context-created",
            "quantifier.reflection.sorts",
            "quantifier.reflection.debruijn-indices",
            "quantifier.reflection.first-declaration",
            "quantifier.reflection.second-declaration",
            "quantifier.reflection.pattern-terms-created",
            "quantifier.reflection.multi-pattern",
            "quantifier.reflection.body-created",
            "quantifier.reflection.forall-kind",
            "quantifier.reflection.declaration-order",
            "quantifier.reflection.body-preserved",
            "quantifier.reflection.explicit-attributes",
            "quantifier.reflection.pattern-counts",
            "quantifier.reflection.reflected-pattern",
            "quantifier.reflection.exists-no-pattern",
            "quantifier.reflection.no-pattern-content",
        ],
    },
    Family {
        id: "contract-quantifier-semantics",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/quantifier_helpers.h"),
            include_str!("../contracts/quantifier_semantics.c")
        ),
        checks: &[
            "quantifier.semantics.context-created",
            "quantifier.semantics.sorts",
            "quantifier.semantics.terms",
            "quantifier.semantics.bodies",
            "quantifier.semantics.bound-constructors",
            "quantifier.semantics.solver-created",
            "quantifier.semantics.forall-negative-control",
            "quantifier.semantics.exists-negative-witness",
            "quantifier.semantics.successor-created",
            "quantifier.semantics.impossible-body-created",
            "quantifier.semantics.exists-impossible",
            "quantifier.semantics.generic-body-created",
            "quantifier.semantics.generic-polarity",
            "quantifier.semantics.nested-variables",
            "quantifier.semantics.nested-body-created",
            "quantifier.semantics.inner-scopes",
            "quantifier.semantics.outer-scopes",
            "quantifier.semantics.forall-exists-finite",
            "quantifier.semantics.forall-exists-negation",
            "quantifier.semantics.exists-forall-finite",
        ],
    },
    Family {
        id: "contract-quantifier-constants",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/quantifier_helpers.h"),
            include_str!("../contracts/quantifier_constants.c")
        ),
        checks: &[
            "quantifier.constants.context-created",
            "quantifier.constants.sort-created",
            "quantifier.constants.terms-created",
            "quantifier.constants.body-created",
            "quantifier.constants.abstraction-constructors",
            "quantifier.constants.abstract-body-created",
            "quantifier.constants.free-constant-preserved",
            "quantifier.constants.source-body-unmodified",
            "quantifier.constants.solver-created",
            "quantifier.constants.exists-free-value",
            "quantifier.constants.exists-free-value-valid",
            "quantifier.constants.forall-free-value-impossible",
            "quantifier.constants.generic-body-created",
            "quantifier.constants.generic-polarity",
            "quantifier.constants.pattern-declaration",
            "quantifier.constants.pattern-application",
            "quantifier.constants.pattern-created",
            "quantifier.constants.identity-body",
            "quantifier.constants.extended-pattern-created",
            "quantifier.constants.abstract-pattern-created",
            "quantifier.constants.pattern-abstracts-only-bound",
            "quantifier.constants.extended-no-pattern-created",
            "quantifier.constants.no-pattern-abstracted",
            "quantifier.constants.ground-application",
            "quantifier.constants.ground-equality",
            "quantifier.constants.ground-counterexample-created",
            "quantifier.constants.counterexample-without-quantifier",
            "quantifier.constants.pattern-quantifier-refutes-counterexample",
            "quantifier.constants.counterexample-scope-restored",
            "quantifier.constants.no-pattern-quantifier-refutes-counterexample",
            "quantifier.constants.retained-after-solver-release",
        ],
    },
];

pub(super) const CLAIMS: &[Claim] = &[
    Claim { family: "contract-quantifier-reflection", check: "quantifier.reflection.debruijn-indices", aspect: Aspect::Output, functions: &["Z3_mk_bound", "Z3_get_ast_kind", "Z3_get_index_value", "Z3_get_sort", "Z3_is_eq_sort"], statement: "The supplied Int index1 and Bool index0 remain distinct bound-variable ASTs of the supplied sorts with those exact de-Bruijn indices." },
    Claim { family: "contract-quantifier-reflection", check: "quantifier.reflection.multi-pattern", aspect: Aspect::Output, functions: &["Z3_mk_pattern", "Z3_pattern_to_ast", "Z3_get_pattern_num_terms", "Z3_get_pattern", "Z3_is_eq_ast"], statement: "The valid two-term pattern contains f(Int#1,Bool#0), then g(Int#1,Bool#0), in precisely that term order." },
    Claim { family: "contract-quantifier-reflection", check: "quantifier.reflection.forall-kind", aspect: Aspect::Output, functions: &["Z3_mk_quantifier_ex", "Z3_is_quantifier_forall", "Z3_is_quantifier_exists", "Z3_get_ast_kind"], statement: "The extended universal constructor creates a quantifier AST classified as forall and not exists." },
    Claim { family: "contract-quantifier-reflection", check: "quantifier.reflection.declaration-order", aspect: Aspect::Output, functions: &["Z3_get_quantifier_num_bound", "Z3_get_quantifier_bound_name", "Z3_get_quantifier_bound_sort", "Z3_mk_int_symbol", "Z3_get_symbol_kind", "Z3_get_symbol_string"], statement: "The two declarations reflect as nonnull string symbols outer_i:Int then inner_b:Bool in supplied source order, independently of reversed de-Bruijn indexing; the comparison helper rejects null and the integer symbol17 without requesting their string contents." },
    Claim { family: "contract-quantifier-reflection", check: "quantifier.reflection.body-preserved", aspect: Aspect::Output, functions: &["Z3_get_quantifier_body", "Z3_is_eq_ast"], statement: "The reflected universal body equals the exact supplied equality of the two retained applications." },
    Claim { family: "contract-quantifier-reflection", check: "quantifier.reflection.explicit-attributes", aspect: Aspect::Output, functions: &["Z3_get_quantifier_weight", "Z3_get_quantifier_id", "Z3_get_quantifier_skolem_id", "Z3_get_symbol_kind", "Z3_get_symbol_string"], statement: "Weight7 and the explicitly supplied nonnull string-symbol qid reflection-qid and skolem ID reflection-skid roundtrip; no unspecified default IDs are compared." },
    Claim { family: "contract-quantifier-reflection", check: "quantifier.reflection.reflected-pattern", aspect: Aspect::Output, functions: &["Z3_get_quantifier_num_patterns", "Z3_get_quantifier_num_no_patterns", "Z3_get_quantifier_pattern_ast", "Z3_get_pattern_num_terms", "Z3_get_pattern"], statement: "The universal quantifier reports one two-term pattern, no excluded patterns, and returns the original two terms in order." },
    Claim { family: "contract-quantifier-reflection", check: "quantifier.reflection.no-pattern-content", aspect: Aspect::Output, functions: &["Z3_mk_quantifier_ex", "Z3_is_quantifier_exists", "Z3_get_quantifier_num_patterns", "Z3_get_quantifier_num_no_patterns", "Z3_get_quantifier_no_pattern_ast", "Z3_get_quantifier_weight", "Z3_get_quantifier_id", "Z3_get_quantifier_skolem_id", "Z3_get_symbol_kind", "Z3_get_symbol_string"], statement: "A separate existential has zero explicit patterns, exactly the excluded g subterm, unchanged body, weight3 and its two supplied nonnull string-symbol attribute names." },
    Claim { family: "contract-quantifier-semantics", check: "quantifier.semantics.bound-constructors", aspect: Aspect::Output, functions: &["Z3_mk_forall", "Z3_mk_exists", "Z3_is_quantifier_forall", "Z3_is_quantifier_exists", "Z3_get_quantifier_num_bound", "Z3_get_quantifier_bound_name", "Z3_get_symbol_kind", "Z3_get_symbol_string", "Z3_get_quantifier_body"], statement: "The bound constructors preserve universal/existential kind; the universal retains one integer_x binder as a nonnull string symbol and the supplied nonnegative body." },
    Claim { family: "contract-quantifier-semantics", check: "quantifier.semantics.forall-negative-control", aspect: Aspect::Output, functions: &["Z3_mk_forall", "Z3_solver_assert", "Z3_solver_check"], statement: "Asserting forall integer x. x>=0 is unsatisfiable, distinguishing a universal binder from a free or existential variable." },
    Claim { family: "contract-quantifier-semantics", check: "quantifier.semantics.exists-negative-witness", aspect: Aspect::Output, functions: &["Z3_mk_exists", "Z3_solver_reset", "Z3_solver_check"], statement: "After resetting the solver, exists integer x. x<0 is satisfiable." },
    Claim { family: "contract-quantifier-semantics", check: "quantifier.semantics.exists-impossible", aspect: Aspect::Output, functions: &["Z3_mk_exists", "Z3_solver_check"], statement: "The existential integer equality x+1=x is unsatisfiable, distinguishing a real existential body from a constant true result." },
    Claim { family: "contract-quantifier-semantics", check: "quantifier.semantics.generic-polarity", aspect: Aspect::Output, functions: &["Z3_mk_quantifier", "Z3_solver_check"], statement: "Using the same integer body x=0, generic forall construction is unsatisfiable and generic exists construction is satisfiable." },
    Claim { family: "contract-quantifier-semantics", check: "quantifier.semantics.forall-exists-negation", aspect: Aspect::Output, functions: &["Z3_mk_bound", "Z3_mk_forall", "Z3_mk_exists", "Z3_solver_check"], statement: "The nested Bool formula forall p exists q. q=p is satisfiable and its negation is unsatisfiable; outer p uses de-Bruijn index1 inside the inner binder." },
    Claim { family: "contract-quantifier-semantics", check: "quantifier.semantics.exists-forall-finite", aspect: Aspect::Output, functions: &["Z3_mk_forall", "Z3_mk_exists", "Z3_solver_check"], statement: "Reversing the nested Bool quantifier kinds gives exists p forall q. q=p, which is unsatisfiable." },
    Claim { family: "contract-quantifier-constants", check: "quantifier.constants.free-constant-preserved", aspect: Aspect::Output, functions: &["Z3_mk_exists_const", "Z3_get_quantifier_body", "Z3_get_quantifier_num_bound", "Z3_get_quantifier_bound_name", "Z3_get_quantifier_bound_sort", "Z3_get_symbol_kind", "Z3_get_symbol_string", "Z3_get_index_value", "Z3_get_app_arg"], statement: "Abstracting only constant abstract_x changes its occurrence to bound index0, preserves the other free constant and reflects the one supplied name as a nonnull string symbol and its Int sort." },
    Claim { family: "contract-quantifier-constants", check: "quantifier.constants.source-body-unmodified", aspect: Aspect::State, functions: &["Z3_mk_forall_const", "Z3_mk_exists_const", "Z3_get_app_arg", "Z3_is_eq_ast"], statement: "The original retained equality still contains both original constant ASTs after the forall/exists constant constructors abstract their copies." },
    Claim { family: "contract-quantifier-constants", check: "quantifier.constants.exists-free-value-valid", aspect: Aspect::Output, functions: &["Z3_mk_exists_const", "Z3_solver_check"], statement: "Exists x. x=free_value is satisfiable and its negation unsatisfiable for the unbound integer constant free_value." },
    Claim { family: "contract-quantifier-constants", check: "quantifier.constants.forall-free-value-impossible", aspect: Aspect::Output, functions: &["Z3_mk_forall_const", "Z3_solver_check"], statement: "Forall integer x. x=free_value is unsatisfiable while free_value stays free." },
    Claim { family: "contract-quantifier-constants", check: "quantifier.constants.generic-polarity", aspect: Aspect::Output, functions: &["Z3_mk_quantifier_const", "Z3_solver_check"], statement: "The generic constant-abstraction constructor with x=7 is unsatisfiable for universal and satisfiable for existential polarity." },
    Claim { family: "contract-quantifier-constants", check: "quantifier.constants.pattern-abstracts-only-bound", aspect: Aspect::Output, functions: &["Z3_mk_quantifier_const_ex", "Z3_get_quantifier_pattern_ast", "Z3_get_pattern", "Z3_get_index_value", "Z3_get_quantifier_weight", "Z3_get_quantifier_id", "Z3_get_quantifier_skolem_id", "Z3_get_symbol_kind", "Z3_get_symbol_string"], statement: "The extended constant constructor abstracts x within f(x,free_value), leaves free_value free, and preserves supplied weight11 and explicit attribute names as nonnull string symbols." },
    Claim { family: "contract-quantifier-constants", check: "quantifier.constants.no-pattern-abstracted", aspect: Aspect::Output, functions: &["Z3_mk_quantifier_const_ex", "Z3_get_quantifier_num_patterns", "Z3_get_quantifier_num_no_patterns", "Z3_get_quantifier_no_pattern_ast", "Z3_get_quantifier_body"], statement: "The no-pattern form has zero explicit patterns and one excluded f term abstracted to the same bound/free arguments as the explicit pattern form, with the same quantified body." },
    Claim { family: "contract-quantifier-constants", check: "quantifier.constants.pattern-quantifier-refutes-counterexample", aspect: Aspect::State, functions: &["Z3_mk_quantifier_const_ex", "Z3_solver_push", "Z3_solver_assert", "Z3_solver_check"], statement: "The free ground counterexample f(0,free_value)!=0 is satisfiable; adding forall x. f(x,free_value)=x with the supplied f pattern makes that solver scope unsatisfiable." },
    Claim { family: "contract-quantifier-constants", check: "quantifier.constants.counterexample-scope-restored", aspect: Aspect::State, functions: &["Z3_solver_pop", "Z3_solver_check"], statement: "Popping the contradictory universal scope restores satisfiability of the original ground counterexample." },
    Claim { family: "contract-quantifier-constants", check: "quantifier.constants.no-pattern-quantifier-refutes-counterexample", aspect: Aspect::State, functions: &["Z3_mk_quantifier_const_ex", "Z3_solver_assert", "Z3_solver_check"], statement: "The separate no-pattern universal form also refutes the same satisfiable ground counterexample; this makes no claim about trigger inference completeness." },
    Claim { family: "contract-quantifier-constants", check: "quantifier.constants.retained-after-solver-release", aspect: Aspect::Lifetime, functions: &["Z3_inc_ref", "Z3_dec_ref", "Z3_solver_dec_ref", "Z3_get_pattern", "Z3_get_quantifier_body", "Z3_get_quantifier_no_pattern_ast"], statement: "Before context destruction, explicitly retained quantifiers, abstracted pattern terms and bodies preserve their observations after solver release and256 balanced temporary integer AST allocations." },
];
