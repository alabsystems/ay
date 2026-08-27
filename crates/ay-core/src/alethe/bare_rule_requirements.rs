// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Alethe rules that cannot authenticate premise-free, argument-free steps.

/// Rules whose pinned implementations require at least one premise or arg.
///
/// This is a measured property of carcara 1.1.0: each implementation rejects
/// the premise/argument count before inspecting the clause. Rules whose
/// evidence count is conclusion-dependent (`la_generic`, `forall_inst`, and
/// `bind`) are intentionally absent, as is the semantic placeholder
/// `lia_generic`.
pub(super) const PREMISE_OR_ARG_REQUIRED_ALETHE_RULES: [&str; 65] = [
    "and",
    "and_intro",
    "and_pos",
    "arrays_ext",
    "arrays_row",
    "arrays_row_contra",
    "bfun_elim",
    "concat_conflict",
    "concat_cprop_prefix",
    "concat_cprop_suffix",
    "concat_csplit_prefix",
    "concat_csplit_suffix",
    "concat_eq",
    "concat_lprop_prefix",
    "concat_lprop_suffix",
    "concat_split_prefix",
    "concat_split_suffix",
    "concat_unify",
    "cong",
    "contraction",
    "cp_addition",
    "cp_division",
    "cp_literal",
    "cp_multiplication",
    "cp_saturation",
    "equiv1",
    "equiv2",
    "ho_cong",
    "implies",
    "ite1",
    "ite2",
    "not_and",
    "not_equiv1",
    "not_equiv2",
    "not_implies1",
    "not_implies2",
    "not_ite1",
    "not_ite2",
    "not_or",
    "not_symm",
    "not_xor1",
    "not_xor2",
    "or",
    "or_neg",
    "pbblast_bvand_ith_bit",
    "pbblast_bvxor_ith_bit",
    "poly_simp_rel",
    "re_concat_unfold_pos",
    "re_inter",
    "re_kleene_star_unfold_pos",
    "re_unfold_neg",
    "re_unfold_neg_concat_fixed_prefix",
    "re_unfold_neg_concat_fixed_suffix",
    "reordering",
    "resolution",
    "strict_resolution",
    "string_decompose",
    "string_length_non_empty",
    "string_length_pos",
    "symm",
    "tautology",
    "th_resolution",
    "weakening",
    "xor1",
    "xor2",
];

/// True if the pinned Alethe checker rejects a bare step with `name` before
/// inspecting its clause because the step has no premise or argument.
#[must_use]
pub fn alethe_rule_requires_premises_or_args(name: &str) -> bool {
    PREMISE_OR_ARG_REQUIRED_ALETHE_RULES
        .binary_search(&name)
        .is_ok()
}
