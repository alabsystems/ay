// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{wire_rule_name, TheoryLemmaKind};

impl TheoryLemmaKind {
    /// Get the Alethe rule name for this lemma kind.
    #[must_use]
    pub fn alethe_rule(&self) -> &'static str {
        match self {
            Self::EufTransitive => "eq_transitive",
            Self::EufReflexive => "eq_reflexive",
            Self::EufCongruent => "eq_congruent",
            Self::EufCongruentPred => "eq_congruent_pred",
            Self::LraFarkas => "la_generic",
            Self::LiaGeneric => "lia_generic",
            Self::LiaModRange => "lia_mod_range",
            Self::BvLiaTautology => "bv_lia_tautology",
            Self::SeqExtensionalCompanionContradiction => "seq_extensional_companion_contradiction",
            Self::BvBitBlast | Self::BvBitBlastGate { .. } => "bv_bitblast",
            Self::ArraySelectStore { index_eq: true } => "read_over_write_pos",
            Self::ArraySelectStore { index_eq: false } => "read_over_write_neg",
            Self::ArrayStorePermutation => "store_permutation",
            Self::ArrayRowChain => "read_over_write_chain",
            Self::ArrayDefaultConst => "array_default_const",
            Self::SetCardNonNegative => "set_card_non_negative",
            Self::SetCardMemberLowerBound => "set_card_member_lower_bound",
            Self::SetCardEmpty => "set_card_empty",
            Self::SetCardMemberCount => "set_card_member_count",
            Self::SetCardEmptyByAssertion => "set_card_empty_by_assertion",
            Self::SetCardChainRecurrence => "set_card_chain_recurrence",
            Self::SubsetReflexive => "subset_reflexive",
            Self::SubsetElementInstance => "subset_element_instance",
            Self::SubsetTransitive => "subset_transitive",
            Self::SubsetGroundEval => "subset_ground_eval",
            Self::ArrayExtensionality => "extensionality",
            Self::FpToBv { .. } => "fp_to_bv",
            Self::StringLengthAxiom => "string_length",
            Self::StringLengthLemma => "string_length_lemma",
            Self::StringContentAxiom => "string_decompose",
            Self::StringNormalForm => "string_code_inj",
            Self::StringGroundEval => "string_ground_eval",
            Self::SeqGroundEval => "seq_ground_eval",
            Self::ArithClauseTautology => "arith_clause_tautology",
            Self::IteBranchProjection => "ite_branch_projection",
            Self::ArrayGuardedRowExpansion => "array_guarded_row_expansion",
            Self::RegexIntersectEmpty => "regex_intersect_empty",
            Self::StringContainmentIdentity => "string_containment_identity",
            Self::StringConcatCancellation => "string_concat_cancellation",
            Self::StringGroundFactorConflict => "string_ground_factor_conflict",
            Self::RegexLengthLowerBound => "regex_length_lower_bound",
            Self::DatatypeDistinct => "dt_distinct",
            Self::DatatypeEnumPigeonhole => "dt_enum_pigeonhole",
            Self::DatatypeSelectorProject => "dt_project",
            Self::DatatypeTesterEval => "dt_tester",
            Self::DatatypeTesterExclusive => "dt_tester_exclusive",
            Self::DatatypeExhaustive => "dt_exhaustive",
            Self::DatatypeConstructorReconstruct => "dt_ctor_reconstruct",
            Self::DatatypeInjective => "dt_injective",
            Self::DatatypeAcyclicDirect => "dt_acyclic_direct",
            Self::DatatypeValueEqCongruence => "dt_value_eq_congruence",
            Self::DatatypeGroundConflict => "dt_ground_conflict",
            Self::OrderIteTautology => "order_ite_tautology",
            Self::BoolTautology => "bool_tautology",
            Self::ArithEqTriangle => "arith_eq_triangle",
            Self::ArithEqImpliesBound => "arith_eq_implies_bound",
            Self::IntBoundsTautology => "int_bounds_tautology",
            Self::IntBoundLatticeGap => "int_bound_lattice_gap",
            Self::IntCutLatticeGap => "int_cut_lattice_gap",
            Self::ArithDisequalitySplit => "arith_disequality_split",
            Self::IteSame => "ite_same",
            Self::FpClassification { .. } => "fp_classification",
            Self::FpRoundingModeDomain => "fp_rm_domain",
            Self::FpForwardError => "fp_forward_error",
            Self::NraIntervalUnsat => "nra_interval_unsat",
            Self::NraUnivariateUnsat => "nra_univariate_unsat",
            Self::Generic => "trust",
            Self::RoundingModeDomain => "fp_rounding_mode_domain",
            Self::FpGroundEval => "fp_ground_eval",
            Self::ArrayFiniteExtensionality => "array_finite_extensionality",
            Self::ArrayFiniteSelectExpansion => "array_finite_select_expansion",
            Self::QuantifierNegatedExistsDual => "quantifier_negated_exists_dual",
            Self::GroundEqualitySubstitution => "ground_equality_substitution",
        }
    }

    /// The rule name that may be written into an emitted Alethe proof.
    ///
    /// Internal names continue to drive AY classifiers and diagnostics; kinds
    /// unsupported by the wire format render as honest unproved steps.
    #[must_use]
    pub fn alethe_wire_rule(&self) -> &str {
        wire_rule_name(self.alethe_rule())
    }

    /// True if this theory lemma kind exports as unverified trust.
    #[must_use]
    pub fn is_trust(&self) -> bool {
        matches!(self, Self::Generic)
    }
}
