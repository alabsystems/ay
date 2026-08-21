// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Stable registry for the one-to-one public Unknown origin taxonomy.

impl UnknownOrigin {
    /// Closed origin inventory. Its order is identical to
    /// [`UnknownReason::ALL`], making the bijection mechanically checkable.
    pub const ALL: [Self; 19] = [
        Self::SolveDeadline,
        Self::DeterministicResourceBudget,
        Self::MemoryBudget,
        Self::InterruptFlag,
        Self::IncompleteSolverLane,
        Self::VerdictCertification,
        Self::EmatchingRoundBudget,
        Self::DeferredInstantiation,
        Self::UnhandledQuantifier,
        Self::CegqiRefinement,
        Self::ExistentialEmatching,
        Self::TheorySplitBudget,
        Self::UnsupportedExpressionSplit,
        Self::UnsupportedFeature,
        Self::UnsupportedArithmeticFragment,
        Self::UnsupportedMixedCollection,
        Self::ExecutorFailure,
        Self::UntaggedSolverUnknown,
        Self::TerminalTrust,
    ];

    /// Stable evidence code for this exact production origin.
    pub const fn code(self) -> &'static str {
        match self {
            Self::SolveDeadline => "solve_deadline",
            Self::DeterministicResourceBudget => "deterministic_resource_budget",
            Self::MemoryBudget => "memory_budget",
            Self::InterruptFlag => "interrupt_flag",
            Self::IncompleteSolverLane => "incomplete_solver_lane",
            Self::VerdictCertification => "verdict_certification",
            Self::TerminalTrust => "terminal_trust",
            Self::EmatchingRoundBudget => "ematching_round_budget",
            Self::DeferredInstantiation => "deferred_instantiation",
            Self::UnhandledQuantifier => "unhandled_quantifier",
            Self::CegqiRefinement => "cegqi_refinement",
            Self::ExistentialEmatching => "existential_ematching",
            Self::TheorySplitBudget => "theory_split_budget",
            Self::UnsupportedExpressionSplit => "unsupported_expression_split",
            Self::UnsupportedFeature => "unsupported_feature",
            Self::UnsupportedArithmeticFragment => "unsupported_arithmetic_fragment",
            Self::UnsupportedMixedCollection => "unsupported_mixed_collection",
            Self::ExecutorFailure => "executor_failure",
            Self::UntaggedSolverUnknown => "untagged_solver_unknown",
        }
    }

    /// The only reason this origin is authorized to publish.
    pub const fn reason(self) -> UnknownReason {
        match self {
            Self::SolveDeadline => UnknownReason::Timeout,
            Self::DeterministicResourceBudget => UnknownReason::ResourceLimit,
            Self::MemoryBudget => UnknownReason::MemoryLimit,
            Self::InterruptFlag => UnknownReason::Interrupted,
            Self::IncompleteSolverLane => UnknownReason::Incomplete,
            Self::VerdictCertification => UnknownReason::SelfCheckRejected,
            Self::TerminalTrust => UnknownReason::ProofTrusted,
            Self::EmatchingRoundBudget => UnknownReason::QuantifierRoundLimit,
            Self::DeferredInstantiation => UnknownReason::QuantifierDeferred,
            Self::UnhandledQuantifier => UnknownReason::QuantifierUnhandled,
            Self::CegqiRefinement => UnknownReason::QuantifierCegqiIncomplete,
            Self::ExistentialEmatching => UnknownReason::QuantifierEmatchingExistsIncomplete,
            Self::TheorySplitBudget => UnknownReason::SplitLimit,
            Self::UnsupportedExpressionSplit => UnknownReason::ExpressionSplit,
            Self::UnsupportedFeature => UnknownReason::Unsupported,
            Self::UnsupportedArithmeticFragment => UnknownReason::UnsupportedArithmetic,
            Self::UnsupportedMixedCollection => UnknownReason::UnsupportedMixedCollection,
            Self::ExecutorFailure => UnknownReason::InternalError,
            Self::UntaggedSolverUnknown => UnknownReason::Unknown,
        }
    }

    /// Stable source-level producer family audited for this origin.
    ///
    /// The conformance probe reports this value alongside whether it exercised
    /// a deterministic public query or the explicit origin fault path. These
    /// are production chokepoints, not test module locations.
    pub const fn production_chokepoint(self) -> &'static str {
        match self {
            Self::SolveDeadline => "executor/check_sat.rs::should_abort_theory_loop",
            Self::DeterministicResourceBudget => {
                "executor/theories/model_helpers.rs::record_sat_unknown_reason"
            }
            Self::MemoryBudget => "executor/check_sat.rs::should_abort_theory_loop",
            Self::InterruptFlag => "executor/check_sat.rs::should_abort_theory_loop",
            Self::IncompleteSolverLane => "executor/check_sat.rs::check_sat_guarded",
            Self::VerdictCertification => {
                "executor/unsat_cert.rs::reject_uncertified_verdict_for_publication"
            }
            Self::TerminalTrust => {
                "executor/unsat_cert.rs::decline_trust_bearing_unsat_under_strict_proofs"
            }
            Self::EmatchingRoundBudget
            | Self::DeferredInstantiation
            | Self::UnhandledQuantifier
            | Self::ExistentialEmatching => {
                "executor/quantifier_loop/result_mapping.rs::map_quantifier_result"
            }
            Self::CegqiRefinement => {
                "executor/quantifier_loop/cegqi_refinement.rs::try_cegqi_arith_refinement"
            }
            Self::TheorySplitBudget => "pipeline_incremental_split_assume_macros.rs::split_loop",
            Self::UnsupportedExpressionSplit => {
                "pipeline_incremental_split_eager_shared_macros.rs::create_expression_split_atoms"
            }
            Self::UnsupportedFeature => "executor.rs::execute_stack_guarded",
            Self::UnsupportedArithmeticFragment => {
                "executor/check_sat.rs::contains_symbolic_integer_power"
            }
            Self::UnsupportedMixedCollection => "executor/theories/seq.rs::solve_seq_auflia",
            Self::ExecutorFailure => "api/solving/check.rs::record_executor_failure_unknown",
            Self::UntaggedSolverUnknown => {
                "executor/lifecycle/unknown_publication.rs::finalize_unknown_publication"
            }
        }
    }
}
