// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
//! OPB/WBO pseudo-Boolean format parser.
//!
//! Parses the competition formats used in PB26 (Pseudo-Boolean Evaluation):
//! - **OPB**: Decision and optimization instances with linear/non-linear
//!   pseudo-Boolean constraints.
//! - **WBO**: Weighted Boolean Optimization instances with hard and soft
//!   constraints.
//!
//! # Format Reference
//!
//! See <https://www.cril.univ-artois.fr/PB24/OPBcompetition.pdf>
//!
//! # Example
//!
//! ```
//! use ay_pb_core::{parse_opb, PbRel};
//!
//! let input = "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n";
//! let instance = parse_opb(input).unwrap();
//! assert_eq!(instance.num_vars, 2);
//! assert_eq!(instance.constraints[0].rel, PbRel::Ge);
//! ```

// ay-pb contains no `unsafe` in production or tests; make that a compiler-
// enforced invariant (matches the workspace's theory crates).
#![forbid(unsafe_code)]

/// Engine A/B switches, set ONCE by the frontend before any solve.
///
/// B14 of the env-flag retirement: these were `AY_PB_*` env vars nothing set
/// (`AY_PB_NO_CLIQUE_COLORING`, `AY_PB_NO_INJCOMP`, `AY_PB_NO_COMPACT_CERT`,
/// `AY_PB_NO_RESTART_FLOOR`, `AY_PB_DISABLE_COUNTING`). Every switch guards a
/// SOUND alternative path — disabling is for A/B measurement, never for
/// correctness. The carrier is a typed set-once bridge (the same shape as
/// ay's `DISABLED_SAT_TECHNIQUES`): the portfolio entry fns have seven
/// downstream consumers and threading a config through every signature is
/// churn without benefit for process-constant switches.
pub mod ab_switches {
    use std::sync::OnceLock;

    /// The switch set. Every field defaults to the SHIPPED engine — all ON.
    /// (B31 flipped the four lanes the official PB-COMP wrapper used to
    /// enable by env export into in-engine defaults; the exports are gone.)
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct PbAbSwitches {
        /// Clique-coloring certified-optimum shortcut (sound, 0-wrong).
        pub clique_coloring: bool,
        /// Injcomp certified-optimum shortcut (sound, 0-wrong).
        pub injcomp: bool,
        /// Compact certificate path (strictly additive; VeriPB re-checks).
        pub compact_cert: bool,
        /// Dense-PB restart floor (without it dense search may never restart).
        pub restart_floor: bool,
        /// Counting propagation (both counting and non-counting are sound).
        pub counting: bool,
        /// Structure-aware BNN feasibility seed (advisory-only starting
        /// point; B31 default-on — the official wrapper always enabled it).
        pub bnn_feas: bool,
        /// BNN-first sequential routing on recognized BNN OPT-LIN instances
        /// (reroutes TIME only; B31 default-on).
        pub bnn_sched: bool,
        /// Product-native (OPT-NLC) primal SLS first-incumbent path
        /// (advisory-only, sanitize-verified; B31 default-on).
        pub sls_nlc: bool,
        /// WBO SLS: the parallel `wbo-sls-opt` worker AND the sequential tail
        /// fallback follow this one switch (B31; the wrapper set both on).
        pub wbo_sls: bool,
        /// Stronger LNS2 neighborhoods (local branching + feasibility pump).
        pub lns2: bool,
        /// Shape-gated symmetry arm (probe-then-augment).
        pub symmetry_arm: bool,
        /// Root EDAC/VAC-lite WCSP probe (B56; opt-in — ships OFF, the one
        /// non-kill switch in the set).
        pub wcsp_edac: bool,
        /// Parallel-portfolio worker policy (B57; was `the --pb-parallel policy`):
        /// `None` = the shipped default (parallel ON, auto/NBCORE-sized),
        /// `Some(0)` = force the sequential path, `Some(n)` = n workers.
        pub parallel_workers: Option<u16>,
        /// Two-club node cap override (B74; `--pb-two-club-max-nodes`).
        pub two_club_max_nodes: Option<u64>,
        /// Two-club branch-rule selector (B74; `--pb-two-club-branch`).
        pub two_club_branch: Option<&'static str>,
        /// Two-club search tracing (B74; `--pb-two-club-trace`).
        pub two_club_trace: bool,
        /// Two-club frontier dump (B74; `--pb-two-club-dump-frontier`).
        pub two_club_dump_frontier: bool,
    }

    impl Default for PbAbSwitches {
        fn default() -> Self {
            Self {
                clique_coloring: true,
                injcomp: true,
                compact_cert: true,
                restart_floor: true,
                counting: true,
                bnn_feas: true,
                bnn_sched: true,
                sls_nlc: true,
                wbo_sls: true,
                lns2: true,
                symmetry_arm: true,
                wcsp_edac: false,
                parallel_workers: None,
                two_club_max_nodes: None,
                two_club_branch: None,
                two_club_trace: false,
                two_club_dump_frontier: false,
            }
        }
    }

    static SWITCHES: OnceLock<PbAbSwitches> = OnceLock::new();

    /// Install the switch set. First caller wins; a second call returns the
    /// rejected value so a misconfigured double-install is loud at the caller.
    ///
    /// # Errors
    ///
    /// The rejected `switches` when a set was already installed.
    pub fn set(switches: PbAbSwitches) -> Result<(), PbAbSwitches> {
        SWITCHES.set(switches).map_err(|_| switches)
    }

    /// The installed switch set, or the all-on default.
    #[must_use]
    pub fn get() -> PbAbSwitches {
        #[cfg(test)]
        if let Some(overridden) = TEST_OVERRIDE.with(std::cell::Cell::get) {
            return overridden;
        }
        if let Some(overridden) =
            consumer_test_override::CONSUMER_OVERRIDE.with(std::cell::Cell::get)
        {
            return overridden;
        }
        SWITCHES.get().copied().unwrap_or_default()
    }

    /// Consumer-crate test seam (B56; same shape as
    /// `ay_core::misc_test_override`): `cfg(test)` seams cannot serve a
    /// consumer crate's own tests, so this doc-hidden thread-local override
    /// is always compiled. Production code must never touch it.
    #[doc(hidden)]
    pub mod consumer_test_override {
        use super::PbAbSwitches;

        thread_local! {
            pub(super) static CONSUMER_OVERRIDE: std::cell::Cell<Option<PbAbSwitches>> =
                const { std::cell::Cell::new(None) };
        }

        /// RAII guard restoring the previous override on drop.
        pub struct Guard(Option<PbAbSwitches>);

        impl Drop for Guard {
            fn drop(&mut self) {
                let prev = self.0;
                CONSUMER_OVERRIDE.with(|c| c.set(prev));
            }
        }

        /// Install a thread-scoped override for the current test.
        #[must_use]
        pub fn set(switches: PbAbSwitches) -> Guard {
            let prev = CONSUMER_OVERRIDE.with(|c| c.replace(Some(switches)));
            Guard(prev)
        }

        /// Whether an override is active on this thread. Frontends use it to
        /// skip the set-once global install (the override IS the resolution).
        #[must_use]
        pub fn active() -> bool {
            CONSUMER_OVERRIDE.with(std::cell::Cell::get).is_some()
        }
    }

    #[cfg(test)]
    thread_local! {
        /// In-process per-test override. The set-once global cannot be
        /// flipped inside one test binary; A/B tests scope an override
        /// through [`TestOverride`] instead (the seam the retired
        /// `ScopedEnvVar` steering used to provide).
        static TEST_OVERRIDE: std::cell::Cell<Option<PbAbSwitches>> =
            const { std::cell::Cell::new(None) };
    }

    /// RAII scope for a test's switch override; restores the previous value
    /// (usually `None`) on drop.
    #[cfg(test)]
    pub(crate) struct TestOverride(Option<PbAbSwitches>);

    #[cfg(test)]
    impl TestOverride {
        pub(crate) fn set(switches: PbAbSwitches) -> Self {
            let prev = TEST_OVERRIDE.with(|c| c.replace(Some(switches)));
            TestOverride(prev)
        }
    }

    #[cfg(test)]
    impl Drop for TestOverride {
        fn drop(&mut self) {
            let prev = self.0;
            TEST_OVERRIDE.with(|c| c.set(prev));
        }
    }
}

pub mod cdcl;
pub mod clique_witness;
mod cp_dense;
mod cutting_planes;
#[cfg(feature = "dev-tools")]
#[doc(hidden)]
pub mod dev_tools;
mod encoding;
mod eq_knapsack;
mod eval;
pub mod jit_candidate;
pub mod linearize;
mod multi_row_bdd;
mod objective_bound;
pub mod optimize;
mod output;
mod parser;
pub mod portfolio;
pub mod preprocess;
mod projected_pattern;
pub mod proof;
pub mod propagation;
mod signal;
mod single_row_dp;
mod solver;
pub mod symmetry;
mod types;
pub mod verify;
#[cfg(any(feature = "certified-proof-artifacts", feature = "dev-tools"))]
#[doc(hidden)]
pub mod veripb_runner;

pub use cdcl::{PbCdclResult, PbCdclSolver, PbCdclStats};
pub use clique_witness::{clique_arm_matches, try_clique_witness};
pub use cutting_planes::{CpConstraint, CpError, RoundToOneResult};
pub use encoding::{
    CnfEncoder, EncodedCnf, EncodingProfile, EncodingStrategy, EncodingStrategyCounts,
};
pub use eval::{verify_all_constraints, wbo_admissible_cost};
pub use jit_candidate::{
    extract_first_jit_candidate, extract_first_jit_candidate_with_policy,
    profile_jit_candidate_telemetry, profile_jit_candidate_telemetry_with_policy,
    profile_jit_kernel_shapes, PbJitBackend, PbJitCandidate, PbJitCandidateTelemetry,
    PbJitExtraction, PbJitExtractionPolicy, PbJitProfile, PbJitRejection, PbKernelKind,
    PbKernelShapeProfile, PboObjectiveBoundProfile,
};
pub use linearize::{is_linear, linearize};
pub use multi_row_bdd::{
    decode_multi_row_bdd_infeasibility_certificate_json,
    decode_multi_row_bdd_infeasibility_certificate_json_with_limits,
    encode_multi_row_bdd_infeasibility_certificate_json,
    encode_multi_row_bdd_infeasibility_certificate_json_with_limits,
    generate_multi_row_bdd_infeasibility_certificate_interruptible,
    generate_multi_row_bdd_infeasibility_certificate_with_limits,
    verify_multi_row_bdd_infeasibility_certificate_interruptible,
    verify_multi_row_bdd_infeasibility_certificate_with_limits, MultiRowBddCertificateCodecError,
    MultiRowBddDecline, MultiRowBddInfeasibilityCertificate, MultiRowBddInfeasibilityProof,
    MultiRowBddLayer, MultiRowBddLimits, MultiRowBddNode,
    MULTI_ROW_BDD_INFEASIBILITY_CERTIFICATE_FORMAT,
};
pub use optimize::gf2_parity::{
    debug_recovered_equalities, gf2_parity_detects_unsat, gf2_parity_detects_unsat_with_recovery,
    gf2_parity_unsat_cp_checked,
};
pub use optimize::matching_cardinality::matching_cardinality_unsat_cp_checked;
pub use optimize::pigeonhole::pigeonhole_unsat_cp_checked;
pub use optimize::wbo::{
    try_certified_wbo_projection, try_wbo_to_pbo, wbo_to_pbo, CertifiedWboProjection,
    WboHardConstraintMapping, WboObjectiveTermMapping, WboProjectionUnsupported,
    WboProjectionUnsupportedReason, WboRelaxationVarMapping, WboRelaxedConstraintDirection,
    WboSoftConstraintMapping, WboToPboError,
};
pub use optimize::wcsp_probe::{wcsp_edac_enabled, wcsp_root_edac_probe, WcspEdacProbe};
pub use optimize::{
    write_max_clique_conflict_row_import_map_csv, OptResult, OptStrategy, OptimizationEngine,
};
pub use output::{PbExactSolution, PbOutputWriter, PbSolution, PbStatus};
pub use parser::{
    instance_to_opb, parse_opb, parse_opb_interruptible, parse_wbo, parse_wbo_interruptible,
    ParseError,
};
pub use preprocess::{preprocess, PreprocessResult};
pub use projected_pattern::{
    enumerate_projected_patterns_interruptible, enumerate_projected_patterns_with_limits,
    solve_projected_pattern_count_interruptible, solve_projected_pattern_count_with_limits,
    verify_projected_pattern_count_solution_interruptible,
    verify_projected_pattern_count_solution_with_limits,
    verify_projected_pattern_frontier_interruptible, verify_projected_pattern_frontier_with_limits,
    ProjectedPattern, ProjectedPatternCountLimits, ProjectedPatternCountSolution,
    ProjectedPatternDecline, ProjectedPatternFrontier, ProjectedPatternLimits,
    ProjectedPatternResource,
};
pub use proof::{
    emit_koops_identity_complement_red_capacity_proof,
    emit_koops_mat12_11_identity_complement_red_capacity_proof, format_constraint,
    format_cp_constraint, format_lit, veripb_input_constraint_count, ConstraintId,
    KoopsIdentityComplementRedCapacityParams, ProofError, ProofStep, VeriPbWriter,
};
pub use propagation::{Lit, LitValue, PbNativeHelperStats, PbPropagator, PropResult};
pub use signal::install_sigterm_flag;
pub use single_row_dp::{
    decode_single_row_dp_infeasibility_certificate_json,
    decode_single_row_dp_infeasibility_certificate_json_with_limits,
    encode_single_row_dp_infeasibility_certificate_json,
    encode_single_row_dp_infeasibility_certificate_json_with_limits,
    generate_single_row_dp_infeasibility_certificate_interruptible,
    generate_single_row_dp_infeasibility_certificate_with_limits,
    solve_single_row_binary_interruptible, solve_single_row_binary_with_limits,
    verify_single_row_dp_infeasibility_certificate_interruptible,
    verify_single_row_dp_infeasibility_certificate_with_limits, SingleRowDpCanonicalItem,
    SingleRowDpCanonicalProblem, SingleRowDpCertificateCodecError, SingleRowDpDecline,
    SingleRowDpIndependentValue, SingleRowDpInfeasibilityCertificate,
    SingleRowDpInfeasibilityProof, SingleRowDpLimits, SingleRowDpOutcome,
    SingleRowDpReachabilityCheckpoint, SINGLE_ROW_DP_INFEASIBILITY_CERTIFICATE_FORMAT,
};
pub use solver::{
    eval_constraint, eval_objective, eval_objective_exact, objective_range_fits_i64,
    ObjectiveEvalError,
};
pub use symmetry::{
    break_symmetries, break_symmetries_with_deadline,
    break_verified_block_symmetries_with_deadline,
    break_verified_candidate_symmetries_with_deadline, detect_interchangeable_groups,
    detect_verified_block_partition_with_deadline, is_highly_symmetric_candidate,
    verify_ordered_block_partition_with_deadline, SymmetryBreakResult, VerifiedBlockPartition,
    VerifiedBlockPartitionDecline, VerifiedBlockTransposition,
};
pub use types::{
    classify_instance, is_cardinality, InstanceClass, PbConstraint, PbInstance, PbLit, PbObjective,
    PbRel, PbTerm, WboInstance,
};
pub use verify::{
    parse_solver_output, verify, OptimalityCheck, SolverOutput, VerifyReport, Z3Mode,
};
