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
