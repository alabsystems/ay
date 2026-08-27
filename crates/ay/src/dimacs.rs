// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! DIMACS CNF solve and authenticated-publication pipeline.
//!
//! The pipeline detects file/stream inputs, selects specialized dense and XOR
//! routes, configures the solver, settles proof and artifact authority, emits
//! ordered statistics and verdicts, and handles bounded finalize rescue. Its
//! private textual fragments preserve the established item paths while keeping
//! each phase small enough to audit independently.

use super::{
    global_elapsed, is_timed_out, sat_competition_wrapper_timeout_policy, stats_output,
    timeout_exit_code_for_sat_competition_wrapper, ProofConfig, ProofFormat, INTERRUPT_HANDLE,
    TIMED_OUT, VERDICT_PRINTED,
};
use crate::proof_artifact::{
    write_sealed_proof_artifact, ProofArtifactProblem, ProofArtifactTheoryMetadata,
};
use sha2::{Digest as _, Sha256};
use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{self, BufWriter, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc, Mutex, OnceLock,
};

#[cfg(test)]
const DIMACS_TIMEOUT_EXIT_CODE: i32 = 124;
const DIMACS_MODEL_LINE_LIMIT: usize = 4096;
const PROOF_OUTPUT_BUFFER_CAPACITY: usize = 1024 * 1024;
const DIMACS_MODEL_OUTPUT_BUFFER_CAPACITY: usize = 1024 * 1024;
include!("dimacs/bodies/authorize_dimacs_unsat_artifacts.rs");
include!("dimacs/bodies/configure_dimacs_solver.rs");
include!("dimacs/bodies/dimacs_run_stats_json.rs");
include!("dimacs/bodies/insert_decompose_lrat_preflight_telemetry.rs");
include!("dimacs/bodies/insert_empty_multiplier_equiv_conservation_scout_stats.rs");
include!("dimacs/bodies/insert_multiplier_equiv_conservation_scout_stats.rs");
include!("dimacs/bodies/maybe_run_dense_clique_php_proof_route.rs");
include!("dimacs/bodies/remove_authenticated_visible_file.rs");
include!("dimacs/bodies/reserve_dimacs_proof_status.rs");
include!("dimacs/bodies/run_dimacs_cube_and_conquer.rs");
include!("dimacs/bodies/run_dimacs_from_content_impl.rs");
include!("dimacs/bodies/run_dimacs_parallel.rs");
include!("dimacs/bodies/run_finalize_rescue.rs");
include!("dimacs/bodies/run_proof_streaming_reader.rs");
include!("dimacs/bodies/run_streaming.rs");
include!("dimacs/bodies/seal_owned_dimacs_proof.rs");
include!("dimacs/bodies/verify_lean_proof.rs");
include!("dimacs/proof_writer.rs");
include!("dimacs/proof_registry.rs");
include!("dimacs/proof_file_creation.rs");
include!("dimacs/proof_publication.rs");
include!("dimacs/proof_sealing.rs");
include!("dimacs/lean_snapshot.rs");
include!("dimacs/input_detection.rs");
include!("dimacs/proof_status.rs");
// Textual inclusion keeps the established DIMACS policy item paths private.
include!("dimacs/variant_policy.rs");
include!("dimacs/variant_routing.rs");
include!("dimacs/run_stats_json.rs");
include!("dimacs/scout_stats.rs");
include!("dimacs/dense_assets.rs");
include!("dimacs/dense_admission.rs");
include!("dimacs/dense_route.rs");
include!("dimacs/dense_rejection.rs");
include!("dimacs/stats_output.rs");
include!("dimacs/proof_authority.rs");
include!("dimacs/input_runs.rs");
include!("dimacs/content_run.rs");
include!("dimacs/sidecars.rs");
include!("dimacs/parallel.rs");
include!("dimacs/solver_runners.rs");
include!("dimacs/proof_verification.rs");
include!("dimacs/configure_support.rs");
include!("dimacs/configuration.rs");
include!("dimacs/finish_entry.rs");
include!("dimacs/finish/human_core.rs");
include!("dimacs/finish/human_preprocessing.rs");
include!("dimacs/finish/human_tail.rs");
include!("dimacs/finish/structured_core.rs");
include!("dimacs/finish/structured_bcp_core.rs");
include!("dimacs/finish/structured_bcp_buckets.rs");
include!("dimacs/finish/structured_identity.rs");
include!("dimacs/finish/structured_identity_rows.rs");
include!("dimacs/finish/structured_search.rs");
include!("dimacs/finish/structured_techniques.rs");
include!("dimacs/finish/structured_runtime.rs");
include!("dimacs/finish/structured_backbone.rs");
include!("dimacs/finish/statistics.rs");
include!("dimacs/finish_pipeline.rs");
include!("dimacs/finalize_rescue.rs");
include!("dimacs/streaming_proof.rs");
include!("dimacs/streaming_solver.rs");

#[cfg(test)]
mod tests;
