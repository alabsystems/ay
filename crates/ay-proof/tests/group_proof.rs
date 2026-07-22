// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated ay-proof integration tests.
//!
//! Covers proof checker error paths, Farkas strict mode, gap detection,
//! theory lemma handling, Alethe export, and quality reexports.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead (#8604).

#[allow(dead_code)]
#[path = "group_proof/common/mod.rs"]
mod common;

#[path = "group_proof/checker_error_paths.rs"]
mod checker_error_paths;
#[path = "group_proof/checker_farkas_strict.rs"]
mod checker_farkas_strict;
#[path = "group_proof/checker_gap_strict_mode.rs"]
mod checker_gap_strict_mode;
#[path = "group_proof/checker_gap_theory_lemma.rs"]
mod checker_gap_theory_lemma;
#[path = "group_proof/checker_gap_trust_fallback_from_missing_hints.rs"]
mod checker_gap_trust_fallback_from_missing_hints;
#[path = "group_proof/checker_gap_warn_only.rs"]
mod checker_gap_warn_only;
#[path = "group_proof/checker_partial_stats.rs"]
mod checker_partial_stats;
#[path = "group_proof/export_alethe_edge_cases.rs"]
mod export_alethe_edge_cases;
#[path = "group_proof/export_alethe_validation.rs"]
mod export_alethe_validation;
#[path = "group_proof/quality_reexports.rs"]
mod quality_reexports;
