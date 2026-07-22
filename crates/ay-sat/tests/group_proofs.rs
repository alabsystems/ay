// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]
#![allow(clippy::panic)]

//! Proof infrastructure test group for ay-sat.
//!
//! Consolidates proof-related tests (forward checker, proof coverage,
//! proof trace, checker e2e) into a single test binary.

mod common;

#[path = "group_proofs/clearlevel0_proof_id_guard.rs"]
mod clearlevel0_proof_id_guard;
#[path = "group_proofs/extension_addclauses_8480.rs"]
mod extension_addclauses_8480;
#[path = "group_proofs/extension_proof_trace.rs"]
mod extension_proof_trace;
#[path = "group_proofs/forward_checker_conflict_analysis.rs"]
mod forward_checker_conflict_analysis;
#[path = "group_proofs/forward_checker_overhead.rs"]
mod forward_checker_overhead;
#[path = "group_proofs/lean4_kernel_e2e.rs"]
mod lean4_kernel_e2e;
#[path = "group_proofs/performance_proofs.rs"]
mod performance_proofs;
#[path = "group_proofs/proof_coverage_p258.rs"]
mod proof_coverage_p258;
#[path = "group_proofs/proofaddkind_reconciliation_guard.rs"]
mod proofaddkind_reconciliation_guard;
#[path = "group_proofs/standalone_checker_e2e.rs"]
mod standalone_checker_e2e;
#[path = "group_proofs/theory_lemma_lrat_guard.rs"]
mod theory_lemma_lrat_guard;
