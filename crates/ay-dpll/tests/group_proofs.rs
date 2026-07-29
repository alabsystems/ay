// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated proofs integration tests for ay-dpll.
//! Groups 12 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

#[path = "group_proofs/carcara_external_check.rs"]
mod carcara_external_check;
#[path = "group_proofs/class4_generic_trust_shapes.rs"]
mod class4_generic_trust_shapes;
#[path = "group_proofs/combined_direct_proof_quality_6756.rs"]
mod combined_direct_proof_quality_6756;
#[path = "group_proofs/combined_incremental_proofs_6755.rs"]
mod combined_incremental_proofs_6755;
#[path = "group_proofs/combined_proof_provenance_6759.rs"]
mod combined_proof_provenance_6759;
#[path = "group_proofs/complementary_literal_rebuild.rs"]
mod complementary_literal_rebuild;
#[path = "group_proofs/congruence_collapse_rebuild.rs"]
mod congruence_collapse_rebuild;
#[path = "group_proofs/incremental_clausification_proofs.rs"]
mod incremental_clausification_proofs;
#[path = "group_proofs/incremental_proof_quality_8154.rs"]
mod incremental_proof_quality_8154;
#[path = "group_proofs/linear_and_collapse_rebuild.rs"]
mod linear_and_collapse_rebuild;
#[path = "group_proofs/multi_equality_farkas_rebuild.rs"]
mod multi_equality_farkas_rebuild;
#[path = "group_proofs/proof_boundary_unsat_9037.rs"]
mod proof_boundary_unsat_9037;
#[path = "group_proofs/proof_ring_repro.rs"]
mod proof_ring_repro;
#[path = "group_proofs/proof_split_loop_unsat_6725.rs"]
mod proof_split_loop_unsat_6725;
#[path = "group_proofs/proof_tracking_contradictory_assumptions.rs"]
mod proof_tracking_contradictory_assumptions;
#[path = "group_proofs/proof_tracking_e2e.rs"]
mod proof_tracking_e2e;
#[path = "group_proofs/proof_tracking_incremental_6716.rs"]
mod proof_tracking_incremental_6716;
#[path = "group_proofs/proof_tracking_lia_assumptions_6725.rs"]
mod proof_tracking_lia_assumptions_6725;
