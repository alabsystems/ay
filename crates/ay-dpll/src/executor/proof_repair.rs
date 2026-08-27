// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic-certificate and trusted-proof repair modules.
//!
//! These implementation modules form one proof-repair subsystem. Keeping the
//! registry here prevents their private topology from inflating the executor's
//! orchestration surface while preserving the existing executor-local paths.

#[cfg(test)]
use super::theories;
use super::{
    proof_euf_lemma, proof_resolution, proof_surface_syntax, Executor,
    NATIVE_API_ASSERTION_PLACEHOLDER,
};

#[path = "proof_farkas.rs"]
pub(super) mod proof_farkas;
#[path = "proof_farkas_synthesis.rs"]
pub(super) mod proof_farkas_synthesis;
#[cfg(test)]
#[path = "proof_farkas_tests.rs"]
mod proof_farkas_tests;
#[path = "proof_farkas_validation.rs"]
pub(super) mod proof_farkas_validation;

#[path = "proof_trust_surgery.rs"]
pub(super) mod proof_trust_surgery;
#[cfg(test)]
#[path = "proof_trust_surgery_guarded_then_tests.rs"]
mod proof_trust_surgery_guarded_then_tests;
#[path = "proof_trust_surgery_ite.rs"]
pub(super) mod proof_trust_surgery_ite;
#[path = "proof_trust_surgery_ite_branch.rs"]
mod proof_trust_surgery_ite_branch;
#[path = "proof_trust_surgery_ite_emit.rs"]
mod proof_trust_surgery_ite_emit;
#[path = "proof_trust_surgery_ite_plan.rs"]
mod proof_trust_surgery_ite_plan;
#[path = "proof_trust_surgery_ite_substituted_bound.rs"]
mod proof_trust_surgery_ite_substituted_bound;
#[cfg(test)]
#[path = "proof_trust_surgery_ite_tests.rs"]
mod proof_trust_surgery_ite_tests;
#[path = "proof_trust_surgery_provenance.rs"]
pub(super) mod proof_trust_surgery_provenance;
#[path = "proof_trust_surgery_provenance_or.rs"]
pub(super) mod proof_trust_surgery_provenance_or;
#[path = "proof_trust_surgery_provenance_or_emit.rs"]
mod proof_trust_surgery_provenance_or_emit;
#[cfg(test)]
#[path = "proof_trust_surgery_provenance_or_false_tests.rs"]
mod proof_trust_surgery_provenance_or_false_tests;
#[cfg(test)]
#[path = "proof_trust_surgery_provenance_or_tests.rs"]
mod proof_trust_surgery_provenance_or_tests;
#[path = "proof_trust_surgery_provenance_or_transfer.rs"]
pub(super) mod proof_trust_surgery_provenance_or_transfer;
#[path = "proof_trust_surgery_surface_audit.rs"]
pub(super) mod proof_trust_surgery_surface_audit;
