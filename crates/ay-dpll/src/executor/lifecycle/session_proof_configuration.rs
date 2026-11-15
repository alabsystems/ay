// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Session proof configuration that one query may borrow and must hand back.
//!
//! Proof demand, the best-effort reconstruction budget and parsed-assertion
//! retention are configured by the host and by explicit proof demands, and
//! retention selects the certification funnel's lanes. Code that changes them
//! for part of ONE query (the quantified trace retry, the non-string sequence
//! corroboration) captures this first and restores it afterwards. Before it
//! did, the borrowed values survived into the next query, which then certified
//! through different lanes than the same query in a fresh process.

use super::Executor;

/// Everything a query may borrow from the session's proof configuration.
///
/// The recorder is deliberately absent: `begin_public_solve` derives it from
/// this configuration for every public decision.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) struct SessionProofConfiguration {
    proof_output_requested: bool,
    proof_artifact_required: bool,
    reconstruction_step_budget: Option<u64>,
    retention: ay_frontend::ParsedRetention,
}

impl Executor {
    /// Capture the session proof configuration before borrowing from it.
    pub(in crate::executor) fn session_proof_configuration(&self) -> SessionProofConfiguration {
        SessionProofConfiguration {
            proof_output_requested: self.proof_output_requested,
            proof_artifact_required: self.proof_artifact_required,
            reconstruction_step_budget: self.proof_reconstruction_step_budget,
            retention: self.ctx.parsed_retention(),
        }
    }

    /// Hand back a configuration captured by [`Self::session_proof_configuration`].
    pub(in crate::executor) fn restore_session_proof_configuration(
        &mut self,
        configuration: SessionProofConfiguration,
    ) {
        let SessionProofConfiguration {
            proof_output_requested,
            proof_artifact_required,
            reconstruction_step_budget,
            retention,
        } = configuration;
        self.proof_output_requested = proof_output_requested;
        self.proof_artifact_required = proof_artifact_required;
        self.proof_reconstruction_step_budget = reconstruction_step_budget;
        self.ctx.restore_parsed_retention(retention);
    }
}
