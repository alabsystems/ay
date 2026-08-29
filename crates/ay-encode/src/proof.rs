// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! The proof-certificate hook.
//!
//! AY produces re-checkable evidence at two levels, and this module is the one
//! place both frontends reach for it:
//!
//! 1. **CHC proof transcript** — [`ProofRun`] binds an
//!    [`ay_chc::ChcPdrProofRun`] (from [`ay_chc::engines::solve_pdr_proof`]) to
//!    the exact [`ay_chc::ChcProblem`] supplied to that solve. Parameterless
//!    [`ProofRun::certificate`] extraction produces consumer evidence and proof
//!    artifacts for that bound problem (model plus replay transcript,
//!    sha256-addressed). model-checker-consumer's
//!    `pdr_proof_run_verdict` and the model-checker consumer's `AYChcProofReplayEvidence` boundary both
//!    consume this.
//! 2. **SAT-level Alethe** (feature `alethe`) — `ay_proof::export_alethe` turns
//!    a low-level [`ay_proof::Proof`] into an Alethe document for carcara /
//!    SMTCoq re-checking. Off by default to keep the leaf crate minimal.
//!
//! BMC runs produce no certificate (both frontends discard the UNSAT payload),
//! so [`Certificate`] is only ever populated on the proof/PDR path.

use ay_chc::{
    ChcPdrProofRun, ChcProofRunArtifacts, ChcProofTranscriptConsumerEvidence,
    ChcProofTranscriptMetadata, VerifiedChcResult,
};

/// A completed PDR proof run bound to the exact problem that was solved.
///
/// Thin wrapper around AY's [`ChcPdrProofRun`] so [`crate::invoke`] can hand a
/// proof run to this module without the caller depending on `ay-chc` directly.
/// The underlying run retains its solved [`ay_chc::ChcProblem`] privately, so
/// a caller cannot mint a certificate whose artifacts describe another problem.
#[derive(Debug)]
pub struct ProofRun {
    run: ChcPdrProofRun,
}

impl ProofRun {
    /// Wrap an AY proof run that already owns its solved problem.
    #[must_use]
    pub(crate) fn new(run: ChcPdrProofRun) -> Self {
        Self { run }
    }

    /// Whether AY independently accepted this run as a proof.
    #[must_use]
    pub fn accepted_as_proof(&self) -> bool {
        self.run.accepted_as_proof()
    }

    /// The sealed semantic result returned by AY.
    pub fn result(&self) -> &VerifiedChcResult {
        self.run.result()
    }

    /// Build a re-checkable [`Certificate`] for this run's solved problem.
    ///
    /// Pulls the consumer evidence + artifact bundle + proof-run metadata
    /// (normalized-input hash, proof status, result) out of the AY proof run.
    /// The problem is captured when the run is created, so evidence extraction
    /// cannot accidentally use a different [`ay_chc::ChcProblem`].
    #[must_use]
    pub fn certificate(&self) -> Certificate {
        Certificate {
            consumer_evidence: self.run.consumer_evidence(),
            artifacts: self.run.proof_run_artifacts(),
            metadata: self.run.metadata().clone(),
        }
    }
}

/// A re-checkable certificate captured from an AY run.
///
/// This is the shared evidence object both frontends digest. It carries AY's
/// CHC proof transcript (model + replay transcript, content-addressed); the
/// optional SAT-level Alethe export is produced on demand via
/// [`Certificate::to_alethe`] when the `alethe` feature is on.
#[derive(Debug, Clone)]
pub struct Certificate {
    /// The typed consumer-evidence boundary (what the model-checker consumer's `AYChcProofReplayEvidence`
    /// and model-checker-consumer's `ChcPdrProofEvidence` wrap).
    consumer_evidence: ChcProofTranscriptConsumerEvidence,
    /// The content-addressed artifact bundle (model + replay transcript).
    ///
    /// Each artifact ([`ChcProofRunArtifacts::model`],
    /// [`ChcProofRunArtifacts::replay_transcript`]) exposes read-only `schema`,
    /// `role`, `digest`, and `bytes` accessors (G5), so model-checker-consumer can build its
    /// per-artifact descriptors + `ChcPdrProofEvidence::proof_grade_from_bytes`
    /// without reaching into `ay-chc`.
    artifacts: ChcProofRunArtifacts,
    /// The proof-run transcript metadata (G6).
    ///
    /// Carries the manifest-binding fields model-checker-consumer's `pdr_proof_run_verdict`
    /// reads through immutable accessors: `normalized_input_sha256`,
    /// `proof_status`, `result`, `accepted_as_proof`, plus `to_json_value()` for
    /// the evidence payload. See
    /// the [`Certificate::metadata_json`], [`Certificate::normalized_input_sha256`],
    /// [`Certificate::proof_status`], and [`Certificate::result`] accessors.
    metadata: ChcProofTranscriptMetadata,
}

impl Certificate {
    /// Whether both evidence views agree this is proof-grade evidence.
    ///
    /// This is derived fail-closed from the immutable consumer evidence and
    /// transcript metadata instead of storing a third independently mutable
    /// acceptance bit.
    #[must_use]
    pub fn accepted_as_proof(&self) -> bool {
        self.consumer_evidence.accepted_for_consumer() && self.metadata.accepted_as_proof()
    }

    /// The typed consumer-evidence boundary for this proof run.
    #[must_use]
    pub fn consumer_evidence(&self) -> &ChcProofTranscriptConsumerEvidence {
        &self.consumer_evidence
    }

    /// The content-addressed model and replay-transcript artifacts.
    #[must_use]
    pub fn artifacts(&self) -> &ChcProofRunArtifacts {
        &self.artifacts
    }

    /// The proof-run transcript metadata.
    #[must_use]
    pub fn metadata(&self) -> &ChcProofTranscriptMetadata {
        &self.metadata
    }

    /// The proof-run metadata rendered as stable JSON (G6).
    ///
    /// This is exactly `run.metadata().to_json_value()`, the value model-checker-consumer
    /// embeds in its `model_checker_consumer.chc-pdr-*` evidence payloads.
    #[must_use]
    pub fn metadata_json(&self) -> serde_json::Value {
        self.metadata.to_json_value()
    }

    /// SHA-256 of the normalized CHC input this proof run was produced for (G6).
    ///
    /// model-checker-consumer cross-checks this against its content-addressed obligation hash.
    #[must_use]
    pub fn normalized_input_sha256(&self) -> &str {
        self.metadata.normalized_input_sha256()
    }

    /// The stable proof-status classification string (G6).
    #[must_use]
    pub fn proof_status(&self) -> &str {
        self.metadata.proof_status()
    }

    /// The semantic CHC result string (`safe` / `unsafe` / `unknown`) (G6).
    #[must_use]
    pub fn result(&self) -> &str {
        self.metadata.result()
    }

    /// Export a SAT-level Alethe proof document for external re-checking
    /// (carcara / SMTCoq), if a low-level [`ay_proof::Proof`] is available.
    ///
    /// Only present under the `alethe` feature. CHC proof transcripts are the
    /// primary evidence; this is the optional secondary SAT-level cert.
    ///
    /// BLOCKED on a missing `ay-chc` → SAT-proof bridge. The Alethe printer
    /// [`ay_proof::try_export_alethe`] needs a low-level `(&ay_proof::Proof,
    /// &ay_core::TermStore)` pair, but a CHC PDR proof run does not surface
    /// either: a [`Certificate`] holds only the CHC transcript evidence
    /// ([`ChcProofTranscriptConsumerEvidence`]) and the content-addressed
    /// artifact bundle ([`ChcProofRunArtifacts`] = JSON model + replay-transcript
    /// byte envelopes, see `ay-chc/src/proof_metadata.rs`). `ay-chc` does not
    /// even depend on `ay-proof`, so there is no SAT-level `Proof` to hand the
    /// printer. Producing real Alethe therefore requires a *new* `ay-chc` entry
    /// point that exposes the PDR run's underlying SAT proof + term store
    /// (proposed: `ChcPdrProofRun::sat_proof(&self) -> Option<(&ay_proof::Proof,
    /// &ay_core::TermStore)>`). Until that lands this cannot be honestly
    /// implemented — emitting anything else would be a fake certificate.
    #[cfg(feature = "alethe")]
    pub fn to_alethe(&self) -> crate::Result<String> {
        // Once `ay-chc` exposes the SAT-level proof for a PDR run this becomes:
        //   let (proof, terms) = self.<run>.sat_proof().ok_or(..)?;
        //   ay_proof::try_export_alethe(proof, terms)
        //       .map_err(|_| crate::EncodeError::Unimplemented("alethe export"))
        Err(crate::EncodeError::Unimplemented(
            "Alethe export requires an ay-chc SAT-proof/term-store bridge",
        ))
    }
}
