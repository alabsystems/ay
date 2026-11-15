// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The evidence gate of the QSAT route's `unsat`.
//!
//! Every QSAT refutation is admitted first by AY's own strict checker over
//! the authored roots. That is not evidence anyone else can check: measured on
//! the branch that introduced the route, 41 of 66 published repro `unsat`s
//! shipped no Alethe document at all (the expansion chain's nested-binder
//! instances, the negated-existential dual, a normalized `and_pos` conjunct)
//! and 19 shipped one pinned carcara rejects at its first `assume` (the
//! replay assumed AY's canonical `(or p q)` for an authored
//! `(not (and (not p) (not q)))`).
//!
//! So in the default posture the route publishes `unsat` only together with
//! the document a consumer will receive: rendered through the same
//! problem-scoped exporter the certificate file and `(get-proof)` use, with no
//! `hole`/`trust` step, and with every premise `assume` an assertion of the
//! input as written. Anything else hands the query back to the legacy path
//! with the route's proof state restored, exactly as for a problem outside
//! its fragment — the route never answers `unsat` without a document.
//!
//! The shed posture (`--z3-mode`, `--no-proof`, `--rigor fast`) produces no
//! document by request and keeps the internal strict admission, unless the
//! caller nevertheless DEMANDED a checked certificate (`--proof FILE`,
//! `--strict-proofs`, `:produce-proofs`, self-check): then the document must
//! render, and under strict rigor carry no unproved step and no foreign
//! premise. QSAT pre-empts the legacy lanes, which often certify the same
//! query cleanly, so a QSAT proof short of the demand is not published:
//! measured on the route's first version, `--strict-proofs` lost four verdicts
//! the legacy path certifies, and `--proof FILE` exited 1 on four.
//!
//! Nothing here grants authority; it only declines.

use ay_core::kani_compat::DetHashMap;
use ay_core::{Proof, TermId};
use ay_proof::{AletheDocumentScan, PartialProofCheck, ProofQuality};

use super::super::Executor;
use super::unsat::Published;
use crate::executor::ProofDeclineMechanism;
use crate::executor_types::UnknownReason;
use crate::normalize_premise_surface;

/// The proof-publication state a QSAT publication attempt may change,
/// restored on a decline so the legacy path starts from exactly what it would
/// have seen had the route not run: the installed proof, its check results,
/// presentation table and decline mechanism, the replay's attempt ledger,
/// and the unknown reason. The qlra lane's nested `unsat` restores it the
/// same way when its certificate falls short of a demanded one, and the
/// implied-universal lane when its document is not the input's own.
pub(in crate::executor) struct ProofStateSnapshot {
    proof: Option<Proof>,
    overrides: Option<DetHashMap<TermId, String>>,
    suppressed: bool,
    quality: Option<ProofQuality>,
    check_result: Option<PartialProofCheck>,
    check_ok: bool,
    decline: Option<ProofDeclineMechanism>,
    replay_ledger: ReplayLedgerSnapshot,
    unknown_reason: Option<UnknownReason>,
}

enum ReplayLedgerSnapshot {
    Saved {
        attempts: u8,
        direct: Option<(u64, u8)>,
    },
    Live,
}

impl ProofStateSnapshot {
    /// Park installed artifacts without cloning an arbitrarily large proof.
    /// The temporary solve owns its own tracker and publication artifacts.
    pub(in crate::executor) fn take_owned(executor: &mut Executor) -> Self {
        Self {
            proof: executor.last_proof.take(),
            overrides: executor.last_proof_term_overrides.take(),
            suppressed: std::mem::replace(
                &mut executor.last_unsat_proof_reconstruction_suppressed,
                false,
            ),
            quality: executor.last_proof_quality.take(),
            check_result: executor.proof_check_result.take(),
            check_ok: std::mem::replace(&mut executor.proof_check_ok, false),
            decline: executor.last_proof_decline.take(),
            // This is still the same query: consumed attempts and the shared
            // wall/source/search envelopes must not be replenished on rollback.
            replay_ledger: ReplayLedgerSnapshot::Live,
            unknown_reason: executor.last_unknown_reason,
        }
    }

    pub(in crate::executor) fn take(executor: &Executor) -> Self {
        Self {
            proof: executor.last_proof.clone(),
            overrides: executor.last_proof_term_overrides.clone(),
            suppressed: executor.last_unsat_proof_reconstruction_suppressed,
            quality: executor.last_proof_quality.clone(),
            check_result: executor.proof_check_result.clone(),
            check_ok: executor.proof_check_ok,
            decline: executor.last_proof_decline,
            replay_ledger: ReplayLedgerSnapshot::Saved {
                attempts: executor.consequence_replay_attempts.get(),
                direct: executor.consequence_replay_direct_state.get(),
            },
            unknown_reason: executor.last_unknown_reason,
        }
    }

    pub(in crate::executor) fn restore(self, executor: &mut Executor) {
        executor.last_proof = self.proof;
        executor.last_proof_term_overrides = self.overrides;
        executor.last_unsat_proof_reconstruction_suppressed = self.suppressed;
        executor.last_proof_quality = self.quality;
        executor.proof_check_result = self.check_result;
        executor.proof_check_ok = self.check_ok;
        executor.last_proof_decline = self.decline;
        if let ReplayLedgerSnapshot::Saved { attempts, direct } = self.replay_ledger {
            executor.consequence_replay_attempts.set(attempts);
            executor.consequence_replay_direct_state.set(direct);
        }
        executor.last_unknown_reason = self.unknown_reason;
    }
}

impl Executor {
    /// Admit a published QSAT `unsat` only with the evidence its posture owes
    /// (module docs); otherwise restore `snapshot` and decline, keeping the
    /// pass's terms when a proof was installed.
    pub(super) fn qsat_unsat_evidence_gate(
        &mut self,
        published: Published,
        route: &'static str,
        snapshot: ProofStateSnapshot,
    ) -> Published {
        if published.0.is_none() {
            return published;
        }
        let refusal = if self.competition_shedding_active() {
            if !self.checked_certificate_demanded() {
                self.qsat_note("qsat.evidence", "shed-posture");
                return published;
            }
            self.qsat_demanded_certificate_refusal()
        } else {
            self.qsat_unsat_document_refusal()
                .or_else(|| self.qsat_strict_demand_internal_refusal())
        };
        match refusal {
            None => {
                self.qsat_note("qsat.evidence", "document");
                published
            }
            Some(reason) => {
                tracing::debug!(target: "ay::qsat", route, reason, "unsat without evidence");
                if tracing::enabled!(target: "ay::qsat", tracing::Level::TRACE) {
                    let mut document = Vec::new();
                    let rendered = self.try_export_installed_proof_alethe_to(&mut document);
                    tracing::trace!(
                        target: "ay::qsat",
                        ok = ?rendered.as_ref().map(Result::is_ok),
                        document = %String::from_utf8_lossy(&document),
                        "refused document"
                    );
                }
                snapshot.restore(self);
                // The route published nothing: the lanes it subsumes (the
                // nested-CEGQI search, the deep-QE retry) answer as they do
                // for a problem outside its fragment, under their own
                // publication rules (`try_qsat_route` records the route as
                // unpublished).
                self.qsat_note("qsat.publish", "unsat-unevidenced");
                self.qsat_note("qsat.unevidenced_route", route);
                self.qsat_note("qsat.evidence", reason);
                (None, published.1)
            }
        }
    }

    /// Why the installed proof's document cannot back a published `unsat`
    /// in the default posture, or `None` when it can.
    fn qsat_unsat_document_refusal(&self) -> Option<&'static str> {
        let mut scan = AletheDocumentScan::default();
        match self.try_export_installed_proof_alethe_to(&mut scan) {
            None => return Some("no-document"),
            Some(Err(error)) => {
                tracing::debug!(target: "ay::qsat", %error, "evidence: render refused");
                return Some("render-refused");
            }
            Some(Ok(())) => {}
        }
        if scan.unproved > 0 {
            return Some("unproved-step");
        }
        if scan.overflowed {
            return Some("premises-unjudged");
        }
        let Some(authored) = self.authored_premise_surfaces() else {
            return Some("premises-unjudged");
        };
        if scan
            .premise_assumes
            .iter()
            .any(|assume| !authored.contains(&normalize_premise_surface(assume)))
        {
            return Some("foreign-assume");
        }
        if self.unsat_proof_terminal_foreign_assume() {
            return Some("foreign-assume");
        }
        if !self.installed_proof_carcara_surface_supported() {
            return Some("carcara-unsupported-surface");
        }
        None
    }

    /// Why the installed proof falls short of a certificate the caller
    /// DEMANDED in the shed posture, or `None` when it meets it (always
    /// `None` when nothing is demanded): the document must render, and under
    /// strict rigor carry no unproved step (printed or on the internal
    /// terminal path) and no premise `assume` that is not an assertion as
    /// written.
    fn qsat_demanded_certificate_refusal(&self) -> Option<&'static str> {
        if !self.checked_certificate_demanded() {
            return None;
        }
        let mut scan = AletheDocumentScan::default();
        match self.try_export_installed_proof_alethe_to(&mut scan) {
            None => return Some("demanded-unrendered"),
            Some(Err(_)) => return Some("demanded-render-refused"),
            Some(Ok(())) => {}
        }
        if self.accepts_discharged_trust_grant() {
            return None;
        }
        if scan.unproved > 0 {
            return Some("demanded-unproved-step");
        }
        if let Some(reason) = self.qsat_strict_demand_internal_refusal() {
            return Some(reason);
        }
        if scan.overflowed {
            return Some("demanded-premises-unjudged");
        }
        if self.unsat_proof_terminal_foreign_assume() {
            return Some("demanded-foreign-assume");
        }
        let Some(authored) = self.authored_premise_surfaces() else {
            return Some("demanded-premises-unjudged");
        };
        if scan
            .premise_assumes
            .iter()
            .any(|assume| !authored.contains(&normalize_premise_surface(assume)))
        {
            return Some("demanded-foreign-assume");
        }
        None
    }

    /// Under a demanded certificate at strict rigor, an unproved (`trust`,
    /// trusted theory lemma, `hole`) step on the installed proof's internal
    /// terminal path, which a printed document may spell as something else.
    fn qsat_strict_demand_internal_refusal(&self) -> Option<&'static str> {
        if !self.checked_certificate_demanded() || self.accepts_discharged_trust_grant() {
            return None;
        }
        let report = self
            .last_proof
            .as_ref()
            .map(ay_proof::terminal_trust_report)
            .unwrap_or_default();
        let internal = report
            .trust_rule_on_path
            .saturating_add(report.trust_theory_lemma_on_path)
            .saturating_add(report.hole_rule_on_path);
        (internal > 0).then_some("demanded-unproved-step")
    }
}
