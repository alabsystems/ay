// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared nested solve for marked-margin `Auto` and `Required` entries.
//!
//! Both entries must use the same nested construction. `Required` seats a
//! validated binary prefix and admits only a complete original-frame tree;
//! `Auto` seats no prefix and also admits an independently verified original-
//! frame Farkas witness. The nested solve deliberately disables certificate
//! filtering: policy belongs to the mapped original verdict, while a reframed
//! optimum need not carry the zero-objective certificate that policy expects.
//!
//! This adds no verdict authority. Every tree leaf is replayed in exact
//! rationals against the original lowered model, `MarginMapping::map` verifies
//! retained evidence, and the outer `finish` gate verifies it again.

use crate::cert::FarkasCertificate;

use super::*;

/// Evidence required before a mapped `Infeasible` may be published.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum MarginEvidenceBar {
    /// The explicit shared-prefix API requires a complete caller-frame tree.
    VerifiedTree,
    /// Ordinary `check` also accepts an independently checked root Farkas.
    VerifiedTreeOrRootFarkas,
}

fn evidence_admitted(bar: MarginEvidenceBar, verdict: &Outcome) -> bool {
    match (bar, verdict) {
        (_, Outcome::Infeasible { tree_cert, .. }) if tree_cert.is_some() => true,
        (MarginEvidenceBar::VerifiedTreeOrRootFarkas, Outcome::Infeasible { cert, .. }) => {
            cert.is_some()
        }
        _ => false,
    }
}

fn root_crossing_farkas(session: &BabSession, bar: MarginEvidenceBar) -> Option<FarkasCertificate> {
    match bar {
        MarginEvidenceBar::VerifiedTree => None,
        MarginEvidenceBar::VerifiedTreeOrRootFarkas => {
            let budget = cert_budget_native(&session.model, &session.opts);
            crate::tree_cert::root_float_farkas(&session.model, budget.deadline)
        }
    }
}

fn trace_refusal(
    bar: MarginEvidenceBar,
    root_farkas: Option<&FarkasCertificate>,
    status: &str,
    prefix_len: usize,
) {
    if !structure_trace_enabled() {
        return;
    }
    eprintln!(
        "--trace margin-nested-refusal bar={} root_farkas={} status={} prefix={}",
        match bar {
            MarginEvidenceBar::VerifiedTree => "verified-tree",
            MarginEvidenceBar::VerifiedTreeOrRootFarkas => "tree-or-root-farkas",
        },
        match (bar, root_farkas) {
            (MarginEvidenceBar::VerifiedTree, _) => "not-attempted",
            (_, Some(_)) => "hit",
            (_, None) => "miss",
        },
        status,
        prefix_len,
    );
}

impl BabSession {
    /// Run the single nested reframe shared by both marked-margin entries.
    pub(super) fn run_reframed_nested(
        &self,
        prepared: crate::margin::PreparedMargin,
        shared_binary_prefix: &[Col],
        target_fsb_prefix: Option<crate::bab::TargetFsbPrefixRequest<'_>>,
        bar: MarginEvidenceBar,
    ) -> Result<crate::margin::Reframed, MilpError> {
        let crate::margin::PreparedMargin {
            reframed_model,
            mapping,
        } = prepared;
        let (sense, threshold) = mapping.telemetry_key();
        let started = Instant::now();
        let target = mapping.proof_target(&self.model);
        let sub_opts = self.opts.clone().with_require_certificates(false);
        let mut sub = BabSession::new(reframed_model, &sub_opts)?;
        sub.hint_branch_order(&self.branch_hints);
        sub.shortlist_root_strong_branch_candidates(&self.root_strong_branch_shortlist);
        let nested = sub.check_with_shared_binary_prefix(
            shared_binary_prefix,
            None,
            MarginMode::ReframedProof(target),
            target_fsb_prefix,
        )?;
        let mut reframed = mapping.map(&self.model, nested);
        if reframed.verdict.is_infeasible() && !evidence_admitted(bar, &reframed.verdict) {
            // Match the plain solve's checked root-witness enrichment. A miss
            // fails closed and marks the profile event as non-deciding.
            let root_farkas = root_crossing_farkas(self, bar);
            trace_refusal(
                bar,
                root_farkas.as_ref(),
                reframed.info.reframed_status,
                shared_binary_prefix.len(),
            );
            reframed.verdict = match root_farkas {
                Some(cert) => Outcome::Infeasible {
                    cert: Some(cert),
                    tree_cert: None,
                },
                None => {
                    reframed.info.decided = false;
                    Outcome::Unknown {
                        reason: UnknownReason::CertificateUnavailable,
                    }
                }
            };
        }
        crate::margin::record(sense, &threshold, &reframed.info, started.elapsed());
        Ok(reframed)
    }
}
