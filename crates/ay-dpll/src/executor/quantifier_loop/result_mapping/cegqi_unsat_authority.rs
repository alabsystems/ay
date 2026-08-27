// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sealed CEGQI UNSAT publication authority.

use super::{Executor, LogicCategory, SolveResult, TermId};
use ay_frontend::SourceContextStamp;

#[must_use = "a checked CEGQI UNSAT certificate must be consumed to publish UNSAT"]
pub(super) struct Checked {
    source_context_stamp: SourceContextStamp,
    /// `true` when consequence replay installed an authored-scope strict proof.
    /// Publication keeps it for the ordinary strict-certification mint; the
    /// artifact firewall is only for the proof-less verdict-only certificate.
    translated_strict_proof: bool,
}

impl Checked {
    pub(super) fn publish(self, executor: &mut Executor) -> SolveResult {
        // Certification and publication are separate calls. Re-check stop and
        // source state at this sole consumption point so the sealed token can
        // never outlive a frontend scope/signature change.
        if executor.should_abort_theory_loop() {
            executor.clear_cegqi_inner_unsat_artifacts();
            return SolveResult::Unknown;
        }
        if self.source_context_stamp != executor.ctx.source_context_stamp() {
            executor.clear_cegqi_inner_unsat_artifacts();
            executor.last_unknown_reason = Some(super::UnknownReason::QuantifierCegqiIncomplete);
            return SolveResult::Unknown;
        }
        if self.translated_strict_proof {
            // The installed proof is the publication artifact; mandatory
            // certification re-checks it from scratch at mint time.
            executor.last_unknown_reason = None;
            return SolveResult::unsat();
        }
        executor.publish_quantified_verdict_only_unsat()
    }
}

pub(super) fn certify(
    executor: &mut Executor,
    snapshot: Option<&[TermId]>,
    category: LogicCategory,
) -> Option<Checked> {
    // A translated authored-scope strict proof is stronger than the
    // proof-suppressed verdict-only certificate. A live proof cascade may
    // already have committed it, so re-validate that exact proof before
    // paying another bounded replay probe.
    if let Some(checked) = certify_installed_strict_proof(executor) {
        return Some(checked);
    }
    if executor.try_translate_authored_consequence_replay_unsat() {
        return Some(Checked {
            source_context_stamp: executor.ctx.source_context_stamp(),
            translated_strict_proof: true,
        });
    }
    if executor.cegqi_consequence_set_is_unsat(snapshot, category) {
        Some(Checked {
            source_context_stamp: executor.ctx.source_context_stamp(),
            translated_strict_proof: false,
        })
    } else {
        None
    }
}

/// Seal an already-installed authored-scope strict refutation without running
/// any fallback producer or proof-less consequence check.
///
/// The proof is re-validated here, [`Checked::publish`] re-checks the source
/// stamp and stop state, and the ordinary publication funnel checks it again.
pub(super) fn certify_installed_strict_proof(executor: &mut Executor) -> Option<Checked> {
    (crate::quant_unit_authority::consequence_replay_enabled()
        && executor.authored_scope_strict_proof_installed())
    .then(|| Checked {
        source_context_stamp: executor.ctx.source_context_stamp(),
        translated_strict_proof: true,
    })
}

/// Publish only an already-installed exact strict proof before a weaker
/// ground-reconstruction fallback can discard it. No producer or proof-less
/// grant is reachable here; every outer publication gate re-checks the proof.
pub(super) fn publish_installed(executor: &mut Executor) -> Option<SolveResult> {
    certify_installed_strict_proof(executor).map(|checked| checked.publish(executor))
}
