// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `process_trace` ends at its refutation: the last step it leaves in the
//! proof is an empty clause.
//!
//! The replay does not stop at the first entry it proves empty. A hint replay
//! or a certified re-derivation can prove a strict subclause, the empty clause
//! included, before the trace's own refutation (#rank-4 increment 1), and the
//! entries after it still emit steps: an input clause's `assume` and `or`, a
//! tautology step, an intermediate resolvent. A step only cites earlier
//! steps, so none of those is a premise of the refutation, but they leave it
//! in the middle of the proof.
//!
//! The UNSAT assembly reads such a proof as a broken chain. Its post-rewrite
//! check (`rewrite_derived_empty_clause`, through
//! `empty_clause_derivation_status`) walks the whole proof and reports
//! `FinalClauseNotEmpty` when the last step is not the empty clause. The
//! repair then truncates the trailing run of resolution steps
//! (`strip_resolution_steps`, which relies on the chain having been "appended
//! at the end by the derive-empty-clause functions") and rebuilds the empty
//! clause without the trace, which the replay consumed. When that run holds
//! the refutation, a valid derivation is discarded.
//!
//! Measured on deductive-checks's set-fold frame (`certification_determinism`), with
//! re-derivation scoped to seeded `trust`/`Generic` leaves
//! (DR-AY-EUF-BRIDGE-20261103): two such originals were re-derived as units
//! near the trace's end, a learned clause after them proved the empty clause,
//! and one more resolvent followed it. The repair replaced the replay's
//! 19-step refutation (three deferred `trust` leaves) with a flat
//! `th_resolution` over 76 `trust` leaves. The published proof then deferred
//! 48 clauses, quantifier instances among them, so step (4a) of the
//! deferred-trust discharge was not eligible and step (4) re-solved the
//! query. Under f1a718aed's wider scope the replay's refutation (again 19
//! steps) happened to be followed by non-resolution steps, so the truncation
//! stopped short of it, and with no re-derivation at all a closer appended it
//! last. Ending the replay at its refutation keeps it whatever the scope.
//!
//! Only steps the replay emitted after the proof's last empty clause are
//! dropped. Every empty-clause root stays, the refutation `process_trace`
//! returns and any later one, so the assembly's choice among them
//! (`select_empty_clause_root`) sees the same candidates. A proof whose last
//! empty clause the seeded proof already carried is left as it is.

use ay_core::{Proof, ProofId, ProofStep};

/// Drop the steps the replay emitted after the proof's last empty clause, once
/// the replay has a `refutation`. `replay_start` is the length of the proof
/// before the replay.
pub(super) fn end_at(proof: &mut Proof, refutation: Option<ProofId>, replay_start: usize) {
    if refutation.is_none() {
        return;
    }
    let Some(last_empty) = proof.steps.iter().rposition(|step| {
        matches!(
            step,
            ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. }
                if clause.is_empty()
        )
    }) else {
        return;
    };
    if last_empty >= replay_start {
        proof.steps.truncate(last_empty.saturating_add(1));
    }
}
