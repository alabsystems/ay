// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The authored-subset UNSAT theorem (#qe-ground-first).
//!
//! Dropping hypotheses only weakens a problem: every model of the authored
//! roots is a model of any subset of them, so a refutation of a SUBSET of the
//! authored roots refutes the query. That is the whole theorem, and it is the
//! one ground-first scheduling (`check_sat/ground_first.rs`) publishes on: the
//! subset is the query without its top-level universal axioms, refuted before
//! any of them is instantiated.
//!
//! The subset's refutation is not taken on the scheduler's word. It is
//! [`Executor::checked_exact_unsat_solve`] — a disposable probe over exactly
//! those roots that publishes UNSAT only through its own mandatory
//! certification funnel, carrying a checked exact-query token (strict proof,
//! an independently checked refutation, an exact semantic theorem, or a
//! `discharged-trust` admission, whose class this certificate inherits and
//! never upgrades). The certificate seals which roots were refuted, by
//! position in the immutable epoch, together with the epoch, the source
//! context, the roots' entry stamps and the whole-store snapshot, so any change
//! to the objects the probe decided makes it stale.
//!
//! It is a SEMANTIC certificate, not a translated artifact: every explicit
//! proof or proof-checking mode continues to fail closed, and the authorizer
//! declines there before paying for a probe.

use ay_core::term::{TermEntryStamp, TermStoreSnapshotStamp};
use ay_core::TermId;
use ay_frontend::SourceContextStamp;

use super::{CheckedExactClosedForallUnsat, ProbeUnsatAuthority, UnsatCertificateKind};
use crate::executor::{CorroborationSource, Executor, QueryAuthorityEpoch, UnsatEvidence};
use crate::executor_types::SolveResult;

/// Sealed source theorem: the authored roots at `subset` are unsatisfiable.
#[derive(Debug)]
pub(in crate::executor) struct CheckedExactAuthoredSubsetUnsat {
    query_epoch: QueryAuthorityEpoch,
    source_declaration_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[TermEntryStamp]>,
    /// Strictly increasing positions into `roots`; non-empty and proper.
    subset: Box<[usize]>,
    /// The class the refuting probe's own funnel admitted it on.
    authority: ProbeUnsatAuthority,
    /// The probe's evidence (level and corroboration), which the theorem
    /// inherits: P4 propagates a nested corroboration to the published label.
    evidence: UnsatEvidence,
    term_snapshot: TermStoreSnapshotStamp,
}

/// Whether `subset` names a non-empty, proper, strictly increasing selection
/// of `len` positions.
fn subset_is_proper(subset: &[usize], len: usize) -> bool {
    !subset.is_empty()
        && subset.len() < len
        && subset.windows(2).all(|pair| pair[0] < pair[1])
        && subset.last().is_some_and(|&last| last < len)
}

impl CheckedExactAuthoredSubsetUnsat {
    /// Whether the subset's refutation was admitted only on `discharged-trust`.
    /// The theorem is then no stronger than that admission.
    pub(super) fn rests_on_discharged_trust(&self) -> bool {
        matches!(self.authority, ProbeUnsatAuthority::DischargedTrust)
    }

    /// The evidence behind the sealed refutation, as the theorem reports it.
    pub(super) fn nested_evidence(&self) -> UnsatEvidence {
        self.evidence
            .nested(CorroborationSource::NestedAuthoredSubset)
    }

    pub(super) fn is_current(&self, executor: &Executor) -> bool {
        !crate::executor::model::scoped_term_evaluation_override_active()
            && self
                .query_epoch
                .is_same_epoch(&executor.query_authority_epoch)
            && self.source_declaration_stamp == executor.ctx.source_context_stamp()
            && self.roots.as_ref() == executor.ctx.assertions.as_slice()
            && self.term_snapshot == executor.ctx.terms.snapshot_stamp()
            && CheckedExactClosedForallUnsat::entries_are_current(
                &executor.ctx.terms,
                &self.roots,
                &self.root_entries,
            )
            && subset_is_proper(&self.subset, self.roots.len())
    }
}

impl Executor {
    /// The authored roots of the current public decision when it is a PLAIN
    /// hard query: a current epoch whose roots are exactly the live assertion
    /// window, with no bound assumption, no solver-declared extension, and no
    /// assumption left on the executor. Posture-independent: unlike
    /// `exact_plain_hard_unsat_scope_is_current`, it does not ask for proof
    /// provenance, which competition shedding never installs.
    pub(in crate::executor) fn plain_hard_query_roots(&self) -> Option<&[TermId]> {
        let epoch = self.unsat_query_epoch.as_ref()?;
        (epoch.is_current(self)
            && epoch.assertions == self.ctx.assertions
            && epoch
                .assumptions
                .as_deref()
                .is_some_and(|assumptions| assumptions.is_empty())
            && epoch.declared_extension.is_empty()
            && epoch.declared_extension_entries.is_empty()
            && epoch.declared_extension_objectives.is_none()
            && epoch.declared_extension_objective_entries.is_none()
            && self.last_assumptions.iter().flatten().next().is_none())
        .then_some(epoch.assertions.as_slice())
    }

    /// Refute the authored roots at `subset` on a certifying probe and seal
    /// the result. `None` on every doubt, leaving the caller's path untouched:
    /// explicit proof, strict and self-check modes decline before paying for
    /// the probe, since the mint would refuse a semantic-only theorem there.
    pub(in crate::executor) fn try_authorize_current_query_exact_authored_subset_unsat(
        &mut self,
        subset: &[usize],
        budget_ms: u64,
    ) -> Option<CheckedExactAuthoredSubsetUnsat> {
        if crate::executor::model::scoped_term_evaluation_override_active()
            || !self.exact_plain_hard_unsat_scope_is_current()
            || self.should_abort_theory_loop()
            || self.strict_unsat_presentation_required()
        {
            return None;
        }
        let (roots, root_entries) = {
            let epoch = self.unsat_query_epoch.as_ref()?;
            (epoch.assertions.clone(), epoch.assertion_entries.clone())
        };
        if !subset_is_proper(subset, roots.len()) {
            return None;
        }
        let obligation: Vec<TermId> = subset.iter().map(|&position| roots[position]).collect();
        let checked = self.checked_exact_unsat_solve(obligation.clone(), budget_ms)?;
        let authority = checked.authority();
        let evidence = checked.evidence();
        if !checked.consume(self, &obligation) {
            return None;
        }
        let term_snapshot = self.ctx.terms.snapshot_stamp();
        // A disposable probe cannot touch the outer query, source epoch, or
        // term store, so any drift here is disqualifying.
        if !self.exact_plain_hard_unsat_scope_is_current()
            || self.should_abort_theory_loop()
            || !self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
                epoch.assertions == roots && epoch.assertion_entries == root_entries
            })
        {
            return None;
        }
        Some(CheckedExactAuthoredSubsetUnsat {
            query_epoch: self.query_authority_epoch.clone(),
            source_declaration_stamp: self.ctx.source_context_stamp(),
            roots: roots.into_boxed_slice(),
            root_entries: root_entries.into_boxed_slice(),
            subset: subset.to_vec().into_boxed_slice(),
            authority,
            evidence,
            term_snapshot,
        })
    }

    /// Emit UNSAT from a sealed authored-subset refutation. Semantic authority,
    /// not a translated artifact, so explicit proof modes continue to fail
    /// closed.
    pub(in crate::executor) fn emit_checked_exact_authored_subset_unsat(
        &mut self,
        evidence: CheckedExactAuthoredSubsetUnsat,
    ) -> SolveResult {
        self.emit_checked_exact_unsat(
            UnsatCertificateKind::CheckedExactAuthoredSubset(evidence),
            "checked exact authored-subset UNSAT evidence was stale at emission",
            "checked exact authored-subset UNSAT has no translated authored-scope proof for the requested proof artifact",
            "verdict_certification.checked_exact_authored_subset",
        )
    }
}

#[cfg(test)]
mod tests {
    use super::subset_is_proper;

    #[test]
    fn subset_must_be_nonempty_proper_and_strictly_increasing() {
        assert!(subset_is_proper(&[0, 2], 3));
        assert!(!subset_is_proper(&[], 3));
        assert!(!subset_is_proper(&[0, 1, 2], 3), "not proper");
        assert!(!subset_is_proper(&[2, 0], 3), "not increasing");
        assert!(!subset_is_proper(&[1, 1], 3), "repeated");
        assert!(!subset_is_proper(&[0, 3], 3), "out of range");
    }
}
