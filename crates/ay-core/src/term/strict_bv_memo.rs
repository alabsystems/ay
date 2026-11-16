// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The strict `bv_bitblast` checker's per-store memo of completed decisions.
//!
//! Proof finalization re-runs the strict checker after each of ~30 surgery
//! passes, so one `BvBitBlast` lemma is re-decided many times per solve on an
//! unchanged clause in an unchanged store. This memo lets a repeated decision
//! cost nothing, in both directions:
//!
//! * ACCEPTED: the decision procedure ran to completion on this exact clause
//!   and accepted it. Read only to skip repeating that identical acceptance.
//! * REFUSED: the proof-producing fallback's COUNTED envelope refused this
//!   exact clause — its conflict, decision, gate, step, hint, byte or replay
//!   caps ran out, or the checked producer found the clause false — before
//!   the outer hang guard. Read only to repeat that refusal instead of paying
//!   the whole counted exhaustion again. A refusal can only make a check FAIL,
//!   so no entry here can ever let a lemma through.
//!
//! What is never recorded: a caller cancellation, a caller-deadline stop, and
//! a hang-guard stop. Those end one ATTEMPT; they are not facts about the
//! clause. The checker decides which outcome is which; this store only keeps
//! what it is handed, under the key it is handed.
//!
//! Both tables are keyed by `TermId`s. [`TermStore::rollback_to`] and
//! `mark_and_compact` — the only two operations that can change what a
//! `TermId` means — drop every acceptance, as they always have. A refusal is
//! kept exactly when it still names the same formula: after a rollback, when
//! every id in its clause survived the truncation; after a compaction, when
//! every id survived and is relabelled through the compaction's own mapping
//! (surviving `TermData` is byte-identical). A `Clone` starts with no
//! acceptances and keeps the refusals: it has the same term at every id.
//! `from_entries` starts empty. Carrying a refusal can only make a check
//! fail, never pass. (Certification re-solves the authored problem in a
//! compacted clone of the solving context; without this each doomed lemma
//! would pay its whole counted exhaustion again there.) A refusal is also
//! keyed by the identity of the counted envelope it was reached under, so it
//! is never reused under different caps.

use std::{cell::RefCell, mem::size_of};

use super::{TermId, TermStore};
use crate::kani_compat::{KaniHashMap, KaniHashSet};

/// Cap on each table. Past it the store stops memoizing and the checker
/// re-runs the decision, so the bound costs time, never correctness — and an
/// untrusted proof cannot grow either table without limit.
const MAX_STRICT_BV_SEMANTICS_MEMO: usize = 4096;

type StrictBvRefusals = KaniHashMap<(u64, Vec<TermId>), Box<str>>;

/// The two tables. Deliberately not `Clone`; see [`Self::for_clone`].
#[derive(Default)]
pub(super) struct StrictBvSemanticsMemo {
    accepted: RefCell<KaniHashSet<Vec<TermId>>>,
    refused: RefCell<StrictBvRefusals>,
}

impl StrictBvSemanticsMemo {
    pub(super) fn clone_entry_count(&self) -> Option<usize> {
        Some(self.refused.try_borrow().ok()?.len())
    }

    // No callback while a RefCell guard is held. The caller prepays the
    // bounded entry walk, then checks this again after its last callback.
    pub(super) fn clone_memory_usage(&self, entry_limit: usize) -> Option<(usize, usize)> {
        let refused = self.refused.try_borrow().ok()?;
        if refused.len() > entry_limit {
            return None;
        }
        let mut bytes = refused.allocation_size();
        for ((_, clause), reason) in refused.iter() {
            bytes = bytes.checked_add(clause.capacity().checked_mul(size_of::<TermId>())?)?;
            bytes = bytes.checked_add(reason.len())?;
        }
        Some((refused.len(), bytes))
    }

    /// The memo a cloned store starts with: the refusals, and no acceptances.
    pub(super) fn for_clone(&self) -> Self {
        Self {
            accepted: RefCell::default(),
            refused: RefCell::new(self.refused.borrow().clone()),
        }
    }

    /// The arena was truncated to `len` terms: ids at or above it may be
    /// re-minted as different terms. Drop every acceptance, and every refusal
    /// naming a reclaimed id; a refusal over surviving ids names the very same
    /// terms and is kept.
    pub(super) fn truncate(&mut self, len: usize) {
        self.accepted.get_mut().clear();
        self.refused
            .get_mut()
            .retain(|(_, clause), _| clause.iter().all(|id| id.index() < len));
    }

    /// The arena was compacted and every surviving term relabelled through
    /// `mapping` (old index to new id; `None` if reclaimed), its `TermData`
    /// otherwise byte-identical. Drop every acceptance; relabel each refusal
    /// whose clause survives whole, so it keeps naming the same formula, and
    /// drop the rest. (Certification re-solves the authored problem in a
    /// compacted clone; without this each doomed lemma would pay its whole
    /// counted exhaustion again there.)
    pub(super) fn remap(&mut self, mapping: &[Option<TermId>]) {
        self.accepted.get_mut().clear();
        let refused = std::mem::take(self.refused.get_mut());
        for ((envelope, clause), reason) in refused {
            let relabelled: Option<Vec<TermId>> = clause
                .iter()
                .map(|id| mapping.get(id.index()).copied().flatten())
                .collect();
            if let Some(clause) = relabelled {
                self.refused.get_mut().insert((envelope, clause), reason);
            }
        }
    }
}

impl TermStore {
    /// Whether `clause` is recorded as having PASSED the strict `bv_bitblast`
    /// semantic decision procedure against this store.
    ///
    /// `true` means that procedure has already run TO COMPLETION on this exact
    /// clause in this exact store and accepted it. A recorded refusal is a
    /// separate table ([`Self::strict_bv_semantics_refusal`]) and can never
    /// make this return `true`.
    #[must_use]
    pub fn strict_bv_semantics_validated(&self, clause: &[TermId]) -> bool {
        self.strict_bv_semantics.accepted.borrow().contains(clause)
    }

    /// Record that the strict `bv_bitblast` semantic decision procedure ran to
    /// completion on `clause` and ACCEPTED it.
    ///
    /// Callers must only call this immediately after such a success.
    pub fn record_strict_bv_semantics_validated(&self, clause: &[TermId]) {
        let mut accepted = self.strict_bv_semantics.accepted.borrow_mut();
        if accepted.len() < MAX_STRICT_BV_SEMANTICS_MEMO {
            accepted.insert(clause.to_vec());
        }
    }

    /// The reason the strict checker's proof-producing fallback REFUSED
    /// `clause` in this store under the counted envelope `envelope`, if it
    /// did. `None` means "decide it", never "it passed".
    #[must_use]
    pub fn strict_bv_semantics_refusal(&self, envelope: u64, clause: &[TermId]) -> Option<String> {
        self.strict_bv_semantics
            .refused
            .borrow()
            .get(&(envelope, clause.to_vec()))
            .map(|reason| reason.to_string())
    }

    /// Record that the proof-producing fallback's counted envelope `envelope`
    /// REFUSED `clause`, with the refusal's `reason`.
    ///
    /// Callers must only record a refusal the counted envelope decided —
    /// never a cancellation, a caller-deadline stop or a hang-guard stop.
    pub fn record_strict_bv_semantics_refusal(
        &self,
        envelope: u64,
        clause: &[TermId],
        reason: &str,
    ) {
        let mut refused = self.strict_bv_semantics.refused.borrow_mut();
        if refused.len() < MAX_STRICT_BV_SEMANTICS_MEMO {
            refused.insert((envelope, clause.to_vec()), reason.into());
        }
    }
}
