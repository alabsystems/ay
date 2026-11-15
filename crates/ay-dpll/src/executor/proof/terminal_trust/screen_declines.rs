// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The wire-gap screen's two support questions that reach the complete
//! bit-blast, asked as one public decision's questions.
//!
//! One decision screens its documents many times, and each screen asks every
//! bit-vector lemma again (`proof_has_known_wire_gap`). Asked while a document
//! is observable, a question answers through the complete bit-blast until the
//! decision's stop, and an unstopped decline is kept in the decision's own
//! record (`ay_proof::BvSupportDeclines`), which answers every later ask of
//! that lemma in the decision without blasting it again. Measured on
//! `bv_affine_source`'s elaborated 64-bit affine identity under
//! `:check-proofs-strict` with no timeout, one decision asked its one lemma
//! 14 times and paid the sweep's 120 s wall at each ask.
//!
//! The record belongs to the decision whose [`QueryAuthorityEpoch`] it holds,
//! the fresh identity of one public decision attempt: asked under another
//! epoch, it is emptied first. A decline it keeps can be a wall clock's (the
//! sweep's), which may decline at one ask what a later ask refutes, so it
//! must never outlive the decision; within the decision it only makes every
//! screen give the answer the first one gave. A decline only declines: it
//! leaves the lemma a gap, and no document is printed from this record.

use std::cell::RefCell;

use ay_core::kani_compat::DetHashMap;
use ay_core::{TermId, TheoryLemmaKind};

use crate::executor::query_authority::QueryAuthorityEpoch;
use crate::executor::Executor;

#[cfg(test)]
#[path = "screen_declines_tests.rs"]
mod tests;

/// One public decision's record of the screen's declines.
#[derive(Default)]
pub(in crate::executor) struct WireGapScreenDeclines {
    /// The decision the record belongs to.
    decision: RefCell<Option<QueryAuthorityEpoch>>,
    declines: ay_proof::BvSupportDeclines,
}

impl Executor {
    /// The current public decision's record, emptied first when it was kept
    /// by another decision.
    pub(in crate::executor) fn wire_gap_screen_declines(&self) -> &ay_proof::BvSupportDeclines {
        let record = &self.wire_gap_screen_declines;
        let mut decision = record.decision.borrow_mut();
        if !decision
            .as_ref()
            .is_some_and(|kept| kept.is_same_epoch(&self.query_authority_epoch))
        {
            record.declines.clear();
            *decision = Some(self.query_authority_epoch.clone());
        }
        &record.declines
    }

    /// The screen's bit-blast support question
    /// (`ay_proof::checked_bv_bitblast_lowering_supported_within_solve`):
    /// asked until `asked`, the decision's stop, when a document is
    /// observable, and with the complete bit-blast unasked (`None`) when none
    /// is.
    pub(super) fn screen_bv_bitblast_supported(
        &self,
        kind: &TheoryLemmaKind,
        clause: &[TermId],
        term_overrides: Option<&DetHashMap<TermId, String>>,
        asked: Option<&dyn Fn() -> bool>,
    ) -> bool {
        let terms = &self.ctx.terms;
        match asked {
            Some(stop) => ay_proof::checked_bv_bitblast_lowering_supported_within_solve(
                terms,
                kind,
                clause,
                term_overrides,
                stop,
                self.wire_gap_screen_declines(),
            ),
            None => ay_proof::checked_bv_bitblast_lowering_supported_asking(
                terms,
                kind,
                clause,
                term_overrides,
                ay_proof::CompleteBlastAsk::NotAsked,
            ),
        }
    }

    /// The screen's structural bit-vector arithmetic question
    /// (`ay_proof::theory_lemma_bv_arithmetic_lowering_supported_within_solve`),
    /// asked as [`Self::screen_bv_bitblast_supported`] asks its own.
    pub(super) fn screen_bv_arithmetic_supported(
        &self,
        kind: &TheoryLemmaKind,
        clause: &[TermId],
        term_overrides: Option<&DetHashMap<TermId, String>>,
        budget: &mut ay_proof::ArithPolySimpPromotionBudget,
        asked: Option<&dyn Fn() -> bool>,
    ) -> bool {
        let terms = &self.ctx.terms;
        match asked {
            Some(stop) => ay_proof::theory_lemma_bv_arithmetic_lowering_supported_within_solve(
                terms,
                kind,
                clause,
                term_overrides,
                budget,
                stop,
                self.wire_gap_screen_declines(),
            ),
            None => ay_proof::theory_lemma_bv_arithmetic_lowering_supported_asking(
                terms,
                kind,
                clause,
                term_overrides,
                budget,
                ay_proof::CompleteBlastAsk::NotAsked,
            ),
        }
    }
}
