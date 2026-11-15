// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The post-expansion ABVFP window: the read elimination planned afresh after
//! the read-over-write expansion, and the `unknown` detail that names the
//! array terms a refused window still holds.

use super::flatten_reads::FlattenAbstain;
use super::FlattenOutcome;
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult, UnknownReason};

impl Executor {
    /// Solve the post-expansion window. A read through a `store` stops the
    /// read elimination on the authored window, but the read-over-write
    /// expansion rewrites it down to its base array (`select (store a i v) j`
    /// is `ite (= i j) v (select a j)`, an array-theory identity), so when
    /// the expansion rewrote anything the elimination is planned afresh on
    /// the expanded window; that window is equivalent to the authored one, so
    /// its verdict transfers. A partial expansion leaves a `store` behind and
    /// abstains again. `note` is updated to the abstention that now applies.
    pub(super) fn solve_abvfp_expanded_window(
        &mut self,
        expansion_rewrote: bool,
        note: &mut Option<FlattenAbstain>,
    ) -> Result<SolveResult> {
        if expansion_rewrote && note.is_some() {
            match self.try_flatten_constant_index_reads()? {
                FlattenOutcome::Decided(result) => return Ok(result),
                FlattenOutcome::Abstained(reason) => *note = Some(reason),
                FlattenOutcome::Undecided => *note = None,
            }
        }
        self.solve_abvfp_final_array_window()
    }

    /// The FP bit-blaster refused (`unsupported`) a window the read
    /// elimination left array terms in: keep the reason and name the gap in
    /// the detail, instead of the generic theory-combination text. A window
    /// with no array left (`NoArrays`) was refused for something else, so it
    /// keeps the generic detail. Diagnostic only; no verdict reads it.
    pub(super) fn name_abvfp_array_gap(&mut self, note: FlattenAbstain) {
        if self.last_unknown_reason != Some(UnknownReason::Unsupported)
            || note == FlattenAbstain::NoArrays
        {
            return;
        }
        self.record_unknown_diagnostic(
            UnknownReason::Unsupported,
            format!(
                "FP bit-blasting cannot encode the array terms left in this ABVFP window; {}",
                note.detail()
            ),
        );
    }
}
