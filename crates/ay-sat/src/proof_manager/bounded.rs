// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Direct, resource-bounded LRAT emission for the in-memory proof producer.

use super::{LastAdd, ProofManager};
use crate::Literal;
use ay_core::time::Instant;
use std::io;

impl ProofManager {
    #[inline]
    pub(crate) fn has_backward_reserved_ids(&self) -> bool {
        !self.backward_reserved_ids.is_empty()
    }

    #[inline]
    pub(crate) fn is_backward_reserved_id(&self, clause_id: u64) -> bool {
        self.backward_reserved_ids.contains(clause_id)
    }

    /// Whether the proof stream's most recent addition is a usable empty
    /// clause. DRAT has no clause-ID visibility bookkeeping; a successful
    /// write is sufficient there. LRAT additionally requires the terminal ID
    /// to remain visible to the standalone checker.
    #[inline]
    pub(crate) fn has_file_visible_terminal_empty(&self) -> bool {
        self.last_add.is_some_and(|last_add| {
            last_add.is_empty && (!self.lrat_mode || self.lrat_id_visible_in_file(last_add.id))
        })
    }

    fn check_bounded_emit_deadline(deadline: Option<Instant>) -> io::Result<()> {
        if deadline.is_some_and(|end| Instant::now() >= end) {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "bounded LRAT emission deadline exceeded",
            ));
        }
        Ok(())
    }

    /// Emit one producer-prevalidated positive-RUP backward step without the
    /// generic signed-RAT preflight's per-step hash-set allocations.
    pub(crate) fn emit_bounded_backward_rup_step(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[i64],
        deadline: Option<Instant>,
    ) -> io::Result<()> {
        if !self.lrat_mode || clause_id == 0 {
            return Ok(());
        }
        if self.lrat_blocked_by_theory_lemmas() {
            return Ok(());
        }
        if !self.backward_reserved_ids.contains(clause_id) {
            if self.lrat_id_visible_in_file(clause_id) {
                return Ok(());
            }
            self.lrat_structural_failure = true;
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "bounded backward LRAT step is neither reserved nor file-visible",
            ));
        }
        if hints.is_empty() {
            self.lrat_structural_failure = true;
            self.lrat_authority_fail_closed = true;
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "bounded derived LRAT step has no RUP hints",
            ));
        }
        for (index, &hint) in hints.iter().enumerate() {
            if index % 1024 == 0 {
                Self::check_bounded_emit_deadline(deadline)?;
            }
            if hint <= 0 || !self.lrat_id_usable_as_hint(hint as u64) {
                self.lrat_structural_failure = true;
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "bounded backward LRAT hint is not a live positive ID",
                ));
            }
        }
        Self::check_bounded_emit_deadline(deadline)?;
        let added_before = self.output.added_count();
        if let Err(error) = self
            .output
            .add_with_id_bounded_prevalidated_rup(clause_id, clause, hints)
        {
            self.lrat_structural_failure = true;
            return Err(error);
        }
        if self.output.added_count() != added_before.saturating_add(1) {
            self.lrat_structural_failure = true;
            return Err(io::Error::other(
                "bounded backward LRAT step was not written",
            ));
        }
        self.known_lrat_ids.insert(clause_id);
        self.backward_reserved_ids.remove(clause_id);
        Self::check_bounded_emit_deadline(deadline)
    }

    /// Emit the terminal empty clause for a producer-prevalidated positive-RUP
    /// chain without generic hint filtering/deduplication buffers.
    pub(crate) fn emit_bounded_empty_rup_step(
        &mut self,
        hints: &[u64],
        deadline: Option<Instant>,
    ) -> io::Result<u64> {
        if !self.lrat_mode || self.lrat_blocked_by_theory_lemmas() {
            return Ok(0);
        }
        if hints.is_empty() {
            self.lrat_structural_failure = true;
            self.lrat_authority_fail_closed = true;
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "bounded empty LRAT step has no RUP hints",
            ));
        }
        for (index, &hint) in hints.iter().enumerate() {
            if index % 1024 == 0 {
                Self::check_bounded_emit_deadline(deadline)?;
            }
            if !self.lrat_id_usable_as_hint(hint) {
                self.lrat_structural_failure = true;
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "bounded empty LRAT hint is not a live positive ID",
                ));
            }
        }
        Self::check_bounded_emit_deadline(deadline)?;
        let added_before = self.output.added_count();
        let clause_id = match self.output.add_bounded_prevalidated_rup(&[], hints) {
            Ok(clause_id) => clause_id,
            Err(error) => {
                self.lrat_structural_failure = true;
                return Err(error);
            }
        };
        if clause_id == 0 || self.output.added_count() != added_before.saturating_add(1) {
            self.lrat_structural_failure = true;
            return Err(io::Error::other(
                "bounded terminal LRAT step was not written",
            ));
        }
        self.known_lrat_ids.insert(clause_id);
        self.next_lrat_id = clause_id + 1;
        #[cfg(debug_assertions)]
        if let Some(ref mut lrat) = self.lrat_checker {
            lrat.add_original(clause_id, &[]);
        }
        self.last_add = Some(LastAdd::new(clause_id, &[]));
        Self::check_bounded_emit_deadline(deadline)?;
        Ok(clause_id)
    }

    /// Complete bounded backfill and retire every reservation that was not
    /// actually emitted. Unreachable reserved IDs must also be removed from
    /// `known_lrat_ids`; merely clearing the reservation bitmap would make
    /// those nonexistent file IDs appear usable to a terminal hint chain.
    pub(crate) fn finish_bounded_backward_emission(
        &mut self,
        deadline: Option<Instant>,
    ) -> io::Result<()> {
        for (index, clause_id) in self.backward_reserved_ids.iter().enumerate() {
            if index % 1024 == 0 {
                Self::check_bounded_emit_deadline(deadline)?;
            }
            self.known_lrat_ids.remove(clause_id);
        }
        Self::check_bounded_emit_deadline(deadline)?;
        self.backward_reserved_ids.clear_and_shrink();
        Ok(())
    }
}
