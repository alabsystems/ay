// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Direct, resource-bounded LRAT emission for the in-memory proof producer.

use super::{LastAdd, ProofManager};
use crate::proof::bounded_emission_cancelled;
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
        !self.has_io_error()
            && self.last_add.is_some_and(|last_add| {
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

    fn controlled_bounded_emission<T>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> io::Result<T>,
    ) -> io::Result<T> {
        if self.output.has_bounded_emission_cancellation() {
            return Err(bounded_emission_cancelled());
        }
        if self.has_io_error() {
            return Err(io::Error::other("bounded LRAT emission previously failed"));
        }
        // Keep terminal authority closed even if a callback/sink unwinds. Every
        // callback also runs through the output's independently poisoned latch.
        self.lrat_structural_failure = true;
        match operation(self) {
            Ok(value) => {
                self.lrat_structural_failure = false;
                Ok(value)
            }
            Err(error) => {
                self.last_add = None;
                self.output.poison_bounded_emission(&error);
                Err(error)
            }
        }
    }

    fn admit_bounded_emission(
        &mut self,
        deadline: Option<Instant>,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        Self::check_bounded_emit_deadline(deadline)?;
        self.output.poll_bounded_emission(keep_going)?;
        // An accepting callback is itself allowed to consume the deadline.
        Self::check_bounded_emit_deadline(deadline)
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
        self.emit_bounded_backward_rup_step_with_cancellation(
            clause_id,
            clause,
            hints,
            deadline,
            &|| true,
        )
    }

    pub(crate) fn emit_bounded_backward_rup_step_with_cancellation(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[i64],
        deadline: Option<Instant>,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        self.controlled_bounded_emission(|manager| {
            manager.emit_controlled_backward_step(clause_id, clause, hints, deadline, keep_going)
        })
    }

    fn emit_controlled_backward_step(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[i64],
        deadline: Option<Instant>,
        keep_going: &dyn Fn() -> bool,
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
            self.output.poll_bounded_emission(keep_going)?;
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
            .add_with_id_bounded_prevalidated_rup_with_cancellation(
                clause_id, clause, hints, keep_going,
            )
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
        self.admit_bounded_emission(deadline, keep_going)
    }

    /// Emit the terminal empty clause for a producer-prevalidated positive-RUP
    /// chain without generic hint filtering/deduplication buffers.
    pub(crate) fn emit_bounded_empty_rup_step(
        &mut self,
        hints: &[u64],
        deadline: Option<Instant>,
    ) -> io::Result<u64> {
        self.emit_bounded_empty_rup_step_with_cancellation(hints, deadline, &|| true)
    }

    pub(crate) fn emit_bounded_empty_rup_step_with_cancellation(
        &mut self,
        hints: &[u64],
        deadline: Option<Instant>,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<u64> {
        self.controlled_bounded_emission(|manager| {
            manager.emit_controlled_empty_step(hints, deadline, keep_going)
        })
    }

    fn emit_controlled_empty_step(
        &mut self,
        hints: &[u64],
        deadline: Option<Instant>,
        keep_going: &dyn Fn() -> bool,
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
            self.output.poll_bounded_emission(keep_going)?;
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
        let clause_id =
            match self
                .output
                .add_bounded_prevalidated_rup_with_cancellation(&[], hints, keep_going)
            {
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
        self.admit_bounded_emission(deadline, keep_going)?;
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
        self.finish_bounded_backward_emission_with_cancellation(deadline, &|| true)
    }

    pub(crate) fn finish_bounded_backward_emission_with_cancellation(
        &mut self,
        deadline: Option<Instant>,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        self.controlled_bounded_emission(|manager| {
            manager.retire_controlled_reservations(deadline, keep_going)
        })
    }

    fn retire_controlled_reservations(
        &mut self,
        deadline: Option<Instant>,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        for (index, clause_id) in self.backward_reserved_ids.iter().enumerate() {
            if index % 1024 == 0 {
                Self::check_bounded_emit_deadline(deadline)?;
            }
            self.output.poll_bounded_emission(keep_going)?;
            self.known_lrat_ids.remove(clause_id);
        }
        Self::check_bounded_emit_deadline(deadline)?;
        self.backward_reserved_ids.clear_and_shrink();
        self.admit_bounded_emission(deadline, keep_going)
    }

    pub(crate) fn flush_with_cancellation(
        &mut self,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        self.controlled_bounded_emission(|manager| {
            manager.output.flush_with_cancellation(keep_going)?;
            if let Some(next_id) = manager.output.next_lrat_id() {
                manager.next_lrat_id = manager.next_lrat_id.max(next_id);
            }
            manager.output.poll_bounded_emission(keep_going)
        })
    }
}

#[cfg(test)]
mod cancellation_tests;
