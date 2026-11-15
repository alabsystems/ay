// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Controlled bounded records. No callback is stored in the erased writer.

use super::*;
use crate::proof::{bounded_emission_cancelled, is_bounded_emission_cancelled};

mod encoding;

pub(super) enum Hints<'a> {
    Unsigned(&'a [u64]),
    Signed(&'a [i64]),
}

impl<W: Write> LratWriter<W> {
    pub(crate) fn poll_bounded_emission(
        &mut self,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        if self.bounded_cancelled {
            return Err(bounded_emission_cancelled());
        }
        let failed = self.io_failed;
        self.io_failed = true;
        self.bounded_cancelled = true;
        if !keep_going() {
            if let Some(flag) = &self.bounded_interrupt {
                flag.store(true, Ordering::Relaxed);
            }
            return Err(bounded_emission_cancelled());
        }
        self.bounded_cancelled = false;
        self.io_failed = failed;
        Ok(())
    }

    pub(crate) fn has_bounded_emission_cancellation(&self) -> bool {
        self.bounded_cancelled
    }

    pub(crate) fn poison_bounded_emission(&mut self, error: &io::Error) {
        self.io_failed = true;
        self.bounded_cancelled |= is_bounded_emission_cancelled(error);
        if let Some(flag) = &self.bounded_interrupt {
            flag.store(true, Ordering::Relaxed);
        }
    }

    fn bounded_record<T>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> io::Result<T>,
    ) -> io::Result<T> {
        // A sink/callback panic after a record prefix also permanently poisons
        // extraction. Only a complete normally returned record clears this flag.
        self.io_failed = true;
        match operation(self) {
            Ok(value) => {
                self.io_failed = false;
                Ok(value)
            }
            Err(error) => {
                self.poison_bounded_emission(&error);
                Err(error)
            }
        }
    }

    pub(crate) fn add_bounded_prevalidated_rup_with_cancellation(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<u64> {
        if self.bounded_cancelled {
            return Err(bounded_emission_cancelled());
        }
        if self.io_failed {
            return Ok(0);
        }
        let id = self.bounded_record(|writer| {
            writer.flush_deletions_controlled(keep_going)?;
            let id = writer.next_id;
            if id > i64::MAX as u64 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "LRAT clause ID exceeds the signed/binary encoding limit",
                ));
            }
            writer.write_bounded_add(id, clause, Hints::Unsigned(hints), keep_going)?;
            Ok(id)
        })?;
        self.next_id = id + 1;
        self.io_failed |= self.next_id > i64::MAX as u64;
        self.latest_id = id;
        self.added_count += 1;
        Ok(id)
    }

    pub(crate) fn add_with_id_bounded_prevalidated_rup_with_cancellation(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[i64],
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        if self.bounded_cancelled {
            return Err(bounded_emission_cancelled());
        }
        if self.io_failed {
            return Ok(());
        }
        if clause_id == 0
            || clause_id > i64::MAX as u64
            || clause_id >= self.next_id
            || clause_id <= self.latest_id
        {
            self.io_failed = true;
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "invalid or non-monotonic pre-assigned bounded LRAT addition",
            ));
        }
        // Delayed additions intentionally precede pending deletions.
        self.bounded_record(|writer| {
            writer.write_bounded_add(clause_id, clause, Hints::Signed(hints), keep_going)
        })?;
        self.latest_id = clause_id;
        self.added_count += 1;
        Ok(())
    }

    fn flush_deletions_controlled(&mut self, keep_going: &dyn Fn() -> bool) -> io::Result<()> {
        if self.pending_deletions.is_empty() {
            return Ok(());
        }
        let mut deletions = std::mem::take(&mut self.pending_deletions);
        if self.binary {
            self.write_all_controlled(b"d", keep_going)?;
            for &id in &deletions {
                self.poll_bounded_emission(keep_going)?;
                let value = id.checked_mul(2).ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "clause ID overflow in bounded binary LRAT encoding",
                    )
                })?;
                self.write_varint_controlled(value, keep_going)?;
            }
            self.write_all_controlled(&[0], keep_going)?;
        } else {
            let id = self.next_id;
            self.next_id = id + 1;
            self.write_bounded_delete_text(id, &deletions, keep_going)?;
            self.latest_id = id;
        }
        self.recycle_pending_deletions(&mut deletions);
        self.pending_deletions = deletions;
        Ok(())
    }

    pub(crate) fn flush_with_cancellation(
        &mut self,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        if self.bounded_cancelled {
            return Err(bounded_emission_cancelled());
        }
        if self.io_failed {
            return Ok(());
        }
        self.bounded_record(|writer| {
            writer.poll_bounded_emission(keep_going)?;
            writer.flush_deletions_controlled(keep_going)?;
            writer.writer.flush()?;
            writer.poll_bounded_emission(keep_going)
        })
    }

    pub(crate) fn into_inner_with_cancellation(
        mut self,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<W> {
        if self.bounded_cancelled {
            return Err(bounded_emission_cancelled());
        }
        if self.io_failed {
            return Err(io::Error::other(
                "LRAT proof writer encountered I/O error during solve",
            ));
        }
        self.bounded_record(|writer| {
            writer.poll_bounded_emission(keep_going)?;
            writer.flush_deletions_controlled(keep_going)
        })?;
        let Self {
            writer,
            pending_deletions,
            text_line,
            bounded_interrupt,
            ..
        } = self;
        drop(pending_deletions);
        drop(text_line);
        drop(bounded_interrupt);
        if !keep_going() {
            return Err(bounded_emission_cancelled());
        }
        Ok(writer)
    }
}

#[cfg(test)]
mod tests;
