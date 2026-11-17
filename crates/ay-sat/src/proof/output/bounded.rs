// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed control for the bounded LRAT producer. Other proof formats retain
//! their legacy paths; these are not used by the bounded ResolutionDag API.

use super::*;

impl ProofOutput {
    pub(crate) fn poll_bounded_emission(
        &mut self,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        match self {
            Self::Lrat(writer) => writer.poll_bounded_emission(keep_going),
            Self::Drat(_) | Self::Veripb(_) => Ok(()),
        }
    }

    pub(crate) fn has_bounded_emission_cancellation(&self) -> bool {
        match self {
            Self::Lrat(writer) => writer.has_bounded_emission_cancellation(),
            Self::Drat(_) | Self::Veripb(_) => false,
        }
    }

    pub(crate) fn poison_bounded_emission(&mut self, error: &io::Error) {
        if let Self::Lrat(writer) = self {
            writer.poison_bounded_emission(error);
        }
    }

    /// Emit a bounded-producer prevalidated positive-RUP addition.
    pub(crate) fn add_bounded_prevalidated_rup_with_cancellation(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<u64> {
        match self {
            Self::Drat(writer) => {
                writer.add(clause)?;
                Ok(0)
            }
            Self::Veripb(writer) => {
                writer.add(clause)?;
                Ok(0)
            }
            Self::Lrat(writer) => {
                writer.add_bounded_prevalidated_rup_with_cancellation(clause, hints, keep_going)
            }
        }
    }

    /// Emit a pre-assigned bounded-producer positive-RUP addition.
    pub(crate) fn add_with_id_bounded_prevalidated_rup_with_cancellation(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[i64],
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        match self {
            Self::Drat(_) | Self::Veripb(_) => Ok(()),
            Self::Lrat(writer) => writer.add_with_id_bounded_prevalidated_rup_with_cancellation(
                clause_id, clause, hints, keep_going,
            ),
        }
    }

    pub(crate) fn flush_with_cancellation(
        &mut self,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        match self {
            Self::Drat(writer) => writer.flush(),
            Self::Veripb(writer) => writer.flush(),
            Self::Lrat(writer) => writer.flush_with_cancellation(keep_going),
        }
    }

    pub(crate) fn into_inner_with_cancellation(
        self,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<BoxedWriter> {
        match self {
            Self::Drat(writer) => writer.into_inner(),
            Self::Veripb(writer) => writer.into_inner(),
            Self::Lrat(writer) => writer.into_inner_with_cancellation(keep_going),
        }
    }
}
