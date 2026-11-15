// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared model work policy. Ordinary replay keeps its original operations;
//! counted replay pays actual visits, replacement capacity and retirement.

use ay_core::original_query::{CountedAdmission, CountedAdmissionError};
use std::convert::Infallible;

pub(crate) trait Work {
    type Error;
    fn work(&self, units: usize) -> Result<(), Self::Error>;
    fn zeros(&self, len: usize) -> Result<Vec<bool>, Self::Error>;
    fn resize(&self, values: &mut Vec<bool>, len: usize) -> Result<(), Self::Error>;
    fn witness_postcondition(
        &self,
        model: &[bool],
        witness: &[crate::Literal],
        clause: &[crate::Literal],
    ) -> Result<(), Self::Error>;
}

pub(crate) struct Ordinary;
pub(crate) struct Counted<'a>(pub(crate) &'a CountedAdmission);

pub(crate) fn ordinary<T>(result: Result<T, Infallible>) -> T {
    match result {
        Ok(value) => value,
        Err(never) => match never {},
    }
}

impl Work for Ordinary {
    type Error = Infallible;

    fn work(&self, _: usize) -> Result<(), Self::Error> {
        Ok(())
    }
    fn zeros(&self, len: usize) -> Result<Vec<bool>, Self::Error> {
        Ok(vec![false; len])
    }
    fn resize(&self, values: &mut Vec<bool>, len: usize) -> Result<(), Self::Error> {
        values.resize(len, false);
        Ok(())
    }
    fn witness_postcondition(
        &self,
        model: &[bool],
        witness: &[crate::Literal],
        clause: &[crate::Literal],
    ) -> Result<(), Self::Error> {
        debug_assert!(
            clause.iter().any(|lit| model
                .get(lit.variable().index())
                .is_some_and(|v| *v == lit.is_positive())),
            "BUG: reconstruct_witness postcondition: clause={clause:?} witness={witness:?}"
        );
        Ok(())
    }
}

impl Work for Counted<'_> {
    type Error = CountedAdmissionError;

    fn work(&self, units: usize) -> Result<(), Self::Error> {
        self.0.admit(units, 0)
    }
    fn zeros(&self, len: usize) -> Result<Vec<bool>, Self::Error> {
        // Match exact-size model collection and vec![false; len] capacities.
        self.0.admit(len, 0)?; // eventual scratch/returned-buffer retirement
        let mut values = crate::counted_storage::try_reserved_exact(self.0, len)?;
        self.0.admit(len, 0)?; // element initialization
        values.resize(len, false);
        Ok(values)
    }
    fn resize(&self, values: &mut Vec<bool>, len: usize) -> Result<(), Self::Error> {
        self.0.admit(1, 0)?;
        let additional = len.saturating_sub(values.len());
        // Reserve the real replacement, then prepay initialization, moves and
        // eventual disposal even when a later observer refuses publication.
        let retirement = len
            .checked_add(values.len())
            .ok_or_else(|| self.0.refuse(CountedAdmissionError::WorkExhausted))?;
        self.0.admit(retirement, 0)?;
        crate::counted_storage::try_reserve(self.0, values, additional)?;
        values.resize(len, false);
        Ok(())
    }
    fn witness_postcondition(
        &self,
        model: &[bool],
        _: &[crate::Literal],
        clause: &[crate::Literal],
    ) -> Result<(), Self::Error> {
        self.0.admit(1, 0)?;
        if super::replay::clause_satisfied_admitted(clause, model, self)? {
            Ok(())
        } else {
            Err(crate::decision_trace::counted_decision::invalid(
                self.0,
                "counted SAT model violates the original model contract",
            ))
        }
    }
}
