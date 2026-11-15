// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared admission policy for actual root materialization. No proof IDs are
//! manufactured on the trace-only lane: the ordinary emission funnel returns
//! zero without a writer. Unit reasons keep their existing stable IDs.

use super::*;
use crate::counted_storage::{try_reserve, Result as AdmissionResult};
use crate::decision_trace::counted_decision::invalid;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, OriginalAdmissionError};
use std::convert::Infallible;

mod counted;
pub(in crate::solver) use counted::Counted;
mod scratch;
pub(super) use scratch::Scratch;
#[cfg(test)]
mod tests;

pub(in crate::solver) struct Ordinary;

pub(in crate::solver) trait Policy {
    type Error;
    fn owner(&self) -> Option<&CountedAdmission>;
    fn enter(&self, s: &mut Solver) -> Result<(), Self::Error>;
    fn work(&self, n: usize) -> Result<(), Self::Error>;
    fn reserve<T>(&self, values: &mut Vec<T>, n: usize) -> Result<(), Self::Error>;
    fn record(&self, s: &mut Solver, lit: Literal) -> Result<(), Self::Error>;
}

impl Policy for Ordinary {
    type Error = Infallible;
    fn owner(&self) -> Option<&CountedAdmission> {
        None
    }
    fn enter(&self, _: &mut Solver) -> Result<(), Infallible> {
        Ok(())
    }
    fn work(&self, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    fn reserve<T>(&self, _: &mut Vec<T>, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    fn record(&self, _: &mut Solver, _: Literal) -> Result<(), Infallible> {
        Ok(())
    }
}
