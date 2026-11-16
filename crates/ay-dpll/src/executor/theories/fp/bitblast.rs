// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP encoding and SAT bit-blasting for predicate linking.

#[cfg(test)]
use ay_core::Sort;
#[cfg(test)]
use ay_core::TermId;
#[cfg(test)]
use ay_fp::FpSolver;

#[cfg(test)]
use super::super::super::Executor;
use super::support::FpPredicateResult;

#[path = "bitblast/backend.rs"]
pub(super) mod backend;
#[path = "bitblast/dispatch.rs"]
mod dispatch;
#[path = "bitblast/to_real_encoding.rs"]
mod to_real_encoding;

#[cfg(test)]
#[path = "bitblast/tests.rs"]
mod tests;

pub(super) use dispatch::bitblast_fp_predicate_controlled;
pub(super) use to_real_encoding::FpRealEncodingError;

#[cfg(test)]
impl Executor {
    /// Try to bitblast a term as an FP predicate using the shared classifier.
    #[cfg(test)]
    pub(super) fn bitblast_fp_predicate(
        &self,
        fp_solver: &mut FpSolver<'_>,
        term: TermId,
    ) -> FpPredicateResult {
        backend::infallible(dispatch::dispatch(&self.ctx.terms, fp_solver, term))
    }
}
