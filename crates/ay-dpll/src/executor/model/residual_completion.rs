// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Transactional installation of replayed array DATA, never SAT authority.

use ay_core::term::{TermData, TermEntryStamp};
use ay_core::{Sort, TermId};
use ay_frontend::{Context, SourceContextStamp};
use ay_model_check::{CompletedArrayAssignment, ModelValue};
use std::sync::Arc;

use super::{eval_memo_clear, scoped_term_evaluation_override_active, Model};

mod constant_functions;
pub(super) use constant_functions::{ConstantArrayFunction, ConstantArrayFunctions};

// Match the existing producer's member ceiling. A caller can concatenate
// several independently extracted batches, so authenticate the bound again
// before allocating or sorting the destination transaction.
const MAX_MEMBERS: usize = 256;

#[derive(Debug, Clone)]
pub(super) struct ResidualArrayModel {
    source: SourceContextStamp,
    // Sorted, bounded by the producer's shared witness budget. Aliases retain
    // one Arc value, not a deep copy of each complete nested record array.
    entries: Vec<(TermId, TermEntryStamp, Arc<ModelValue>)>,
    constant_functions: Option<Arc<ConstantArrayFunctions>>,
}

#[derive(Debug, thiserror::Error)]
pub(super) enum ResidualCompletionError {
    #[error("residual completion cannot be installed in a contextual evaluation")]
    ContextualEvaluation,
    #[error("residual completion contains no assignments")]
    Empty,
    #[error("residual completion exceeds the bounded member allowance")]
    TooManyMembers,
    #[error("residual completion names a stale or non-array variable")]
    InvalidMember,
    #[error("residual completion contains a duplicate member")]
    DuplicateMember,
    #[error("residual completion allocation was refused")]
    Allocation,
}

impl Model {
    /// Validate the entire sealed data batch before replacing model state.
    ///
    /// The producer has already checked each complete value against the term's
    /// exact sort. Entry birth identities bind those immutable sorts here. The
    /// caller MUST then run a new residual-disabled check over the complete
    /// original query, including quantified roots, before publishing SAT.
    /// This method deliberately creates neither a verdict nor a model seal.
    pub(super) fn install_residual_arrays(
        &mut self,
        ctx: &Context,
        assignments: Vec<CompletedArrayAssignment>,
    ) -> Result<(), ResidualCompletionError> {
        if scoped_term_evaluation_override_active() {
            return Err(ResidualCompletionError::ContextualEvaluation);
        }
        if assignments.is_empty() {
            return Err(ResidualCompletionError::Empty);
        }
        if assignments.len() > MAX_MEMBERS {
            return Err(ResidualCompletionError::TooManyMembers);
        }
        let mut entries = Vec::new();
        entries
            .try_reserve_exact(assignments.len())
            .map_err(|_| ResidualCompletionError::Allocation)?;
        for assignment in assignments {
            let (term, stamp, value) = assignment.into_parts();
            if ctx.terms.entry_stamp(term) != Some(stamp)
                || !matches!(ctx.terms.get(term), TermData::Var(..))
                || !matches!(ctx.terms.sort(term), Sort::Array(_))
                || !matches!(value.as_ref(), ModelValue::Array(_))
            {
                return Err(ResidualCompletionError::InvalidMember);
            }
            entries.push((term, stamp, value));
        }
        entries.sort_unstable_by_key(|(term, _, _)| *term);
        if entries.windows(2).any(|pair| pair[0].0 == pair[1].0) {
            return Err(ResidualCompletionError::DuplicateMember);
        }
        let package = ResidualArrayModel {
            source: ctx.source_context_stamp(),
            entries,
            constant_functions: self
                .residual_arrays
                .as_ref()
                .filter(|prior| prior.source == ctx.source_context_stamp())
                .and_then(|prior| prior.constant_functions.clone()),
        };
        self.revoke_all_quantified_model_seals();
        self.residual_arrays = Some(package);
        eval_memo_clear();
        Ok(())
    }

    pub(super) fn has_residual_arrays(&self) -> bool {
        self.residual_arrays.is_some()
    }

    /// Adding query-expression AST nodes is allowed. Declaration/assertion
    /// scope changes or recycling ANY owned member invalidate the whole batch.
    pub(super) fn residual_arrays_are_current(&self, ctx: &Context) -> bool {
        self.residual_arrays.as_ref().is_none_or(|package| {
            package.source == ctx.source_context_stamp()
                && package
                    .entries
                    .iter()
                    .all(|(term, stamp, _)| ctx.terms.entry_stamp(*term) == Some(*stamp))
        })
    }

    pub(super) fn residual_array_value(
        &self,
        ctx: &Context,
        term: TermId,
    ) -> Result<Option<&ModelValue>, ()> {
        if !self.residual_arrays_are_current(ctx) {
            return Err(());
        }
        let Some(package) = &self.residual_arrays else {
            return Ok(None);
        };
        Ok(package
            .entries
            .binary_search_by_key(&term, |(member, _, _)| *member)
            .ok()
            .map(|index| package.entries[index].2.as_ref()))
    }
}

#[cfg(test)]
mod tests;
