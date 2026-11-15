// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prepaid query-view preparation, not native execution admission.

use super::{Context, InternalQueryWindow, PublicAssertionMetadata};
use ay_core::original_query::{QueryError, WorkBudget};
use ay_core::{Sort, TermId};
use std::mem::size_of;
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};

impl Context {
    /// Run a query-view transaction using the caller's SAME work/copy sink.
    ///
    /// Only root validation, new root/default-metadata buffers and query-view
    /// moves are priced here. The operation must separately prepay its own
    /// construction, solving, proof checks and temporary-state disposal. This
    /// method does not attach an owner to a solver or authorize any verdict.
    ///
    /// Saved outer query state is restored before returning or resuming an
    /// unwind. In particular, no active saved window escapes to an original
    /// owner's later fallible final poll. The operation returns unit, not a
    /// model, proof or result capability. Callers still validate their own
    /// source/term stamps and perform their final owner poll AFTER any later
    /// child disposal. For sticky operation-panic handling, the caller uses
    /// its existing OriginalAdmission::with_work scope, not a fresh grant.
    #[doc(hidden)]
    pub fn with_internal_query_window_with_work(
        &mut self,
        roots: &[TermId],
        work: &mut WorkBudget<'_>,
        operation: impl FnOnce(&mut Context, &mut WorkBudget<'_>) -> Result<(), QueryError>,
    ) -> Result<(), QueryError> {
        let (roots, metadata) = prepare(self, roots, work)?;
        let window = install(self, roots, metadata);
        let result = catch_unwind(AssertUnwindSafe(|| operation(self, work)));
        let restored = self.restore_internal_query_window(window);
        // Restoration has disposed of the temporary query-local fields. The
        // caller must have prepaid any payloads it installed in those fields.
        match result {
            Err(payload) => resume_unwind(payload),
            Ok(result) => {
                let final_poll = work.charge(0);
                result?;
                final_poll?;
                if !restored {
                    return Err(QueryError::Invalid(
                        "query window source or term prefix changed",
                    ));
                }
                Ok(())
            }
        }
    }
}

fn storage_bytes(count: usize) -> Option<usize> {
    let row = size_of::<TermId>().checked_add(size_of::<PublicAssertionMetadata>())?;
    // Two exact requested-capacity buffers, one fill and eventual disposal;
    // the factor four is a logical-copy upper bound, not allocator/RSS sizing.
    let payload = count.checked_mul(row)?.checked_mul(4)?;
    let fixed = size_of::<InternalQueryWindow>()
        .checked_mul(4)?
        .checked_add(256)?;
    payload.checked_add(fixed)
}

fn prepare(
    context: &Context,
    roots: &[TermId],
    work: &mut WorkBudget<'_>,
) -> Result<(Vec<TermId>, Vec<PublicAssertionMetadata>), QueryError> {
    work.charge(0)?;
    let bytes = storage_bytes(roots.len()).ok_or_else(|| work.refuse_exhaustion())?;
    work.admit(256, bytes)?;
    for &root in roots {
        work.charge(128)?;
        if context.terms.entry_stamp(root).is_none() {
            return Err(QueryError::Invalid("query window root is not live"));
        }
        if !matches!(context.terms.sort(root), Sort::Bool) {
            return Err(QueryError::Invalid("query window root is not Boolean"));
        }
    }
    let mut copied = Vec::new();
    let mut metadata = Vec::new();
    copied
        .try_reserve_exact(roots.len())
        .map_err(|_| work.refuse_exhaustion())?;
    metadata
        .try_reserve_exact(roots.len())
        .map_err(|_| work.refuse_exhaustion())?;
    for &root in roots {
        work.charge(0)?;
        copied.push(root);
        metadata.push(PublicAssertionMetadata::default());
    }
    // Every row's validation, copy, default metadata and both refusal/success
    // disposal paths were prepaid before any allocation or fill. No callback
    // can inspect/mutate the borrowed Context during those constant-size moves.
    work.charge(0)?;
    Ok((copied, metadata))
}

fn install(
    context: &mut Context,
    roots: Vec<TermId>,
    metadata: Vec<PublicAssertionMetadata>,
) -> InternalQueryWindow {
    InternalQueryWindow {
        source_context_stamp: context.source_context_stamp(),
        term_prefix: context.terms.snapshot_stamp(),
        assertions: std::mem::replace(&mut context.assertions, roots),
        assertion_finite_set_metadata: std::mem::replace(
            &mut context.assertion_finite_set_metadata,
            metadata,
        ),
        assertions_parsed: std::mem::take(&mut context.assertions_parsed),
        parsed_retention: context.parsed_retention.suspend(),
        pass_parsed_assertions: std::mem::take(&mut context.definitional_pass.parsed),
        objectives: std::mem::take(&mut context.objectives),
        objective_finite_set_metadata: std::mem::take(&mut context.objective_finite_set_metadata),
        soft_constraints: std::mem::take(&mut context.soft_constraints),
        soft_finite_set_metadata: std::mem::take(&mut context.soft_finite_set_metadata),
        objective_sequence: std::mem::take(&mut context.objective_sequence),
        named_terms: std::mem::take(&mut context.named_terms),
        polymorphic_assertions: std::mem::take(&mut context.polymorphic_assertions),
        authored_assertions: std::mem::take(&mut context.authored_assertions),
        materialized_polymorphic_assertions: std::mem::replace(
            &mut context.materialized_polymorphic_assertions,
            0,
        ),
        polymorphic_instantiation_complete: std::mem::replace(
            &mut context.polymorphic_instantiation_complete,
            true,
        ),
    }
}

#[cfg(test)]
mod tests;
