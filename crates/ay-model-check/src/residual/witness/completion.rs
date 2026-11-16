// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retain one exact replayed extension, without exporting a SAT capability.

use super::*;
use ay_core::term::TermEntryStamp;
use std::sync::Arc;

/// The ordinary gate verdict and, when needed, its exact free-array extension.
///
/// No completion is attached to a refutation, refusal, or already-complete
/// model. The borrowed extension is not an independent publication permit.
pub struct ModelConfirmation<'a> {
    verdict: GateVerdict,
    completion: Option<ArrayCompletion<'a>>,
}

impl<'a> ModelConfirmation<'a> {
    pub(crate) fn new(verdict: GateVerdict, completion: Option<ArrayCompletion<'a>>) -> Self {
        Self {
            verdict,
            completion,
        }
    }

    /// The unchanged model-check verdict.
    pub fn verdict(&self) -> &GateVerdict {
        &self.verdict
    }

    /// Consume the result. Installing completion data requires a new full-root
    /// check; this verdict does not authenticate a later mutated model.
    pub fn into_parts(self) -> (GateVerdict, Option<ArrayCompletion<'a>>) {
        (self.verdict, self.completion)
    }
}

/// Exact typed arrays used by the gate's residual-disabled replay.
///
/// The original term store, model and assertion slice remain borrowed. Only
/// data can escape through [`Self::into_assignments`]. A native consumer must
/// authenticate entry stamps, revoke old model-relative seals, install the
/// complete batch and freshly check all original assertions before publishing.
/// Model callbacks retain their existing contract and resource limitations;
/// this type adds no global callback, cancellation, RSS or latency guarantee.
pub struct ArrayCompletion<'a> {
    terms: &'a TermStore,
    _assertions: &'a [TermId],
    completed: CompletedModel<'a>,
    budget: WitnessBudget,
}

impl<'a> ArrayCompletion<'a> {
    pub(super) fn new(
        terms: &'a TermStore,
        assertions: &'a [TermId],
        completed: CompletedModel<'a>,
        budget: WitnessBudget,
    ) -> Self {
        Self {
            terms,
            _assertions: assertions,
            completed,
            budget,
        }
    }

    /// Extract a complete, stamped DATA batch, in increasing term-index order.
    ///
    /// Aliases share one `Arc` allocation for their class's entire value; no
    /// nested array or record payload is cloned. Conversion consumes the same
    /// bounded witness allowance and may conservatively refuse. A `None` never
    /// returns a prefix, and these values alone confer no SAT authority.
    pub fn into_assignments(mut self) -> Option<Vec<CompletedArrayAssignment>> {
        let members = self.completed.member_roots.len();
        let classes = self.completed.arrays.len();
        if members == 0 || members > super::super::MAX_WITNESS_MEMBERS || classes > members {
            return None;
        }
        let bytes = extraction_bytes(members, classes)?;
        let comparisons = members.checked_mul(members.checked_add(classes)?)?;
        let next = self.budget.index_comparisons.checked_add(comparisons)?;
        if next > MAX_INDEX_COMPARISONS || !self.budget.spend_value_nodes(bytes) {
            return None;
        }
        self.budget.index_comparisons = next;
        // Prepay both vectors, Arc headers/payload moves and bounded lookup /
        // sorting work before the first new allocation. Values were completely
        // charged and sort-checked before the original replay.
        let mut values = Vec::new();
        values.try_reserve_exact(classes).ok()?;
        let mut out = Vec::new();
        out.try_reserve_exact(members).ok()?;
        for (root, value) in self.completed.arrays {
            values.push((root, Arc::new(value)));
        }
        for (term, root) in self.completed.member_roots {
            let value = &values.iter().find(|(candidate, _)| *candidate == root)?.1;
            out.push(CompletedArrayAssignment {
                term,
                stamp: self.terms.entry_stamp(term)?,
                value: Arc::clone(value),
            });
        }
        out.sort_unstable_by_key(|assignment| assignment.term);
        Some(out)
    }
}

fn extraction_bytes(members: usize, classes: usize) -> Option<usize> {
    let member_bytes = members.checked_mul(size_of::<CompletedArrayAssignment>())?;
    // Arc owns one moved ModelValue, two reference counts and conservative
    // allocator bookkeeping, in addition to the temporary root/Arc vector.
    let class_bytes = classes.checked_mul(
        size_of::<ModelValue>()
            .checked_add(size_of::<(TermId, Arc<ModelValue>)>())?
            .checked_add(64)?,
    )?;
    member_bytes.checked_add(class_bytes)
}

/// One live array leaf and its complete typed value; DATA, not a proof token.
pub struct CompletedArrayAssignment {
    term: TermId,
    stamp: TermEntryStamp,
    value: Arc<ModelValue>,
}

impl CompletedArrayAssignment {
    /// Original array variable's exact term index.
    pub fn term(&self) -> TermId {
        self.term
    }

    /// Birth identity that must still match the destination term store.
    pub fn stamp(&self) -> TermEntryStamp {
        self.stamp
    }

    /// Complete class value, shared by every alias assignment.
    pub fn value(&self) -> &Arc<ModelValue> {
        &self.value
    }

    /// Move the data into a native model installation transaction.
    pub fn into_parts(self) -> (TermId, TermEntryStamp, Arc<ModelValue>) {
        (self.term, self.stamp, self.value)
    }
}

#[cfg(test)]
mod tests;
