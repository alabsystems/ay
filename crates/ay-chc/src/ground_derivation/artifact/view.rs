// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Allocation-free playback of a validated ground-derivation snapshot.

use super::{ChcValidatedGroundDerivation, GroundDerivationStep, SmtValue};

/// A borrowed step from one validated ground-derivation snapshot.
///
/// Clause indices refer to the original source order authenticated by
/// [`ChcValidatedGroundDerivation::source_clause_sequence_sha256`]. The view
/// grants no authority for a different or subsequently mutated problem. Keep
/// the snapshot paired with its authenticated source hashes and revalidate at
/// each deserialization or trust boundary.
///
/// Values retain their exact [`SmtValue`] representation, including wide
/// integers, wide bitvectors, and nested array entry order and duplicates.
/// Accessors neither clone nor allocate. Private evaluator metadata, including
/// finite-UF observations and their marker keys, is not a source binding and is
/// excluded. This type has no public constructor, mutator, or serialization.
///
/// A view cannot outlive its validated snapshot:
///
/// ```compile_fail
/// use ay_chc::{ChcGroundDerivationStepView, ChcValidatedGroundDerivation};
/// fn escape(snapshot: ChcValidatedGroundDerivation) -> ChcGroundDerivationStepView<'static> {
///     snapshot.step(0).unwrap()
/// }
/// ```
///
/// A caller cannot construct a view without a validated snapshot:
///
/// ```compile_fail
/// use ay_chc::ChcGroundDerivationStepView;
/// let fabricated = ChcGroundDerivationStepView {};
/// ```
///
/// Borrowed values cannot be mutated through the view:
///
/// ```compile_fail
/// use ay_chc::{ChcGroundDerivationStepView, SmtValue};
/// fn mutate(view: ChcGroundDerivationStepView<'_>) {
///     *view.source_binding("x").unwrap() = SmtValue::Int(0);
/// }
/// ```
pub struct ChcGroundDerivationStepView<'a> {
    step: &'a GroundDerivationStep,
}

impl ChcValidatedGroundDerivation {
    /// Borrow one validated step, or return `None` when `index` is out of range.
    ///
    /// The view refers only to this snapshot and does not authenticate a new or
    /// mutated source problem. No values are cloned or allocated.
    pub fn step(&self, index: usize) -> Option<ChcGroundDerivationStepView<'_>> {
        self.derivation
            .steps
            .get(index)
            .map(|step| ChcGroundDerivationStepView { step })
    }

    /// Borrow all steps in their validated derivation order, without allocation.
    ///
    /// Premises precede their consumers. This is not a source-clause sort: a
    /// source clause may occur in multiple derivation steps.
    pub fn steps(&self) -> impl ExactSizeIterator<Item = ChcGroundDerivationStepView<'_>> + '_ {
        self.derivation
            .steps
            .iter()
            .map(|step| ChcGroundDerivationStepView { step })
    }
}

impl<'a> ChcGroundDerivationStepView<'a> {
    /// Index of this step's clause in the authenticated original source order.
    pub fn clause_index(&self) -> usize {
        self.step.clause_index
    }

    /// Validated premise step indices, in body-predicate order.
    ///
    /// Repeated premise indices are preserved; no sorting or deduplication occurs.
    pub fn premises(&self) -> &'a [usize] {
        &self.step.premises
    }

    /// Borrow the exact value bound to a source-variable name.
    ///
    /// Missing names and all NUL-prefixed private evaluator names return `None`.
    pub fn source_binding(&self, name: &str) -> Option<&'a SmtValue> {
        if name.starts_with('\0') {
            return None;
        }
        self.step.env.get(name)
    }

    /// Borrow all source-variable bindings; iteration order is unspecified.
    ///
    /// NUL-prefixed private evaluator names are excluded. Names and values are
    /// borrowed unchanged; this is not the canonical wire binding order.
    pub fn source_bindings(&self) -> impl Iterator<Item = (&'a str, &'a SmtValue)> + 'a {
        self.step
            .env
            .iter()
            .filter(|(name, _)| !name.starts_with('\0'))
            .map(|(name, value)| (name.as_str(), value))
    }
}

#[cfg(test)]
mod tests;
