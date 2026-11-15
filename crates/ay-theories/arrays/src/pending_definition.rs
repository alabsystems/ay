// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unresolved array substitutions are model data, separate from read conflicts.

use super::{ArrayModel, Sort, TermId, TermStore};
use ay_core::term::{TermData, TermEntryStamp};

const MAX_PENDING_DEFINITIONS: usize = 4096;
const MAX_SORT_WORK: usize = 1024;
const MAX_SORT_DEPTH: usize = 64;
const MAX_SORT_NAME_BYTES: usize = 256;

/// The exact, birth-stamped endpoints of an unresolved array substitution.
///
/// This records a candidate definition, never a checked model or source grant.
/// Term entry identities bind both the expression and its immutable full sort;
/// no recursive sort clone is needed to retain that identity. A consumer must
/// additionally authenticate the current query's recorded substitution edge.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PendingArrayDefinition {
    source: TermId,
    target: TermId,
    source_stamp: TermEntryStamp,
    target_stamp: TermEntryStamp,
}

impl PendingArrayDefinition {
    /// Source variable whose old interpretation is withheld.
    #[must_use]
    pub fn source(self) -> TermId {
        self.source
    }

    /// Exact replacement expression recorded by the producer.
    #[must_use]
    pub fn target(self) -> TermId {
        self.target
    }

    /// Authenticate both live term entries and their exact array sort.
    #[must_use]
    pub fn matches_current(self, terms: &TermStore) -> bool {
        // Capture checked the full sorts. A birth stamp authenticates the
        // immutable (expression, full sort) entry, so matching BOTH stamps
        // preserves that relation without repeating a recursive sort walk on
        // every fixpoint lookup. A reused/compacted slot gets a fresh stamp.
        terms.entry_stamp(self.source) == Some(self.source_stamp)
            && terms.entry_stamp(self.target) == Some(self.target_stamp)
    }

    fn capture(terms: &TermStore, source: TermId, target: TermId) -> Option<Self> {
        let source_stamp = terms.entry_stamp(source)?;
        let target_stamp = terms.entry_stamp(target)?;
        if source == target
            || !matches!(terms.get(source), TermData::Var(_, _))
            || !same_array_sort(terms.sort(source), terms.sort(target))
        {
            return None;
        }
        Some(Self {
            source,
            target,
            source_stamp,
            target_stamp,
        })
    }
}

impl ArrayModel {
    /// Whether an interpretation is withheld by a protected conflict OR an
    /// unresolved definition. Removing a pending record never removes a conflict.
    #[must_use]
    pub fn is_withheld(&self, term: &TermId) -> bool {
        self.read_conflicted.contains(term)
            || self.pending_definitions.contains_key(term)
            || self.pending_definition_dependents.contains(term)
    }

    /// Whether any array interpretation is currently withheld.
    #[must_use]
    pub fn has_withheld_arrays(&self) -> bool {
        !self.read_conflicted.is_empty()
            || !self.pending_definitions.is_empty()
            || !self.pending_definition_dependents.is_empty()
    }

    /// All withheld term IDs. A term with both reasons may occur twice.
    pub fn withheld_arrays(&self) -> impl Iterator<Item = &TermId> {
        self.read_conflicted
            .iter()
            .chain(self.pending_definitions.keys())
            .chain(self.pending_definition_dependents.iter())
    }

    /// Withhold a real same-sort substitution until its RHS has a complete
    /// interpretation. Unsupported or excessive provenance stays protected and
    /// cannot be discharged by the late pending-definition recovery path.
    pub fn defer_array_definition(&mut self, terms: &TermStore, source: TermId, target: TermId) {
        if self.read_conflicted.contains(&source) {
            return;
        }
        let Some(record) = PendingArrayDefinition::capture(terms, source, target) else {
            self.read_conflicted.insert(source);
            return;
        };
        if let Some(previous) = self.pending_definitions.get(&source) {
            if previous != &record {
                self.read_conflicted.insert(source);
            }
            return;
        }
        if self.pending_definitions.len() >= MAX_PENDING_DEFINITIONS {
            self.read_conflicted.insert(source);
            return;
        }
        self.pending_definitions.insert(source, record);
    }

    /// Remove only the exact pending record after a complete RHS interpretation
    /// has been installed. A protected conflict, stale birth or changed target
    /// keeps the source withheld. This grants no solve/publication authority.
    pub fn discharge_array_definition(
        &mut self,
        terms: &TermStore,
        source: TermId,
        target: TermId,
    ) -> bool {
        if self.read_conflicted.contains(&source) {
            return false;
        }
        let Some(record) = self.pending_definitions.get(&source).copied() else {
            return false;
        };
        if record.target != target || !record.matches_current(terms) {
            return false;
        }
        self.pending_definitions.remove(&source);
        true
    }
}

fn same_array_sort(left: &Sort, right: &Sort) -> bool {
    matches!((left, right), (Sort::Array(_), Sort::Array(_)))
        && same_sort(left, right, &mut MAX_SORT_WORK, 0)
}

fn same_sort(left: &Sort, right: &Sort, work: &mut usize, depth: usize) -> bool {
    if *work == 0 || depth >= MAX_SORT_DEPTH {
        return false;
    }
    *work -= 1;
    match (left, right) {
        (Sort::Bool, Sort::Bool)
        | (Sort::Int, Sort::Int)
        | (Sort::Real, Sort::Real)
        | (Sort::String, Sort::String)
        | (Sort::RegLan, Sort::RegLan)
        | (Sort::Char, Sort::Char)
        | (Sort::Complex, Sort::Complex) => true,
        (Sort::BitVec(a), Sort::BitVec(b)) => a.width == b.width,
        (Sort::FloatingPoint(a, b), Sort::FloatingPoint(c, d)) => a == c && b == d,
        (Sort::Uninterpreted(a), Sort::Uninterpreted(b)) | (Sort::TypeVar(a), Sort::TypeVar(b)) => {
            a.len() <= MAX_SORT_NAME_BYTES && b.len() <= MAX_SORT_NAME_BYTES && a == b
        }
        (Sort::FiniteDomain(a, n), Sort::FiniteDomain(b, m)) => {
            a.len() <= MAX_SORT_NAME_BYTES && b.len() <= MAX_SORT_NAME_BYTES && a == b && n == m
        }
        (Sort::Array(a), Sort::Array(b)) => {
            same_sort(&a.index_sort, &b.index_sort, work, depth + 1)
                && same_sort(&a.element_sort, &b.element_sort, work, depth + 1)
        }
        (Sort::Seq(a), Sort::Seq(b)) => same_sort(a, b, work, depth + 1),
        // Inline schemas and unknown future variants retain protected
        // withholding; this new recovery path never clones a schema.
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ArrayInterpretation;
    use ay_core::original_query::WorkBudget;
    use std::ops::ControlFlow;

    fn fixture() -> (TermStore, TermId, TermId, TermId) {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::bitvec(8), Sort::Uninterpreted("Cell".into()));
        let source = terms.mk_var("source", sort.clone());
        let target = terms.mk_var("target", sort.clone());
        let other = terms.mk_var("other", sort);
        (terms, source, target, other)
    }

    #[test]
    fn unresolved_definition_withholds_old_data_without_inventing_a_read_conflict() {
        let (terms, source, target, _) = fixture();
        let mut model = ArrayModel::default();
        let old = ArrayInterpretation {
            default: Some("old decoupled spelling".into()),
            ..Default::default()
        };
        model.array_values.insert(source, old.clone());
        model.defer_array_definition(&terms, source, target);
        assert!(model.is_withheld(&source));
        assert!(!model.read_conflicted.contains(&source));
        assert_eq!(model.array_values.get(&source), Some(&old));
        let pending = model.pending_definitions[&source];
        assert_eq!(pending.target(), target);
        assert!(pending.matches_current(&terms));
        assert!(model.clone().is_withheld(&source));
    }

    #[test]
    fn true_conflict_added_after_pending_capture_cannot_be_discharged() {
        let (terms, source, target, _) = fixture();
        let mut model = ArrayModel::default();
        model.defer_array_definition(&terms, source, target);
        let pending = model.pending_definitions[&source];
        model.read_conflicted.insert(source);
        assert!(!model.discharge_array_definition(&terms, source, target));
        assert!(model.read_conflicted.contains(&source));
        assert_eq!(model.pending_definitions.get(&source), Some(&pending));
        assert!(model.is_withheld(&source));
    }

    #[test]
    fn wrong_target_cannot_discharge_an_exact_pending_edge() {
        let (terms, source, target, other) = fixture();
        let mut model = ArrayModel::default();
        model.defer_array_definition(&terms, source, target);
        assert!(!model.discharge_array_definition(&terms, source, other));
        assert!(model.is_withheld(&source));
        assert!(model.discharge_array_definition(&terms, source, target));
        assert!(!model.is_withheld(&source));
        assert!(model.read_conflicted.is_empty());
    }

    #[test]
    fn reused_target_slot_does_not_resurrect_pending_provenance() {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::Int, Sort::Int);
        let source = terms.mk_var("source", sort.clone());
        let checkpoint = terms.rollback_checkpoint();
        let target = terms.mk_var("discarded", sort.clone());
        let mut model = ArrayModel::default();
        model.defer_array_definition(&terms, source, target);
        let pending = model.pending_definitions[&source];
        terms.rollback_to(checkpoint);
        let reused = terms.mk_var("different", sort);
        assert_eq!(reused, target);
        assert!(!pending.matches_current(&terms));
        assert!(!model.discharge_array_definition(&terms, source, reused));
        assert_eq!(model.pending_definitions.get(&source), Some(&pending));
    }

    #[test]
    fn incompatible_or_conflicting_pending_definitions_stay_protected() {
        let (mut terms, source, target, other) = fixture();
        let wrong = terms.mk_var("wrong", Sort::array(Sort::Int, Sort::Int));
        let mut wrong_sort = ArrayModel::default();
        wrong_sort.defer_array_definition(&terms, source, wrong);
        assert!(wrong_sort.read_conflicted.contains(&source));
        assert!(!wrong_sort.pending_definitions.contains_key(&source));

        let mut conflicting = ArrayModel::default();
        conflicting.defer_array_definition(&terms, source, target);
        conflicting.defer_array_definition(&terms, source, other);
        assert!(conflicting.read_conflicted.contains(&source));
        assert!(!conflicting.discharge_array_definition(&terms, source, target));
    }

    #[test]
    fn excessive_sort_work_preserves_protected_withholding() {
        let mut terms = TermStore::new();
        let mut nested = Sort::Int;
        for _ in 0..MAX_SORT_DEPTH {
            nested = Sort::Seq(Box::new(nested));
        }
        let sort = Sort::array(Sort::Int, nested);
        let source = terms.mk_var("source", sort.clone());
        let target = terms.mk_var("target", sort);
        let mut model = ArrayModel::default();
        model.defer_array_definition(&terms, source, target);
        assert!(model.read_conflicted.contains(&source));
        assert!(model.pending_definitions.is_empty());
    }

    #[test]
    fn controlled_copy_preserves_both_independent_withholding_reasons() {
        let (terms, source, target, other) = fixture();
        let mut model = ArrayModel::default();
        model.defer_array_definition(&terms, source, target);
        model.read_conflicted.insert(other);
        model.pending_definition_dependents.insert(target);
        let mut checkpoint = || ControlFlow::Continue(());
        let mut work = WorkBudget::new(1_000_000, &mut checkpoint);
        let copy = model
            .try_clone_with_budget(&mut work)
            .expect("bounded small data");
        assert_eq!(copy.pending_definitions, model.pending_definitions);
        assert_eq!(copy.read_conflicted, model.read_conflicted);
        assert_eq!(
            copy.pending_definition_dependents,
            model.pending_definition_dependents
        );
        assert!(copy.is_withheld(&source));
        assert!(copy.is_withheld(&other));
        assert!(copy.is_withheld(&target));
    }
}
