// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict proof-kind recognition for injected datatype axioms.

use ay_core::{TermId, TermStore, TheoryLemmaKind};

use crate::executor::Executor;

impl Executor {
    /// Record a typed injected axiom after strict recognition succeeds.
    pub(super) fn record_recognized_dt_axiom(&mut self, axiom: TermId, kind: TheoryLemmaKind) {
        let _ = self
            .proof_tracker
            .add_theory_lemma_with_kind(vec![axiom], kind);
        self.injected_axiom_theory_kinds.insert(axiom, kind);
    }
}

/// Classify only when the strict checker's own recognizer accepts the clause.
/// Specific schemas precede the bounded ground refuter so they retain their
/// precise kind.
pub(super) fn recognized_axiom_kind(
    terms: &TermStore,
    clause: &[TermId],
    datatypes: &[(String, Vec<String>)],
    ctor_selectors: &[(String, Vec<String>)],
) -> Option<TheoryLemmaKind> {
    if ay_proof::recognize_datatype_selector_project(terms, clause, ctor_selectors) {
        return Some(TheoryLemmaKind::DatatypeSelectorProject);
    }
    if ay_proof::recognize_datatype_exhaustive(terms, clause, datatypes) {
        return Some(TheoryLemmaKind::DatatypeExhaustive);
    }
    if ay_proof::recognize_datatype_constructor_reconstruct(
        terms,
        clause,
        datatypes,
        ctor_selectors,
    ) {
        return Some(TheoryLemmaKind::DatatypeConstructorReconstruct);
    }
    if ay_proof::recognize_datatype_tester_eval_with_selectors(
        terms,
        clause,
        datatypes,
        ctor_selectors,
    ) {
        return Some(TheoryLemmaKind::DatatypeTesterEval);
    }
    if ay_proof::recognize_datatype_tester_exclusive(terms, clause, datatypes) {
        return Some(TheoryLemmaKind::DatatypeTesterExclusive);
    }
    if ay_proof::recognize_datatype_value_eq_congruence(terms, clause, datatypes, ctor_selectors) {
        return Some(TheoryLemmaKind::DatatypeValueEqCongruence);
    }
    if ay_proof::recognize_datatype_acyclic_direct(terms, clause, datatypes) {
        return Some(TheoryLemmaKind::DatatypeAcyclicDirect);
    }
    if ay_proof::recognize_euf_congruent(terms, clause) {
        return Some(TheoryLemmaKind::EufCongruent);
    }
    if ay_proof::recognize_euf_congruent_pred(terms, clause) {
        return Some(TheoryLemmaKind::EufCongruentPred);
    }
    if ay_proof::recognize_euf_transitive(terms, clause) {
        return Some(TheoryLemmaKind::EufTransitive);
    }
    if ay_proof::recognize_euf_reflexive(terms, clause) {
        return Some(TheoryLemmaKind::EufReflexive);
    }
    if ay_proof::recognize_array_guarded_row_expansion(terms, clause) {
        return Some(TheoryLemmaKind::ArrayGuardedRowExpansion);
    }
    // Preserve the historical EUF labels above when a congruence clause also
    // happens to fit an array-row sub-schema.  The remaining context-free
    // array kinds are admitted only when the strict array recognizer itself
    // accepts the recorded clause.
    if let Some(kind) = ay_proof::recognize_array_theory_lemma(terms, clause) {
        if matches!(
            kind,
            TheoryLemmaKind::ArraySelectStore { .. }
                | TheoryLemmaKind::ArrayStorePermutation
                | TheoryLemmaKind::ArrayRowChain
                | TheoryLemmaKind::ArrayDefaultConst
                | TheoryLemmaKind::ArrayFiniteSelectExpansion
                | TheoryLemmaKind::ArrayFiniteExtensionality
        ) {
            return Some(kind);
        }
    }
    ay_proof::recognize_datatype_ground_conflict(terms, clause, datatypes, ctor_selectors)
        .then_some(TheoryLemmaKind::DatatypeGroundConflict)
}

#[cfg(test)]
mod tests {
    use ay_core::{ArraySort, Sort, Symbol};

    use super::*;

    fn int_array_sort(index_sort: Sort) -> Sort {
        Sort::Array(Box::new(ArraySort::new(index_sort, Sort::Int)))
    }

    #[test]
    fn recognizes_strict_row1_array_leaf() {
        let mut terms = TermStore::new();
        let array_sort = int_array_sort(Sort::Int);
        let array = terms.mk_var("array", array_sort);
        let index = terms.mk_var("index", Sort::Int);
        let value = terms.mk_var("value", Sort::Int);
        let store = terms.mk_store(array, index, value);
        // Preserve the primitive ROW1 syntax: `mk_select` folds this exact read
        // to `value` before the proof recognizer can inspect it.
        let select = terms.mk_app(Symbol::named("select"), [store, index], Sort::Int);
        let row1 = terms.mk_eq(select, value);

        assert_eq!(
            recognized_axiom_kind(&terms, &[row1], &[], &[]),
            Some(TheoryLemmaKind::ArraySelectStore { index_eq: true })
        );
    }

    #[test]
    fn recognizes_complete_bool_finite_extensionality_leaf() {
        let mut terms = TermStore::new();
        let array_sort = int_array_sort(Sort::Bool);
        let left = terms.mk_var("left", array_sort.clone());
        let right = terms.mk_var("right", array_sort);
        let false_index = terms.mk_bool(false);
        let true_index = terms.mk_bool(true);
        let array_equality = terms.mk_eq(left, right);
        let left_false = terms.mk_select(left, false_index);
        let right_false = terms.mk_select(right, false_index);
        let false_cell = terms.mk_eq(left_false, right_false);
        let left_true = terms.mk_select(left, true_index);
        let right_true = terms.mk_select(right, true_index);
        let true_cell = terms.mk_eq(left_true, right_true);
        let pointwise = terms.mk_and(vec![false_cell, true_cell]);
        let extensionality = terms.mk_eq(array_equality, pointwise);

        assert_eq!(
            recognized_axiom_kind(&terms, &[extensionality], &[], &[]),
            Some(TheoryLemmaKind::ArrayFiniteExtensionality)
        );
    }

    #[test]
    fn declines_skolemized_extensionality_without_witness_provenance() {
        let mut terms = TermStore::new();
        let array_sort = int_array_sort(Sort::Int);
        let left = terms.mk_var("left", array_sort.clone());
        let right = terms.mk_var("right", array_sort);
        let witness = terms.mk_var("witness", Sort::Int);
        let array_equality = terms.mk_eq(left, right);
        let left_read = terms.mk_select(left, witness);
        let right_read = terms.mk_select(right, witness);
        let read_equality = terms.mk_eq(left_read, right_read);
        let read_disequality = terms.mk_not(read_equality);
        let extensionality = terms.mk_or(vec![array_equality, read_disequality]);

        assert!(
            ay_proof::recognize_array_extensionality(&terms, &[extensionality]).is_some(),
            "the negative must exercise an exact extensionality shape"
        );
        assert_eq!(
            recognized_axiom_kind(&terms, &[extensionality], &[], &[]),
            None,
            "shape alone cannot authenticate a fresh difference witness"
        );
    }

    #[test]
    fn preserves_euf_label_for_overlapping_select_congruence() {
        let mut terms = TermStore::new();
        let array_sort = int_array_sort(Sort::Int);
        let left = terms.mk_var("left", array_sort.clone());
        let right = terms.mk_var("right", array_sort);
        let index = terms.mk_var("index", Sort::Int);
        let roots_equal = terms.mk_eq(left, right);
        let premise = terms.mk_not(roots_equal);
        let left_read = terms.mk_select(left, index);
        let right_read = terms.mk_select(right, index);
        let conclusion = terms.mk_eq(left_read, right_read);
        let clause = [premise, conclusion];

        assert_eq!(
            ay_proof::recognize_array_theory_lemma(&terms, &clause),
            Some(TheoryLemmaKind::ArrayRowChain),
            "the ordering regression must exercise an overlapping array schema"
        );
        assert!(ay_proof::recognize_euf_congruent(&terms, &clause));
        assert_eq!(
            recognized_axiom_kind(&terms, &clause, &[], &[]),
            Some(TheoryLemmaKind::EufCongruent),
            "adding array attribution must not churn historical EUF labels"
        );
    }

    #[test]
    fn recognizes_guarded_row_expansion_leaf() {
        let mut terms = TermStore::new();
        let array_sort = int_array_sort(Sort::Int);
        let read_array = terms.mk_var("read_array", array_sort.clone());
        let base_array = terms.mk_var("base_array", array_sort.clone());
        let store_index = terms.mk_var("store_index", Sort::Int);
        let probe_index = terms.mk_var("probe_index", Sort::Int);
        let value = terms.mk_var("value", Sort::Int);
        let store = terms.mk_app(
            Symbol::named("store"),
            [base_array, store_index, value],
            array_sort,
        );
        let guarded_equality = terms.mk_eq(read_array, store);
        let guard = terms.mk_not(guarded_equality);
        let condition = terms.mk_eq(store_index, probe_index);
        let read = terms.mk_select(read_array, probe_index);
        let base_read = terms.mk_select(base_array, probe_index);
        let stored_case = terms.mk_eq(value, read);
        let untouched_case = terms.mk_eq(base_read, read);
        let expansion = terms.mk_ite_raw(condition, stored_case, untouched_case);
        let axiom = terms.mk_or(vec![guard, expansion]);

        assert!(ay_proof::recognize_array_guarded_row_expansion(
            &terms,
            &[axiom]
        ));
        assert_eq!(
            ay_proof::recognize_array_theory_lemma(&terms, &[axiom]),
            None,
            "the dedicated guarded-row schema must not depend on the general recognizer"
        );
        assert_eq!(
            recognized_axiom_kind(&terms, &[axiom], &[], &[]),
            Some(TheoryLemmaKind::ArrayGuardedRowExpansion)
        );
    }
}
