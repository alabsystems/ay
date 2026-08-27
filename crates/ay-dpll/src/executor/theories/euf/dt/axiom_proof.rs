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
    ay_proof::recognize_datatype_ground_conflict(terms, clause, datatypes, ctor_selectors)
        .then_some(TheoryLemmaKind::DatatypeGroundConflict)
}
