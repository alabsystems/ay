// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::cell::Cell;

#[test]
fn document_fold_admission_cannot_reset_an_exhausted_owner() {
    let mut terms = ay_core::TermStore::new();
    let term = terms.mk_var("p", Sort::Bool);
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(0));
    assert!(!printer.folded_document_equivalence_admitted(term, "(or p false)", "p"));
    assert!(printer.work_used() > 0);
    assert!(matches!(
        printer.work_budget_error(0),
        AlethePrintError::EmissionBudgetExhausted { budget: 0, .. }
    ));
}

#[test]
fn document_fold_renderer_cannot_reset_an_exhausted_owner() {
    let mut terms = ay_core::TermStore::new();
    let term = terms.mk_var("p", Sort::Bool);
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(0));
    let (document, nodes) = printer.render_authored_assume_bridge(
        ProofId(0),
        term,
        "(or p false)",
        "p",
        AuthoredAssumeBridge::FoldedDocumentEquivalence,
    );
    assert!(document.is_none());
    assert_eq!(nodes, 0);
    assert!(printer.work_used() > 0);
}

#[test]
fn refused_document_fold_owner_stays_refused_across_admission_and_emission() {
    let mut terms = ay_core::TermStore::new();
    let term = terms.mk_var("p", Sort::Bool);
    let calls = Cell::new(0);
    let mut owner = || {
        calls.set(calls.get() + 1);
        calls.get() != 1
    };
    let printer = AlethePrinter::new(&terms).with_emission_progress(&mut owner);
    assert!(!printer.folded_document_equivalence_admitted(term, "(or p false)", "p"));
    let (document, nodes) = printer.render_authored_assume_bridge(
        ProofId(0),
        term,
        "(or p false)",
        "p",
        AuthoredAssumeBridge::FoldedDocumentEquivalence,
    );
    assert!(document.is_none());
    assert_eq!(nodes, 0);
    assert_eq!(calls.get(), 1);
    assert_eq!(printer.work_used(), 0);
    assert!(matches!(
        printer.work_budget_error(0),
        AlethePrintError::EmissionStopped { .. }
    ));
}

#[test]
fn admission_and_emission_spend_one_cumulative_owner_budget() {
    let mut terms = ay_core::TermStore::new();
    let term = terms.mk_var("p", Sort::Bool);
    let baseline = AlethePrinter::new(&terms);
    assert!(baseline.folded_document_equivalence_admitted(term, "(or p false)", "p"));
    let admission_work = baseline.work_used();
    assert!(admission_work > 0);
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(admission_work));
    assert!(printer.folded_document_equivalence_admitted(term, "(or p false)", "p"));
    assert_eq!(printer.work_used(), admission_work);
    assert!(
        printer
            .render_authored_assume_bridge(
                ProofId(0),
                term,
                "(or p false)",
                "p",
                AuthoredAssumeBridge::FoldedDocumentEquivalence,
            )
            .0
            .is_none(),
        "rendering cannot renew the spent admission allowance"
    );
}
