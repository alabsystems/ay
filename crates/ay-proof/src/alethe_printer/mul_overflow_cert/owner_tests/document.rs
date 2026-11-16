// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::super::{AlethePrintError, AlethePrinter};
use super::super::proof::{Prem, Proof};
use super::super::term::Sort;
use super::EmissionProgress;
use ay_core::{ProofId, TheoryLemmaKind};
use std::cell::Cell;

fn derive_with(p: &mut Proof<'_>) -> Option<u32> {
    let x = p.t.var("x", Sort::Bool);
    let premise = p.assume(x);
    p.derive(&[x], &[Prem::Step(premise)], &[])
}

#[test]
fn derive_accepting_owner_preserves_document_and_budget() {
    let mut ordinary = Proof::new("t1.mo".into(), "@w".into());
    assert!(derive_with(&mut ordinary).is_some());
    let mut callback = || true;
    let mut controlled = Proof::new_with_progress(
        "t1.mo".into(),
        "@w".into(),
        EmissionProgress::with_caller(&mut callback),
    );
    assert!(derive_with(&mut controlled).is_some());
    assert_eq!(controlled.out, ordinary.out);
    assert_eq!(controlled.budget, ordinary.budget);
}

#[test]
fn every_derive_poll_refuses_without_reopening_the_owner() {
    let calls = Cell::new(0);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    let mut p = Proof::new_with_progress(
        "t1.mo".into(),
        "@w".into(),
        EmissionProgress::with_caller(&mut accepting),
    );
    assert!(derive_with(&mut p).is_some());
    assert!(calls.get() > 1);
    for stop_at in 1..=calls.get() {
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let mut candidate = Proof::new_with_progress("t1.mo".into(), "@w".into(), owner.clone());
        assert!(derive_with(&mut candidate).is_none());
        assert_eq!(seen.get(), stop_at);
        let remaining = candidate.budget;
        let x = candidate.t.var("x", Sort::Bool);
        assert!(candidate.derive(&[x], &[], &[]).is_none());
        assert_eq!(candidate.budget, remaining);
        assert_eq!(seen.get(), stop_at);
        assert!(owner.refused());
    }
}

#[test]
fn certificate_accepting_owner_preserves_text_and_final_id() {
    let (terms, eq) = super::super::tests::clause_of(4);
    let ordinary = AlethePrinter::new(&terms)
        .format_mul_overflow_division(ProofId(7), &[eq])
        .expect("ordinary certificate");
    let mut callback = || true;
    let controlled = AlethePrinter::new(&terms)
        .with_emission_progress(&mut callback)
        .format_mul_overflow_division(ProofId(7), &[eq])
        .expect("controlled certificate");
    assert_eq!(controlled, ordinary);
    assert!(controlled
        .lines()
        .last()
        .expect("last step")
        .starts_with("(step t7 "));
}

#[test]
fn certificate_inner_and_final_refusal_abandon_text() {
    super::super::LAST_CERTIFICATE.with(|last| *last.borrow_mut() = None);
    let (terms, eq) = super::super::tests::clause_of(4);
    let calls = Cell::new(0);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    let accepted = AlethePrinter::new(&terms)
        .with_emission_progress(&mut accepting)
        .format_mul_overflow_division(ProofId(7), &[eq]);
    assert!(accepted.is_some());
    assert!(
        calls.get() > 10,
        "exercise inner refutations and final publication"
    );
    for stop_at in [10, calls.get()] {
        super::super::LAST_CERTIFICATE.with(|last| *last.borrow_mut() = None);
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
        assert!(printer
            .format_mul_overflow_division(ProofId(7), &[eq])
            .is_none());
        assert_eq!(seen.get(), stop_at);
        assert!(printer
            .format_mul_overflow_division(ProofId(7), &[eq])
            .is_none());
        assert_eq!(seen.get(), stop_at);
    }
}

#[test]
fn theory_lemma_owner_refusal_is_typed_not_an_honest_hole() {
    let (terms, eq) = super::super::tests::clause_of(4);
    let mut callback = || false;
    let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
    let result = printer.format_theory_lemma(
        ProofId(7),
        "bv",
        &[eq],
        None,
        &TheoryLemmaKind::BvMulOverflowDivision,
        None,
    );
    assert!(matches!(
        result,
        Err(AlethePrintError::EmissionStopped { steps_rendered: 7 })
    ));
}
