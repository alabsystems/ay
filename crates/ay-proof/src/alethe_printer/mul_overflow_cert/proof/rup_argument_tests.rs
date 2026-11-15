// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::super::term::Sort;
use super::*;
use crate::{check_alethe_document, ProblemScope};

fn one_premise_document(negative: bool) -> String {
    let mut proof = Proof::new("t".into(), "@shared_".into());
    let atom = proof.t.var("p", Sort::Bool);
    let not_atom = proof.t.not(atom);
    let (literal, opposite) = if negative {
        (not_atom, atom)
    } else {
        (atom, not_atom)
    };
    let premise = proof.assume(literal);
    let repeated = proof
        .derive(&[literal], &[Prem::Step(premise)], &[])
        .expect("the real one-premise Boolean derivation");
    assert_eq!(proof.clause(repeated), &[literal]);
    assert!(
        proof.out.contains(":rule drup"),
        "exercise the actual fallback, not resolution"
    );
    assert!(
        proof.out.contains(":args ((cl"),
        "actual printer clause arguments"
    );
    let contra = proof.assume(opposite);
    let final_step = proof
        .derive(&[], &[Prem::Step(repeated), Prem::Step(contra)], &[])
        .expect("real contradictory BCP closure");
    assert!(proof.clause(final_step).is_empty());
    proof.out
}

#[test]
fn actual_boolean_drup_printer_positive_literal_document_round_trips() {
    let document = one_premise_document(false);
    let scope =
        ProblemScope::from_smtlib_source("(declare-const p Bool) (assert p) (assert (not p))");
    let report = check_alethe_document(&document, &scope).expect("printed clause arguments");
    assert_eq!((report.assumes, report.steps), (2, 2));
}

#[test]
fn actual_boolean_drup_printer_negative_literal_document_round_trips() {
    let document = one_premise_document(true);
    let scope =
        ProblemScope::from_smtlib_source("(declare-const p Bool) (assert p) (assert (not p))");
    assert_eq!(
        check_alethe_document(&document, &scope)
            .expect("negative literal")
            .steps,
        2
    );
}

#[test]
fn an_unentailed_boolean_target_does_not_gain_drup_authority() {
    let mut proof = Proof::new("t".into(), "@shared_".into());
    let p = proof.t.var("p", Sort::Bool);
    let q = proof.t.var("q", Sort::Bool);
    let premise = proof.assume(p);
    let before = proof.out.clone();
    assert!(proof
        .derive(&[q], &[Prem::Step(premise)], &[p, q])
        .is_none());
    assert_eq!(
        proof.out, before,
        "document parser repair grants no semantic authority"
    );
}
