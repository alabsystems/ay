// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The complete blaster must derive the exact terms its consumer reads.

use super::*;
use ay_core::TermStore;
use num_bigint::BigInt;

struct SurfaceFixture {
    terms: TermStore,
    literal: TermId,
    changes: Vec<(TermId, &'static str)>,
}

fn fixture() -> SurfaceFixture {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(4);
    let a = terms.mk_var("a", word.clone());
    let p = terms.mk_var("p", Sort::Bool);
    let one = terms.mk_bitvec(BigInt::from(1), 4);
    let add = terms.mk_app(Symbol::named("bvadd"), [a, one], word.clone());
    let joined = terms.mk_app(Symbol::named("concat"), [a, a], Sort::bitvec(8));
    let low = terms.mk_app(
        Symbol::indexed("extract", vec![3, 0]),
        [joined],
        word.clone(),
    );
    let selected = terms.mk_ite_raw(p, add, low);
    let equality = terms.mk_app(Symbol::named("="), [selected, a], Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let root = terms.mk_app(Symbol::named("and"), [p, not_p, equality], Sort::Bool);
    let literal = terms.mk_not_raw(root);
    SurfaceFixture {
        terms,
        literal,
        changes: vec![
            (a, "b"),
            (p, "q"),
            (one, "a"),
            (add, "a"),
            (joined, "#x00"),
            (low, "#b0000"),
            (selected, "a"),
            (equality, "true"),
            (not_p, "p"),
            (root, "true"),
            (literal, "false"),
        ],
    }
}

#[test]
fn changed_surface_at_every_dag_layer_is_refused() {
    let f = fixture();
    let plain = AlethePrinter::new(&f.terms);
    assert!(plain
        .format_bv_complete_blast_refutation(ProofId(1), &[f.literal])
        .is_some());
    for &(term, spelling) in &f.changes {
        let mut overrides = DetHashMap::default();
        overrides.insert(term, spelling.to_string());
        let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&overrides));
        assert!(
            printer
                .format_bv_complete_blast_refutation(ProofId(1), &[f.literal])
                .is_none(),
            "changed term {term:?} to {spelling}"
        );
    }
}

#[test]
fn canonical_and_unrelated_overrides_preserve_the_complete_proof() {
    let mut f = fixture();
    let unrelated = f.terms.mk_var("unused", Sort::Bool);
    let plain = AlethePrinter::new(&f.terms);
    let expected = plain
        .format_bv_complete_blast_refutation(ProofId(1), &[f.literal])
        .unwrap();
    let mut overrides = DetHashMap::default();
    for &(term, _) in &f.changes {
        overrides.insert(term, plain.format_term(term));
    }
    overrides.insert(unrelated, "false".to_string());
    let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&overrides));
    assert_eq!(
        printer.format_bv_complete_blast_refutation(ProofId(1), &[f.literal]),
        Some(expected)
    );
}

#[test]
fn canonical_ancestor_cannot_hide_a_changed_descendant() {
    let f = fixture();
    let plain = AlethePrinter::new(&f.terms);
    let mut overrides = DetHashMap::default();
    overrides.insert(f.literal, plain.format_term(f.literal));
    overrides.insert(f.changes[2].0, "a".to_string());
    let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&overrides));
    assert!(printer
        .format_bv_complete_blast_refutation(ProofId(1), &[f.literal])
        .is_none());
}

#[test]
fn exhausted_surface_work_budget_cannot_emit_a_complete_proof() {
    let f = fixture();
    let printer = AlethePrinter::new_with_overrides_and_budget(&f.terms, None, Some(1));
    assert!(printer
        .format_bv_complete_blast_refutation(ProofId(1), &[f.literal])
        .is_none());
}

#[test]
fn effective_bridge_and_skolem_spellings_must_agree() {
    let f = fixture();
    let constant = f.changes[2].0;
    for skolem in [false, true] {
        let printer = AlethePrinter::new(&f.terms);
        let overrides = if skolem {
            &printer.skolem_overrides
        } else {
            &printer.let_bridge_renderings
        };
        overrides.borrow_mut().insert(constant, "a".to_string());
        assert!(printer
            .format_bv_complete_blast_refutation(ProofId(1), &[f.literal])
            .is_none());
    }
}
