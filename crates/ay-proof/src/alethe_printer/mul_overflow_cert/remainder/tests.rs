// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::alethe_printer::AlethePrinter;
use ay_core::{ProofId, Sort as CoreSort, Symbol, TermStore};
use std::cell::Cell;

fn document(width: u32, progress: EmissionProgress<'_>) -> Option<String> {
    let clause = format!("(cl (or (= d (_ bv0 {width})) (bvult (bvurem x d) d)))");
    certificate(width, "x", "d", "@ur_", "t1", &clause, progress)
}

fn checked_document_shape(width: u32) {
    let text = document(width, EmissionProgress::default()).expect("complete stage certificate");
    assert!(text.contains(":rule bitblast_urem"));
    assert!(text.contains(":rule forall_inst"));
    assert!(text.contains(":rule bind"));
    assert!(!text.contains(":rule hole"));
    assert!(!text.contains(":rule trust"));
    assert!(text
        .lines()
        .last()
        .unwrap()
        .starts_with("(step t1 (cl (or (= d "));
    assert!(text.lines().last().unwrap().contains(":rule reordering"));
    // This is structural generator coverage, NOT external rule validation.
    // Fresh Clean replay remains a separate qualification requirement.
}

#[test]
fn remainder_certificate_width_one() {
    checked_document_shape(1);
}
#[test]
fn remainder_certificate_odd_width() {
    checked_document_shape(3);
}
#[test]
fn remainder_certificate_width_32() {
    checked_document_shape(32);
}
#[test]
fn remainder_certificate_width_64() {
    checked_document_shape(64);
}
#[test]
fn remainder_certificate_width_128() {
    checked_document_shape(128);
}

#[test]
fn unsupported_width_and_original_stop_decline_before_stage_construction() {
    for width in [0, 129] {
        assert!(document(width, EmissionProgress::default()).is_none());
    }
    for width in [1, 3, 32, 64, 128] {
        let mut callback = || false;
        let owner = EmissionProgress::with_caller(&mut callback);
        assert!(document(width, owner.clone()).is_none());
        assert!(owner.refused());
        assert!(document(width, owner).is_none());
    }
}

#[test]
fn accepting_original_owner_preserves_bytes_and_refusal_stays_terminal() {
    let ordinary = document(1, EmissionProgress::default()).unwrap();
    let calls = Cell::new(0);
    let mut continuing = || {
        calls.set(calls.get() + 1);
        true
    };
    let controlled = document(1, EmissionProgress::with_caller(&mut continuing)).unwrap();
    assert_eq!(controlled, ordinary);
    assert!(calls.get() > 10);
    for stop in [1, 2, calls.get() / 2, calls.get() - 1, calls.get()] {
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        assert!(document(1, owner.clone()).is_none());
        assert!(owner.refused());
        assert_eq!(seen.get(), stop);
        assert!(document(1, owner).is_none());
        assert_eq!(seen.get(), stop);
    }
}

fn fixture(width: u32) -> (TermStore, ay_core::TermId) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", CoreSort::bitvec(width));
    let d = terms.mk_var("d", CoreSort::bitvec(width));
    let zero = terms.mk_bitvec(0.into(), width);
    let rem = terms.mk_app(Symbol::named("bvurem"), [x, d], CoreSort::bitvec(width));
    let guard = terms.mk_app(Symbol::named("="), [d, zero], CoreSort::Bool);
    let range = terms.mk_app(Symbol::named("bvult"), [rem, d], CoreSort::Bool);
    let theorem = terms.mk_app(Symbol::named("or"), [guard, range], CoreSort::Bool);
    (terms, theorem)
}

#[test]
fn export_uses_exact_cumulative_work_and_rejects_a_changed_source_surface() {
    let (terms, root) = fixture(1);
    let printer = AlethePrinter::new(&terms);
    let expected = printer.format_urem_bound(ProofId(7), &[root]).unwrap();
    let used = printer.work_used();
    assert!(used > 0);
    for (budget, accepted) in [(used, true), (used - 1, false), (0, false)] {
        let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(budget));
        let result = printer.format_urem_bound(ProofId(7), &[root]);
        assert_eq!(result.is_some(), accepted);
        if accepted {
            assert_eq!(result.unwrap(), expected);
        }
    }
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(root, "true".into());
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, Some(&overrides), None);
    assert!(printer.format_urem_bound(ProofId(7), &[root]).is_none());
}

#[test]
fn native_theorem_has_checked_authority_and_never_accepts_an_empty_clause() {
    use ay_core::{Proof as CoreProof, TheoryLemmaKind};
    let (mut terms, root) = fixture(3);
    let negative = terms.mk_not_raw(root);
    let mut proof = CoreProof::new();
    let premise = proof.add_assume(negative, None);
    let lemma = proof.add_theory_lemma_with_kind("bv", vec![root], TheoryLemmaKind::BvUremBound);
    proof.add_resolution(Vec::new(), root, premise, lemma);
    crate::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[negative])).unwrap();
    assert!(crate::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[])).is_err());
    let mut corrupt = CoreProof::new();
    corrupt.add_theory_lemma_with_kind("bv", vec![], TheoryLemmaKind::BvUremBound);
    assert!(
        crate::check_proof_strict_with_context(&corrupt, &terms, None, None, Some(&[])).is_err()
    );
}
