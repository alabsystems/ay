// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{FpOp, Symbol};

#[test]
fn wide_nan_identity_uses_constant_schema_budget_and_rejects_ieee_equality() {
    for equality in ["=", "fp.eq"] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("nan-budget-x", Sort::FloatingPoint(15, 113));
        let y = terms.mk_var("nan-budget-y", Sort::FloatingPoint(15, 113));
        let nx = terms.mk_app(Symbol::named("fp.isNaN"), [x], Sort::Bool);
        let ny = terms.mk_app(Symbol::named("fp.isNaN"), [y], Sort::Bool);
        let eq = terms.mk_app(Symbol::named(equality), [x, y], Sort::Bool);
        let not_eq = terms.mk_not_raw(eq);
        let not_x = terms.mk_not_raw(nx);
        let not_y = terms.mk_not_raw(ny);
        let mut proof = Proof::new();
        let ax = proof.add_assume(nx, None);
        let ay = proof.add_assume(ny, None);
        let ae = proof.add_assume(not_eq, None);
        let lemma = proof.add_theory_lemma_with_kind(
            "fp",
            vec![not_x, not_y, eq],
            TheoryLemmaKind::FpClassification {
                operation: FpOp::IsNaN,
            },
        );
        let first = proof.add_resolution(vec![not_y, eq], nx, lemma, ax);
        let second = proof.add_resolution(vec![eq], ny, first, ay);
        proof.add_resolution(vec![], eq, second, ae);
        let mut work = 0usize;
        let mut bytes = 0usize;
        let result = check_proof_strict_with_context_and_progress(
            &proof,
            &terms,
            None,
            None,
            Some(&[nx, ny, not_eq]),
            &mut |w, b| {
                work = work.saturating_add(w);
                bytes = bytes.saturating_add(b);
                work <= 1_000_000 && bytes <= 8 * 1024 * 1024
            },
        );
        if equality == "=" {
            assert!(result.is_ok(), "{result:?}; work={work}, bytes={bytes}");
        } else {
            assert!(result.is_err(), "IEEE equality of NaNs is false");
        }
        assert!(matches!(
            check_proof_strict_with_context_and_progress(
                &proof,
                &terms,
                None,
                None,
                Some(&[nx, ny, not_eq]),
                &mut |_, _| false,
            ),
            Err(ProofCheckError::ResourceLimit | ProofCheckError::Cancelled)
        ));
    }
}

#[test]
fn ground_fp_classification_checks_under_its_real_assignment_budget() {
    for valid in [true, false] {
        let mut terms = TermStore::new();
        let value = terms.mk_app(
            Symbol::indexed(if valid { "NaN" } else { "+zero" }, vec![15, 113]),
            [],
            Sort::FloatingPoint(15, 113),
        );
        let predicate = terms.mk_app(Symbol::named("fp.isNaN"), [value], Sort::Bool);
        let negative = terms.mk_not_raw(predicate);
        let mut proof = Proof::new();
        let assumption = proof.add_assume(negative, None);
        let lemma = proof.add_theory_lemma_with_kind(
            "fp",
            vec![predicate],
            TheoryLemmaKind::FpClassification {
                operation: FpOp::IsNaN,
            },
        );
        proof.add_resolution(vec![], predicate, lemma, assumption);
        let mut work = 0usize;
        let mut bytes = 0usize;
        let outcome = check_proof_strict_with_context_and_progress(
            &proof,
            &terms,
            None,
            None,
            Some(&[negative]),
            &mut |w, b| {
                work = work.saturating_add(w);
                bytes = bytes.saturating_add(b);
                work <= 100_000 && bytes <= 1024 * 1024
            },
        );
        if valid {
            assert!(outcome.is_ok(), "{outcome:?}; work={work}, bytes={bytes}");
        } else {
            assert!(matches!(
                outcome,
                Err(ProofCheckError::InvalidTheoryLemma { .. })
            ));
        }
        assert!(matches!(
            check_proof_strict_with_context_and_progress(
                &proof,
                &terms,
                None,
                None,
                Some(&[negative]),
                &mut |_, _| false,
            ),
            Err(ProofCheckError::ResourceLimit | ProofCheckError::Cancelled)
        ));
    }
}

#[test]
fn fp_assignment_census_deduplicates_shared_variables_and_keeps_the_ceiling() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("fp-meter-x", Sort::FloatingPoint(3, 5));
    let y = terms.mk_var("fp-meter-y", Sort::FloatingPoint(3, 5));
    let z = terms.mk_var("fp-meter-z", Sort::FloatingPoint(63, 3));
    let assignments = |roots: &[TermId]| {
        charge_step_payload_walks(&terms, roots, &mut |_, _| true)
            .unwrap()
            .1
    };
    assert_eq!(assignments(&[]), 1);
    assert_eq!(assignments(&[x, x]), 256);
    assert_eq!(assignments(&[x, y, x]), 65_536);
    assert_eq!(assignments(&[x, y, z]), 65_536);
}
