// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::checker::bv_affine::complement_relation;
use ay_core::{Proof, TermStore, TheoryLemmaKind};

#[test]
fn complement_original_relocations_have_native_and_external_proofs() {
    for (name, problem) in [
        (
            "call",
            include_str!("../../../../ay-dpll/tests/fixtures/complement_call.smt2"),
        ),
        (
            "page",
            include_str!("../../../../ay-dpll/tests/fixtures/complement_page.smt2"),
        ),
    ] {
        let mut context = ay_frontend::Context::new();
        for command in ay_frontend::parse(problem).unwrap() {
            context.process_command(&command).unwrap();
        }
        let parsed = context.assertions_parsed()[0].clone();
        let root = super::aggregate_tests::raw_fixture_term(&mut context, &parsed);
        let TermData::Not(equality) = *context.terms.get(root) else {
            panic!("negated equality")
        };
        assert!(
            complement_relation(&context.terms, &[equality], &mut |_, _| true)
                .unwrap()
                .is_some()
        );
        let mut proof = Proof::new();
        let assume = proof.add_assume(root, None);
        let lemma = proof.add_theory_lemma_with_kind(
            "bv",
            vec![equality],
            TheoryLemmaKind::ArithClauseTautology,
        );
        proof.add_resolution(vec![], equality, assume, lemma);
        crate::check_proof_strict(&proof, &context.terms).expect("native strict check");
        let text = crate::try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &context.terms,
            &[root],
            None,
        )
        .unwrap();
        assert!(
            text.contains(":rule poly_simp_rel")
                && !text.contains(":rule hole")
                && !text.contains(":rule trust")
        );
        let path = std::env::temp_dir().join(format!(
            "ay-complement-original-{name}-{}.json",
            std::process::id()
        ));
        std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":text})).unwrap()).unwrap();
        println!("independent replay certificate: {}", path.display());
    }
}

fn app(terms: &mut TermStore, op: &str, a: TermId, b: TermId, width: u32) -> TermId {
    terms.mk_app(Symbol::named(op), [a, b], Sort::bitvec(width))
}

#[test]
fn complement_widths_and_operand_orders_are_checked() {
    for width in [1, 9, 32, 64, 128] {
        for reversed in [false, true] {
            let mut terms = TermStore::new();
            let x = terms.mk_var("x", Sort::bitvec(width));
            let maximum = terms.mk_bitvec((u128::MAX >> (128 - width)).into(), width);
            let complement = if reversed {
                app(&mut terms, "bvxor", x, maximum, width)
            } else {
                app(&mut terms, "bvxor", maximum, x, width)
            };
            let left = app(&mut terms, "bvadd", x, complement, width);
            let equality = terms.mk_app(Symbol::named("="), [maximum, left], Sort::Bool);
            assert!(complement_relation(&terms, &[equality], &mut |_, _| true)
                .unwrap()
                .is_some());
            let printer = AlethePrinter::new(&terms);
            let text = printer
                .format_bv_complement_affine_identity(ProofId(7), &[equality])
                .unwrap();
            let assertion = format!("(not {})", printer.format_term(equality));
            let problem = format!("(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))\n(assert {assertion})\n(check-sat)\n");
            let proof = format!("(assume a {assertion})\n{text}(step done (cl) :rule resolution :premises (a t7))\n");
            let path = std::env::temp_dir().join(format!(
                "ay-complement-width-{width}-{reversed}-{}.json",
                std::process::id()
            ));
            std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":proof})).unwrap()).unwrap();
            println!("independent replay certificate: {}", path.display());
        }
    }
}

#[test]
fn complement_wrong_masks_overrides_and_cancelled_attempts_decline() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(9));
    let maximum = terms.mk_bitvec(511.into(), 9);
    for value in [0, 1, 255, 510] {
        let mask = terms.mk_bitvec(value.into(), 9);
        let inv = app(&mut terms, "bvxor", x, mask, 9);
        let sum = app(&mut terms, "bvadd", x, inv, 9);
        let equality = terms.mk_app(Symbol::named("="), [sum, maximum], Sort::Bool);
        assert!(complement_relation(&terms, &[equality], &mut |_, _| true)
            .unwrap()
            .is_none());
        assert!(!crate::recognize_arith_clause_tautology(
            &terms,
            &[equality]
        ));
    }
    let inv = app(&mut terms, "bvxor", x, maximum, 9);
    let sum = app(&mut terms, "bvadd", x, inv, 9);
    let equality = terms.mk_app(Symbol::named("="), [sum, maximum], Sort::Bool);
    assert!(complement_relation(&terms, &[equality], &mut |_, _| false).is_err());
    let mut overrides = DetHashMap::default();
    overrides.insert(maximum, "(_ bv510 9)".into());
    assert!(AlethePrinter::new_with_overrides(&terms, Some(&overrides))
        .format_bv_complement_affine_identity(ProofId(7), &[equality])
        .is_none());
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(1024));
    assert!(printer
        .format_bv_complement_affine_identity(ProofId(7), &[equality])
        .is_none());
    assert!(printer.work_budget_exhausted());
}

#[test]
fn complement_publication_shares_the_arithmetic_attempt_cap() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(1));
    let one = terms.mk_bitvec(1.into(), 1);
    let inv = app(&mut terms, "bvxor", x, one, 1);
    let sum = app(&mut terms, "bvadd", x, inv, 1);
    let equality = terms.mk_app(Symbol::named("="), [sum, one], Sort::Bool);
    let kind = TheoryLemmaKind::ArithClauseTautology;
    let mut budget = crate::ArithPolySimpPromotionBudget::standalone();
    for _ in 0..8 {
        assert!(!crate::theory_lemma_poly_simp_lowering_supported(
            &terms,
            &kind,
            None,
            &[equality],
            None,
            &mut budget
        ));
        assert!(crate::theory_lemma_bv_arithmetic_lowering_supported(
            &terms,
            &kind,
            &[equality],
            None,
            &mut budget
        ));
    }
    assert!(!crate::theory_lemma_bv_arithmetic_lowering_supported(
        &terms,
        &kind,
        &[equality],
        None,
        &mut budget
    ));
    let root = terms.mk_not_raw(equality);
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let mut lemma = assume;
    for _ in 0..17 {
        lemma = proof.add_theory_lemma_with_kind("bv", vec![equality], kind.clone());
    }
    proof.add_resolution(vec![], equality, assume, lemma);
    let text =
        crate::try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[root], None)
            .unwrap();
    assert!(text.contains(":rule hole"));
    assert!(!text.contains(":rule poly_simp_rel"));
}
