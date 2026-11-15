// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Proof, TheoryLemmaKind};

fn publish(name: &str, problem: &str) {
    let mut context = ay_frontend::Context::new();
    for command in ay_frontend::parse(problem).unwrap() {
        context.process_command(&command).unwrap();
    }
    let parsed = context.assertions_parsed()[0].clone();
    let root = super::super::aggregate_tests::raw_fixture_term(&mut context, &parsed);
    let negated = context.terms.mk_not_raw(root);
    assert!(
        context_identity(&context.terms, &[negated], &mut |_, _| true)
            .unwrap()
            .is_some(),
        "{name}"
    );
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "bv",
        vec![negated],
        TheoryLemmaKind::ArithClauseTautology,
    );
    proof.add_resolution(vec![], root, assume, lemma);
    crate::check_proof_strict(&proof, &context.terms).expect("strict native check");
    let text = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &context.terms,
        &[root],
        None,
    )
    .unwrap();
    assert!(text.contains(":rule ite_simplify"), "{name}: {text}");
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    let path = std::env::temp_dir().join(format!("ay-context-{name}-{}.json", std::process::id()));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":text})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn context_original_exception_queries_have_checked_proofs() {
    for (name, problem) in [
        (
            "catch-all",
            include_str!("../../../../../ay-dpll/tests/fixtures/context_catch_all.smt2"),
        ),
        (
            "out-of-range",
            include_str!("../../../../../ay-dpll/tests/fixtures/context_out_of_range.smt2"),
        ),
        (
            "landing-pad",
            include_str!("../../../../../ay-dpll/tests/fixtures/context_landing_pad.smt2"),
        ),
    ] {
        publish(name, problem);
    }
}

#[test]
fn context_bool_guards_work_at_full_word_widths() {
    for width in [1, 9, 32, 64, 128] {
        let problem = format!("(set-logic QF_BV) (declare-const g Bool) (declare-const x (_ BitVec {width})) (declare-const y (_ BitVec {width})) (assert (and g (not (= x (ite g x y))))) (check-sat)");
        publish(&format!("width-{width}"), &problem);
    }
}

#[test]
fn context_missing_guards_wrong_branches_and_overrides_decline() {
    for (guard, yes, no, expected) in [
        ("g", "x", "y", true),
        ("h", "x", "y", false),
        ("g", "y", "x", false),
    ] {
        let problem = format!("(set-logic QF_BV) (declare-const g Bool) (declare-const h Bool) (declare-const x (_ BitVec 64)) (declare-const y (_ BitVec 64)) (assert (and {guard} (not (= x (ite g {yes} {no}))))) (check-sat)");
        let mut context = ay_frontend::Context::new();
        for command in ay_frontend::parse(&problem).unwrap() {
            context.process_command(&command).unwrap();
        }
        let parsed = context.assertions_parsed()[0].clone();
        let root = super::super::aggregate_tests::raw_fixture_term(&mut context, &parsed);
        let negated = context.terms.mk_not_raw(root);
        let result = context_identity(&context.terms, &[negated], &mut |_, _| true).unwrap();
        assert_eq!(result.is_some(), expected);
        if let Some(identity) = result {
            assert!(context_identity(&context.terms, &[negated], &mut |_, _| false).is_err());
            assert!(
                context_identity(&context.terms, &[identity.equality], &mut |_, _| true)
                    .unwrap()
                    .is_none()
            );
            let mut overrides = DetHashMap::default();
            overrides.insert(identity.right, "y".into());
            assert!(
                AlethePrinter::new_with_overrides(&context.terms, Some(&overrides))
                    .format_bv_context_identity(ProofId(7), &[negated])
                    .is_none()
            );
            let printer =
                AlethePrinter::new_with_overrides_and_budget(&context.terms, None, Some(1024));
            assert!(printer
                .format_bv_context_identity(ProofId(7), &[negated])
                .is_none());
            assert!(printer.work_budget_exhausted());
        }
    }
}
