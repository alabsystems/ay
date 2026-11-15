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
    let root = aggregate_tests::raw_fixture_term(&mut context, &parsed);
    let negative = context.terms.mk_not_raw(root);
    assert!(
        partition_identity(&context.terms, &[negative], &mut |_, _| true)
            .unwrap()
            .is_some(),
        "{name}"
    );
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "bv",
        vec![negative],
        TheoryLemmaKind::ArithClauseTautology,
    );
    proof.add_resolution(vec![], root, assume, lemma);
    crate::check_proof_strict(&proof, &context.terms).expect("strict native proof check");
    let text = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &context.terms,
        &[root],
        None,
    )
    .unwrap();
    assert!(text.contains(":rule pbblast_bv"), "{name}: {text}");
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    let path =
        std::env::temp_dir().join(format!("ay-partition-{name}-{}.json", std::process::id()));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":text})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn original_twenty_four_way_coverage_has_a_checked_proof() {
    publish(
        "original",
        include_str!("../../../../../ay-dpll/tests/fixtures/partition_coverage.smt2"),
    );
}

fn problem(width: u32, point: u128, upper: u128) -> String {
    let zero = format!("(_ bv0 {width})");
    let one = format!("(_ bv1 {width})");
    let pc = format!("(_ bv{point} {width})");
    let upper = format!("(_ bv{upper} {width})");
    let before = format!("(ite (and (bvule {zero} {pc}) (bvult {pc} s)) {one} {zero})");
    let after =
        format!("(ite (and (bvule e {pc}) (bvult {pc} (bvadd (bvsub {upper} e) e))) {one} {zero})");
    let middle = format!("(ite (and (bvule s {pc}) (bvult {pc} e)) {one} {zero})");
    format!("(set-logic QF_BV) (declare-const s (_ BitVec {width})) (declare-const e (_ BitVec {width})) (assert (and (bvule s e) (not (= true (= (bvadd (bvadd {before} {after}) {middle}) {one}))))) (check-sat)")
}

#[test]
fn partition_boundaries_and_full_word_widths_have_checked_proofs() {
    for width in [1, 9, 32, 64, 128] {
        publish(&format!("width-{width}"), &problem(width, 0, 1));
    }
    publish("last-in-range", &problem(9, 254, 255));
}

#[test]
fn partition_missing_order_wrong_indicators_and_outside_points_decline() {
    let original = problem(9, 2, 8);
    for input in [
        original.replace("(bvule s e)", "true"),
        original.replace("(bvule s e)", "(bvuge s e)"),
        original.replace("(bvule s (_ bv2 9))", "(bvult s (_ bv2 9))"),
        original.replace("(bvult (_ bv2 9) e)", "(bvule (_ bv2 9) e)"),
        problem(9, 8, 8),
        original.replace("(_ bv1 9) (_ bv0 9)", "(_ bv0 9) (_ bv0 9)"),
    ] {
        let mut context = ay_frontend::Context::new();
        for command in ay_frontend::parse(&input).unwrap() {
            context.process_command(&command).unwrap();
        }
        let parsed = context.assertions_parsed()[0].clone();
        let root = aggregate_tests::raw_fixture_term(&mut context, &parsed);
        let negative = context.terms.mk_not_raw(root);
        assert!(
            partition_identity(&context.terms, &[negative], &mut |_, _| true)
                .unwrap()
                .is_none(),
            "{input}"
        );
    }
}

#[test]
fn partition_source_overrides_and_publication_budget_decline() {
    let input = problem(64, 2, 8);
    let mut context = ay_frontend::Context::new();
    for command in ay_frontend::parse(&input).unwrap() {
        context.process_command(&command).unwrap();
    }
    let parsed = context.assertions_parsed()[0].clone();
    let root = aggregate_tests::raw_fixture_term(&mut context, &parsed);
    let negative = context.terms.mk_not_raw(root);
    let identity = partition_identity(&context.terms, &[negative], &mut |_, _| true)
        .unwrap()
        .unwrap();
    let mut overrides = DetHashMap::default();
    overrides.insert(identity.ordered, "(bvuge s e)".into());
    assert!(
        AlethePrinter::new_with_overrides(&context.terms, Some(&overrides))
            .format_bv_partition_identity(ProofId(11), &[negative])
            .is_none()
    );
    let printer = AlethePrinter::new_with_overrides_and_budget(&context.terms, None, Some(1024));
    assert!(printer
        .format_bv_partition_identity(ProofId(11), &[negative])
        .is_none());
    assert!(printer.work_budget_exhausted());
}
