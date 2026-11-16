// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{certificate, native, TestResult};
use super::*;

#[test]
fn addition_offset_words_share_carries_after_constant_reassociation() {
    for width in [1, 8, 32, 64, 128] {
        let mut terms = ay_core::TermStore::new();
        let x = terms.mk_var("offset_x", Sort::bitvec(width));
        let y = terms.mk_var("offset_y", Sort::bitvec(width));
        let c = terms.mk_bitvec(7.into(), width);
        let cx = terms.mk_app(Symbol::named("bvadd"), [c, x], Sort::bitvec(width));
        let left = terms.mk_app(Symbol::named("bvadd"), [cx, y], Sort::bitvec(width));
        let xy = terms.mk_app(Symbol::named("bvadd"), [x, y], Sort::bitvec(width));
        let right = terms.mk_app(Symbol::named("bvadd"), [xy, c], Sort::bitvec(width));
        let printer = AlethePrinter::new(&terms);
        let mut proof = PackedProof::new(&printer, ProofId(7)).unwrap();
        let mut circuit = Circuit::new(&mut proof);
        let left = circuit.word(left, 0).unwrap();
        let right = circuit.word(right, 0).unwrap();
        assert!(
            left.bits == right.bits,
            "reassociated offset at width {width}"
        );
        assert_ne!(left.equality.left, right.equality.left);
        assert!(proof.out.contains(":rule poly_simp"));
    }
}

#[test]
fn addition_offset_original_wasm_query_has_a_wire_certificate() -> TestResult {
    let query = include_str!("../fixtures/wasm-offset-i64.smt2");
    let (mut context, root, _) = tests::original(query)?;
    let mut proof = ay_core::Proof::new();
    let assume = proof.add_assume(root, None);
    let (normalized, unit) =
        crate::derive_bv_offset_normalization(&mut context.terms, &mut proof, root, assume)
            .ok_or("checked offset bridge declined")?;
    assert_ne!(root, normalized);
    let negative = context.terms.mk_not_raw(normalized);
    let lemma = proof.add_theory_lemma_with_kind(
        "bv",
        vec![negative],
        ay_core::TheoryLemmaKind::BvBitBlast,
    );
    proof.add_resolution(vec![], normalized, unit, lemma);
    assert!(crate::check_proof_strict(&proof, &context.terms)?.is_complete());
    crate::validate_reachable_assumes_in_problem_scope(&proof, &[root])?;
    let text = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &context.terms,
        &[root],
        None,
    )?;
    let gaps: Vec<_> = text
        .lines()
        .filter(|line| line.contains(":rule hole") || line.contains(":rule trust"))
        .take(8)
        .map(|line| line.chars().take(300).collect::<String>())
        .collect();
    let path = std::env::temp_dir().join(format!("ay-offset-bridge-{}.json", std::process::id()));
    std::fs::write(
        &path,
        serde_json::to_vec(&serde_json::json!({
            "type":"alethe_certificate", "version":"1.0", "problem":query, "proof":text,
        }))?,
    )?;
    println!("independent checked-bridge certificate: {}", path.display());
    assert!(text.contains(":rule poly_simp"));
    assert!(gaps.is_empty(), "wire gaps: {gaps:?}");
    certificate("wasm-offset-canonical", query)
}

#[test]
fn addition_offset_changed_constant_stays_a_counterexample() -> TestResult {
    let problem = "(set-logic QF_BV)(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))(assert (not (= (bvadd (bvadd #x07 x) y) (bvadd (bvadd x y) #x08))))(check-sat)";
    assert!(!native(problem)?);
    let (context, _, negative) = tests::original(problem)?;
    assert!(AlethePrinter::new(&context.terms)
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    Ok(())
}
