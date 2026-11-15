// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{certificate, native, original, TestResult};
use super::*;

const ORIGINAL: [(&str, &str); 3] = [
    ("psllq", include_str!("../fixtures/packed-psllq.smt2")),
    ("psrlq", include_str!("../fixtures/packed-psrlq.smt2")),
    ("pmuludq", include_str!("../fixtures/packed-pmuludq.smt2")),
];

#[test]
fn original_packed_operations_keep_native_source_validation() -> TestResult {
    let mut failures = Vec::new();
    for (name, problem) in ORIGINAL {
        let (context, root, negative) = original(problem)?;
        let mut proof = ay_core::Proof::new();
        let assume = proof.add_assume(root, None);
        let lemma = proof.add_theory_lemma_with_kind(
            "bv",
            vec![negative],
            ay_core::TheoryLemmaKind::BvBitBlast,
        );
        proof.add_resolution(vec![], root, assume, lemma);
        if let Err(error) = crate::check_proof_strict(&proof, &context.terms) {
            failures.push(format!("{name}: {error:?}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    Ok(())
}

#[test]
fn original_packed_operations_export_operand_congruence_proofs() -> TestResult {
    for (name, problem) in ORIGINAL {
        certificate(name, problem)?;
    }
    Ok(())
}

fn operation_problem(op: &str, width: usize) -> String {
    let high = width - 1;
    format!("(set-logic QF_BV)(declare-const a (_ BitVec {width}))(declare-const b (_ BitVec {width}))(assert (not (= ({op} ((_ extract {high} 0) (concat b a)) b) ({op} a b))))(check-sat)")
}

#[test]
fn congruence_preserves_full_operations_at_boundary_widths() -> TestResult {
    for width in [1, 9, 64] {
        for op in ["bvshl", "bvlshr", "bvashr", "bvmul"] {
            let problem = operation_problem(op, width);
            certificate(&format!("congruence-{op}-{width}"), &problem)?;
        }
    }
    Ok(())
}

#[test]
fn changed_operand_or_operator_does_not_receive_a_congruence_proof() -> TestResult {
    for op in ["bvshl", "bvlshr", "bvashr", "bvmul"] {
        let problem = operation_problem(op, 8);
        for changed in [
            problem.replacen(&format!("({op} a b)"), &format!("({op} b b)"), 1),
            problem.replacen(&format!("({op} a b)"), "(bvxor a b)", 1),
        ] {
            assert_ne!(problem, changed);
            assert!(!native(&changed)?, "{op}");
            let (context, _, negative) = original(&changed)?;
            assert!(AlethePrinter::new(&context.terms)
                .format_bv_circuit_refutation(ProofId(7), &[negative])
                .is_none());
        }
    }
    Ok(())
}

#[test]
fn congruence_checks_widths_source_spelling_and_output_budget() -> TestResult {
    let mut terms = ay_core::TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(9));
    let bad = terms.mk_app(Symbol::named("bvmul"), &[x, y], Sort::bitvec(8));
    let eq = terms.mk_app(Symbol::named("="), &[bad, bad], Sort::Bool);
    assert!(AlethePrinter::new(&terms)
        .format_bv_packed_identity(ProofId(7), &[eq])
        .is_none());
    let (context, root, negative) = original(ORIGINAL[0].1)?;
    let mut overrides = DetHashMap::default();
    overrides.insert(root, "false".into());
    assert!(
        AlethePrinter::new_with_overrides(&context.terms, Some(&overrides))
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none()
    );
    let printer = AlethePrinter::new_with_overrides_and_budget(&context.terms, None, Some(1024));
    assert!(printer
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    assert!(printer.work_budget_exhausted());
    Ok(())
}
