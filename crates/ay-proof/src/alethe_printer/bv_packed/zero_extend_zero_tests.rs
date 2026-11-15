// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{capture_alethe_dialect_report, with_alethe_dialect, AletheDialect, CleanOnlySpelling};
use ay_core::TermStore;

fn retain(name: &str, width: u32, assertion: &str, steps: &str) {
    let problem = format!(
        "(set-logic QF_BV)\n(declare-const byte (_ BitVec {width}))\n(assert {assertion})\n(check-sat)\n"
    );
    let proof = format!(
        "(assume a {assertion})\n{steps}(step done (cl) :rule resolution :premises (a t7))\n"
    );
    let envelope = serde_json::json!({
        "type": "alethe_certificate", "version": "1.0", "problem": problem, "proof": proof,
    });
    let dir = std::env::temp_dir().join(format!("ay-zero-extend-zero-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}.json"));
    std::fs::write(&path, serde_json::to_vec_pretty(&envelope).unwrap()).unwrap();
    println!("zero-extension replay: {}", path.display());
}

#[test]
fn clean_zero_extend_zero_packed_words_use_the_disclosed_identity() {
    for width in [1, 8, 64, 128] {
        let mut terms = TermStore::new();
        let byte = terms.mk_var("byte", Sort::bitvec(width));
        let first = terms.mk_app(
            Symbol::indexed("zero_extend", vec![0]),
            [byte],
            Sort::bitvec(width),
        );
        let nested = terms.mk_app(
            Symbol::indexed("zero_extend", vec![0]),
            [first],
            Sort::bitvec(width),
        );
        let equality = terms.mk_app(Symbol::named("="), [nested, byte], Sort::Bool);
        let printer = AlethePrinter::new(&terms);
        let (steps, report) = capture_alethe_dialect_report(|| {
            with_alethe_dialect(AletheDialect::Clean, || {
                printer.format_bv_packed_identity(ProofId(7), &[equality])
            })
        });
        let steps = steps.expect("the identical bits have an ordinary identity/transport proof");
        assert_eq!(
            report.first_clean_only(),
            Some(CleanOnlySpelling::ZeroExtendAsConcat)
        );
        assert!(steps.contains(":rule refl") && steps.contains(":rule trans"));
        assert!(!steps.contains(":rule hole") && !steps.contains(":rule trust"));
        let assertion = format!("(not {})", printer.format_term(equality));
        retain(&format!("packed-clean-{width}"), width, &assertion, &steps);
    }
}

#[test]
fn zero_extend_zero_pinned_word_keeps_closed_cases_and_no_clean_reading() {
    let mut terms = TermStore::new();
    let byte = terms.mk_var("byte", Sort::bitvec(1));
    let extended = terms.mk_app(
        Symbol::indexed("zero_extend", vec![0]),
        [byte],
        Sort::bitvec(1),
    );
    let equality = terms.mk_app(Symbol::named("="), [extended, byte], Sort::Bool);
    let printer = AlethePrinter::new(&terms);
    let (steps, report) = capture_alethe_dialect_report(|| {
        with_alethe_dialect(AletheDialect::PinnedCarcara, || {
            printer.format_bv_packed_identity(ProofId(7), &[equality])
        })
    });
    let steps = steps.expect("the existing pinned closed cases remain");
    assert!(steps.contains(":rule subproof") && steps.contains(":rule evaluate"));
    assert!(report.is_pinned_spelling(), "{report:?}");
    retain(
        "packed-pinned-1",
        1,
        &format!("(not {})", printer.format_term(equality)),
        &steps,
    );
}

#[test]
fn clean_zero_extend_zero_rejects_a_wrong_bit_plan_or_arity_before_output_growth() {
    let mut terms = TermStore::new();
    let byte = terms.mk_var("byte", Sort::bitvec(1));
    let printer = AlethePrinter::new(&terms);
    with_alethe_dialect(AletheDialect::Clean, || {
        let mut proof = PackedProof::new(&printer, ProofId(7)).unwrap();
        let source = proof.vector(byte, 0).unwrap();
        let before = (proof.out.len(), proof.definitions.len(), proof.next);
        assert!(proof
            .wire_operation(
                "(_ zero_extend 0)",
                source.clone(),
                None,
                vec!["false".into()]
            )
            .is_none());
        assert_eq!(
            (proof.out.len(), proof.definitions.len(), proof.next),
            before
        );
        assert!(proof
            .wire_operation(
                "(_ zero_extend 0)",
                source.clone(),
                Some("#b0"),
                source.bits
            )
            .is_none());
        assert_eq!(
            (proof.out.len(), proof.definitions.len(), proof.next),
            before
        );
    });
}

#[test]
fn zero_extend_zero_does_not_identify_different_words_or_bypass_printer_work() {
    let mut terms = TermStore::new();
    let byte = terms.mk_var("byte", Sort::bitvec(1));
    let other = terms.mk_var("other", Sort::bitvec(1));
    let extended = terms.mk_app(
        Symbol::indexed("zero_extend", vec![0]),
        [byte],
        Sort::bitvec(1),
    );
    let wrong = terms.mk_app(Symbol::named("="), [extended, other], Sort::Bool);
    assert!(AlethePrinter::new(&terms)
        .format_bv_packed_identity(ProofId(7), &[wrong])
        .is_none());
    let right = terms.mk_app(Symbol::named("="), [extended, byte], Sort::Bool);
    assert!(
        AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(0))
            .format_bv_packed_identity(ProofId(7), &[right])
            .is_none()
    );
}
