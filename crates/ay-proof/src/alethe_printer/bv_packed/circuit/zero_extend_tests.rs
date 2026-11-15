// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{certificate, original, TestResult};
use super::*;
use crate::{capture_alethe_dialect_report, AletheDialect, CleanOnlySpelling};

fn identity_problem(bits: u32, extra: u32) -> String {
    let result = bits + extra;
    let right = if extra == 0 {
        "x".to_string()
    } else {
        format!("(concat (_ bv0 {extra}) x)")
    };
    format!("(set-logic QF_BV)(declare-const x (_ BitVec {bits}))(assert (not (= ((_ zero_extend {extra}) x) {right})))(check-sat) ; result-width={result}")
}

#[test]
fn circuit_small_support_zero_extend_has_only_discharged_closed_cases() -> TestResult {
    for (bits, extra) in [(1, 0), (1, 7), (8, 8), (8, 56)] {
        let problem = identity_problem(bits, extra);
        let (context, _, negative) = original(&problem)?;
        let printer = AlethePrinter::new(&context.terms);
        assert_eq!(
            super::super::super::dialect::current(),
            AletheDialect::Clean
        );
        let (document, report) = capture_alethe_dialect_report(|| {
            printer.format_bv_circuit_refutation(ProofId(7), &[negative])
        });
        let document = document.ok_or("the checked small-support circuit renders")?;
        if extra == 0 {
            assert_eq!(
                report.first_clean_only(),
                Some(CleanOnlySpelling::ZeroExtendAsConcat)
            );
            assert!(document.contains(":rule refl") && document.contains(":rule trans"));
            assert!(!document.contains("(forall ") && !document.contains(":rule forall_inst"));
        } else {
            assert!(report.is_pinned_spelling(), "{bits}/{extra}: {report:?}");
            assert!(document.contains(":rule evaluate"));
            assert!(document.contains(":rule subproof"));
        }
        assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
        // Independent replay consumes the original source problem and the
        // genuine regenerated proof; this writes a complete certificate.
        certificate(&format!("checked-zero-extend-{bits}-{extra}"), &problem)?;
    }
    Ok(())
}

#[test]
fn circuit_small_support_zero_extend_rejects_false_padding_and_sign_twins() -> TestResult {
    for right in ["(concat #x01 x)", "((_ sign_extend 8) x)"] {
        let problem = format!("(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (and (= x #x80) (not (= ((_ zero_extend 8) x) {right}))))(check-sat)");
        let (context, _, negative) = original(&problem)?;
        // x=128 is a concrete original-query witness for BOTH twins:
        // zero-extension is 128, bad padding is 384, sign-extension is 65408.
        assert!(
            AlethePrinter::new(&context.terms)
                .format_bv_circuit_refutation(ProofId(7), &[negative])
                .is_none(),
            "a satisfiable source must have no refutation: {right}"
        );
    }
    Ok(())
}

#[test]
fn circuit_nine_symbolic_bits_keep_the_clean_only_fallback_report() -> TestResult {
    let problem = identity_problem(9, 7);
    let (context, _, negative) = original(&problem)?;
    let printer = AlethePrinter::new(&context.terms);
    let (document, report) = capture_alethe_dialect_report(|| {
        printer.format_bv_circuit_refutation(ProofId(7), &[negative])
    });
    let document = document.ok_or("the unchanged Clean-only fallback renders")?;
    assert_eq!(
        report.first_clean_only(),
        Some(CleanOnlySpelling::ZeroExtendAsConcat)
    );
    assert!(document.contains("(concat (_ bv0 7) x)"));
    assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
    Ok(())
}

#[test]
fn circuit_checked_zero_extend_exhaustion_never_falls_back_to_clean_refl() -> TestResult {
    let (context, _, negative) = original(&identity_problem(8, 56))?;
    let printer = AlethePrinter::new_with_overrides_and_budget(&context.terms, None, Some(1024));
    let (document, report) = capture_alethe_dialect_report(|| {
        printer.format_bv_circuit_refutation(ProofId(7), &[negative])
    });
    assert!(document.is_none());
    assert!(printer.work_budget_exhausted());
    assert!(
        report.is_pinned_spelling(),
        "refusal must not select a Clean shortcut"
    );
    Ok(())
}

#[test]
fn circuit_zero_extend_wrong_index_arity_and_result_width_are_refused() {
    for (indices, width) in [(vec![], 16), (vec![8, 8], 16), (vec![7], 16), (vec![8], 17)] {
        let mut terms = ay_core::TermStore::new();
        let byte = terms.mk_var("byte", Sort::bitvec(8));
        let malformed = terms.mk_app(
            Symbol::indexed("zero_extend", indices),
            [byte],
            Sort::bitvec(width),
        );
        let equality = terms.mk_app(Symbol::named("="), [malformed, malformed], Sort::Bool);
        let root = terms.mk_not_raw(equality);
        let negative = terms.mk_not_raw(root);
        let printer = AlethePrinter::new(&terms);
        assert!(printer
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none());
    }
}
