// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{certificate, native, original, TestResult};
use super::*;

fn problem(width: usize, signed: bool) -> String {
    let extension = if signed { "sign_extend" } else { "zero_extend" };
    let value = "(bvmul a b)";
    let wide = format!("(bvmul ((_ {extension} {width}) a) ((_ {extension} {width}) b))");
    let high = format!("((_ extract {} {width}) {wide})", 2 * width - 1);
    let expected_high = if signed {
        format!("(bvashr {value} (_ bv{} {width}))", width - 1)
    } else {
        format!("(_ bv0 {width})")
    };
    let specification = format!("(not (= {wide} ((_ {extension} {width}) {value})))");
    let instruction = format!("(not (= {high} {expected_high}))");
    format!("(set-logic QF_BV)(declare-const a (_ BitVec {width}))(declare-const b (_ BitVec {width}))(assert (not (= (concat (ite {specification} #b1 #b0) {value}) (concat (ite {instruction} #b1 #b0) {value}))))(check-sat)")
}

#[test]
fn product_overflow_native_proofs_preserve_the_complete_widened_source() -> TestResult {
    for width in [1, 2, 8, 16, 64] {
        for signed in [false, true] {
            assert!(
                native(&problem(width, signed))?,
                "width {width}, signed {signed}"
            );
        }
    }
    Ok(())
}

#[test]
fn product_overflow_exports_full_arithmetic_and_checked_prefixes() -> TestResult {
    for width in [1, 2, 8, 16, 64] {
        for signed in [false, true] {
            certificate(
                &format!("mul-overflow-{width}-{signed}"),
                &problem(width, signed),
            )?;
        }
    }
    Ok(())
}

#[test]
fn exact_original_compiler_multiply_overflow_queries_are_certified() -> TestResult {
    for (name, input) in [
        (
            "original-smul",
            include_str!("../fixtures/checked-smul-64.smt2"),
        ),
        (
            "original-umul",
            include_str!("../fixtures/checked-umul-64.smt2"),
        ),
    ] {
        assert!(native(input)?, "{name}");
        certificate(name, input)?;
    }
    Ok(())
}

#[test]
fn product_overflow_refuses_changed_high_or_low_results() -> TestResult {
    for signed in [false, true] {
        let input = problem(4, signed);
        for wrong in [
            // Dropping two high bits is observably wrong: unsigned 8*8
            // loses overflow, and signed 2*2 acquires a spurious overflow.
            input.replacen("((_ extract 7 4)", "((_ extract 5 2)", 1),
            input.replacen("(bvmul a b)", "(bvmul a a)", 1),
        ] {
            assert_ne!(input, wrong);
            assert!(!native(&wrong)?, "signed {signed}: {wrong}");
            let (context, _, negative) = original(&wrong)?;
            assert!(AlethePrinter::new(&context.terms)
                .format_bv_circuit_refutation(ProofId(7), &[negative])
                .is_none());
        }
    }
    Ok(())
}

#[test]
fn product_generation_refuses_malformed_widths_and_small_output_budget() -> TestResult {
    let mut terms = ay_core::TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(9));
    let bad = terms.mk_app(Symbol::named("bvmul"), [a, b], Sort::bitvec(8));
    let eq = terms.mk_app(Symbol::named("="), [bad, bad], Sort::Bool);
    assert!(AlethePrinter::new(&terms)
        .format_bv_packed_identity(ProofId(7), &[eq])
        .is_none());
    let (context, root, negative) = original(&problem(64, true))?;
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
