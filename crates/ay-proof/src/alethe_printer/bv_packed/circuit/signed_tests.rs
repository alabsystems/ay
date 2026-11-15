// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{certificate, native, original, TestResult};
use super::*;

const COMPILER_CASES: [(&str, &str); 8] = [
    ("sge32", include_str!("../fixtures/cset-sge-32.smt2")),
    ("sge64", include_str!("../fixtures/cset-sge-64.smt2")),
    ("slt32", include_str!("../fixtures/cset-slt-32.smt2")),
    ("slt64", include_str!("../fixtures/cset-slt-64.smt2")),
    ("sgt32", include_str!("../fixtures/cset-sgt-32.smt2")),
    ("sgt64", include_str!("../fixtures/cset-sgt-64.smt2")),
    ("sle32", include_str!("../fixtures/cset-sle-32.smt2")),
    ("sle64", include_str!("../fixtures/cset-sle-64.smt2")),
];

#[test]
fn original_signed_cset_queries_have_native_and_exported_derivations() -> TestResult {
    for (name, problem) in COMPILER_CASES {
        assert!(native(problem)?, "{name}");
        certificate(&format!("cset-{name}"), problem)?;
    }
    Ok(())
}

#[test]
fn signed_order_dualities_preserve_sign_and_strictness() -> TestResult {
    for width in [2, 9, 32, 64, 128] {
        for (op, dual) in [("bvslt", "bvsge"), ("bvsgt", "bvsle")] {
            let problem = format!(
                "(set-logic QF_BV)(declare-const a (_ BitVec {width}))(declare-const b (_ BitVec {width}))(assert (and ({op} a b) ({dual} a b)))(check-sat)"
            );
            assert!(native(&problem)?);
            certificate(&format!("signed-duality-{op}-{width}"), &problem)?;
        }
    }
    let problem = "(set-logic QF_BV)(declare-const a (_ BitVec 1))(declare-const b (_ BitVec 1))(assert (not (= (bvslt a b) (and (= a #b1) (= b #b0)))))(check-sat)";
    assert!(native(problem)?);
    certificate("signed-lt-one-bit", problem)?;
    Ok(())
}

#[test]
fn signed_cset_refuses_wrong_predicates_and_overflow() -> TestResult {
    for (name, problem) in COMPILER_CASES {
        let op = &name[..3];
        let unsigned = problem.replace(&format!("(bv{op} a b)"), &format!("(bvu{} a b)", &op[1..]));
        let reversed = problem.replace(&format!("(bv{op} a b)"), &format!("(bv{op} b a)"));
        let overflow = problem.replace("(and (not (= ((_ extract", "(or (not (= ((_ extract");
        for changed in [unsigned, reversed, overflow] {
            assert_ne!(problem, changed);
            assert!(!native(&changed)?, "{name}");
            let (context, _, negative) = original(&changed)?;
            assert!(AlethePrinter::new(&context.terms)
                .format_bv_circuit_refutation(ProofId(7), &[negative])
                .is_none());
        }
    }
    Ok(())
}

#[test]
fn signed_circuit_preserves_source_and_budget_refusals() -> TestResult {
    let (context, root, negative) = original(COMPILER_CASES[0].1)?;
    let mut overrides = DetHashMap::default();
    overrides.insert(root, "false".into());
    assert!(
        AlethePrinter::new_with_overrides(&context.terms, Some(&overrides))
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none()
    );
    let printer = AlethePrinter::new_with_overrides_and_budget(&context.terms, None, Some(64));
    assert!(printer
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    assert!(printer.work_budget_exhausted());
    Ok(())
}

#[test]
fn signed_positive_shift_has_a_checked_general_circuit() -> TestResult {
    let problem = "(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (and (bvslt #x00 x) (bvule x (concat #b0 ((_ extract 7 1) x)))))(check-sat)";
    assert!(native(problem)?);
    certificate("signed-positive-shift", problem)?;
    Ok(())
}

#[test]
fn signed_order_refuses_malformed_operands_and_one_bit_dualities() -> TestResult {
    let mut terms = ay_core::TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(16));
    let c = terms.mk_bool(true);
    for op in ["bvslt", "bvsle", "bvsgt", "bvsge"] {
        for args in [vec![a, b], vec![a, c], vec![a]] {
            let root = terms.mk_app(Symbol::named(op), &args, Sort::Bool);
            let negative = terms.mk_not_raw(root);
            assert!(AlethePrinter::new(&terms)
                .format_bv_circuit_refutation(ProofId(7), &[negative])
                .is_none());
        }
    }
    // Carcara's signed PB rule has no empty low-bit sum at width one.
    // Direct bvslt is supported there, but its PB dualities stay refused.
    let problem = "(set-logic QF_BV)(declare-const a (_ BitVec 1))(declare-const b (_ BitVec 1))(assert (and (bvslt a b) (bvsge a b)))(check-sat)";
    assert!(native(problem)?);
    let (context, _, negative) = original(problem)?;
    assert!(AlethePrinter::new(&context.terms)
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    Ok(())
}
