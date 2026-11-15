// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{certificate, native, original, TestResult};
use super::*;

fn signed_overflow(width: u32, subtract: bool) -> String {
    let op = if subtract { "bvsub" } else { "bvadd" };
    let msb = width - 1;
    let value = format!("({op} a b)");
    let exact = format!("({op} ((_ sign_extend 1) a) ((_ sign_extend 1) b))");
    let spec = format!("(not (= {exact} ((_ sign_extend 1) {value})))");
    let same = format!("(= ((_ extract {msb} {msb}) a) ((_ extract {msb} {msb}) b))");
    let signs = if subtract {
        format!("(not {same})")
    } else {
        same
    };
    let changed =
        format!("(not (= ((_ extract {msb} {msb}) a) ((_ extract {msb} {msb}) {value})))");
    let machine = format!("(and {signs} {changed})");
    format!("(set-logic QF_BV)(declare-const a (_ BitVec {width}))(declare-const b (_ BitVec {width}))(assert (not (= (concat (ite {spec} #b1 #b0) {value}) (concat (ite {machine} #b1 #b0) {value}))))(check-sat)")
}

fn unsigned_overflow(width: u32, subtract: bool) -> String {
    let op = if subtract { "bvsub" } else { "bvadd" };
    let value = format!("({op} a b)");
    let exact = format!("({op} ((_ zero_extend 1) a) ((_ zero_extend 1) b))");
    let spec = format!("(not (= {exact} ((_ zero_extend 1) {value})))");
    let machine = if subtract {
        "(bvult a b)".into()
    } else {
        format!("(bvult {value} a)")
    };
    format!("(set-logic QF_BV)(declare-const a (_ BitVec {width}))(declare-const b (_ BitVec {width}))(assert (not (= (concat (ite {spec} #b1 #b0) {value}) (concat (ite {machine} #b1 #b0) {value}))))(check-sat)")
}

#[test]
fn unsigned_checked_overflow_uses_the_complete_widened_arithmetic() -> TestResult {
    for width in [1, 8, 64] {
        for subtract in [false, true] {
            let problem = unsigned_overflow(width, subtract);
            let name = format!("unsigned-overflow-{width}-{subtract}");
            assert!(native(&problem)?, "{name}");
            certificate(&name, &problem)?;
        }
    }
    Ok(())
}

#[test]
fn unsigned_checked_overflow_rejects_changed_carry_or_borrow() -> TestResult {
    for subtract in [false, true] {
        let problem = unsigned_overflow(8, subtract);
        let wrong = problem.replace("bvult", "bvuge");
        assert!(!native(&wrong)?);
        let (context, _, negative) = original(&wrong)?;
        assert!(AlethePrinter::new(&context.terms)
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none());
    }
    Ok(())
}

#[test]
fn signed_checked_overflow_uses_the_complete_widened_arithmetic() -> TestResult {
    for width in [1, 8, 64] {
        for subtract in [false, true] {
            let problem = signed_overflow(width, subtract);
            let name = format!("signed-overflow-{width}-{subtract}");
            assert!(native(&problem)?, "{name}");
            certificate(&name, &problem)?;
        }
    }
    Ok(())
}

#[test]
fn signed_checked_overflow_rejects_changed_overflow_bit() -> TestResult {
    for subtract in [false, true] {
        let problem = signed_overflow(8, subtract);
        let changed = problem.replacen("(ite (and ", "(ite (or ", 1);
        assert_ne!(problem, changed);
        assert!(!native(&changed)?);
        let (context, _, negative) = original(&changed)?;
        assert!(AlethePrinter::new(&context.terms)
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none());
    }
    Ok(())
}

#[test]
fn arithmetic_negations_keep_nested_polarity_and_conditional_values() -> TestResult {
    for width in [1, 9, 64, 128] {
        let problem = format!("(set-logic QF_BV)(declare-const a (_ BitVec {width}))(declare-const c Bool)(assert (not (= (ite (ite c true false) (bvneg (bvnot a)) ((_ sign_extend 0) a)) (ite c (bvadd a (_ bv1 {width})) a))))(check-sat)");
        assert!(native(&problem)?, "{width}");
        certificate(&format!("negation-ite-{width}"), &problem)?;
    }
    Ok(())
}

#[test]
fn arithmetic_rejects_bad_widths_and_unbound_condition() {
    let mut terms = ay_core::TermStore::new();
    let bit = terms.mk_bool(true);
    let word = terms.mk_var("a", Sort::bitvec(8));
    for malformed in [
        terms.mk_app(
            Symbol::indexed("sign_extend", vec![1]),
            &[word],
            Sort::bitvec(8),
        ),
        terms.mk_app(Symbol::named("bvsub"), &[word, bit], Sort::bitvec(8)),
        terms.mk_app(Symbol::named("ite"), &[word, word, word], Sort::bitvec(8)),
    ] {
        let eq = terms.mk_app(Symbol::named("="), &[malformed, word], Sort::Bool);
        let root = terms.mk_not_raw(eq);
        let negative = terms.mk_not_raw(root);
        assert!(AlethePrinter::new(&terms)
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none());
    }
}

#[test]
fn original_compiler_checked_overflow_formulas_have_native_and_exported_proofs() -> TestResult {
    for (name, input) in [
        (
            "original-sadd",
            include_str!("../fixtures/checked-sadd-64.smt2"),
        ),
        (
            "original-ssub",
            include_str!("../fixtures/checked-ssub-64.smt2"),
        ),
        (
            "original-uadd",
            include_str!("../fixtures/checked-uadd-64.smt2"),
        ),
        (
            "original-usub",
            include_str!("../fixtures/checked-usub-64.smt2"),
        ),
    ] {
        assert!(native(input)?, "{name}");
        certificate(name, input)?;
    }
    Ok(())
}
