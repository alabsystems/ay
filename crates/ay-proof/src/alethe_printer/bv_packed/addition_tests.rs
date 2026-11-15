// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::TermStore;

pub(super) fn certificate(name: &str, terms: &TermStore, equality: TermId, declarations: &str) {
    let printer = AlethePrinter::new(terms);
    let steps = printer
        .format_bv_packed_identity(ProofId(7), &[equality])
        .expect(name);
    assert!(!steps.contains(":rule hole") && !steps.contains(":rule trust"));
    let assertion = format!("(not {})", printer.format_term(equality));
    let problem =
        format!("(set-logic QF_ABV)\n{declarations}\n(assert {assertion})\n(check-sat)\n");
    let proof = format!(
        "(assume a {assertion})\n{steps}(step done (cl) :rule resolution :premises (a t7))\n"
    );
    let certificate = serde_json::json!({"type":"alethe_certificate", "version":"1.0", "problem":problem, "proof":proof});
    let path = std::env::temp_dir().join(format!(
        "ay-packed-address-{}-{name}.json",
        std::process::id()
    ));
    std::fs::write(&path, serde_json::to_vec(&certificate).expect("JSON")).expect("certificate");
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn packed_constant_addition_exports_commuted_constants_and_carries() {
    for (width, offset) in [(1, 1u128), (9, 511), (64, 9), (128, u128::MAX)] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("base", Sort::bitvec(width));
        let c = terms.mk_bitvec(offset.into(), width);
        let left = terms.mk_app(Symbol::named("bvadd"), [x, c], Sort::bitvec(width));
        let right = terms.mk_app(Symbol::named("bvadd"), [c, x], Sort::bitvec(width));
        let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
        certificate(
            &format!("commute-{width}"),
            &terms,
            equality,
            &format!("(declare-const base (_ BitVec {width}))"),
        );
    }
}

#[test]
fn packed_constant_addition_exports_zero_and_closed_wrapping_sum() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("base", Sort::bitvec(9));
    let max = terms.mk_bitvec(511.into(), 9);
    let one = terms.mk_bitvec(1.into(), 9);
    let zero = terms.mk_app(Symbol::named("bvadd"), [max, one], Sort::bitvec(9));
    let actual = terms.mk_app(Symbol::named("bvadd"), [zero, x], Sort::bitvec(9));
    let equality = terms.mk_app(Symbol::named("="), [actual, x], Sort::Bool);
    certificate(
        "wrap-zero",
        &terms,
        equality,
        "(declare-const base (_ BitVec 9))",
    );
}

#[test]
fn packed_addition_decomposes_symbolic_pairs_and_refuses_bad_widths() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("base", Sort::bitvec(9));
    let y = terms.mk_var("other", Sort::bitvec(9));
    let zero = terms.mk_bitvec(0.into(), 8);
    let symbolic = terms.mk_app(Symbol::named("bvadd"), [x, y], Sort::bitvec(9));
    let reflexive = terms.mk_app(Symbol::named("="), [symbolic, symbolic], Sort::Bool);
    certificate(
        "symbolic-word",
        &terms,
        reflexive,
        "(declare-const base (_ BitVec 9))\n(declare-const other (_ BitVec 9))",
    );
    let malformed = terms.mk_app(Symbol::named("bvadd"), [zero, x], Sort::bitvec(9));
    for (actual, expected) in [(malformed, malformed), (symbolic, x)] {
        let equality = terms.mk_app(Symbol::named("="), [actual, expected], Sort::Bool);
        assert!(AlethePrinter::new(&terms)
            .format_bv_packed_identity(ProofId(7), &[equality])
            .is_none());
    }
}

#[test]
fn packed_carry_export_charges_failed_attempts_against_the_outer_budget() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("base", Sort::bitvec(128));
    let one = terms.mk_bitvec(1.into(), 128);
    let value = terms.mk_app(Symbol::named("bvadd"), [x, one], Sort::bitvec(128));
    let equality = terms.mk_app(Symbol::named("="), [value, value], Sort::Bool);
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(1024));
    assert!(printer
        .format_bv_packed_identity(ProofId(7), &[equality])
        .is_none());
    assert!(printer.work_budget_exhausted());
    let charged = printer.work_used();
    assert!(charged < 16_384, "stops during the first bounded word");
    assert!(printer
        .format_bv_packed_identity(ProofId(8), &[equality])
        .is_none());
    assert_eq!(
        printer.work_used(),
        charged,
        "exhaustion stops another candidate"
    );
}
