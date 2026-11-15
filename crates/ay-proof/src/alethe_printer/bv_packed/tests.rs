// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::TermStore;

#[path = "../../../tests/fixtures/packed_mask.rs"]
mod packed_mask;
use packed_mask::{query, Mutation};

fn root_equality(terms: &TermStore, root: TermId) -> TermId {
    let TermData::Not(equality) = terms.get(root) else {
        panic!("negated equality")
    };
    *equality
}

#[test]
fn packed_selector_constant_conditions_and_equal_branches_have_checked_steps() {
    for width in [1, 2, 8, 128] {
        for condition in [Some(true), Some(false), None] {
            let mut terms = TermStore::new();
            let x = terms.mk_var("x", Sort::bitvec(width));
            let y = terms.mk_var("y", Sort::bitvec(width));
            let c = match condition {
                Some(value) => terms.mk_bool(value),
                None => terms.mk_var("condition", Sort::Bool),
            };
            let no = if condition.is_none() { x } else { y };
            let selected = terms.mk_ite_raw(c, x, no);
            let expected = if condition == Some(false) { y } else { x };
            let equality = terms.mk_app(Symbol::named("="), [selected, expected], Sort::Bool);
            let printer = AlethePrinter::new(&terms);
            let steps = printer
                .format_bv_packed_identity(ProofId(7), &[equality])
                .expect("constant condition or equal branches");
            let assertion = format!("(not {})", printer.format_term(equality));
            let problem = format!(
                "(set-logic QF_BV)\n(declare-fun x () (_ BitVec {width}))\n\
                 (declare-fun y () (_ BitVec {width}))\n(declare-fun condition () Bool)\n\
                 (assert {assertion})\n(check-sat)\n"
            );
            let proof = format!("(assume a {assertion})\n{steps}(step done (cl) :rule resolution :premises (a t7))\n");
            let certificate = serde_json::json!({
                "type": "alethe_certificate", "version": "1.0", "problem": problem, "proof": proof,
            });
            let path = std::env::temp_dir().join(format!(
                "ay-packed-selector-{}-width{width}-{condition:?}.json",
                std::process::id()
            ));
            std::fs::write(&path, serde_json::to_vec(&certificate).expect("JSON"))
                .expect("certificate fixture");
            println!("independent replay certificate: {}", path.display());
        }
    }
}

#[test]
fn packed_selector_exports_discharge_all_cases_and_preserve_the_exact_problem() {
    for (name, mutation) in [
        ("canonical", Mutation::None),
        ("bit6", Mutation::WrongMaskBit),
    ] {
        let (terms, root) = query(mutation);
        let printer = AlethePrinter::new(&terms);
        let equality = root_equality(&terms, root);
        let steps = printer
            .format_bv_packed_identity(ProofId(7), &[equality])
            .expect("canonical selector identity exports");
        assert!(steps.contains(":rule bitblast_concat"));
        assert!(steps.contains(":rule bitblast_extract"));
        assert!(steps.contains(":rule subproof"));
        assert!(!steps.contains(":rule hole"));
        assert!(!steps.contains(":rule trust"));
        assert_eq!(
            steps.matches("(anchor ").count(),
            steps.matches(":discharge ").count()
        );
        let assertion = printer.format_term(root);
        let proof = format!(
            "(assume a {assertion})\n{steps}(step done (cl) :rule resolution :premises (a t7))\n"
        );
        let problem = format!(
            "(set-logic QF_BV)\n(declare-fun mask_bits () (_ BitVec 16))\n\
             (declare-fun true_lo () (_ BitVec 64))\n(declare-fun true_hi () (_ BitVec 64))\n\
             (declare-fun false_lo () (_ BitVec 64))\n(declare-fun false_hi () (_ BitVec 64))\n\
             (assert {assertion})\n(check-sat)\n"
        );
        let certificate = serde_json::json!({
            "type": "alethe_certificate", "version": "1.0", "problem": problem, "proof": proof,
        });
        // Retain exact bytes for independent checker replay by the local gate.
        // This unit test checks exporter behavior, not external acceptance.
        let path = std::env::temp_dir().join(format!(
            "ay-packed-selector-{}-{name}.json",
            std::process::id()
        ));
        std::fs::write(&path, serde_json::to_vec(&certificate).expect("JSON"))
            .expect("certificate fixture");
        println!("independent replay certificate: {}", path.display());
    }
}

#[test]
fn packed_selector_declines_wrong_data_choice_and_changed_surface() {
    for mutation in [Mutation::ReversedChoice, Mutation::WrongSourceByte] {
        let (terms, root) = query(mutation);
        assert!(AlethePrinter::new(&terms)
            .format_bv_packed_identity(ProofId(0), &[root_equality(&terms, root)])
            .is_none());
    }
    let (terms, root) = query(Mutation::None);
    let equality = root_equality(&terms, root);
    let TermData::App(_, args) = terms.get(equality) else {
        panic!("equality")
    };
    let mask = (0..terms.len())
        .map(|index| TermId(index as u32))
        .find(|term| matches!(terms.get(*term), TermData::Var(name, _) if name == "mask_bits"))
        .expect("mask variable");
    for changed in [equality, args[0], mask] {
        let mut overrides = DetHashMap::default();
        overrides.insert(changed, "false".into());
        assert!(AlethePrinter::new_with_overrides(&terms, Some(&overrides))
            .format_bv_packed_identity(ProofId(0), &[equality])
            .is_none());
    }
}

#[test]
fn packed_selector_validates_discarded_children_widths_and_depth() {
    let mut terms = TermStore::new();
    let byte = terms.mk_var("byte", Sort::bitvec(8));
    let malformed = terms.mk_app(
        Symbol::indexed("extract", vec![99, 92]),
        [byte],
        Sort::bitvec(8),
    );
    let joined = terms.mk_app(Symbol::named("concat"), [malformed, byte], Sort::bitvec(16));
    let projected = terms.mk_app(
        Symbol::indexed("extract", vec![7, 0]),
        [joined],
        Sort::bitvec(8),
    );
    let equality = terms.mk_app(Symbol::named("="), [projected, byte], Sort::Bool);
    assert!(AlethePrinter::new(&terms)
        .format_bv_packed_identity(ProofId(0), &[equality])
        .is_none());
    let wide = terms.mk_var("wide", Sort::bitvec(129));
    let equality = terms.mk_app(Symbol::named("="), [wide, wide], Sort::Bool);
    assert!(AlethePrinter::new(&terms)
        .format_bv_packed_identity(ProofId(0), &[equality])
        .is_none());
    let mut nested = byte;
    for _ in 0..=MAX_DEPTH {
        nested = terms.mk_app(
            Symbol::indexed("extract", vec![7, 0]),
            [nested],
            Sort::bitvec(8),
        );
    }
    let equality = terms.mk_app(Symbol::named("="), [nested, byte], Sort::Bool);
    assert!(AlethePrinter::new(&terms)
        .format_bv_packed_identity(ProofId(0), &[equality])
        .is_none());
}
