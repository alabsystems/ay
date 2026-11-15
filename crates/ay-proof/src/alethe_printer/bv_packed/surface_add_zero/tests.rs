// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::TermStore;

#[test]
fn zero_addition_surface_bridges_export_checked_circuits_in_both_directions() {
    for (width, zero) in [
        (1, "#b0"),
        (8, "#x00"),
        (64, "(_ bv0 64)"),
        (128, "(_ bv0 128)"),
    ] {
        let mut terms = TermStore::new();
        let variable = terms.mk_var("p", Sort::bitvec(width));
        let printer = AlethePrinter::new(&terms);
        for (order, sum) in [format!("(bvadd p {zero})"), format!("(bvadd {zero} p)")]
            .iter()
            .enumerate()
        {
            for reversed in [false, true] {
                let (left, right) = if reversed {
                    ("p", sum.as_str())
                } else {
                    (sum.as_str(), "p")
                };
                let steps = printer
                    .format_bv_add_zero_surface_equivalence("bridge", left, right, variable)
                    .unwrap()
                    .join("\n");
                assert!(!steps.contains(":rule hole") && !steps.contains(":rule trust"));
                let assertion = format!("(not (= {left} {right}))");
                let problem = format!("(set-logic QF_BV)(declare-const p (_ BitVec {width}))(assert {assertion})(check-sat)");
                let proof = format!("(assume premise {assertion})\n{steps}\n(step done (cl) :rule resolution :premises (premise bridge))\n");
                let path = std::env::temp_dir().join(format!(
                    "ay-surface-add-zero-{width}-{order}-{reversed}-{}.json",
                    std::process::id()
                ));
                std::fs::write(&path,serde_json::to_vec(&serde_json::json!({
                    "type":"alethe_certificate", "version":"1.0", "problem":problem, "proof":proof
                })).unwrap()).unwrap();
                println!("independent replay certificate: {}", path.display());
            }
        }
    }
}

#[test]
fn surface_bridge_refuses_changed_values_widths_heads_symbols_and_endpoints() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("p", Sort::bitvec(8));
    let printer = AlethePrinter::new(&terms);
    for (left, right) in [
        ("(bvadd p #x01)", "p"),
        ("(bvadd p #b0)", "p"),
        ("(bvadd q #x00)", "p"),
        ("(bvadd p #x00)", "q"),
        ("(bvadd p #x00 #x00)", "p"),
        ("(bvmul p #x00)", "p"),
        ("(bvadd p #x00)", "(bvadd #x00 p)"),
    ] {
        assert!(
            printer
                .format_bv_add_zero_surface_equivalence("bridge", left, right, variable)
                .is_none(),
            "{left} versus {right}"
        );
    }
    let zero = terms.mk_bitvec(0.into(), 8);
    assert!(AlethePrinter::new(&terms)
        .format_bv_add_zero_surface_equivalence("bridge", "(bvadd p #x00)", "p", zero)
        .is_none());
}

#[test]
fn surface_bridge_obeys_the_enclosing_output_work_budget() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("p", Sort::bitvec(128));
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(1024));
    assert!(printer
        .format_bv_add_zero_surface_equivalence("bridge", "(bvadd p (_ bv0 128))", "p", variable)
        .is_none());
    assert!(printer.work_budget_exhausted());
    let used = printer.work_used();
    assert!(printer
        .format_bv_add_zero_surface_equivalence("again", "(bvadd p (_ bv0 128))", "p", variable)
        .is_none());
    assert_eq!(printer.work_used(), used);
}
