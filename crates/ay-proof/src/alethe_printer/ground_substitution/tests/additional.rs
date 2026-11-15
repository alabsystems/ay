// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn retained_letleak_lemmas_have_checked_wire_derivations() {
    // Retained diagnostic lemma shapes, using the standard unsigned-BV to Int
    // builtin in both the problem and proof. This fixture is not a production
    // alias adapter and does not establish a whole-query solver certificate.
    for (name, problem) in [
        (
            "letleak-instance",
            include_str!("fixtures/letleak-instance.smt2"),
        ),
        (
            "letleak-refutation",
            include_str!("fixtures/letleak-refutation.smt2"),
        ),
    ] {
        publish_fixture(name, parse_problem(problem.to_owned()));
    }
}

#[test]
fn oversized_text_and_indexed_equality_hypotheses_are_refused() {
    let (mut terms, mut clause, roots, _) = fixture(&["(= x 1)"], "(R x y)", "(R 1 y)");
    let source = roots[1];
    let huge = "x".repeat(MAX_INPUT + 1);
    for channel in 0..4 {
        let mut overrides = HashMap::default();
        if channel == 0 {
            overrides.insert(source, huge.clone());
        }
        let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
        match channel {
            1 => {
                printer
                    .let_bridge_renderings
                    .borrow_mut()
                    .insert(source, huge.clone());
            }
            2 => {
                printer
                    .skolem_overrides
                    .borrow_mut()
                    .insert(source, huge.clone());
            }
            3 => {
                printer
                    .format_cache
                    .borrow_mut()
                    .insert(source, huge.clone());
            }
            _ => {}
        }
        assert!(printer
            .format_ground_substitution(ProofId(5), &clause)
            .is_none());
        assert_eq!(
            printer.work_used(),
            MAX_NODES as u64,
            "must stop before copying text"
        );
    }
    let TermData::App(_, args) = terms.get(roots[0]) else {
        panic!("pin")
    };
    let fake = terms.mk_app(Symbol::indexed("=", vec![0]), args.clone(), Sort::Bool);
    clause[0] = terms.mk_not_raw(fake);
    assert!(AlethePrinter::new(&terms)
        .format_ground_substitution(ProofId(5), &clause)
        .is_none());
    let huge_name = terms.mk_var(huge, Sort::Bool);
    clause[0] = huge_name;
    let printer = AlethePrinter::new(&terms);
    assert!(printer
        .format_ground_substitution(ProofId(5), &clause)
        .is_none());
    assert_eq!(printer.work_used(), MAX_NODES as u64);
}

#[test]
fn printer_owned_alias_channels_cannot_change_the_lemma() {
    let (terms, clause, roots, _) = fixture(&["(= x 1)"], "(R x y)", "(R 1 y)");
    for is_skolem in [false, true] {
        let printer = AlethePrinter::new(&terms);
        if is_skolem {
            printer
                .skolem_overrides
                .borrow_mut()
                .insert(roots[1], "false".to_owned());
        } else {
            printer
                .let_bridge_renderings
                .borrow_mut()
                .insert(roots[1], "false".to_owned());
        }
        assert!(printer
            .format_ground_substitution(ProofId(5), &clause)
            .is_none());
    }
}
