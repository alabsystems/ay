// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn authored_fixture() -> (TermStore, Vec<TermId>, Vec<TermId>, String) {
    parse_problem(
        "(set-logic ALL)
        (declare-const x Int) (declare-const y Int)
        (declare-const v (_ BitVec 8))
        (assert (= x 1))
        (assert (= v #x01))
        (assert (or (not (= x 1)) (and (< y x) (= v #x01))))
        (assert (not (or false (and (< y 1) (= #x01 #x01)))))
        (check-sat)"
            .to_owned(),
    )
}

#[test]
fn ground_substitution_authored_literals_emit_explicit_surface_bridges() {
    let fixture = authored_fixture();
    let mut overrides = HashMap::default();
    for &root in &fixture.2[..fixture.2.len() - 1] {
        let canonical = crate::format_term_alethe(&fixture.0, root);
        overrides.insert(root, canonical.replace("#b00000001", "#x01"));
    }
    let target = *fixture.1.last().unwrap();
    overrides.insert(
        target,
        crate::format_term_alethe(&fixture.0, target).replace("#b00000001", "#x01"),
    );
    let mut allowance = MAX_WORK;
    assert!(checked_ground_substitution_lowering_supported(
        &fixture.0,
        &fixture.1,
        Some(&overrides),
        &mut allowance
    ));
    let printer =
        AlethePrinter::new_with_overrides_and_budget(&fixture.0, Some(&overrides), Some(MAX_WORK));
    let text = printer
        .format_ground_substitution(ProofId(20), &fixture.1)
        .unwrap();
    assert!(text.rfind("(assume ").unwrap() < text.find("(step ").unwrap());
    assert!(
        text.matches(":rule refl").count() >= 3,
        "pin, source and target each need an explicit bridge"
    );
    publish_overridden_fixture("authored-literals", fixture, Some(overrides));
}

#[test]
fn ground_substitution_authored_changes_and_budgets_still_refuse() {
    let (terms, clause, roots, _) = authored_fixture();
    for &root in roots[..roots.len() - 1].iter().chain(clause.last()) {
        let canonical = crate::format_term_alethe(&terms, root);
        let changed = if canonical.contains("#b00000001") {
            canonical.replace("#b00000001", "#x02")
        } else {
            canonical.replace(" 1)", " 2)")
        };
        assert_ne!(canonical, changed);
        let overrides = HashMap::from_iter([(root, changed)]);
        assert!(!checked_ground_substitution_lowering_supported(
            &terms,
            &clause,
            Some(&overrides),
            &mut MAX_WORK.clone()
        ));
    }
    let mut overrides = HashMap::default();
    for &root in &roots {
        overrides.insert(
            root,
            crate::format_term_alethe(&terms, root).replace("#b00000001", "#x01"),
        );
    }
    for mut work in [0, 1, 1024, 200_000] {
        assert!(!checked_ground_substitution_lowering_supported(
            &terms,
            &clause,
            Some(&overrides),
            &mut work
        ));
        assert_eq!(work, 0);
    }
}
