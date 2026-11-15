// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::kani_compat::DetHashMap;

/// Two DISTINCT `TermId`s for one fact: `(= s 0)` and `(= (+ s 0) 0)`.
/// The clause the producer mints for them is `(cl (= s 0) (not (= (+ s 0) 0)))`.
fn fixture() -> (TermStore, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let int = Sort::Int;
    let s = terms.mk_var("s", int.clone());
    let zero = terms.mk_int(0.into());
    let sum = terms.mk_app(Symbol::named("+"), [s, zero], int);
    let conclusion = terms.mk_app(Symbol::named("="), [s, zero], Sort::Bool);
    let hypothesis = terms.mk_app(Symbol::named("="), [sum, zero], Sort::Bool);
    let negated = terms.mk_not_raw(hypothesis);
    (terms, conclusion, hypothesis, negated)
}

#[test]
fn respelled_equality_implication_bridges_each_operand() {
    let (terms, conclusion, _, negated) = fixture();
    let overrides = DetHashMap::default();
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let steps = printer
        .format_respelled_atom_implication(ProofId(1), &[conclusion, negated])
        .expect("a poly-respelled atom implication must lower");
    assert!(
        steps.contains("(step t1.ri.0 (cl (= (+ s 0) s)) :rule poly_simp)"),
        "{steps}"
    );
    assert!(
        steps.contains("(step t1.ri.1 (cl (= 0 0)) :rule refl)"),
        "{steps}"
    );
    assert!(
        steps.contains(
            "(step t1.ri.e (cl (= (= (+ s 0) 0) (= s 0))) :rule cong :premises (t1.ri.0 t1.ri.1))"
        ),
        "{steps}"
    );
    assert!(steps.contains(":rule equiv_pos2"), "{steps}");
    assert!(
        steps.contains("(step t1 (cl (= s 0) (not (= (+ s 0) 0))) :rule resolution"),
        "{steps}"
    );
    assert!(
        !steps.contains(":rule hole") && !steps.contains(":rule trust"),
        "{steps}"
    );
    // MEASURED outside the harness: carcara 1.1.0 (git 9a352ee) answers
    // `valid` on exactly this derivation, and `invalid` at this step when the
    // operand bridge is perturbed to `(= (+ s 1) s)`.
}

#[test]
fn identically_printed_literals_bridge_by_refl() {
    let (terms, conclusion, hypothesis, negated) = fixture();
    // The hypothesis carries the conclusion's authored spelling: two
    // `TermId`s, one printed atom, so the equivalence is `refl`.
    let overrides = [(hypothesis, "(= s 0)".to_string())].into_iter().collect();
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let steps = printer
        .format_respelled_atom_implication(ProofId(1), &[conclusion, negated])
        .expect("an identically printed pair must lower");
    assert!(
        steps.contains("(step t1.ri.e (cl (= (= s 0) (= s 0))) :rule refl)"),
        "{steps}"
    );
    assert!(!steps.contains("poly_simp"), "{steps}");
    assert!(steps.contains(":rule equiv_pos2"), "{steps}");
}

#[test]
fn respelled_bridge_refuses_what_it_cannot_decide() {
    let mut terms = TermStore::new();
    let int = Sort::Int;
    let s = terms.mk_var("s", int.clone());
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let shifted_sum = terms.mk_app(Symbol::named("+"), [s, one], int);
    let conclusion = terms.mk_app(Symbol::named("="), [s, zero], Sort::Bool);
    // A DIFFERENT polynomial on the left operand.
    let shifted = terms.mk_app(Symbol::named("="), [shifted_sum, zero], Sort::Bool);
    let not_shifted = terms.mk_not_raw(shifted);
    // An order relation, which `la_generic` reads on its own.
    let order = terms.mk_app(Symbol::named("<"), [s, zero], Sort::Bool);
    let not_order = terms.mk_not_raw(order);
    let overrides = DetHashMap::default();
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    for (label, clause) in [
        ("different polynomial", vec![conclusion, not_shifted]),
        ("order relation", vec![order, not_order]),
        ("two positive literals", vec![conclusion, shifted]),
        ("not two literals", vec![conclusion]),
    ] {
        assert!(
            printer
                .format_respelled_atom_implication(ProofId(1), &clause)
                .is_none(),
            "{label}"
        );
    }
}

#[test]
fn outer_negation_override_must_match_the_proved_hypothesis() {
    let (terms, conclusion, _, negated) = fixture();
    for surface in [
        // Equivalent, but the existing derivation proves the independently
        // printed `(+ s 0)` hypothesis, not this separate outer-node spelling.
        "(not (= s 0))",
        "(not (= s 1))",
        "(not (= t 0))",
        "(= (+ s 0) 0)",
        "(not (not (= (+ s 0) 0)))",
    ] {
        for clause in [[conclusion, negated], [negated, conclusion]] {
            let overrides = [(negated, surface.to_string())].into_iter().collect();
            let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
            assert!(
                printer
                    .format_respelled_atom_implication(ProofId(1), &clause)
                    .is_none(),
                "{surface}"
            );
            // Exercise the real TheoryLemma dispatch too. With no Farkas
            // witness this route must retain its existing loud refusal,
            // never mistake a newly printed clause for the proved one.
            let step = ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: clause.to_vec(),
                farkas: None,
                kind: ay_core::TheoryLemmaKind::LraFarkas,
                lia: None,
            };
            assert!(
                matches!(
                    printer.format_step(&step, ProofId(1)),
                    Err(AlethePrintError::MissingFarkasAnnotation { .. })
                ),
                "{surface}"
            );
        }
    }
}

#[test]
fn consistent_negation_shells_preserve_both_clause_orders() {
    let (terms, conclusion, hypothesis, negated) = fixture();
    for hypothesis_surface in ["(= (+ s 0) 0)", "(= s 0)"] {
        for clause in [[conclusion, negated], [negated, conclusion]] {
            let overrides = [
                (hypothesis, hypothesis_surface.to_string()),
                (negated, format!("(not  {hypothesis_surface})")),
            ]
            .into_iter()
            .collect();
            let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
            let step = ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: clause.to_vec(),
                farkas: None,
                kind: ay_core::TheoryLemmaKind::LraFarkas,
                lia: None,
            };
            let text = printer
                .format_step(&step, ProofId(1))
                .expect("the actual negative literal names the bridged hypothesis");
            assert!(text.contains("t1.ri.e"), "{text}");
            assert!(
                text.contains(&format!(
                    "(step t1 {} :rule resolution",
                    printer.format_clause(&clause)
                )),
                "{text}"
            );
            assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
        }
    }
}

#[test]
fn negative_literal_binding_preserves_the_render_work_limit() {
    let (terms, conclusion, _, negated) = fixture();
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(1));
    assert!(printer
        .format_respelled_atom_implication(ProofId(1), &[conclusion, negated])
        .is_none());
    assert!(printer.work_budget_exhausted());
}
