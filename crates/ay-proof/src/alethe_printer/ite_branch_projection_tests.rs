// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
use super::*;

fn fixture(
    then: bool,
    reversed: bool,
    swapped: bool,
    packed: bool,
) -> (TermStore, Vec<TermId>, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let ite = terms.mk_ite_raw(c, a, b);
    let selected = if then { a } else { b };
    let pair = if reversed {
        [selected, ite]
    } else {
        [ite, selected]
    };
    let eq = terms.mk_app(Symbol::named("="), pair, Sort::Bool);
    let guard = if then { terms.mk_not_raw(c) } else { c };
    let mut clause = vec![guard, eq];
    if swapped {
        clause.swap(0, 1);
    }
    if packed {
        clause = vec![terms.mk_app(Symbol::named("or"), clause, Sort::Bool)];
    }
    (terms, clause, c, ite, eq)
}

#[test]
fn ite_projection_lowering_variants_emit_complete_consumer_certificates() {
    for then in [true, false] {
        for reversed in [false, true] {
            for swapped in [false, true] {
                for packed in [false, true] {
                    let (terms, clause, c, _, eq) = fixture(then, reversed, swapped, packed);
                    assert!(crate::recognize_ite_branch_projection(&terms, &clause));
                    let printer =
                        AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(1_000_000));
                    let lowered = printer
                        .format_ite_branch_projection(ProofId(0), &clause)
                        .expect("checked definition lowering");
                    assert!(!lowered.contains(":rule hole"));
                    let equality = printer.format_derived_literal(eq);
                    let condition = printer.format_derived_literal(c);
                    let fact = if then {
                        condition.clone()
                    } else {
                        format!("(not {condition})")
                    };
                    let problem = format!(
                        "(set-logic QF_UFLIA)\n(declare-const c Bool)\n(declare-const a Int)\n(declare-const b Int)\n(assert {fact})\n(assert (not {equality}))\n(check-sat)\n"
                    );
                    let flat = if packed {
                        let packed_text = printer.format_derived_literal(clause[0]);
                        let fields = split_application(&packed_text, "or")
                            .expect("actual packed literal order");
                        format!(
                            "\n(step flat (cl {}) :rule or :premises (t0))",
                            fields.join(" ")
                        )
                    } else {
                        String::new()
                    };
                    let premise = if packed { "flat" } else { "t0" };
                    let proof = format!(
                        "(assume h0 {fact})\n(assume h1 (not {equality}))\n{lowered}{flat}\n(step end (cl) :rule resolution :premises ({premise} h0 h1))\n"
                    );
                    println!(
                        "ITE_PROJECTION_CERT={}",
                        serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":proof})
                    );
                }
            }
        }
    }
}

#[test]
fn ite_projection_printed_role_mutations_and_exhausted_screen_refuse() {
    let (terms, clause, c, ite, eq) = fixture(true, false, false, false);
    for (term, text) in [
        (ite, "(= a b)"),
        (ite, "(ite c b a)"),
        (clause[0], "(not d)"),
        (eq, "(= (ite c a b) b)"),
    ] {
        let mut overrides = HashMap::default();
        overrides.insert(term, text.into());
        let mut work = 1_000_000;
        assert!(
            !checked_ite_branch_projection_lowering_supported(
                &terms,
                &clause,
                Some(&overrides),
                &mut work
            ),
            "{text}"
        );
    }
    // Consistent atom renaming preserves this tautology; it conveys no
    // source-premise authority, which the caller checks independently.
    let mut renamed = HashMap::default();
    renamed.insert(c, "d".into());
    let mut work = 100_000;
    assert!(checked_ite_branch_projection_lowering_supported(
        &terms,
        &clause,
        Some(&renamed),
        &mut work
    ));
    let mut work = 0;
    assert!(!checked_ite_branch_projection_lowering_supported(
        &terms, &clause, None, &mut work
    ));
    let mut work = 1;
    assert!(!checked_ite_branch_projection_lowering_supported(
        &terms, &clause, None, &mut work
    ));
    assert_eq!(work, 0);
    let mut work = 100_000;
    assert!(checked_ite_branch_projection_lowering_supported(
        &terms, &clause, None, &mut work
    ));
    assert!(work < 100_000);
}

#[test]
fn ite_projection_wide_malformed_packing_refuses_before_flattening() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let packed = terms.mk_app(Symbol::named("or"), vec![c; 4096], Sort::Bool);
    let mut work = 1;
    assert!(!checked_ite_branch_projection_lowering_supported(
        &terms,
        &[packed],
        None,
        &mut work
    ));
    assert_eq!(
        work, 1,
        "header refusal requires no render/flatten allowance"
    );
}

#[test]
fn ite_projection_composite_condition_and_mixed_bv_literals_keep_exact_value_width() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::bitvec(2));
    let q = terms.mk_var("q", Sort::bitvec(2));
    let condition = terms.mk_app(Symbol::named("="), [p, q], Sort::Bool);
    let one = terms.mk_bitvec(1.into(), 2);
    let memory = terms.mk_app(Symbol::named("ordinary_memory"), [q], Sort::bitvec(2));
    let ite = terms.mk_ite_raw(condition, one, memory);
    let equality = terms.mk_app(Symbol::named("="), [ite, one], Sort::Bool);
    let guard = terms.mk_not_raw(condition);
    for (literal, expected) in [
        ("(_ bv1 2)", true),
        ("(_ bv01 2)", true),
        ("(_ bv2 2)", false),
        ("(_ bv1 3)", false),
    ] {
        let mut overrides = HashMap::default();
        overrides.insert(ite, format!("(ite (= p q) {literal} (ordinary_memory q))"));
        let mut work = 100_000;
        assert_eq!(
            checked_ite_branch_projection_lowering_supported(
                &terms,
                &[guard, equality],
                Some(&overrides),
                &mut work
            ),
            expected,
            "{literal}"
        );
    }
}
