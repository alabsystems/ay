// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derived comparisons reach the complete blast through the pseudo-Boolean
//! rules, and only a refutable lemma prints.

use super::*;
use ay_core::{ProofStep, TermStore, TheoryLemmaKind};

/// `(cl (not (and (first x y) (second x y))))` over two 8-bit words.
fn lemma(terms: &mut TermStore, first: &str, second: &str) -> TermId {
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(8));
    let first = terms.mk_app(Symbol::named(first), vec![x, y], Sort::Bool);
    let second = terms.mk_app(Symbol::named(second), vec![x, y], Sort::Bool);
    let both = terms.mk_app(Symbol::named("and"), vec![first, second], Sort::Bool);
    terms.mk_not_raw(both)
}

fn printed(first: &str, second: &str) -> String {
    let mut terms = TermStore::new();
    let literal = lemma(&mut terms, first, second);
    let step = ProofStep::TheoryLemma {
        theory: "bv".to_string(),
        clause: vec![literal],
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlast,
        lia: None,
    };
    AlethePrinter::new(&terms)
        .format_step(&step, ProofId(1))
        .unwrap_or_else(|error| panic!("({first}, {second}) must print: {error:?}"))
}

/// Each derived comparison conjoined with its complement is refuted without a
/// hole, through its own `pbblast_*` rule, and the non-strict ones through
/// `la_generic` as well.
#[test]
fn a_derived_comparison_and_its_complement_print_a_complete_refutation() {
    for (derived, complement) in [
        ("bvugt", "bvule"),
        ("bvuge", "bvult"),
        ("bvsgt", "bvsle"),
        ("bvsge", "bvslt"),
    ] {
        let text = printed(derived, complement);
        assert!(
            !text.contains(":rule hole") && !text.contains(":rule trust"),
            "({derived}, {complement}) must print without a hole:\n{}",
            &text[..text.len().min(400)]
        );
        assert!(text.contains(&format!(":rule pbblast_{derived}")));
        assert!(text.contains(":rule la_generic"));
    }
}

/// A satisfiable conjunction is never dressed as a refutation.
#[test]
fn a_satisfiable_pair_of_derived_comparisons_stays_a_hole() {
    for (first, second) in [("bvugt", "bvuge"), ("bvsgt", "bvsge"), ("bvsle", "bvule")] {
        let text = printed(first, second);
        assert!(
            text.contains(":rule hole"),
            "({first}, {second}) is satisfiable and must not print a refutation"
        );
    }
}

#[test]
fn an_unchecked_order_rule_is_refused_before_any_document_state_changes() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let mut blaster = Blaster::new(&printer, ProofId(7), "@order_".into());
    let out_of_range = SRef::pos(u32::MAX);
    let before_next = blaster.next_id;
    let before_steps = blaster.steps.clone();
    let before_text = blaster.text_used;
    let before_planned = blaster.planned.len();
    let before_work = printer.work_used();

    assert_eq!(
        blaster.equate(out_of_range, out_of_range, "invented"),
        None,
        "rule conversion must refuse before the circuit references are read"
    );
    assert_eq!(blaster.next_id, before_next);
    assert_eq!(blaster.steps, before_steps);
    assert_eq!(blaster.text_used, before_text);
    assert_eq!(blaster.planned.len(), before_planned);
    assert_eq!(printer.work_used(), before_work);
}
