// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Wire-lowering tests for `AletheRule::Reordering`.
//!
//! Unlike `fresh_def_bound`, this rule IS externally checkable: `reordering` is
//! a pinned Alethe rule in `CHECKABLE_ALETHE_RULES`, so the honest lowering is
//! its own name and the external checker re-runs the same permutation check
//! `validate_reordering` does.
//!
//! The near-misses these tests exist to prevent, both of which this campaign
//! has hit before on other rules:
//!
//! 1. **`hole`.** If the variant were not mapped in `AletheRule::name()`, the
//!    generic renderer's `wire_rule_for_printed_step` would fall through to
//!    `UNPROVED_STEP_RULE` and every one of these steps would ship as a hole —
//!    turning a proof the checker can re-derive into a `holey` document.
//! 2. **A name the checker does not implement** (carcara: `UnknownRule` =>
//!    `invalid`, which is *no* proof rather than a weaker one).
//!
//! Both are pinned by exact text below, not by a `contains`.

use super::*;
use ay_core::{AletheRule, Sort, TermStore};

/// `(step tN (cl (not (= a b)) (= b c) (not (= a c))) :rule reordering
///  :premises (t3))` — the exact shape the packed-EUF lane emits. (`mk_eq`
/// canonicalises operand order, which is why the printed equalities read
/// `(= b c)` / `(= a c)`.)
fn reordering_step(terms: &mut TermStore) -> ProofStep {
    let sort = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", sort.clone());
    let b = terms.mk_var("b", sort.clone());
    let c = terms.mk_var("c", sort);
    let eq_ab = terms.mk_eq(a, b);
    let eq_ca = terms.mk_eq(c, a);
    let eq_cb = terms.mk_eq(c, b);
    let not_ab = terms.mk_not_raw(eq_ab);
    let not_ca = terms.mk_not_raw(eq_ca);
    ProofStep::Step {
        rule: AletheRule::Reordering,
        clause: vec![not_ab, eq_cb, not_ca],
        premises: vec![ProofId(3)],
        args: Vec::new(),
    }
}

#[test]
fn a_reordering_step_lowers_to_the_reordering_wire_rule() {
    let mut terms = TermStore::new();
    let step = reordering_step(&mut terms);
    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(4))
        .expect("a permutation step must render, not error");
    assert_eq!(
        rendered,
        "(step t4 (cl (not (= a b)) (= b c) (not (= a c))) :rule reordering :premises (t3))"
    );
}

#[test]
fn a_reordering_step_never_lowers_to_hole_or_an_unknown_rule() {
    let mut terms = TermStore::new();
    let step = reordering_step(&mut terms);
    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(4))
        .expect("must render");
    assert!(!rendered.contains(":rule hole"), "{rendered}");
    assert!(!rendered.contains(":rule trust"), "{rendered}");
    assert!(!rendered.contains(":args"), "{rendered}");
    assert!(
        rendered.contains(":premises (t3)"),
        "the premise must survive: without it `reordering` proves nothing — {rendered}"
    );
    // The rule the document names must be one the pinned checker implements.
    assert!(ay_core::is_checkable_alethe_rule("reordering"));
    assert_eq!(
        ay_core::wire_rule_name("reordering"),
        "reordering",
        "the wire mapping must not silently withdraw the rule"
    );
}
