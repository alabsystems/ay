// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A congruence premise that quotes the AUTHORED spelling of a bit-vector
//! literal while the congruence conclusion prints the canonical one.
//!
//! The authored-assume override re-spells a whole assumed equality — here
//! `(= mem2 (store mem idx #xAA))` — never its subterms, so the congruence
//! that consumes it prints the same internal store as
//! `(store mem idx #b10101010)`. The two texts are ONE term to carcara's
//! parser, but the premise-spelling bridge used to demand an arithmetic
//! identity between them and refused the whole document. This is the exact
//! shape of QF_ABV `csplit_repro_many_trivial_selects_unsat` (and the first
//! refusal of the `model_checker_consumer_quantified_safety` `uf_record` / `wide_table*`
//! rows, whose premises quote `(_ bv65 64)` and `(_ bv4 8)`), which lost a
//! Carcara-valid certificate once 779076535 retained the native resolution.
//!
//! The MUTATION DIFFERENTIAL at the bottom keeps the refusal honest: a premise
//! quoting a different VALUE or a different WIDTH is not a spelling of the same
//! term, and the printer must go back to refusing.

use crate::{try_export_alethe_with_problem_scope_and_overrides, AlethePrintError};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;

struct BvLiteralPremiseFixture {
    terms: TermStore,
    proof: Proof,
    overrides: DetHashMap<TermId, String>,
    scope: Vec<TermId>,
}

/// `authored` is the text the problem wrote for the assumed equality; the
/// internal store always carries the 8-bit value `170` (`#xAA`).
fn build(authored: &str, reversed: bool) -> BvLiteralPremiseFixture {
    let mut terms = TermStore::new();
    let bv8 = Sort::bitvec(8);
    let bv32 = Sort::bitvec(32);
    let array = Sort::array(bv32.clone(), bv8.clone());
    let mem = terms.mk_var("mem", array.clone());
    let mem2 = terms.mk_var("mem2", array.clone());
    let idx = terms.mk_var("idx", bv32);
    let value = terms.mk_bitvec(BigInt::from(0xAA), 8);
    // Raw applications: the smart constructors would fold the read-over-write
    // this fixture needs to keep visible.
    let store = terms.mk_app(Symbol::named("store"), [mem, idx, value], array);
    let assumed = if reversed {
        terms.mk_app(Symbol::named("="), [store, mem2], Sort::Bool)
    } else {
        terms.mk_app(Symbol::named("="), [mem2, store], Sort::Bool)
    };
    let left = terms.mk_app(Symbol::named("select"), [mem2, idx], bv8.clone());
    let right = terms.mk_app(Symbol::named("select"), [store, idx], bv8);
    let conclusion = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);

    let mut overrides = DetHashMap::default();
    overrides.insert(assumed, authored.to_string());

    let mut proof = Proof::new();
    let premise = proof.add_assume(assumed, None);
    proof.add_rule_step(AletheRule::Cong, vec![conclusion], vec![premise], vec![]);

    BvLiteralPremiseFixture {
        terms,
        proof,
        overrides,
        scope: vec![assumed],
    }
}

fn export(fixture: &BvLiteralPremiseFixture) -> Result<String, AlethePrintError> {
    try_export_alethe_with_problem_scope_and_overrides(
        &fixture.proof,
        &fixture.terms,
        &fixture.scope,
        Some(&fixture.overrides),
    )
}

#[test]
fn authored_bitvector_literal_in_a_premise_is_bridged_by_refl() {
    let fixture = build("(= mem2 (store mem idx #xAA))", false);
    let output = export(&fixture)
        .expect("the premise quotes the same term in another literal spelling and must render");
    assert!(
        output.contains("(assume t0 (= mem2 (store mem idx #xAA)))"),
        "the assume must keep the authored spelling the problem matches: {output}"
    );
    assert!(
        output.contains(
            "(step t1.ac0.r (cl (= (store mem idx #xAA) (store mem idx #b10101010))) :rule refl)"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t1.ac0 (cl (= mem2 (store mem idx #b10101010))) :rule trans :premises (t0 t1.ac0.r))"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t1 (cl (= (select mem2 idx) (select (store mem idx #b10101010) idx))) :rule cong :premises (t1.ac0))"
        ),
        "{output}"
    );
    assert!(!output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule trust"), "{output}");
}

/// The indexed `(_ bvN W)` spelling the `uf_record` row quotes, and a premise
/// stored in the opposite orientation (carcara's `trans` reorients a link).
#[test]
fn indexed_literal_spelling_in_a_reversed_premise_is_bridged_by_refl() {
    let fixture = build("(= (store mem idx (_ bv170 8)) mem2)", true);
    let output = export(&fixture).expect("a reversed premise is still the licensing hypothesis");
    assert!(
        output.contains(
            "(step t1.ac0.r (cl (= (store mem idx (_ bv170 8)) (store mem idx #b10101010))) :rule refl)"
        ),
        "{output}"
    );
    assert!(
        output.contains(":rule cong :premises (t1.ac0))"),
        "{output}"
    );
    assert!(!output.contains(":rule hole"), "{output}");
}

/// MUTATION DIFFERENTIAL (value). `#xAB` is not a spelling of `#xAA`; no
/// `refl` may relate them and the refusal must survive, naming both texts.
#[test]
fn a_premise_quoting_a_different_value_is_still_refused() {
    let fixture = build("(= mem2 (store mem idx #xAB))", false);
    let error = export(&fixture).expect_err("#xAB and #xAA are different terms");
    let reason = format!("{error}");
    assert!(
        reason.contains("position-preserving congruence"),
        "the loud refusal must survive: {reason}"
    );
    assert!(
        reason.contains(r#"left="(store mem idx #xAB)""#)
            && reason.contains(r#"right="(store mem idx #b10101010)""#),
        "the refusal must name the two spellings it could not relate: {reason}"
    );
}

/// MUTATION DIFFERENTIAL (width). `#x00AA` has the same value at width 16; it
/// is a different sort, so it must not be admitted as a respelling either.
#[test]
fn a_premise_quoting_a_different_width_is_still_refused() {
    let fixture = build("(= mem2 (store mem idx #x00AA))", false);
    let error = export(&fixture).expect_err("a 16-bit literal is not the 8-bit term");
    assert!(
        format!("{error}").contains("position-preserving congruence"),
        "{error}"
    );
}
