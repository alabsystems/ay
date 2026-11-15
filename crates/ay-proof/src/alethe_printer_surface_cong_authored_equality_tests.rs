// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A congruence position whose two PRINTED spellings are an equality the
//! PROBLEM asserts.
//!
//! Equality substitution rewrites `(+ F a)` to `1` because the query asserts
//! `(= (+ F a) 1)`. Both sides of the resulting congruence conclusion then hold
//! the SAME internal argument, while the left still prints the authored
//! spelling its surface override records and the right prints the canonical
//! `1`. Internally the position is reflexive and carries no premise, so nothing
//! in the proof object explains the divergence and the narrow
//! multiplication-commutation repair declines — which cost QF_LIA
//! `CircularTrains-PT-096__RC-02` its whole (complete, trust-free) certificate.
//!
//! The repair reads the reason off the problem: the `assume` carrying that
//! equality. The MUTATION DIFFERENTIAL at the bottom is what makes that a
//! derivation rather than a fabricated bridge — change the asserted constant
//! and the bridge must stop applying and the printer must go back to refusing.

use crate::{try_export_alethe_with_problem_scope_and_overrides, AlethePrintError};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;

fn raw_equality(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

/// The whole fixture, parameterised by the constant the problem asserts the
/// authored sum to equal (`asserted`) and the constant the congruence
/// conclusion actually carries (`substituted`).
///
/// With `asserted == substituted` the assume is the reason the two spellings
/// denote the same term; with `asserted != substituted` the problem relates the
/// sum to a DIFFERENT value and no honest bridge exists.
struct SurfaceCongFixture {
    terms: TermStore,
    proof: Proof,
    overrides: DetHashMap<TermId, String>,
    scope: Vec<TermId>,
}

fn build(asserted: i64, substituted: i64, reverse_assume: bool) -> SurfaceCongFixture {
    let mut terms = TermStore::new();
    let f = terms.mk_var("F", Sort::Int);
    let a = terms.mk_var("a", Sort::Int);
    let sum = terms.mk_app(Symbol::named("+"), [f, a], Sort::Int);
    let asserted_const = terms.mk_int(BigInt::from(asserted));
    let substituted_const = terms.mk_int(BigInt::from(substituted));
    let assumed = if reverse_assume {
        raw_equality(&mut terms, asserted_const, sum)
    } else {
        raw_equality(&mut terms, sum, asserted_const)
    };

    // A second congruence position that DOES differ internally, so the step is
    // a real congruence with a real premise and the repair under test is not
    // the only thing holding it up.
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let c_eq_d = raw_equality(&mut terms, c, d);

    let left = terms.mk_app(Symbol::named("g"), [substituted_const, c], Sort::Int);
    let right = terms.mk_app(Symbol::named("g"), [substituted_const, d], Sort::Int);
    let conclusion = raw_equality(&mut terms, left, right);

    // The surface override: the LEFT application still prints its authored
    // first argument, the right prints the canonical constant.
    let mut overrides = DetHashMap::default();
    overrides.insert(left, "(g (+ F a) c)".to_string());

    let mut proof = Proof::new();
    let assume_id = proof.add_assume(assumed, None);
    let premise_id = proof.add_assume(c_eq_d, None);
    let _ = assume_id;
    proof.add_rule_step(AletheRule::Cong, vec![conclusion], vec![premise_id], vec![]);

    SurfaceCongFixture {
        terms,
        proof,
        overrides,
        // The problem declares `g` and applies it, exactly as it declares the
        // constants above; the exporter resolves a proof's function symbols
        // against the problem's applications (`application_heads.rs`).
        scope: vec![assumed, c_eq_d, conclusion],
    }
}

fn export(fixture: &SurfaceCongFixture) -> Result<String, AlethePrintError> {
    try_export_alethe_with_problem_scope_and_overrides(
        &fixture.proof,
        &fixture.terms,
        &fixture.scope,
        Some(&fixture.overrides),
    )
}

#[test]
fn authored_equality_discharges_a_reflexive_congruence_position() {
    let fixture = build(1, 1, false);
    let output = export(&fixture)
        .expect("the position is licensed by the asserted equality and must render, not decline");
    // The assume is cited, through a reflexive first leg so the bridge id
    // carries the clause the final `cong` reads.
    assert!(
        output.contains("(step t2.ac0.eq (cl (= (+ F a) (+ F a))) :rule refl)"),
        "{output}"
    );
    assert!(
        output.contains("(step t2.ac0 (cl (= (+ F a) 1)) :rule trans :premises (t2.ac0.eq t0))"),
        "{output}"
    );
    // The genuinely differing position still uses its own native premise.
    assert!(
        output
            .contains("(step t2 (cl (= (g (+ F a) c) (g 1 d))) :rule cong :premises (t2.ac0 t1))"),
        "{output}"
    );
    // No unproved step was introduced to buy the rendering.
    assert!(!output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule trust"), "{output}");
}

#[test]
fn a_reversed_authored_equality_is_reoriented_by_symm() {
    let fixture = build(1, 1, true);
    let output = export(&fixture).expect("a reversed assume is still the licensing hypothesis");
    assert!(
        output.contains("(step t2.ac0 (cl (= (+ F a) 1)) :rule symm :premises (t0))"),
        "{output}"
    );
    assert!(
        output
            .contains("(step t2 (cl (= (g (+ F a) c) (g 1 d))) :rule cong :premises (t2.ac0 t1))"),
        "{output}"
    );
    assert!(!output.contains(":rule hole"), "{output}");
}

/// MUTATION DIFFERENTIAL. Flip the truth of the source term: the problem now
/// asserts the authored sum equals `2` while the congruence substituted `1`.
/// The bridge must stop applying, and the printer must go back to refusing the
/// step rather than citing an assume for a clause it does not carry.
#[test]
fn a_different_asserted_value_stops_the_bridge_and_restores_the_refusal() {
    let fixture = build(2, 1, false);
    let error = export(&fixture)
        .expect_err("no assume relates `(+ F a)` to `1`, so nothing licenses the position");
    let reason = format!("{error}");
    assert!(
        reason.contains("position-preserving congruence"),
        "the loud refusal must survive: {reason}"
    );
    assert!(
        reason.contains(r#"left="(+ F a)""#) && reason.contains(r#"right="1""#),
        "the refusal must name the two spellings it could not relate: {reason}"
    );
}

/// The same flip in the reversed orientation: a `(= 2 (+ F a))` assume must not
/// be reoriented into a claim about `1`.
#[test]
fn a_different_asserted_value_stops_the_reversed_bridge_too() {
    let fixture = build(2, 1, true);
    let error = export(&fixture).expect_err("a reversed but unrelated assume licenses nothing");
    assert!(
        format!("{error}").contains("position-preserving congruence"),
        "{error}"
    );
}
