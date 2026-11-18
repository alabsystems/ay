// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public-export regressions: a mixed BV lemma is checked, not allowed.
use super::{assert_carcara_accepts, assert_carcara_verdict};
use ay_core::kani_compat::DetHashMap;
use ay_core::{Proof, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};
use ay_proof::{
    checked_bv_bitblast_lowering_supported, try_export_alethe_with_problem_scope_and_overrides,
};

struct Fixture {
    terms: TermStore,
    proof: Proof,
    assumptions: Vec<TermId>,
    consequence: TermId,
    problem: String,
}

fn fixture(width: u32, increment: u32, kind: TheoryLemmaKind) -> Fixture {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(width);
    let x = terms.mk_var("x", word.clone());
    let y = terms.mk_var("y", word.clone());
    let p = terms.mk_var("p", Sort::Bool);
    let one = terms.mk_bitvec(1.into(), width);
    let other = terms.mk_bitvec(increment.into(), width);
    let left = terms.mk_app(Symbol::named("bvadd"), [x, one], word.clone());
    let right = terms.mk_app(Symbol::named("bvadd"), [y, other], word);
    let premise = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let consequence = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let not_premise = terms.mk_not_raw(premise);
    let not_consequence = terms.mk_not_raw(consequence);
    let not_p = terms.mk_not_raw(p);
    // Two positive literals, in different positions relative to the negative
    // premise. The unrelated p must also be normalized before the final id.
    let clause = vec![consequence, not_premise, p];
    assert!(!checked_bv_bitblast_lowering_supported(
        &terms, &kind, &clause, None
    ));
    let mut proof = Proof::new();
    let h0 = proof.add_assume(premise, None);
    let h1 = proof.add_assume(not_consequence, None);
    let h2 = proof.add_assume(not_p, None);
    let lemma = proof.add_theory_lemma_with_kind("bv", clause, kind);
    let first = proof.add_resolution(vec![consequence, p], premise, lemma, h0);
    let second = proof.add_resolution(vec![p], consequence, first, h1);
    proof.add_resolution(vec![], p, second, h2);
    Fixture {
        terms,
        proof,
        assumptions: vec![premise, not_consequence, not_p],
        consequence,
        problem: format!(
            "(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))\n\
             (declare-const y (_ BitVec {width}))\n(declare-const p Bool)\n\
             (assert (= x y))\n\
             (assert (not (= (bvadd x (_ bv1 {width})) (bvadd y (_ bv{increment} {width})))))\n\
             (assert (not p))\n(check-sat)\n"
        ),
    }
}

fn export(f: &Fixture, overrides: Option<&DetHashMap<TermId, String>>) -> String {
    try_export_alethe_with_problem_scope_and_overrides(
        &f.proof,
        &f.terms,
        &f.assumptions,
        overrides,
    )
    .expect("the public exporter retains a checked document or an honest hole")
}

#[test]
fn mixed_bv_clause_positive_literals_are_derived_and_carcara_valid() {
    for width in [4, 8] {
        for kind in [
            TheoryLemmaKind::BvBitBlast,
            TheoryLemmaKind::BvBitBlastGate {
                gate_type: ay_core::BvGateType::Add,
                width,
            },
        ] {
            let f = fixture(width, 1, kind);
            let document = export(&f, None);
            assert!(!document.contains(":rule hole"), "{document}");
            assert!(!document.contains(":rule trust"), "{document}");
            assert!(document.contains(":rule and_neg"), "{document}");
            assert!(document.matches(":rule not_not").count() >= 2, "{document}");
            assert_carcara_accepts("mixed_bv_clause", &f.problem, &document);
        }
    }
}

#[test]
fn mixed_bv_clause_sat_twin_retains_an_honest_hole() {
    // x=y=0, p=false satisfies the problem when the second increment is 2.
    let f = fixture(4, 2, TheoryLemmaKind::BvBitBlast);
    let document = export(&f, None);
    assert!(document.contains(":rule hole"), "{document}");
    assert_carcara_verdict("mixed_bv_clause_sat", &f.problem, &document, "holey");
}

#[test]
fn mixed_bv_clause_authored_literal_spelling_and_changed_value_are_distinct() {
    let f = fixture(8, 1, TheoryLemmaKind::BvBitBlast);
    for (surface, expected) in [
        ("(= (bvadd x #x01) (bvadd y #x01))", "valid"),
        ("(= (bvadd x #x01) (bvadd y #x02))", "invalid"),
    ] {
        let mut overrides = DetHashMap::default();
        overrides.insert(f.consequence, surface.to_string());
        match try_export_alethe_with_problem_scope_and_overrides(
            &f.proof,
            &f.terms,
            &f.assumptions,
            Some(&overrides),
        ) {
            Ok(document) => {
                if expected == "invalid" {
                    assert!(document.contains(":rule hole"), "{document}");
                }
                assert_carcara_verdict("mixed_bv_clause_surface", &f.problem, &document, expected);
            }
            Err(_) => assert_eq!(expected, "invalid", "an unchanged value must be exportable"),
        }
    }
}

#[test]
fn mixed_bv_clause_double_negation_step_is_checked_by_carcara() {
    let f = fixture(4, 1, TheoryLemmaKind::BvBitBlast);
    let document = export(&f, None);
    assert!(!document.contains(":rule hole"), "{document}");
    let needle = "(cl (not (not (not p))) p) :rule not_not";
    assert_eq!(document.matches(needle).count(), 1, "{document}");
    let forged = document.replacen(needle, "(cl (not (not (not p))) (not p)) :rule not_not", 1);
    assert_carcara_verdict(
        "mixed_bv_clause_bad_not_not",
        &f.problem,
        &forged,
        "invalid",
    );
}
