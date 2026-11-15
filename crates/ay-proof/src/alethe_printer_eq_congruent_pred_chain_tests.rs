// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The equality-predicate `eq_congruent_pred` lemma printed as the chain it
//! is, and the declines that must survive.
//!
//! The shape is QF_AX `three_store_chain`'s only hole: the conclusion atom
//! `(= v d)` (interned order) prints in the problem's `(= d v)`, so the
//! printed argument positions no longer pair with the hypotheses.

use crate::try_export_alethe_with_problem_scope_and_overrides;
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};

struct Equalities {
    terms: TermStore,
    /// `(= v v)`, `(= d c)`, `(= v c)`, `(= v d)`, each exactly as oriented.
    vv: TermId,
    dc: TermId,
    vc: TermId,
    vd: TermId,
}

fn equalities() -> Equalities {
    let mut terms = TermStore::new();
    let [v, c, d] = ["v", "c", "d"].map(|name| terms.mk_var(name, Sort::Int));
    let mut eq = |lhs, rhs| terms.mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
    let (vv, dc, vc, vd) = (eq(v, v), eq(d, c), eq(v, c), eq(v, d));
    Equalities {
        terms,
        vv,
        dc,
        vc,
        vd,
    }
}

/// `(= d c)`, `(= v c)` and `(not (= v d))` refuted through the
/// `EufCongruentPred` lemma `(cl (not (= v v)) (not (= d c)) (not (= v c))
/// (= v d))` and `eq_reflexive`; the lemma is `t3`.
fn refutation(fixture: &mut Equalities) -> Proof {
    let Equalities {
        terms,
        vv,
        dc,
        vc,
        vd,
    } = fixture;
    let (vv, dc, vc, vd) = (*vv, *dc, *vc, *vd);
    let negated = |terms: &mut TermStore, atom| terms.mk_not_raw(atom);
    let (not_vv, not_dc, not_vc, not_vd) = (
        negated(terms, vv),
        negated(terms, dc),
        negated(terms, vc),
        negated(terms, vd),
    );
    let mut proof = Proof::new();
    let hyp_dc = proof.add_assume(dc, None);
    let hyp_vc = proof.add_assume(vc, None);
    let hyp_vd = proof.add_assume(not_vd, None);
    let lemma = proof.add_step(ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause: vec![not_vv, not_dc, not_vc, vd],
        farkas: None,
        kind: TheoryLemmaKind::EufCongruentPred,
        lia: None,
    });
    let refl = proof.add_rule_step(AletheRule::EqReflexive, vec![vv], vec![], vec![]);
    let step = proof.add_resolution(vec![not_dc, not_vc, vd], vv, lemma, refl);
    let step = proof.add_resolution(vec![not_vc, vd], dc, step, hyp_dc);
    let step = proof.add_resolution(vec![vd], vc, step, hyp_vc);
    proof.add_resolution(Vec::new(), vd, step, hyp_vd);
    proof
}

fn export(fixture: &Equalities, proof: &Proof, overrides: &[(TermId, &str)]) -> String {
    let overrides: DetHashMap<TermId, String> = overrides
        .iter()
        .map(|&(term, spelling)| (term, spelling.to_string()))
        .collect();
    let scope: Vec<TermId> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    try_export_alethe_with_problem_scope_and_overrides(
        proof,
        &fixture.terms,
        &scope,
        Some(&overrides),
    )
    .expect("the refutation exports")
}

fn lemma_line(document: &str) -> &str {
    document
        .lines()
        .find(|line| line.starts_with("(step t3 "))
        .expect("the lemma is t3")
}

/// THE DEFECT, and its differential. With the conclusion printed in the
/// authored order the positions no longer pair, so the step used to ship as
/// `hole`; it is now the `eq_transitive` chain over the same printed text.
/// In the interned order it is still the ordinary `eq_congruent_pred`.
#[test]
fn an_equality_predicate_respelled_out_of_position_is_the_chain_it_states() {
    let mut fixture = equalities();
    let proof = refutation(&mut fixture);
    assert!(ay_proof_strict(&proof, &fixture.terms));
    let respelled = export(&fixture, &proof, &[(fixture.vd, "(= d v)")]);
    assert_eq!(
        lemma_line(&respelled),
        "(step t3 (cl (not (= v v)) (not (= d c)) (not (= v c)) (= d v)) :rule eq_transitive)",
        "{respelled}"
    );
    let interned = export(&fixture, &proof, &[]);
    assert_eq!(
        lemma_line(&interned),
        "(step t3 (cl (not (= v v)) (not (= d c)) (not (= v c)) (= v d)) :rule eq_congruent_pred)",
        "{interned}"
    );
}

/// NEGATIVE TWIN. A hypothesis re-spelled into text that is no equality of
/// the chain's terms (the sixth false green's `ite` encoding) leaves no
/// chain over the printed literals: the step keeps the honest hole.
#[test]
fn a_respelled_hypothesis_keeps_the_hole() {
    let mut fixture = equalities();
    let proof = refutation(&mut fixture);
    let document = export(
        &fixture,
        &proof,
        &[
            (fixture.vd, "(= d v)"),
            (fixture.dc, "(= (ite (not (= d c)) 1 0) 0)"),
        ],
    );
    let lemma = lemma_line(&document);
    assert!(lemma.ends_with(":rule hole)"), "{document}");
    assert!(!document.contains(":rule eq_transitive"), "{document}");
}

fn ay_proof_strict(proof: &Proof, terms: &TermStore) -> bool {
    crate::check_proof_strict(proof, terms).is_ok()
}
