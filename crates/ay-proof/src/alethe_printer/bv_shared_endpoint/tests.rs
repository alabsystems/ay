// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MUTATION DIFFERENTIALS for the shared-endpoint constant-conflict lowering,
//! in the shape `alethe_printer_printed_rule_gate_tests.rs` established.
//!
//! The defect class is the one that keeps shipping: the rule name is read off
//! the TERM DAG, the term text is read off a SURFACE OVERRIDE, and nothing
//! downstream compares the two. Each test exports the same proof twice — once
//! with the override that moves the printed text out from under the rule and
//! once without. The un-mutated export must render the rule BYTE-IDENTICALLY
//! (a guard that fires on correct steps destroys the evidence the mutated half
//! is measured against); the mutated export must refuse.

use crate::try_export_alethe_with_problem_scope_and_overrides;
use ay_core::kani_compat::DetHashMap;
use ay_core::{Proof, Sort, Symbol, TermId, TermStore};

/// `(cl (not (and (= t #b00000101) (= t #b00000110))))` — the clause the joint
/// guarded collapse hands the printer, and the shape
/// [`super::AlethePrinter::format_bv_shared_endpoint_constant_conflict`]
/// lowers to `and_pos` + `eq_transitive` + `evaluate`.
///
/// Returns the proof, the two conjuncts, the conjunction root, the shared term
/// and the clause literal — so a mutation can be aimed at each of them
/// separately, and so the problem scope can be the literal itself rather than
/// a helper that folds every step into it.
struct SharedEndpointConflict {
    proof: Proof,
    conjuncts: [TermId; 2],
    root: TermId,
    shared: TermId,
    literal: TermId,
}

fn shared_endpoint_conflict_proof(terms: &mut TermStore) -> SharedEndpointConflict {
    use ay_core::TheoryLemmaKind;
    use num_bigint::BigInt;

    let bv8 = Sort::BitVec(ay_core::BitVecSort { width: 8 });
    let shared = terms.mk_var("t", bv8.clone());
    let five = terms.mk_bitvec(BigInt::from(5), 8);
    let six = terms.mk_bitvec(BigInt::from(6), 8);
    let left = terms.mk_app(Symbol::named("="), [shared, five], Sort::Bool);
    let right = terms.mk_app(Symbol::named("="), [shared, six], Sort::Bool);
    let root = terms.mk_app(Symbol::named("and"), [left, right], Sort::Bool);
    let literal = terms.mk_not_raw(root);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("bv", vec![literal], TheoryLemmaKind::BvBitBlast);
    SharedEndpointConflict {
        proof,
        conjuncts: [left, right],
        root,
        shared,
        literal,
    }
}

fn export(
    fixture: &SharedEndpointConflict,
    overrides: Option<&DetHashMap<TermId, String>>,
    terms: &TermStore,
) -> String {
    try_export_alethe_with_problem_scope_and_overrides(
        &fixture.proof,
        terms,
        &[fixture.literal],
        overrides,
    )
    .expect("the export must still produce a document")
}

/// The exact step whose premises are read off the SURFACE and whose conclusion
/// is read off the TERM DAG. This is the one the lowering may only ever print
/// when the two agree.
const SHARED_ENDPOINT_EQ_TRANSITIVE: &str = "(step t0.sec.t (cl (not (= t #b00000101)) \
     (not (= t #b00000110)) (= #b00000101 #b00000110)) :rule eq_transitive)";

#[test]
fn shared_endpoint_conflict_over_an_unmutated_surface_still_renders_evaluate() {
    let mut terms = TermStore::new();
    let fixture = shared_endpoint_conflict_proof(&mut terms);
    let output = export(&fixture, None, &terms);
    // A guard that fires on correct steps destroys the evidence the mutated
    // half is measured against, so the un-mutated rendering is pinned
    // byte-for-byte.
    assert!(
        output.contains(
            "(step t0.sec.a (cl (not (and (= t #b00000101) (= t #b00000110))) \
             (= t #b00000101)) :rule and_pos :args (0))"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.sec.b (cl (not (and (= t #b00000101) (= t #b00000110))) \
             (= t #b00000110)) :rule and_pos :args (1))"
        ),
        "{output}"
    );
    assert!(output.contains(SHARED_ENDPOINT_EQ_TRANSITIVE), "{output}");
    assert!(
        output.contains("(step t0.sec.ev (cl (= (= #b00000101 #b00000110) false)) :rule evaluate)"),
        "{output}"
    );
    assert!(!output.contains(":rule hole"), "{output}");
    assert!(!output.contains("@bbterm"), "{output}");
}

/// THE DEFECT THE SHIPPED GUARD COULD NOT SEE.
///
/// The lowering names two conjuncts as the premises of an `eq_transitive`
/// whose conclusion is the pair of CONSTANTS it decoded. The premises reach
/// the checker as PRINTED TEXT, so an override on a conjunct moves the premise
/// out from under the conclusion: with `(= t #b00000101)` re-spelled as
/// `(= t five)` the printed chain runs `five — t — #b00000110` while the
/// printed conclusion still says `(= #b00000101 #b00000110)`, and carcara
/// answers `checking failed on step 't0.sec.t' with rule 'eq_transitive':
/// broken transitivity chain: can't prove '(= (_ bv5 8) (_ bv6 8))' / invalid`.
///
/// A root-only reassembly cannot see that: `format_term_data` builds an `and`
/// application as `(and <printed args>)`, so comparing the printed root with
/// `(and {printed conjuncts})` is true BY CONSTRUCTION for every term whose own
/// `TermId` carries no override — and in this lane's production shape the root
/// is the SYNTHESIZED `terms.mk_app("and", roots)` of
/// `promote_joint_bv_guarded_collapse` while the conjuncts are the AUTHORED
/// assertions, i.e. exactly the terms an override is registered on.
#[test]
fn shared_endpoint_conflict_whose_printed_premise_moves_is_refused() {
    for (label, target) in [("first conjunct", 0usize), ("second conjunct", 1usize)] {
        let mut terms = TermStore::new();
        let fixture = shared_endpoint_conflict_proof(&mut terms);
        let mut overrides = DetHashMap::default();
        // A re-spelling that is still a well-formed equality over the same
        // shared term — the benign-looking case, and the one that ships a
        // false claim.
        overrides.insert(fixture.conjuncts[target], "(= t five)".to_string());
        let output = export(&fixture, Some(&overrides), &terms);
        assert!(
            !output.contains("t0.sec."),
            "{label}: the lane fired over a premise it cannot have read: {output}"
        );
        assert!(!output.contains(":rule eq_transitive"), "{label}: {output}");
        assert!(
            !output.contains("(= #b00000101 #b00000110)"),
            "{label}: a conclusion off the term DAG shipped under a premise \
             off the surface: {output}"
        );
    }
}

/// The same differential aimed at the SHARED term. A shared override that is
/// one token is harmless — both premises print it identically, so the printed
/// chain still meets at one endpoint — and the lane must NOT decline on it.
/// An override that is not a single term breaks the premise's arity, and the
/// lane must decline: `(= a b #b00000101)` is no longer an equality whose
/// other side is the constant the conclusion names.
#[test]
fn shared_endpoint_conflict_reads_the_shared_term_off_the_printed_premise() {
    // Harmless: one token, spelled the same in both premises.
    let mut terms = TermStore::new();
    let fixture = shared_endpoint_conflict_proof(&mut terms);
    let mut renamed = DetHashMap::default();
    renamed.insert(fixture.shared, "x".to_string());
    let output = export(&fixture, Some(&renamed), &terms);
    assert!(
        output.contains(
            "(step t0.sec.t (cl (not (= x #b00000101)) (not (= x #b00000110)) \
             (= #b00000101 #b00000110)) :rule eq_transitive)"
        ),
        "{output}"
    );

    // Not one token: the printed premise is a THREE-argument `=`, so the
    // chain it states is not the chain the conclusion names.
    let mut terms = TermStore::new();
    let fixture = shared_endpoint_conflict_proof(&mut terms);
    let mut split = DetHashMap::default();
    split.insert(fixture.shared, "a b".to_string());
    let output = export(&fixture, Some(&split), &terms);
    assert!(!output.contains("t0.sec."), "{output}");
    assert!(!output.contains(":rule eq_transitive"), "{output}");
}

/// And aimed at the ROOT, which is what the shipped guard already covered:
/// `and_pos :args (k)` indexes the printed conjunction, so a re-spelled root
/// must decline rather than index into a different term. Kept as a control so
/// the replacement guard is shown to cover everything the old one did.
#[test]
fn shared_endpoint_conflict_whose_printed_root_is_respelled_is_refused() {
    let mut terms = TermStore::new();
    let fixture = shared_endpoint_conflict_proof(&mut terms);
    let mut overrides = DetHashMap::default();
    overrides.insert(fixture.root, "(and p q)".to_string());
    let output = export(&fixture, Some(&overrides), &terms);
    assert!(!output.contains("t0.sec."), "{output}");
    assert!(!output.contains(":rule evaluate"), "{output}");
}
