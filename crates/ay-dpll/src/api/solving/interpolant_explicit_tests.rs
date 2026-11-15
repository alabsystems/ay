// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the fail-closed (Explicit-mode) traversal on hand-built
//! proofs: one test per failure kind, the release locality check, and the
//! positive shared-pivot / Farkas-leaf cases for all three systems.
//! Workstream D Rung 1 (WP-D1-P).

use super::*;
use ay_core::{FarkasAnnotation, Sort};
use num_bigint::BigInt;
use num_rational::BigRational;

fn real(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(BigInt::from(n)))
}

/// A = { q }, B = { (or (not q) r), (not r) }; the refutation goes through
/// the `or` elimination of the B assertion (as executor proofs do).
struct SharedPivot {
    terms: TermStore,
    proof: Proof,
    groups: Vec<Vec<TermId>>,
    q: TermId,
}

fn shared_pivot() -> SharedPivot {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let not_q = terms.mk_not_raw(q);
    let not_r = terms.mk_not_raw(r);
    let b1 = terms.mk_app(ay_core::Symbol::named("or"), vec![not_q, r], Sort::Bool);
    let mut proof = Proof::new();
    let s0 = proof.add_assume(q, None);
    let s1 = proof.add_assume(b1, None);
    let s2 = proof.add_assume(not_r, None);
    let s3 = proof.add_rule_step(AletheRule::Or, vec![not_q, r], vec![s1], Vec::new());
    let s4 = proof.add_resolution(vec![not_q], r, s3, s2);
    let _s5 = proof.add_resolution(Vec::new(), q, s0, s4);
    SharedPivot {
        terms,
        proof,
        groups: vec![vec![q], vec![b1, not_r]],
        q,
    }
}

fn run(
    terms: &mut TermStore,
    proof: &Proof,
    groups: &[Vec<TermId>],
    mask: u128,
    strength: InterpolantStrength,
) -> Result<TermId, InterpolantFailure> {
    let view = ProofView::build(proof)?;
    let occ = GroupOccurrence::build(terms, groups);
    explicit_interpolant(terms, proof, &view, &occ, mask, strength)
}

#[test]
fn shared_pivot_all_systems_serve_q() {
    for strength in [
        InterpolantStrength::Strongest,
        InterpolantStrength::Default,
        InterpolantStrength::Weakest,
    ] {
        let mut sp = shared_pivot();
        let itp = run(&mut sp.terms, &sp.proof, &sp.groups, 0b01, strength)
            .unwrap_or_else(|e| panic!("{strength:?}: {e}"));
        // A = q, B ⊨ ¬q: the only Craig interpolant over {q} is q.
        assert_eq!(itp, sp.q, "{strength:?} must serve exactly q");
    }
}

/// A = { x <= 0 }, B = { x >= 1 } over Reals, refuted by one Farkas lemma.
struct FarkasCase {
    terms: TermStore,
    groups: Vec<Vec<TermId>>,
    a1: TermId,
    b1: TermId,
    x: TermId,
}

fn farkas_case() -> FarkasCase {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = real(&mut terms, 0);
    let one = real(&mut terms, 1);
    let a1 = terms.mk_le(x, zero);
    let b1 = terms.mk_ge(x, one);
    FarkasCase {
        terms,
        groups: vec![vec![a1], vec![b1]],
        a1,
        b1,
        x,
    }
}

/// assume a1; assume b1; lemma [¬a1, ¬b1]; resolve a1; resolve b1.
fn farkas_proof(fc: &mut FarkasCase, lemma: ProofStep) -> Proof {
    let not_a1 = fc.terms.mk_not_raw(fc.a1);
    let not_b1 = fc.terms.mk_not_raw(fc.b1);
    let mut proof = Proof::new();
    let s0 = proof.add_assume(fc.a1, None);
    let s1 = proof.add_assume(fc.b1, None);
    let s2 = proof.add_step(lemma);
    let s3 = proof.add_resolution(vec![not_b1], fc.a1, s0, s2);
    let _s4 = proof.add_resolution(Vec::new(), fc.b1, s1, s3);
    let _ = not_a1;
    proof
}

fn lra_lemma(
    fc: &mut FarkasCase,
    farkas: Option<FarkasAnnotation>,
    kind: TheoryLemmaKind,
) -> ProofStep {
    let not_a1 = fc.terms.mk_not_raw(fc.a1);
    let not_b1 = fc.terms.mk_not_raw(fc.b1);
    ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: vec![not_a1, not_b1],
        farkas,
        kind,
        lia: None,
    }
}

#[test]
fn farkas_leaf_serves_the_a_part_sum() {
    let mut fc = farkas_case();
    let lemma = lra_lemma(
        &mut fc,
        Some(FarkasAnnotation::from_ints(&[1, 1])),
        TheoryLemmaKind::LraFarkas,
    );
    let proof = farkas_proof(&mut fc, lemma);
    for strength in [
        InterpolantStrength::Strongest,
        InterpolantStrength::Default,
        InterpolantStrength::Weakest,
    ] {
        let mut terms = fc.terms.clone();
        let itp = run(&mut terms, &proof, &fc.groups, 0b01, strength)
            .unwrap_or_else(|e| panic!("{strength:?}: {e}"));
        // The A-part Farkas sum `x <= 0`, Real-typed and untightened.
        let vars = vars_of(&terms, itp);
        assert_eq!(vars, vec![fc.x], "{strength:?}: only the shared x");
        match terms.get(itp) {
            TermData::App(sym, args) => {
                assert_eq!(sym.name(), "<=", "{strength:?}: non-strict row");
                assert!(args.iter().all(|&a| terms.sort(a) == &Sort::Real));
            }
            other => panic!("{strength:?}: unexpected interpolant shape {other:?}"),
        }
    }
}

#[test]
fn uncertified_arithmetic_lemma_fails_closed() {
    let mut fc = farkas_case();
    let lemma = lra_lemma(&mut fc, None, TheoryLemmaKind::LraFarkas);
    let proof = farkas_proof(&mut fc, lemma);
    let err = run(
        &mut fc.terms,
        &proof,
        &fc.groups,
        0b01,
        InterpolantStrength::Strongest,
    )
    .expect_err("a Farkas lemma without a certificate must fail closed");
    assert_eq!(err, InterpolantFailure::UncertifiedLeaf { step: 2 });
}

#[test]
fn rejected_certificate_fails_closed() {
    let mut fc = farkas_case();
    // `x <= 0` alone is satisfiable: the weights do not refute.
    let lemma = lra_lemma(
        &mut fc,
        Some(FarkasAnnotation::from_ints(&[1, 0])),
        TheoryLemmaKind::LraFarkas,
    );
    let proof = farkas_proof(&mut fc, lemma);
    let err = run(
        &mut fc.terms,
        &proof,
        &fc.groups,
        0b01,
        InterpolantStrength::Default,
    )
    .expect_err("a certificate that does not verify must fail closed");
    assert_eq!(err, InterpolantFailure::UncertifiedLeaf { step: 2 });
}

#[test]
fn generic_trust_lemma_fails_closed() {
    let mut fc = farkas_case();
    let lemma = lra_lemma(&mut fc, None, TheoryLemmaKind::Generic);
    let proof = farkas_proof(&mut fc, lemma);
    let err = run(
        &mut fc.terms,
        &proof,
        &fc.groups,
        0b01,
        InterpolantStrength::Weakest,
    )
    .expect_err("a trust lemma must fail closed");
    assert_eq!(err, InterpolantFailure::TrustStep { step: 2 });
}

#[test]
fn assertion_dependent_lemma_kind_fails_closed() {
    // `SetCardEmptyByAssertion` is valid only under a problem assertion, so
    // it must never be served as a valid-clause leaf.
    let mut fc = farkas_case();
    let lemma = lra_lemma(&mut fc, None, TheoryLemmaKind::SetCardEmptyByAssertion);
    let proof = farkas_proof(&mut fc, lemma);
    for strength in [
        InterpolantStrength::Strongest,
        InterpolantStrength::Default,
        InterpolantStrength::Weakest,
    ] {
        let err = run(&mut fc.terms.clone(), &proof, &fc.groups, 0b01, strength)
            .expect_err("an assertion-dependent lemma must fail closed");
        assert_eq!(
            err,
            InterpolantFailure::UncertifiedLeaf { step: 2 },
            "{strength:?}"
        );
    }
}

#[test]
fn resolution_whose_stated_clause_drops_a_literal_fails_closed() {
    // The true resolvent of `a1` and `[¬a1, ¬b1]` on `a1` is `[¬b1]`; the
    // step states the empty clause. The partial interpolant would be for
    // `[¬b1]`, so serving it as a refutation must fail closed.
    let mut fc = farkas_case();
    let lemma = lra_lemma(
        &mut fc,
        Some(FarkasAnnotation::from_ints(&[1, 1])),
        TheoryLemmaKind::LraFarkas,
    );
    let mut proof = Proof::new();
    let s0 = proof.add_assume(fc.a1, None);
    let _s1 = proof.add_assume(fc.b1, None);
    let s2 = proof.add_step(lemma);
    let _s3 = proof.add_resolution(Vec::new(), fc.a1, s0, s2);
    let err = run(
        &mut fc.terms,
        &proof,
        &fc.groups,
        0b01,
        InterpolantStrength::Default,
    )
    .expect_err("a resolution step that drops a resolvent literal must fail closed");
    assert_eq!(err, InterpolantFailure::UnsupportedStep { step: 3 });
}

#[test]
fn trust_step_fails_closed() {
    let mut fc = farkas_case();
    let not_a1 = fc.terms.mk_not_raw(fc.a1);
    let not_b1 = fc.terms.mk_not_raw(fc.b1);
    let lemma = ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![not_a1, not_b1],
        premises: Vec::new(),
        args: Vec::new(),
    };
    let proof = farkas_proof(&mut fc, lemma);
    let err = run(
        &mut fc.terms,
        &proof,
        &fc.groups,
        0b01,
        InterpolantStrength::Default,
    )
    .expect_err("a Trust step must fail closed");
    assert_eq!(err, InterpolantFailure::TrustStep { step: 2 });
    assert_eq!(ProofView::build(&proof).map(|v| v.trust_steps), Ok(1));
}

#[test]
fn unreachable_trust_step_is_ignored() {
    let mut fc = farkas_case();
    let lemma = lra_lemma(
        &mut fc,
        Some(FarkasAnnotation::from_ints(&[1, 1])),
        TheoryLemmaKind::LraFarkas,
    );
    let not_a1 = fc.terms.mk_not_raw(fc.a1);
    let mut proof = Proof::new();
    // A dead Trust step before the refutation proper.
    proof.add_rule_step(AletheRule::Trust, vec![not_a1], Vec::new(), Vec::new());
    let s0 = proof.add_assume(fc.a1, None);
    let s1 = proof.add_assume(fc.b1, None);
    let s2 = proof.add_step(lemma);
    let not_b1 = fc.terms.mk_not_raw(fc.b1);
    let s3 = proof.add_resolution(vec![not_b1], fc.a1, s0, s2);
    let _ = proof.add_resolution(Vec::new(), fc.b1, s1, s3);
    assert_eq!(ProofView::build(&proof).map(|v| v.trust_steps), Ok(0));
    run(
        &mut fc.terms,
        &proof,
        &fc.groups,
        0b01,
        InterpolantStrength::Strongest,
    )
    .expect("a Trust step the root does not use must not block extraction");
}

#[test]
fn undecodable_leaf_fails_closed() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = real(&mut terms, 0);
    let one = real(&mut terms, 1);
    let xy = terms.mk_mul(vec![x, y]);
    let a1 = terms.mk_le(xy, zero);
    let b1 = terms.mk_ge(xy, one);
    let mut fc = FarkasCase {
        terms,
        groups: vec![vec![a1], vec![b1]],
        a1,
        b1,
        x,
    };
    let lemma = lra_lemma(
        &mut fc,
        Some(FarkasAnnotation::from_ints(&[1, 1])),
        TheoryLemmaKind::LraFarkas,
    );
    let proof = farkas_proof(&mut fc, lemma);
    let err = run(
        &mut fc.terms,
        &proof,
        &fc.groups,
        0b01,
        InterpolantStrength::Strongest,
    )
    .expect_err("a nonlinear row must fail closed");
    assert_eq!(err, InterpolantFailure::UndecodableLeaf { step: 2 });
}

#[test]
fn unclassified_literal_fails_closed() {
    // A lemma literal over a variable that occurs in no group.
    let mut fc = farkas_case();
    let z = fc.terms.mk_var("z", Sort::Real);
    let zero = real(&mut fc.terms, 0);
    let fresh = fc.terms.mk_le(z, zero);
    let not_a1 = fc.terms.mk_not_raw(fc.a1);
    let not_fresh = fc.terms.mk_not_raw(fresh);
    let lemma = ProofStep::TheoryLemma {
        theory: "Bool".to_string(),
        clause: vec![not_a1, not_fresh],
        farkas: None,
        kind: TheoryLemmaKind::BoolTautology,
        lia: None,
    };
    let proof = farkas_proof(&mut fc, lemma);
    let err = run(
        &mut fc.terms,
        &proof,
        &fc.groups,
        0b01,
        InterpolantStrength::Default,
    )
    .expect_err("an atom over a variable of neither side must fail closed");
    assert_eq!(err, InterpolantFailure::UnclassifiedLiteral { step: 2 });
}

#[test]
fn assume_of_a_non_root_term_fails_closed() {
    let mut fc = farkas_case();
    let z = fc.terms.mk_var("z", Sort::Real);
    let zero = real(&mut fc.terms, 0);
    let fresh = fc.terms.mk_le(z, zero);
    let not_fresh = fc.terms.mk_not_raw(fresh);
    let mut proof = Proof::new();
    let s0 = proof.add_assume(fresh, None);
    let s1 = proof.add_rule_step(AletheRule::Trust, vec![not_fresh], Vec::new(), Vec::new());
    let _ = proof.add_resolution(Vec::new(), fresh, s0, s1);
    let err = run(
        &mut fc.terms,
        &proof,
        &fc.groups,
        0b01,
        InterpolantStrength::Default,
    )
    .expect_err("an Assume of a term no group asserts must fail closed");
    assert_eq!(err, InterpolantFailure::UnclassifiedLiteral { step: 0 });
}

#[test]
fn missing_premise_fails_closed() {
    let mut fc = farkas_case();
    let mut proof = Proof::new();
    let s0 = proof.add_assume(fc.a1, None);
    // Premise 7 does not exist (and does not precede this step).
    let _ = proof.add_resolution(Vec::new(), fc.a1, s0, ProofId(7));
    let err = run(
        &mut fc.terms,
        &proof,
        &fc.groups,
        0b01,
        InterpolantStrength::Default,
    )
    .expect_err("a missing premise must fail closed, never default to true");
    assert_eq!(err, InterpolantFailure::MissingPremise { step: 1 });
}

#[test]
fn unsupported_rules_fail_closed() {
    let mut fc = farkas_case();
    let not_b1 = fc.terms.mk_not_raw(fc.b1);
    let mut proof = Proof::new();
    let s0 = proof.add_assume(fc.a1, None);
    let s1 = proof.add_assume(fc.b1, None);
    let s2 = proof.add_rule_step(AletheRule::Drup, vec![not_b1], vec![s0], Vec::new());
    let _ = proof.add_resolution(Vec::new(), fc.b1, s1, s2);
    let err = run(
        &mut fc.terms,
        &proof,
        &fc.groups,
        0b01,
        InterpolantStrength::Default,
    )
    .expect_err("a DRUP step has no interpolation rule");
    assert_eq!(err, InterpolantFailure::UnsupportedStep { step: 2 });
}

#[test]
fn non_refutation_proof_is_no_proof() {
    let mut fc = farkas_case();
    let mut proof = Proof::new();
    proof.add_assume(fc.a1, None);
    assert!(matches!(
        run(
            &mut fc.terms,
            &proof,
            &fc.groups,
            0b01,
            InterpolantStrength::Default
        ),
        Err(InterpolantFailure::NoProof)
    ));
    let empty = Proof::new();
    assert!(matches!(
        ProofView::build(&empty),
        Err(InterpolantFailure::NoProof)
    ));
}

#[test]
fn non_local_valid_clause_fails_closed() {
    // A "tautology" whose A-restriction and B-restriction both carry local
    // symbols has no local leaf form (the mixed-literal case).
    let mut terms = TermStore::new();
    let xa = terms.mk_var("xa", Sort::Real);
    let yb = terms.mk_var("yb", Sort::Real);
    let s = terms.mk_var("s", Sort::Real);
    let zero = real(&mut terms, 0);
    let a1 = terms.mk_le(xa, s);
    let b1 = terms.mk_le(s, yb);
    let ga = terms.mk_le(xa, zero);
    let gb = terms.mk_le(yb, zero);
    let groups = vec![vec![a1, ga], vec![b1, gb]];
    let not_ga = terms.mk_not_raw(ga);
    let not_gb = terms.mk_not_raw(gb);
    let mut proof = Proof::new();
    let s0 = proof.add_assume(ga, None);
    let s1 = proof.add_assume(gb, None);
    let s2 = proof.add_rule_step(
        AletheRule::OrNeg,
        vec![not_ga, not_gb],
        Vec::new(),
        Vec::new(),
    );
    let s3 = proof.add_resolution(vec![not_gb], ga, s0, s2);
    let _ = proof.add_resolution(Vec::new(), gb, s1, s3);
    let err = run(
        &mut terms,
        &proof,
        &groups,
        0b01,
        InterpolantStrength::Default,
    )
    .expect_err("no local leaf form exists");
    assert!(
        matches!(err, InterpolantFailure::NonLocal { .. }),
        "{err:?}"
    );
}

#[test]
fn release_locality_check_rejects_non_shared_variables() {
    // The root check is `Cut::require_local`, compiled in every profile
    // (this test runs under `--release` in the WP-D1-P gate).
    let mut fc = farkas_case();
    let z = fc.terms.mk_var("z", Sort::Real);
    let zero = real(&mut fc.terms, 0);
    let groups = vec![vec![fc.a1], vec![fc.b1, fc.terms.mk_le(z, zero)]];
    let occ = GroupOccurrence::build(&fc.terms, &groups);
    let cut = Cut::new(&fc.terms, &occ, 0b01, InterpolantStrength::Default);
    assert!(cut.require_local(&fc.terms, fc.a1).is_ok(), "x is shared");
    let z_atom = fc.terms.mk_le(z, zero);
    assert_eq!(
        cut.require_local(&fc.terms, z_atom),
        Err(InterpolantFailure::NonLocal {
            var: "z".to_string()
        })
    );
}

#[test]
fn composite_subterm_labels_follow_occurrence() {
    // A ∋ (and p q), B ∋ ¬(and p q): the composite is shared (AB), p/q
    // occur in both through it.
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let pq = terms.mk_app(ay_core::Symbol::named("and"), vec![p, q], Sort::Bool);
    let not_pq = terms.mk_not_raw(pq);
    let groups = vec![vec![pq], vec![not_pq]];
    let occ = GroupOccurrence::build(&terms, &groups);
    let cut = Cut::new(&terms, &occ, 0b01, InterpolantStrength::Strongest);
    assert_eq!(cut.class_of(&terms, pq), Some(AtomClass::Ab));
    // A's top-level conjuncts are root-level (an Assume of `p` is an A leaf).
    assert_eq!(occ.roots.get(&p).copied(), Some(0b01));
    let mut proof = Proof::new();
    let s0 = proof.add_assume(pq, None);
    let s1 = proof.add_assume(not_pq, None);
    let _ = proof.add_resolution(Vec::new(), pq, s0, s1);
    let itp = run(
        &mut terms,
        &proof,
        &groups,
        0b01,
        InterpolantStrength::Strongest,
    )
    .expect("shared composite");
    assert_eq!(itp, pq, "McMillan: the shared composite itself");
}

#[test]
fn preprocessed_leaves_take_the_groups_that_hold_all_their_sources() {
    // A = { a1, a2 }, B = { b1 }; the solver refuted preprocessed leaves:
    // `from_a` (sources a1, a2), `from_both` (a1, b1), `unsourced` (none) and
    // `from_a_and` = (and c d) from a1, whose conjuncts become A roots too.
    let mut terms = TermStore::new();
    let mut var = |name: &str| terms.mk_var(name, Sort::Bool);
    let (a1, a2, b1) = (var("a1"), var("a2"), var("b1"));
    let (from_a, from_both, unsourced) = (var("fa"), var("fb"), var("fu"));
    let (c, d) = (var("c"), var("d"));
    let from_a_and = terms.mk_app(ay_core::Symbol::named("and"), vec![c, d], Sort::Bool);
    let groups = vec![vec![a1, a2], vec![b1]];
    let mut occ = GroupOccurrence::build(&terms, &groups);
    let mut sources: HashMap<TermId, Vec<TermId>> = HashMap::default();
    sources.insert(from_a, vec![a1, a2]);
    sources.insert(from_both, vec![a1, b1]);
    sources.insert(unsourced, Vec::new());
    sources.insert(from_a_and, vec![a1]);
    occ.attribute_preprocessed_leaves(&terms, &sources);
    assert_eq!(occ.root_bits(&terms, from_a), 0b01);
    assert_eq!(
        occ.root_bits(&terms, from_both),
        0,
        "no single group implies it"
    );
    assert_eq!(
        occ.root_bits(&terms, unsourced),
        0,
        "no sources is no authority"
    );
    assert_eq!(occ.root_bits(&terms, from_a_and), 0b01);
    assert_eq!(
        occ.root_bits(&terms, c),
        0b01,
        "conjunct of an attributed leaf"
    );
    // An authored root keeps exactly its own groups.
    assert_eq!(occ.root_bits(&terms, b1), 0b10);
}
