// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};

use super::proof_farkas::{reconstruct_missing_farkas_coefficients, try_lra_farkas_reconstruction};
use super::proof_farkas_synthesis::{
    synthesize_equality_farkas, synthesize_mixed_equality_arithmetic_farkas,
};
use super::proof_farkas_validation::{
    certificate_valid_for_blocking_clause, sanitize_farkas_annotations,
};
use ay_core::{Proof, ProofStep, Sort, Symbol, TermStore, TheoryLemmaKind, TheoryLit};

#[test]
fn equality_recovery_handles_exact_real_constants() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("real_value", Sort::Real);
    let three_halves = terms.mk_rational(BigRational::new(3.into(), 2.into()));
    let five_halves = terms.mk_rational(BigRational::new(5.into(), 2.into()));
    // Preserve opposite authored orientations. `mk_eq` may canonicalize both
    // rows to the same operand order, which would miss the array/Real conflict
    // this regression is intended to cover.
    let first = terms.mk_app(Symbol::named("="), [value, three_halves], Sort::Bool);
    let second = terms.mk_app(Symbol::named("="), [five_halves, value], Sort::Bool);
    let clause = vec![terms.mk_not_raw(first), terms.mk_not_raw(second)];

    let farkas = synthesize_equality_farkas(&terms, &clause)
        .expect("distinct exact Real constants require the unit equality certificate");
    assert_eq!(farkas.coefficients, vec![Rational64::from_integer(1); 2]);
    let conflict = vec![TheoryLit::new(first, true), TheoryLit::new(second, true)];
    ay_core::proof_validation::verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("the synthesized Real certificate must replay exactly");
}

#[test]
fn mixed_equality_recovery_handles_scaled_equality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));
    let two_x = terms.mk_mul(vec![two, x]);
    let equality = terms.mk_eq(two_x, y);
    let positive = terms.mk_gt(x, zero);
    let non_positive = terms.mk_le(y, zero);
    let clause = vec![
        terms.mk_not_raw(equality),
        terms.mk_not_raw(positive),
        terms.mk_not_raw(non_positive),
    ];

    let farkas = synthesize_mixed_equality_arithmetic_farkas(&mut terms, &clause)
        .expect("2*x=y, x>0, y<=0 needs a recovered equality multiplier");
    assert_eq!(
        farkas.coefficients,
        vec![
            Rational64::new(1, 2),
            Rational64::from(1),
            Rational64::new(1, 2),
        ],
        "the equality multiplier must follow its coefficient 2"
    );

    let conflict = vec![
        TheoryLit::new(equality, true),
        TheoryLit::new(positive, true),
        TheoryLit::new(non_positive, true),
    ];
    ay_core::proof_validation::verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("the recovered certificate must replay against the original rows");
}

#[test]
fn replacement_shape_certificate_is_not_authority_for_original_clause() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let equality = terms.mk_eq(x, y);
    let positive = terms.mk_gt(x, zero);
    let non_positive = terms.mk_le(y, zero);
    let candidate_clause = vec![
        terms.mk_not_raw(equality),
        terms.mk_not_raw(positive),
        terms.mk_not_raw(non_positive),
    ];
    let certificate = synthesize_mixed_equality_arithmetic_farkas(&mut terms, &candidate_clause)
        .expect("candidate replacement is a valid arithmetic contradiction");

    let true_term = terms.true_term();
    let original_clause = vec![
        terms.mk_not_raw(true_term),
        candidate_clause[1],
        candidate_clause[2],
    ];
    assert!(!certificate_valid_for_blocking_clause(
        &terms,
        &original_clause,
        &certificate,
    ));

    let mut candidate_farkas = None;
    let mut candidate_kind = TheoryLemmaKind::LiaGeneric;
    assert!(try_lra_farkas_reconstruction(
        &terms,
        &candidate_clause,
        &mut candidate_farkas,
        &mut candidate_kind,
    ));
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: original_clause.clone(),
        farkas: None,
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });
    reconstruct_missing_farkas_coefficients(&mut terms, &mut proof, &[equality], &[], &|| false);
    let ProofStep::TheoryLemma { farkas, clause, .. } = &proof.steps[0] else {
        panic!("expected theory lemma");
    };
    assert_eq!(clause, &original_clause);
    assert!(farkas.is_none());
}

#[test]
fn rewrite_rebinds_then_clears_collapsed_farkas_certificate() {
    use ay_core::kani_compat::DetHashMap;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let upper = terms.mk_le(x, zero);
    let lower = terms.mk_ge(x, one);
    let not_upper = terms.mk_not_raw(upper);
    let not_lower = terms.mk_not_raw(lower);
    let certificate = ay_core::FarkasAnnotation::from_ints(&[1, 1]);
    assert!(certificate_valid_for_blocking_clause(
        &terms,
        &[not_upper, not_lower],
        &certificate,
    ));

    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: vec![not_upper, not_lower],
        farkas: Some(certificate),
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });
    let mut rewrites = DetHashMap::default();
    rewrites.insert(not_lower, not_upper);
    super::Executor::rewrite_proof_terms(&mut terms, &mut proof, &rewrites)
        .expect("Farkas lemmas retain their existing checked rewrite path");

    let ProofStep::TheoryLemma { clause, farkas, .. } = &proof.steps[0] else {
        panic!("expected theory lemma");
    };
    assert_eq!(clause, &[not_upper]);
    assert!(farkas.is_none());
}

#[test]
fn post_rewrite_sanitation_clears_stale_existing_annotation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let upper = terms.mk_le(x, zero);
    let lower = terms.mk_ge(x, one);
    let not_upper = terms.mk_not_raw(upper);
    let not_lower = terms.mk_not_raw(lower);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: vec![not_upper],
        farkas: Some(ay_core::FarkasAnnotation::from_ints(&[1, 1])),
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });

    sanitize_farkas_annotations(&terms, &mut proof);

    let ProofStep::TheoryLemma { farkas, .. } = &proof.steps[0] else {
        panic!("expected theory lemma");
    };
    assert!(farkas.is_none());
    assert_ne!(not_upper, not_lower);
}

/// `x + 2y ≥ 4, x ≤ 1, y ≤ 1` needs the Farkas multipliers `(1, 1, 2)`, so the
/// payload-free funnel's unit arm declines it and labels it `IntCgCutChain`
/// (`funnel_cut_chain_tests.rs`). Farkas reconstruction runs on that kind
/// and relabels the lemma `LraFarkas` with the rational certificate, the
/// externally checkable route; a rationally SATISFIABLE cut chain
/// (`2x ≥ 1, 2x ≤ 1`, satisfied at `x = 1/2`) has no certificate to find and
/// keeps its payload-free kind.
#[test]
fn reconstruction_relabels_a_non_unit_farkas_cut_chain() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let (one, two, four) = (
        terms.mk_int(BigInt::from(1)),
        terms.mk_int(BigInt::from(2)),
        terms.mk_int(BigInt::from(4)),
    );
    let two_y = terms.mk_mul(vec![y, two]);
    let sum = terms.mk_add(vec![x, two_y]);
    let low = terms.mk_le(four, sum);
    let x_le = terms.mk_le(x, one);
    let y_le = terms.mk_le(y, one);
    let non_unit = vec![
        terms.mk_not_raw(low),
        terms.mk_not_raw(x_le),
        terms.mk_not_raw(y_le),
    ];
    let (kind, _) = crate::theory_inference::infer_theory_lemma_kind_from_clause_terms_and_farkas(
        &terms, &non_unit, None, None,
    );
    assert_eq!(kind, TheoryLemmaKind::IntCgCutChain);

    let two_x = terms.mk_mul(vec![x, two]);
    let half_low = terms.mk_le(one, two_x);
    let half_high = terms.mk_le(two_x, one);
    let parity = vec![terms.mk_not_raw(half_low), terms.mk_not_raw(half_high)];
    assert!(ay_core::proof_validation::recognize_int_cg_cut_chain(
        &terms, &parity
    ));

    let mut proof = Proof::new();
    for clause in [&non_unit, &parity] {
        proof.add_step(ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: clause.clone(),
            farkas: None,
            kind: TheoryLemmaKind::IntCgCutChain,
            lia: None,
        });
    }
    reconstruct_missing_farkas_coefficients(&mut terms, &mut proof, &[], &[], &|| false);

    let ProofStep::TheoryLemma { kind, farkas, .. } = &proof.steps[0] else {
        panic!("expected theory lemma");
    };
    assert_eq!(*kind, TheoryLemmaKind::LraFarkas);
    let farkas = farkas.as_ref().expect("the rational certificate");
    assert!(certificate_valid_for_blocking_clause(
        &terms, &non_unit, farkas
    ));
    assert_ne!(farkas.coefficients, vec![Rational64::from_integer(1); 3]);

    let ProofStep::TheoryLemma { kind, farkas, .. } = &proof.steps[1] else {
        panic!("expected theory lemma");
    };
    assert_eq!(*kind, TheoryLemmaKind::IntCgCutChain);
    assert!(farkas.is_none());
}

/// `count` arithmetic lemmas `(cl (not (< x_i 0)) (not (> x_i 0)))`, each
/// declared `LraFarkas` with no certificate, each certifiable on its own.
fn uncertified_lemmas(terms: &mut TermStore, count: usize) -> Proof {
    let zero = terms.mk_rational(BigRational::from_integer(0.into()));
    let mut proof = Proof::new();
    for index in 0..count {
        let x = terms.mk_var(&format!("poll_x{index}"), Sort::Real);
        let below = terms.mk_lt(x, zero);
        let above = terms.mk_gt(x, zero);
        proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![terms.mk_not_raw(below), terms.mk_not_raw(above)],
            farkas: None,
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
    }
    proof
}

fn certified(proof: &Proof) -> Vec<bool> {
    proof
        .steps
        .iter()
        .map(|step| matches!(step, ProofStep::TheoryLemma { farkas, .. } if farkas.is_some()))
        .collect()
}

/// The pass polls its stop before EVERY reconstruction attempt
/// (#r30-4a-nested-assembly-count): the proof assembly charges each poll to
/// its count, so a poll per attempt is what lets an allowance end the pass at
/// an attempt the query fixes. A stop seen at the second poll leaves exactly
/// one lemma certified. Counterfactual: polling every 16 lemmas, as the pass
/// did, polls once here and certifies all three.
#[test]
fn the_farkas_pass_polls_before_every_reconstruction_attempt() {
    let mut terms = TermStore::new();
    let mut proof = uncertified_lemmas(&mut terms, 3);
    let polls = std::cell::Cell::new(0_u32);
    let count = || {
        polls.set(polls.get() + 1);
        false
    };
    reconstruct_missing_farkas_coefficients(&mut terms, &mut proof, &[], &[], &count);
    assert_eq!(polls.get(), 3, "one poll per attempt");
    assert_eq!(certified(&proof), vec![true; 3], "each lemma certifies");

    let mut proof = uncertified_lemmas(&mut terms, 3);
    polls.set(0);
    let stop_at_second = || {
        polls.set(polls.get() + 1);
        polls.get() > 1
    };
    reconstruct_missing_farkas_coefficients(&mut terms, &mut proof, &[], &[], &stop_at_second);
    assert_eq!(polls.get(), 2);
    assert_eq!(certified(&proof), vec![true, false, false]);
}

/// Every retry against an equality assertion is polled too: they are where
/// the attempts multiply (`finstore_7373_0110`'s nested assembly ran 7738
/// attempts). The clause below holds a simplified `(not true)` and neither
/// equality certifies it, so the pass makes one first attempt and one retry
/// per equality. Counterfactual: polling only before a lemma's first attempt
/// sees one poll.
#[test]
fn every_equality_retry_is_polled_too() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("retry_x", Sort::Int);
    let y = terms.mk_var("retry_y", Sort::Int);
    let z = terms.mk_var("retry_z", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let x_is_y = terms.mk_eq(x, y);
    let x_is_z = terms.mk_eq(x, z);
    let positive = terms.mk_gt(x, zero);
    let non_positive = terms.mk_le(y, zero);
    let true_term = terms.true_term();
    let clause = vec![
        terms.mk_not_raw(true_term),
        terms.mk_not_raw(positive),
        terms.mk_not_raw(non_positive),
    ];
    let lemma = |clause: &Vec<_>| {
        let mut proof = Proof::new();
        proof.add_step(ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: clause.clone(),
            farkas: None,
            kind: TheoryLemmaKind::LiaGeneric,
            lia: None,
        });
        proof
    };
    let polls = std::cell::Cell::new(0_u32);
    let count = || {
        polls.set(polls.get() + 1);
        false
    };
    let mut proof = lemma(&clause);
    reconstruct_missing_farkas_coefficients(&mut terms, &mut proof, &[x_is_y, x_is_z], &[], &count);
    assert_eq!(polls.get(), 3, "the first attempt and two retries");
    assert_eq!(certified(&proof), vec![false]);

    polls.set(0);
    let stop_at_second = || {
        polls.set(polls.get() + 1);
        polls.get() > 1
    };
    let mut proof = lemma(&clause);
    reconstruct_missing_farkas_coefficients(
        &mut terms,
        &mut proof,
        &[x_is_y, x_is_z],
        &[],
        &stop_at_second,
    );
    assert_eq!(polls.get(), 2, "a stop ends the retries and the pass");
}
