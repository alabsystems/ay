// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The crosswise walk, the positional walk it follows, and the operand swap
//! the walk shares with the frontier.

use super::super::add_bvand_commutative_congruence_proof;
use super::{add_crosswise_congruence_proof, add_ring_operand_swap, RING_COMMUTATIVE_OPERATORS};
use ay_core::{
    AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind,
};
use num_bigint::BigInt;

/// `(concat (ite (= ((_ extract sign sign) word) #b1) ones zeros) word)` for
/// a 32-bit `word`: external-codegen's spelling of a sign extension when `sign` is 31.
fn spelled_sign_extend(terms: &mut TermStore, word: TermId, sign: u32) -> TermId {
    let bit = terms.mk_app(
        Symbol::indexed("extract", vec![sign, sign]),
        [word],
        Sort::bitvec(1),
    );
    let one = terms.mk_bitvec(BigInt::from(1), 1);
    let negative = terms.mk_app(Symbol::named("="), [bit, one], Sort::Bool);
    let ones = terms.mk_bitvec((BigInt::from(1) << 32) - 1, 32);
    let zeros = terms.mk_bitvec(BigInt::from(0), 32);
    let fill = terms.mk_ite_raw(negative, ones, zeros);
    terms.mk_app(Symbol::named("concat"), [fill, word], Sort::bitvec(64))
}

fn sign_extend(terms: &mut TermStore, word: TermId) -> TermId {
    terms.mk_app(
        Symbol::indexed("sign_extend", vec![32]),
        [word],
        Sort::bitvec(64),
    )
}

fn product(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("bvmul"), [a, b], Sort::bitvec(64))
}

/// external-codegen's `SMULL` products with the right one's operands swapped:
/// `(bvmul sx' sy')` against `(bvmul (sign_extend y) (sign_extend x))`, where
/// `sx'` tests bit `sign` of `x`.
fn commuted_smull(terms: &mut TermStore, sign: u32) -> (TermId, TermId) {
    let x = terms.mk_var("x", Sort::bitvec(32));
    let y = terms.mk_var("y", Sort::bitvec(32));
    let (spelled_x, spelled_y) = (
        spelled_sign_extend(terms, x, sign),
        spelled_sign_extend(terms, y, 31),
    );
    let (extended_x, extended_y) = (sign_extend(terms, x), sign_extend(terms, y));
    (
        product(terms, spelled_x, spelled_y),
        product(terms, extended_y, extended_x),
    )
}

fn lemma_kinds(proof: &Proof) -> Vec<TheoryLemmaKind> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma { kind, .. } => Some(*kind),
            _ => None,
        })
        .collect()
}

fn rule_of(proof: &Proof, step: ProofId) -> Option<&AletheRule> {
    match &proof.steps[usize::try_from(step.0).ok()?] {
        ProofStep::Step { rule, .. } => Some(rule),
        _ => None,
    }
}

/// Closes `step`'s `(= left right)` against its negation; the candidate must
/// replay strictly with no trust and no hole.
fn assert_strict_refutation(
    terms: &mut TermStore,
    mut proof: Proof,
    (left, right): (TermId, TermId),
    step: ProofId,
) {
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let assume = proof.add_assume(negated, None);
    proof.add_resolution(vec![], equality, assume, step);
    let quality =
        ay_proof::check_proof_strict(&proof, terms).expect("the crossed walk must replay strictly");
    assert_eq!((quality.trust_count, quality.hole_count), (0, 0));
}

/// The commuted row's product is closed crosswise: `cong` to the mirrored
/// right side over the two operand identities (one joint bit-blast lemma, no
/// multiplier in it), the ring lane's operand swap, and `trans`.
#[test]
fn the_walker_closes_a_commuted_product_crosswise() {
    let mut terms = TermStore::new();
    let (left, right) = commuted_smull(&mut terms, 31);
    let mut proof = Proof::new();
    let step = add_crosswise_congruence_proof(&mut terms, &mut proof, left, right)
        .expect("the crossed operand identities close the product");
    assert_eq!(rule_of(&proof, step), Some(&AletheRule::Trans));
    assert_eq!(
        lemma_kinds(&proof),
        [
            TheoryLemmaKind::BvBitBlast,
            TheoryLemmaKind::ArithClauseTautology
        ],
        "{:#?}",
        proof.steps
    );
    assert_strict_refutation(&mut terms, proof, (left, right), step);
}

/// The high half of the commuted product (external-codegen's `SMULH` shape): the
/// frontier never walks an indexed root, so only the walker closes it, by
/// `cong` over the `extract` whose premise is the crossed product.
#[test]
fn the_walker_lifts_a_crossed_product_through_an_indexed_root() {
    let mut terms = TermStore::new();
    let (low, high) = commuted_smull(&mut terms, 31);
    let half = |terms: &mut TermStore, word| {
        terms.mk_app(
            Symbol::indexed("extract", vec![63, 32]),
            [word],
            Sort::bitvec(32),
        )
    };
    let (left, right) = (half(&mut terms, low), half(&mut terms, high));
    let mut proof = Proof::new();
    let step = add_crosswise_congruence_proof(&mut terms, &mut proof, left, right)
        .expect("the crossed product lifts through the extract");
    assert_eq!(rule_of(&proof, step), Some(&AletheRule::Cong));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Trans,
            ..
        }
    )));
    assert_strict_refutation(&mut terms, proof, (left, right), step);
}

/// NEGATIVE twin: with bit 30 tested, neither pairing of the operands is an
/// identity, so the walk declines and leaves nothing behind.
#[test]
fn the_walker_declines_a_commuted_product_with_a_false_operand() {
    let mut terms = TermStore::new();
    let (left, right) = commuted_smull(&mut terms, 30);
    let mut proof = Proof::new();
    assert!(add_crosswise_congruence_proof(&mut terms, &mut proof, left, right).is_none());
    assert!(proof.steps.is_empty(), "{:#?}", proof.steps);
}

/// The positional walk, tried before the ring lane, never crosses: a pure ring
/// identity reaching it keeps the ring lane's single lemma.
#[test]
fn the_positional_walk_never_crosses() {
    let mut terms = TermStore::new();
    let (left, right) = commuted_smull(&mut terms, 31);
    let mut proof = Proof::new();
    assert!(add_bvand_commutative_congruence_proof(&mut terms, &mut proof, left, right).is_none());
    assert!(proof.steps.is_empty(), "{:#?}", proof.steps);
}

/// `depth` sums crossed over a commuted product, `(bvadd .. (bvmul a b) x)`
/// against `(bvadd x .. (bvmul b a))`: one operand swap per node.
fn crossed_chain(terms: &mut TermStore, depth: usize) -> (TermId, TermId) {
    let sort = Sort::bitvec(8);
    let [a, b, x] = ["a", "b", "x"].map(|name| terms.mk_var(name, sort.clone()));
    let mut left = terms.mk_app(Symbol::named("bvmul"), [a, b], sort.clone());
    let mut right = terms.mk_app(Symbol::named("bvmul"), [b, a], sort.clone());
    for _ in 0..depth {
        left = terms.mk_app(Symbol::named("bvadd"), [left, x], sort.clone());
        right = terms.mk_app(Symbol::named("bvadd"), [x, right], sort.clone());
    }
    (left, right)
}

/// A crosswise certificate may hold at most as many swaps as the printer
/// promotes to `poly_simp` in one proof. One more would print as holes, so
/// the walk declines and leaves nothing behind.
#[test]
fn a_crosswise_walk_needing_more_swaps_than_print_declines() {
    let cap = ay_proof::MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF;
    let mut terms = TermStore::new();
    let (left, right) = crossed_chain(&mut terms, cap - 1);
    let mut proof = Proof::new();
    let step = add_crosswise_congruence_proof(&mut terms, &mut proof, left, right)
        .expect("the cap's worth of swaps is printable");
    assert_eq!(
        lemma_kinds(&proof),
        vec![TheoryLemmaKind::ArithClauseTautology; cap]
    );
    assert_strict_refutation(&mut terms, proof, (left, right), step);

    let (left, right) = crossed_chain(&mut terms, cap);
    let mut proof = Proof::new();
    assert!(add_crosswise_congruence_proof(&mut terms, &mut proof, left, right).is_none());
    assert!(proof.steps.is_empty(), "{:#?}", proof.steps);
}

/// The swap is offered only for a binary ring application with two distinct
/// operands, and it is the ring lane's own `ArithClauseTautology`.
#[test]
fn only_a_binary_ring_application_has_an_operand_swap() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(64);
    let c = terms.mk_var("c", sort.clone());
    let d = terms.mk_var("d", sort.clone());
    let e = terms.mk_var("e", sort.clone());
    for op in RING_COMMUTATIVE_OPERATORS {
        let right = terms.mk_app(Symbol::named(op), [c, d], sort.clone());
        let mut proof = Proof::new();
        let swap = add_ring_operand_swap(&mut terms, &mut proof, right).expect(op);
        let mirror = terms.mk_app(Symbol::named(op), [d, c], sort.clone());
        let equality = terms.mk_app(Symbol::named("="), [mirror, right], Sort::Bool);
        assert_eq!((swap.mirror, swap.equality), (mirror, equality), "{op}");
        assert_eq!(lemma_kinds(&proof), [TheoryLemmaKind::ArithClauseTautology]);
        assert_strict_refutation(&mut terms, proof, (mirror, right), swap.step);
    }
    let mut refused = Vec::new();
    for op in [
        "bvand", "bvor", "bvxor", "bvsub", "bvudiv", "bvurem", "bvshl", "concat",
    ] {
        let sort = if op == "concat" {
            Sort::bitvec(128)
        } else {
            sort.clone()
        };
        refused.push(terms.mk_app(Symbol::named(op), [c, d], sort));
    }
    refused.push(terms.mk_app(Symbol::named("bvmul"), [c, c], sort.clone()));
    refused.push(terms.mk_app(Symbol::named("bvmul"), [c, d, e], sort.clone()));
    refused.push(c);
    for right in refused {
        let mut proof = Proof::new();
        assert!(add_ring_operand_swap(&mut terms, &mut proof, right).is_none());
        assert!(proof.steps.is_empty(), "{:#?}", proof.steps);
    }
}

/// NEGATIVE twin of the swap's authority: pinned Carcara's `aci_simp` admits
/// the false `(= (bvmul c c) c)`, but the ring lane that decides the swap (and
/// prints it `poly_simp`) refuses every non-swap, and the strict checker
/// rejects one forged as an `ArithClauseTautology`.
#[test]
fn the_ring_lane_refuses_what_is_no_operand_swap() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(64);
    let c = terms.mk_var("c", sort.clone());
    let d = terms.mk_var("d", sort.clone());
    let square = terms.mk_app(Symbol::named("bvmul"), [c, c], sort.clone());
    let product = terms.mk_app(Symbol::named("bvmul"), [d, c], sort.clone());
    let sum = terms.mk_app(Symbol::named("bvadd"), [c, c], sort.clone());
    for (left, right) in [(square, c), (product, square), (sum, c)] {
        let forged = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
        assert!(!ay_proof::recognize_arith_clause_tautology(
            &terms,
            &[forged]
        ));
        let negated = terms.mk_not_raw(forged);
        let mut proof = Proof::new();
        let assume = proof.add_assume(negated, None);
        let lemma = proof.add_theory_lemma_with_kind(
            "bv",
            vec![forged],
            TheoryLemmaKind::ArithClauseTautology,
        );
        proof.add_resolution(vec![], forged, assume, lemma);
        assert!(ay_proof::check_proof_strict(&proof, &terms).is_err());
    }
}
