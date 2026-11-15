// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The frontier route on external-codegen's `SMULL` obligation (gate row 2049),
//! called directly. The collapse promotion tries the congruence walker's
//! bounded leaf first, and that route certifies the row end to end
//! (`tests/bv_frontier_source.rs`), so only these tests reach the frontier.

use super::*;
use ay_core::ProofStep;

/// The low 32 bits of a fresh 64-bit `name`, and `(concat (ite (= ((_ extract
/// sign sign) lo) #b1) ones zeros) lo)`: the sign extension external-codegen spells
/// out when `sign` is 31.
fn spelled_low_word(terms: &mut TermStore, name: &str, sign: u32) -> (TermId, TermId) {
    let register = terms.mk_var(name, Sort::bitvec(64));
    let low = terms.mk_app(
        Symbol::indexed("extract", vec![31, 0]),
        [register],
        Sort::bitvec(32),
    );
    let bit = terms.mk_app(
        Symbol::indexed("extract", vec![sign, sign]),
        [low],
        Sort::bitvec(1),
    );
    let one = terms.mk_bitvec(BigInt::from(1), 1);
    let negative = terms.mk_app(Symbol::named("="), [bit, one], Sort::Bool);
    let ones = terms.mk_bitvec((BigInt::from(1) << 32) - 1, 32);
    let zeros = terms.mk_bitvec(BigInt::from(0), 32);
    let fill = terms.mk_ite_raw(negative, ones, zeros);
    let spelled = terms.mk_app(Symbol::named("concat"), [fill, low], Sort::bitvec(64));
    (low, spelled)
}

/// The row's two products; `sign` is the bit the first operand's spelling
/// tests.
fn smull(terms: &mut TermStore, sign: u32) -> (TermId, TermId) {
    let (low12, spelled12) = spelled_low_word(terms, "x12", sign);
    let (low7, spelled7) = spelled_low_word(terms, "x7", 31);
    let extend = |terms: &mut TermStore, low| {
        terms.mk_app(
            Symbol::indexed("sign_extend", vec![32]),
            [low],
            Sort::bitvec(64),
        )
    };
    let (extended12, extended7) = (extend(terms, low12), extend(terms, low7));
    let product = |terms: &mut TermStore, a, b| {
        terms.mk_app(Symbol::named("bvmul"), [a, b], Sort::bitvec(64))
    };
    (
        product(terms, spelled12, spelled7),
        product(terms, extended12, extended7),
    )
}

#[test]
fn the_smull_frontier_is_one_bit_blast_lemma_closed_by_eq_congruent() {
    let mut executor = Executor::new();
    let (left, right) = smull(&mut executor.ctx.terms, 31);
    let mut candidate = Proof::new();
    let step = executor
        .bv_frontier_identity(&mut candidate, left, right)
        .expect("the two operand identities are the frontier");
    // The multiplier is never blasted: the one lemma is the conjunction of the
    // operand identities, and the product is closed by congruence.
    let kinds: Vec<TheoryLemmaKind> = candidate
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma { kind, .. } => Some(*kind),
            _ => None,
        })
        .collect();
    assert_eq!(
        kinds,
        [TheoryLemmaKind::BvBitBlast, TheoryLemmaKind::EufCongruent],
        "{:#?}",
        candidate.steps
    );
    let terms = &mut executor.ctx.terms;
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let assume = candidate.add_assume(negated, None);
    candidate.add_resolution(vec![], equality, assume, step);
    let quality = ay_proof::check_proof_strict(&candidate, &executor.ctx.terms)
        .expect("the frontier certificate must pass strict replay");
    assert_eq!((quality.trust_count, quality.hole_count), (0, 0));
}

/// Bit 30 is not the operand's sign: that frontier pair is false, so the
/// route declines and leaves nothing in the candidate.
#[test]
fn a_frontier_testing_the_wrong_sign_bit_is_declined() {
    let mut executor = Executor::new();
    let (left, right) = smull(&mut executor.ctx.terms, 30);
    let mut candidate = Proof::new();
    assert!(executor
        .bv_frontier_identity(&mut candidate, left, right)
        .is_none());
    assert!(candidate.steps.is_empty(), "{:#?}", candidate.steps);
}

/// `(f b a)` for the binary application `(f a b)`.
fn swapped(terms: &mut TermStore, product: TermId) -> TermId {
    let TermData::App(symbol, args) = terms.get(product).clone() else {
        panic!("a binary application");
    };
    let sort = terms.sort(product).clone();
    terms.mk_app(symbol, [args[1], args[0]], sort)
}

fn lemma_kinds(candidate: &Proof) -> Vec<TheoryLemmaKind> {
    candidate
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma { kind, .. } => Some(*kind),
            _ => None,
        })
        .collect()
}

/// Closes `step`'s `(= left right)` against its negation and replays the
/// candidate strictly.
fn assert_strict_refutation(
    executor: &mut Executor,
    mut candidate: Proof,
    left: TermId,
    right: TermId,
    step: ProofId,
) {
    let terms = &mut executor.ctx.terms;
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let assume = candidate.add_assume(negated, None);
    candidate.add_resolution(vec![], equality, assume, step);
    let quality = ay_proof::check_proof_strict(&candidate, &executor.ctx.terms)
        .expect("the crossed certificate must pass strict replay");
    assert_eq!((quality.trust_count, quality.hole_count), (0, 0));
}

/// The row with the right product's operands swapped. Positionally, both
/// operand pairs differ on a sample; crosswise, both agree. The product is
/// closed by congruence to the swapped right side and the ring lane's operand
/// swap, and the multiplier is never blasted: the one bit-blast lemma is the
/// operand conjunction.
#[test]
fn a_commuted_smull_frontier_is_matched_crosswise() {
    let mut executor = Executor::new();
    let (left, right) = smull(&mut executor.ctx.terms, 31);
    let right = swapped(&mut executor.ctx.terms, right);
    let mut candidate = Proof::new();
    let step = executor
        .bv_frontier_identity(&mut candidate, left, right)
        .expect("the crossed operand identities are the frontier");
    assert_eq!(
        lemma_kinds(&candidate),
        [
            TheoryLemmaKind::BvBitBlast,
            TheoryLemmaKind::ArithClauseTautology,
            TheoryLemmaKind::EufCongruent,
            TheoryLemmaKind::EufTransitive,
        ],
        "{:#?}",
        candidate.steps
    );
    let expensive = candidate
        .steps
        .iter()
        .filter(|step| {
            matches!(step, ProofStep::TheoryLemma { kind: TheoryLemmaKind::BvBitBlast, clause, .. }
                if ay_proof::bv_bitblast_requires_proof_producer(&executor.ctx.terms, clause))
        })
        .count();
    assert_eq!(expensive, 1, "{:#?}", candidate.steps);
    assert_strict_refutation(&mut executor, candidate, left, right, step);
}

/// A skeleton that differs only by an operand swap below the product has no
/// frontier, and so no bit-blast lemma at all: the swap is the ring lane's.
#[test]
fn a_swap_below_a_product_needs_no_frontier_lemma() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let (a, b, c) = (
        terms.mk_var("a", Sort::bitvec(64)),
        terms.mk_var("b", Sort::bitvec(64)),
        terms.mk_var("c", Sort::bitvec(64)),
    );
    let sum = terms.mk_app(Symbol::named("bvadd"), [a, b], Sort::bitvec(64));
    let left = terms.mk_app(Symbol::named("bvmul"), [sum, c], Sort::bitvec(64));
    let mirrored = swapped(terms, sum);
    let right = terms.mk_app(Symbol::named("bvmul"), [mirrored, c], Sort::bitvec(64));
    let mut candidate = Proof::new();
    let step = executor
        .bv_frontier_identity(&mut candidate, left, right)
        .expect("a swap below the product is closed by congruence");
    assert_eq!(
        lemma_kinds(&candidate),
        [
            TheoryLemmaKind::ArithClauseTautology,
            TheoryLemmaKind::EufReflexive,
            TheoryLemmaKind::EufCongruent,
        ],
        "{:#?}",
        candidate.steps
    );
    assert_strict_refutation(&mut executor, candidate, left, right, step);
}

/// NEGATIVE twin of the crossed match: with bit 30 tested, the crossed pair
/// over `x12` disagrees on a sample too, so the node is not crossed, the
/// positional frontier fails its samples, and nothing is left behind.
#[test]
fn a_commuted_frontier_testing_the_wrong_sign_bit_is_declined() {
    let mut executor = Executor::new();
    let (left, right) = smull(&mut executor.ctx.terms, 30);
    let right = swapped(&mut executor.ctx.terms, right);
    let mut candidate = Proof::new();
    assert!(executor
        .bv_frontier_identity(&mut candidate, left, right)
        .is_none());
    assert!(candidate.steps.is_empty(), "{:#?}", candidate.steps);
}
