// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Crosswise matching of a commutative ring node.
//!
//! Both collapse routes lift a folded identity through the skeleton its two
//! sides share, and Alethe's `cong` and `eq_congruent` match arguments BY
//! POSITION. A sum or product written with its operands in the other order on
//! one side, `(f a b)` against `(f c d)` with `a = d` and `b = c`, therefore had
//! no proof in either route, and the collapse fell through to the
//! whole-identity bit-blast. For a wide product that is a miter of two
//! multipliers whose adder trees sum the partial products in different orders.
//! Measured on external-codegen's `SMULL` row with one product's operands swapped
//! (2026-10-06): that bit-blast swept until the strict producer's 300 s hang
//! guard and published `unknown` for an UNSAT query.
//!
//! Such a node is closed in three steps. Congruence over `(a, d)` and `(b, c)`
//! gives `(f a b) = (f d c)`. The operand swap gives `(f d c) = (f c d)`.
//! Transitivity joins the two. The swap is a
//! [`TheoryLemmaKind::ArithClauseTautology`]: the strict checker's existing
//! `bv_affine` ring lane decides it, because both sides normalize to one
//! polynomial over the opaque operands. It is never priced as a proof-producing
//! bit-blast. It prints as Alethe `poly_simp`, which pinned Carcara checks and
//! which refuses a non-swap such as `(= (bvmul a b) (bvmul a a))`. Only the
//! ring operators are crossed, because only their swap is a ring identity.
//!
//! The crosswise walk runs only after the positional walk and the ring lane
//! have declined (`bv_identity_lemma`). A pure ring identity such as a sum of
//! commuted products keeps its single `poly_simp` lemma from the ring lane.
//! Crossed node by node, it costs one swap per product. A route also declines
//! when its certificate would hold more swaps than
//! `ay_proof::MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF`, the most `poly_simp`
//! promotions the printer makes in one proof. Past that cap the swaps print as
//! holes, and the wire-gap repair that follows bit-blasts the whole query.
//! Measured on a sum of twenty commuted 64-bit products (2026-10-07): with the
//! crosswise walk tried first, that repair ran past 100 s on a 10 s query
//! budget. The ring lane decides the same query in 8 ms.
//!
//! Nothing is authorized here. The swap is admitted by
//! `ay_proof::recognize_arith_clause_tautology`, the validator's own code. Each
//! crossed operand pair is proved like any other pair, and a pairing that is
//! wrong leaves a pair that nothing proves.

use super::*;
use ay_core::ProofStep;

#[cfg(test)]
#[path = "crossed_tests.rs"]
mod tests;

/// The binary operators whose operand swap is a ring identity.
pub(in crate::executor::proof) const RING_COMMUTATIVE_OPERATORS: [&str; 2] = ["bvadd", "bvmul"];

/// A checked operand swap `(= mirror right)` for `right = (f c d)`.
pub(in crate::executor::proof) struct OperandSwap {
    /// `(f d c)`, interned raw so that its operand order is kept.
    pub(in crate::executor::proof) mirror: TermId,
    /// `(= mirror right)`.
    pub(in crate::executor::proof) equality: TermId,
    /// The step that proves `equality`.
    pub(in crate::executor::proof) step: ProofId,
}

/// Adds the operand swap of `right = (f c d)` to `proof`, where `f` is one of
/// [`RING_COMMUTATIVE_OPERATORS`] and `c` and `d` differ. Returns `None`, and
/// adds nothing, for any other term or when the ring recognizer refuses the
/// swap.
pub(in crate::executor::proof) fn add_ring_operand_swap(
    terms: &mut TermStore,
    proof: &mut Proof,
    right: TermId,
) -> Option<OperandSwap> {
    let TermData::App(symbol @ Symbol::Named(_), args) = terms.get(right).clone() else {
        return None;
    };
    let &[c, d] = args.as_slice() else {
        return None;
    };
    let sort = terms.sort(right).clone();
    if !RING_COMMUTATIVE_OPERATORS.contains(&symbol.name())
        || c == d
        || !matches!(sort, Sort::BitVec(_))
    {
        return None;
    }
    let mirror = terms.mk_app(symbol, [d, c], sort);
    let equality = terms.mk_app(Symbol::named("="), [mirror, right], Sort::Bool);
    if !ay_proof::recognize_arith_clause_tautology(terms, &[equality]) {
        return None;
    }
    let step = proof.add_theory_lemma_with_kind(
        "bv",
        vec![equality],
        TheoryLemmaKind::ArithClauseTautology,
    );
    Some(OperandSwap {
        mirror,
        equality,
        step,
    })
}

/// [`super::add_bvand_commutative_congruence_proof`], also matching a binary
/// ring node crosswise where its positional descent fails (module docs).
/// Returns `None`, and leaves `proof` as it was, when the walk declines or its
/// certificate would exceed [`exceeds_printable_swaps`].
pub(in crate::executor::proof) fn add_crosswise_congruence_proof(
    terms: &mut TermStore,
    proof: &mut Proof,
    left: TermId,
    right: TermId,
) -> Option<ProofId> {
    let start = proof.steps.len();
    let result = walk_with_joint_leaves(terms, proof, (left, right), start, true)
        .filter(|_| !exceeds_printable_swaps(proof, start));
    if result.is_none() {
        proof.steps.truncate(start);
    }
    result
}

/// Whether the steps of `proof` from `start` hold more `ArithClauseTautology`
/// lemmas than the printer promotes to `poly_simp` in one proof
/// (`ay_proof::MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF`).
pub(in crate::executor::proof) fn exceeds_printable_swaps(proof: &Proof, start: usize) -> bool {
    proof
        .steps
        .iter()
        .skip(start)
        .filter(|step| {
            matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::ArithClauseTautology,
                    ..
                }
            )
        })
        .count()
        > ay_proof::MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF
}

/// The walker's crossed arm. The positional descent below a binary ring node
/// `left = (f a b)`, `right = (f c d)` has failed. This proves
/// `(= left right)` as `cong` to the mirror over `(a, d)` and `(b, c)`, then
/// the operand swap, joined by `trans`. When the mirror is `left` itself, the
/// swap alone is the proof. Returns `None` when the node is not a binary ring
/// node or a crossed pair has no proof. Steps it added before failing are left
/// for the caller to truncate.
pub(super) fn crossed_ring_node(
    terms: &mut TermStore,
    proof: &mut Proof,
    (left, right): (TermId, TermId),
    memo: &mut DetHashMap<(TermId, TermId), ProofId>,
    visited: &mut usize,
    leaves: &mut BoundedLeaves,
) -> Option<ProofId> {
    let (TermData::App(left_symbol, left_args), TermData::App(right_symbol, _)) =
        (terms.get(left).clone(), terms.get(right))
    else {
        return None;
    };
    let &[a, b] = left_args.as_slice() else {
        return None;
    };
    if left_symbol != *right_symbol {
        return None;
    }
    let swap = add_ring_operand_swap(terms, proof, right)?;
    let step = if swap.mirror == left {
        swap.step
    } else {
        let TermData::App(_, mirror_args) = terms.get(swap.mirror).clone() else {
            return None;
        };
        let premises = descend(terms, proof, vec![a, b], mirror_args, memo, visited, leaves)?;
        if premises.is_empty() {
            return None;
        }
        let forward = terms.mk_app(Symbol::named("="), [left, swap.mirror], Sort::Bool);
        let congruent = proof.add_rule_step(AletheRule::Cong, vec![forward], premises, Vec::new());
        let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
        proof.add_rule_step(
            AletheRule::Trans,
            vec![equality],
            vec![congruent, swap.step],
            Vec::new(),
        )
    };
    memo.insert((left, right), step);
    Some(step)
}
