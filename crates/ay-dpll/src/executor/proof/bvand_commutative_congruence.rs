// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap;
use ay_core::term::{Constant, TermData};
use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};

/// Pure-syntax leaf shape predicates — which crux to hand the recognizer.
mod leaf_shapes;

use leaf_shapes::{
    is_idempotent_bv_gate_of, is_ult_one_eq_zero_of, is_unsigned_compare_duality_of,
};

const MAX_CONGRUENCE_NODES: usize = 256;

/// Build an exact equality proof when two terms differ only by local bit-vector
/// gate rewrites — a binary `bvand` operand swap, a `bvand`/`bvor` idempotency
/// collapse, or an unsigned comparison/negated-strict-dual swap — below
/// otherwise identical applications/ites.
///
/// Every rewrite leaf is first admitted by `ay-proof`'s independent
/// proof-producing BV recognizer (bit-blast + surfaced LRAT replay at wide
/// widths). Ordinary `cong` steps then lift those checked equalities through
/// the exact raw source tree. This is intentionally not a normalization
/// assumption: the original, unnormalized assertion remains the proof's
/// `assume`, and every rewrite edge is explicit and checker-replayed.
pub(super) fn add_bvand_commutative_congruence_proof(
    terms: &mut TermStore,
    proof: &mut Proof,
    left: TermId,
    right: TermId,
) -> Option<ProofId> {
    let initial_step_count = proof.steps.len();
    let mut memo = DetHashMap::default();
    let mut visited = 0;
    let result = recurse(terms, proof, left, right, &mut memo, &mut visited);
    if result.is_none() {
        // Keep the caller's candidate transactional: a valid swap proved in an
        // early argument must not survive when a later differing argument
        // falls outside this exact lane.
        proof.steps.truncate(initial_step_count);
    }
    result
}

fn recurse(
    terms: &mut TermStore,
    proof: &mut Proof,
    left: TermId,
    right: TermId,
    memo: &mut DetHashMap<(TermId, TermId), ProofId>,
    visited: &mut usize,
) -> Option<ProofId> {
    if left == right {
        return None;
    }
    if let Some(&step) = memo.get(&(left, right)) {
        return Some(step);
    }
    *visited = visited.checked_add(1)?;
    if *visited > MAX_CONGRUENCE_NODES || terms.sort(left) != terms.sort(right) {
        return None;
    }

    let left_data = terms.get(left).clone();
    let right_data = terms.get(right).clone();
    if let (TermData::App(left_symbol, left_args), TermData::App(right_symbol, right_args)) =
        (&left_data, &right_data)
    {
        if matches!(left_symbol, Symbol::Named(name) if name == "bvand")
            && matches!(right_symbol, Symbol::Named(name) if name == "bvand")
            && left_args.len() == 2
            && right_args.as_slice() == [left_args[1], left_args[0]]
            && matches!(terms.sort(left), Sort::BitVec(_))
        {
            let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
            if !ay_proof::recognize_bv_bitblast(terms, &[equality]) {
                return None;
            }
            let step =
                proof.add_theory_lemma_with_kind("bv", vec![equality], TheoryLemmaKind::BvBitBlast);
            memo.insert((left, right), step);
            return Some(step);
        }
    }

    // Bit-wise idempotency leaf: one side is `(bvand t t)` / `(bvor t t)` and
    // the other side is exactly that repeated operand `t`. Unlike the swap
    // above, the two sides here have DIFFERENT shapes (an application against
    // its own argument), so the lockstep descent below can never reach it — it
    // has to be recognized as a leaf or the whole rewrite spine is refused.
    //
    // This is the shape a code generator's guard obligations keep producing:
    // `(= (ite (= t #b0..0) #b1 #b0) (ite (= (bvand t t) #b0..0) #b1 #b0))`,
    // where the gate sits two levels below the equated `ite`s and is therefore
    // invisible to the printer's top-level idempotency lowering. Minting the
    // small `(= t (bvand t t))` crux here and lifting it with `cong` puts a
    // clause the printer CAN lower where the coarse whole-`ite` lemma — which
    // AY can decide but not typeset — used to sit.
    //
    // Nothing is authorized by matching the shape: the recognizer call below
    // is the same independent semantic gate the swap arm uses, so a
    // non-idempotent gate is refused there, not here.
    if is_idempotent_bv_gate_of(terms, left, right) || is_idempotent_bv_gate_of(terms, right, left)
    {
        let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
        if !ay_proof::recognize_bv_bitblast(terms, &[equality]) {
            return None;
        }
        let step =
            proof.add_theory_lemma_with_kind("bv", vec![equality], TheoryLemmaKind::BvBitBlast);
        memo.insert((left, right), step);
        return Some(step);
    }

    // Unsigned comparison / negated-strict-dual leaf: one side is `(bvuge a b)`
    // / `(bvule a b)` and the other is the negation of its exact strict dual.
    // Like the idempotency leaf above, the two sides have DIFFERENT top
    // symbols (a comparison against a `not`), so the lockstep descent below can
    // never reach it — it has to be recognized as a leaf or the whole rewrite
    // spine is refused.
    //
    // This is the shape a code generator's BOUNDS and SHIFT-RANGE guard
    // obligations produce, one guard over from the division-guard idempotency
    // shape above:
    // `(= (ite (bvuge lhs rhs) #b1 #b0) (ite (not (bvult lhs rhs)) #b1 #b0))`,
    // where the intended side spells the guard with the `bvuge` primitive and
    // the EMITTED side is the machine's `AE` condition code, i.e. the negation
    // of the carry flag `(bvult lhs rhs)`. The two comparisons sit one level
    // below the equated `ite`s and are therefore invisible to any top-level
    // printer lowering.
    //
    // Nothing is authorized by matching the shape: the recognizer call below is
    // the same independent semantic gate the two arms above use, so a
    // non-dual pair (`bvugt` against `(not (bvult ...))`, which differs exactly
    // when the operands are equal) is refused there, not here.
    if is_unsigned_compare_duality_of(terms, left, right)
        || is_unsigned_compare_duality_of(terms, right, left)
    {
        let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
        if !ay_proof::recognize_bv_bitblast(terms, &[equality]) {
            return None;
        }
        let step =
            proof.add_theory_lemma_with_kind("bv", vec![equality], TheoryLemmaKind::BvBitBlast);
        memo.insert((left, right), step);
        return Some(step);
    }

    // Zero-test duality leaf: one side is `(bvult v 1)` and the other tests
    // `v` (or its idempotent collapse `(bvand v v)`) for equality with zero.
    // The two sides have different top symbols (`bvult` against `=`), so —
    // exactly like the two leaves above — the lockstep descent can never reach
    // this pair and it must be recognized whole. This is the DivZero /
    // NullIfZero guard-carrier condition-code shape (`E` = "is zero") after
    // the guards were re-phrased over `bvult`; see
    // [`is_ult_one_eq_zero_of`]. The recognizer call below is the same
    // independent semantic gate as always: a non-identity (wrong constant,
    // wrong width, different subjects) is refused there, not here.
    if is_ult_one_eq_zero_of(terms, left, right) || is_ult_one_eq_zero_of(terms, right, left) {
        let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
        if !ay_proof::recognize_bv_bitblast(terms, &[equality]) {
            return None;
        }
        let step =
            proof.add_theory_lemma_with_kind("bv", vec![equality], TheoryLemmaKind::BvBitBlast);
        memo.insert((left, right), step);
        return Some(step);
    }

    let (left_args, right_args) = match (left_data, right_data) {
        (TermData::App(left_symbol, left_args), TermData::App(right_symbol, right_args))
            if left_symbol == right_symbol && left_args.len() == right_args.len() =>
        {
            (left_args, right_args)
        }
        (
            TermData::Ite(left_condition, left_then, left_else),
            TermData::Ite(right_condition, right_then, right_else),
        ) => (
            vec![left_condition, left_then, left_else],
            vec![right_condition, right_then, right_else],
        ),
        _ => return None,
    };

    let mut premises = Vec::new();
    for (left_arg, right_arg) in left_args.into_iter().zip(right_args) {
        if left_arg == right_arg {
            continue;
        }
        premises.push(recurse(terms, proof, left_arg, right_arg, memo, visited)?);
    }
    if premises.is_empty() {
        return None;
    }
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let step = proof.add_rule_step(AletheRule::Cong, vec![equality], premises, Vec::new());
    memo.insert((left, right), step);
    Some(step)
}
