// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};

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

/// Is `gate` the bit-wise idempotent application `(bvand t t)` / `(bvor t t)`
/// whose repeated operand is exactly `operand`?
///
/// PURE SYNTAX, and deliberately so — this decides only which small crux to
/// hand the recognizer, never whether that crux is true. `TermStore` is
/// hash-consed, so `TermId` equality IS syntactic identity, and the whole
/// side condition is O(1): no assignment is enumerated and no bounded-width
/// budget is consumed.
///
/// The operator list is exactly the printer's `decode_idempotent_bv_gate`
/// (`ay_proof::alethe_printer`) and must stay in lock-step with it, since a
/// leaf this admits but the printer cannot lower falls back to the honest
/// `hole`. `bvxor` must NEVER be added: `(bvxor t t)` is zero rather than `t`,
/// and even that true identity has no one-step `*_simplify` discharge.
fn is_idempotent_bv_gate_of(terms: &TermStore, gate: TermId, operand: TermId) -> bool {
    let TermData::App(Symbol::Named(op), args) = terms.get(gate) else {
        return false;
    };
    if !matches!(op.as_str(), "bvand" | "bvor") {
        return false;
    }
    let [first, second] = args.as_slice() else {
        return false;
    };
    *first == *second && *first == operand && matches!(terms.sort(gate), Sort::BitVec(_))
}

/// The STRICT unsigned comparison whose negation is exactly `op`, for the ONE
/// operand order this walker admits (`(bvuge a b)` is `(not (bvult a b))`, NOT
/// `(not (bvugt b a))` — same fact, different printed operand order, and the
/// printer's derivation is per-operand-position).
///
/// The table is exactly the printer's `decode_unsigned_compare_duality`
/// (`ay_proof::alethe_printer`) and must stay in lock-step with it: a leaf this
/// admits but the printer cannot lower falls back to the honest `hole`.
///
/// SIGNED comparisons (`bvsge`/`bvslt`, `bvsle`/`bvsgt`) are deliberately
/// ABSENT. The identity holds for them too, but Carcara's pseudo-Boolean
/// lowering for a signed comparison carries a separate negative-weight sign
/// term, so it is a DIFFERENT derivation that would need its own
/// machine-checked witness. Admitting it here without that would relocate the
/// hole rather than close it.
fn unsigned_strict_dual(op: &str) -> Option<&'static str> {
    match op {
        "bvuge" => Some("bvult"),
        "bvule" => Some("bvugt"),
        _ => None,
    }
}

/// Strip one negation, in either spelling the store can hold.
fn decode_not(terms: &TermStore, term: TermId) -> Option<TermId> {
    match terms.get(term) {
        TermData::Not(inner) => Some(*inner),
        TermData::App(Symbol::Named(name), args) if name == "not" && args.len() == 1 => {
            Some(args[0])
        }
        _ => None,
    }
}

/// Is `non_strict` an unsigned comparison `(bvuge a b)` / `(bvule a b)` whose
/// exact negated strict dual — `(not (bvult a b))` / `(not (bvugt a b))` over
/// the SAME two operands in the SAME order — is `negated_strict`?
///
/// PURE SYNTAX, exactly like [`is_idempotent_bv_gate_of`], and for the same
/// reason: this decides only which small crux to hand the recognizer, never
/// whether that crux is true. `TermStore` is hash-consed, so the operand
/// comparisons are `TermId` identity and the whole side condition is O(1) — no
/// assignment is enumerated and no bounded-width budget is consumed.
fn is_unsigned_compare_duality_of(
    terms: &TermStore,
    non_strict: TermId,
    negated_strict: TermId,
) -> bool {
    let TermData::App(Symbol::Named(op), args) = terms.get(non_strict) else {
        return false;
    };
    let Some(strict) = unsigned_strict_dual(op.as_str()) else {
        return false;
    };
    let [left_operand, right_operand] = args.as_slice() else {
        return false;
    };
    let (left_operand, right_operand) = (*left_operand, *right_operand);
    let Some(inner) = decode_not(terms, negated_strict) else {
        return false;
    };
    let TermData::App(Symbol::Named(inner_op), inner_args) = terms.get(inner) else {
        return false;
    };
    inner_op.as_str() == strict
        && inner_args.as_slice() == [left_operand, right_operand]
        && matches!(terms.sort(left_operand), Sort::BitVec(_))
        && terms.sort(left_operand) == terms.sort(right_operand)
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

#[cfg(test)]
mod unsigned_compare_duality_tests {
    use super::*;

    /// Build `(<op> lhs rhs)` and `(not (<dual> <a> <b>))` over fresh width-`w`
    /// variables, returning both plus the store.
    fn pair(width: u32, op: &str, dual: &str, dual_swapped: bool) -> (TermStore, TermId, TermId) {
        let mut terms = TermStore::new();
        let sort = Sort::bitvec(width);
        let lhs = terms.mk_var("lhs", sort.clone());
        let rhs = terms.mk_var("rhs", sort);
        let non_strict = terms.mk_app(Symbol::named(op), [lhs, rhs], Sort::Bool);
        let strict_args = if dual_swapped { [rhs, lhs] } else { [lhs, rhs] };
        let strict = terms.mk_app(Symbol::named(dual), strict_args, Sort::Bool);
        let negated = terms.mk_not(strict);
        (terms, non_strict, negated)
    }

    /// The two admitted pairs are recognized in BOTH argument orders.
    #[test]
    fn admits_exactly_the_two_unsigned_dual_pairs() {
        for (op, dual) in [("bvuge", "bvult"), ("bvule", "bvugt")] {
            let (terms, non_strict, negated) = pair(32, op, dual, false);
            assert!(
                is_unsigned_compare_duality_of(&terms, non_strict, negated),
                "{op}/{dual} must be recognized"
            );
            assert!(
                !is_unsigned_compare_duality_of(&terms, negated, non_strict),
                "{op}/{dual}: the predicate is oriented; the caller tries both orders"
            );
        }
    }

    /// SYNTAX GATE, negative direction. Every one of these must be refused by
    /// the predicate itself, so the recognizer is never even consulted.
    #[test]
    fn refuses_wrong_operator_wrong_order_and_signed() {
        // A genuinely FALSE pair: `bvugt` and `not bvult` differ at lhs == rhs.
        let (terms, non_strict, negated) = pair(32, "bvugt", "bvult", false);
        assert!(!is_unsigned_compare_duality_of(&terms, non_strict, negated));
        // Right fact, WRONG printed operand order — the printer's derivation is
        // per-operand-position, so this must not reach it.
        let (terms, non_strict, negated) = pair(32, "bvuge", "bvult", true);
        assert!(!is_unsigned_compare_duality_of(&terms, non_strict, negated));
        // Crossed duals: `bvuge` against `not bvugt` is false at lhs == rhs.
        let (terms, non_strict, negated) = pair(32, "bvuge", "bvugt", false);
        assert!(!is_unsigned_compare_duality_of(&terms, non_strict, negated));
        // SIGNED: true, but out of the printer's lane, so it must stay a hole.
        for (op, dual) in [("bvsge", "bvslt"), ("bvsle", "bvsgt")] {
            let (terms, non_strict, negated) = pair(32, op, dual, false);
            assert!(
                !is_unsigned_compare_duality_of(&terms, non_strict, negated),
                "{op}/{dual} has no printer lowering, so the leaf must decline"
            );
        }
    }

    /// AUTHORISATION LANE. The predicate only SELECTS a crux; this pins that the
    /// independent semantic gate actually decides it — accepting the true pairs
    /// at every width the guard-carrier canary asks for (8/32/64), and REFUSING
    /// the false `bvugt` variant. A regression here would turn the new leaf into
    /// a relocated hole, never into a false authorisation.
    #[test]
    fn recognizer_authorizes_true_pairs_and_refuses_false_ones() {
        for width in [8_u32, 16, 32, 64] {
            for (op, dual) in [("bvuge", "bvult"), ("bvule", "bvugt")] {
                let (mut terms, non_strict, negated) = pair(width, op, dual, false);
                let crux = terms.mk_app(Symbol::named("="), [non_strict, negated], Sort::Bool);
                assert!(
                    ay_proof::recognize_bv_bitblast(&terms, &[crux]),
                    "w={width} {op}/{dual}: the semantic gate must decide the crux"
                );
            }
            let (mut terms, non_strict, negated) = pair(width, "bvugt", "bvult", false);
            let crux = terms.mk_app(Symbol::named("="), [non_strict, negated], Sort::Bool);
            assert!(
                !ay_proof::recognize_bv_bitblast(&terms, &[crux]),
                "w={width}: a FALSE pair must be refused by the semantic gate"
            );
        }
    }
}
