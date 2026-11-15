// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::{Constant, TermData};
use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};

/// Pure-syntax admission for the general bounded, wiring-only leaf.
mod bounded_leaf;
/// Crosswise matching of a commutative ring node, shared with the frontier.
mod crossed;
/// Pure-syntax leaf shape predicates — which crux to hand the recognizer.
mod leaf_shapes;

use bounded_leaf::is_bounded_wiring_leaf_pair;
pub(super) use crossed::{
    add_crosswise_congruence_proof, add_ring_operand_swap, exceeds_printable_swaps,
    RING_COMMUTATIVE_OPERATORS,
};

use leaf_shapes::{
    is_idempotent_bv_gate_of, is_ult_one_eq_zero_of, is_unsigned_compare_duality_of,
};

const MAX_CONGRUENCE_NODES: usize = 256;

/// General bounded leaves one walk may use.
const MAX_BOUNDED_LEAVES: usize = 4;

/// The general-leaf state of one walk.
///
/// A general leaf at a wide width is an EXPENSIVE `BvBitBlast` lemma: the
/// strict checker prices each one at a full proof-producing replay, and one
/// strict walk's envelope admits a single such price. So a walk that needs
/// several general leaves must not mint one lemma per leaf. The walk therefore
/// runs twice: the planning pass decides every leaf with the recognizer and
/// records the accepted equalities (as ordinary lemmas, discarded afterwards);
/// the emitting pass proves their CONJUNCTION as one `BvBitBlast` lemma —
/// itself re-decided by the recognizer — and hands each leaf its `and_pos`
/// projection instead of a lemma of its own.
#[derive(Default)]
struct BoundedLeaves {
    /// Leaves accepted in the planning pass, in walk order, with the step each
    /// was minted as (so a rolled-back descent can drop exactly its own).
    accepted: Vec<((TermId, TermId), ProofId)>,
    /// Pairs the recognizer refused: decided once, however often reached.
    refused: DetHashSet<(TermId, TermId)>,
    /// Emitting pass: the projection step proving each planned leaf.
    provided: Option<DetHashMap<(TermId, TermId), ProofId>>,
    /// Whether a binary ring node whose positional descent fails is retried
    /// crosswise (`crossed`). Set only by `add_crosswise_congruence_proof`.
    crosswise: bool,
}

/// Build an exact equality proof when two terms differ only by local bit-vector
/// rewrites below otherwise identical applications/ites: a binary `bvand`
/// operand swap, a `bvand`/`bvor` idempotency collapse, an unsigned
/// comparison/negated-strict-dual swap, or — generally — any bounded,
/// arithmetic-free differing pair (see `bounded_leaf`). This walk matches
/// arguments by position only; `crossed::add_crosswise_congruence_proof` is
/// the same walk that also closes a `bvadd` or `bvmul` node crosswise.
///
/// The general leaf is what keeps a collapse whose two sides share an
/// expensive circuit (a wide `bvmul`) from being refuted as one whole miter:
/// only the differing operands are bit-blasted, and `cong` lifts their
/// equality through the shared operator.
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
    let result = walk_with_joint_leaves(terms, proof, (left, right), initial_step_count, false);
    if result.is_none() {
        // Keep the caller's candidate transactional: a valid swap proved in an
        // early argument must not survive when a later differing argument
        // falls outside this exact lane.
        proof.steps.truncate(initial_step_count);
    }
    result
}

fn walk_with_joint_leaves(
    terms: &mut TermStore,
    proof: &mut Proof,
    (left, right): (TermId, TermId),
    initial_step_count: usize,
    crosswise: bool,
) -> Option<ProofId> {
    let mut leaves = BoundedLeaves {
        crosswise,
        ..BoundedLeaves::default()
    };
    let planned = walk(terms, proof, left, right, &mut leaves)?;
    if leaves.accepted.len() < 2 {
        return Some(planned);
    }

    // Re-emit with one joint lemma for all general leaves.
    proof.steps.truncate(initial_step_count);
    let equalities: Vec<TermId> = leaves
        .accepted
        .iter()
        .map(|&((l, r), _)| terms.mk_app(Symbol::named("="), [l, r], Sort::Bool))
        .collect();
    let joint = terms.mk_app(Symbol::named("and"), equalities.clone(), Sort::Bool);
    if !ay_proof::recognize_bv_bitblast(terms, &[joint]) {
        return None;
    }
    let joint_step =
        proof.add_theory_lemma_with_kind("bv", vec![joint], TheoryLemmaKind::BvBitBlast);
    let not_joint = terms.mk_not_raw(joint);
    let mut provided = DetHashMap::default();
    for (position, (&equality, &(pair, _))) in equalities.iter().zip(&leaves.accepted).enumerate() {
        let projection = proof.add_rule_step(
            AletheRule::AndPos(u32::try_from(position).ok()?),
            vec![not_joint, equality],
            Vec::new(),
            vec![joint],
        );
        let leaf = proof.add_resolution(vec![equality], joint, projection, joint_step);
        provided.insert(pair, leaf);
    }
    leaves.provided = Some(provided);
    walk(terms, proof, left, right, &mut leaves)
}

fn walk(
    terms: &mut TermStore,
    proof: &mut Proof,
    left: TermId,
    right: TermId,
    leaves: &mut BoundedLeaves,
) -> Option<ProofId> {
    let mut memo = DetHashMap::default();
    let mut visited = 0;
    recurse(terms, proof, left, right, &mut memo, &mut visited, leaves)
}

fn recurse(
    terms: &mut TermStore,
    proof: &mut Proof,
    left: TermId,
    right: TermId,
    memo: &mut DetHashMap<(TermId, TermId), ProofId>,
    visited: &mut usize,
    leaves: &mut BoundedLeaves,
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
        _ => return bounded_leaf(terms, proof, left, right, memo, leaves),
    };

    let descent_start = proof.steps.len();
    let Some(premises) = descend(terms, proof, left_args, right_args, memo, visited, leaves) else {
        return retry_after_failed_descent(
            terms,
            proof,
            (left, right),
            memo,
            visited,
            leaves,
            descent_start,
        );
    };
    if premises.is_empty() {
        return None;
    }
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let step = proof.add_rule_step(AletheRule::Cong, vec![equality], premises, Vec::new());
    memo.insert((left, right), step);
    Some(step)
}

/// Prove each differing argument pair of a lockstep descent, in order; `None`
/// as soon as one pair has no proof.
fn descend(
    terms: &mut TermStore,
    proof: &mut Proof,
    left_args: Vec<TermId>,
    right_args: Vec<TermId>,
    memo: &mut DetHashMap<(TermId, TermId), ProofId>,
    visited: &mut usize,
    leaves: &mut BoundedLeaves,
) -> Option<Vec<ProofId>> {
    let mut premises = Vec::new();
    for (left_arg, right_arg) in left_args.into_iter().zip(right_args) {
        if left_arg != right_arg {
            premises.push(recurse(
                terms, proof, left_arg, right_arg, memo, visited, leaves,
            )?);
        }
    }
    Some(premises)
}

/// The lockstep descent below `(left, right)` found no proof for some argument
/// pair. Drop that node's partial descent (and every memo entry or planned
/// leaf naming a dropped step). Then, in a crosswise walk, try a binary ring
/// node crosswise (`crossed`), and failing that the pair whole as a bounded
/// leaf: a `bvxor` operand swap, say, has no per-argument proof but is itself
/// small.
fn retry_after_failed_descent(
    terms: &mut TermStore,
    proof: &mut Proof,
    (left, right): (TermId, TermId),
    memo: &mut DetHashMap<(TermId, TermId), ProofId>,
    visited: &mut usize,
    leaves: &mut BoundedLeaves,
    descent_start: usize,
) -> Option<ProofId> {
    drop_steps_from(proof, memo, leaves, descent_start);
    if leaves.crosswise {
        let crossed =
            crossed::crossed_ring_node(terms, proof, (left, right), memo, visited, leaves);
        if crossed.is_some() {
            return crossed;
        }
        drop_steps_from(proof, memo, leaves, descent_start);
    }
    bounded_leaf(terms, proof, left, right, memo, leaves)
}

/// Truncate `proof` to `start` steps, with every memo entry and planned leaf
/// that names a dropped step.
fn drop_steps_from(
    proof: &mut Proof,
    memo: &mut DetHashMap<(TermId, TermId), ProofId>,
    leaves: &mut BoundedLeaves,
    start: usize,
) {
    let kept = |step: &ProofId| usize::try_from(step.0).is_ok_and(|id| id < start);
    proof.steps.truncate(start);
    memo.retain(|_, step| kept(step));
    leaves.accepted.retain(|(_, step)| kept(step));
}

/// Prove `left = right` whole as a general bounded leaf: admitted by the pure
/// syntax gate, then decided by the independent semantic recognizer. In the
/// emitting pass a planned leaf is its joint-lemma projection instead.
fn bounded_leaf(
    terms: &mut TermStore,
    proof: &mut Proof,
    left: TermId,
    right: TermId,
    memo: &mut DetHashMap<(TermId, TermId), ProofId>,
    bounded_leaves: &mut BoundedLeaves,
) -> Option<ProofId> {
    if let Some(provided) = &bounded_leaves.provided {
        let step = *provided.get(&(left, right))?;
        memo.insert((left, right), step);
        return Some(step);
    }
    if bounded_leaves.accepted.len() >= MAX_BOUNDED_LEAVES
        || bounded_leaves.refused.contains(&(left, right))
        || !is_bounded_wiring_leaf_pair(terms, left, right)
    {
        return None;
    }
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    if !ay_proof::recognize_bv_bitblast(terms, &[equality]) {
        bounded_leaves.refused.insert((left, right));
        return None;
    }
    let step = proof.add_theory_lemma_with_kind("bv", vec![equality], TheoryLemmaKind::BvBitBlast);
    bounded_leaves.accepted.push(((left, right), step));
    memo.insert((left, right), step);
    Some(step)
}
