// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A folded BV identity proved by congruence over a checked frontier.
//!
//! When the two sides of a folded `(= L R)` share one application skeleton
//! and differ only in a few bit-vector subterms, the identity is proved
//! without bit-blasting the skeleton: the differing pairs `(s_i, t_i)` — the
//! frontier — are proved together as ONE [`TheoryLemmaKind::BvBitBlast`]
//! lemma `(and (= s_1 t_1) .. (= s_n t_n))` (just `(= s t)` for a single
//! pair), each conjunct is projected with `and_pos` and resolution, and the
//! skeleton is closed bottom-up by [`TheoryLemmaKind::EufCongruent`] (an
//! argument position whose two sides are one term is discharged by
//! [`TheoryLemmaKind::EufReflexive`]).
//!
//! One lemma, not one per pair: the strict checker precharges every
//! proof-producing bit-blast lemma its full per-lemma allowance
//! (`MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA`, 768 MiB) against the proof's
//! envelope, so two separate 64-bit frontier lemmas already exceed a 1.25 GiB
//! envelope and the whole certificate is refused with `ResourceLimit`
//! (measured on gate row 2049), however cheap each pair is to decide.
//!
//! It is offered only when the skeleton holds an operator a bit-blast pays for
//! quadratically (a product, a quotient or a remainder): there, bit-blasting
//! the whole identity is a miter of two such circuits whose inputs merely
//! differ in spelling. Measured on external-codegen's `SMULL` obligation (gate row
//! 2049): `(bvmul (concat (ite ..) x) (concat (ite ..) y))` against
//! `(bvmul ((_ sign_extend 32) x) ((_ sign_extend 32) y))` spent the whole
//! 130 s budget replaying the whole-identity bit-blast (two 64-bit
//! multipliers), while the frontier conjunction is two 64-bit slice
//! identities the recognizer proves at once: the certificate is published in
//! 3 s and Clean verifies it.
//!
//! Some skeleton nodes are matched CROSSWISE. Such a node is a `bvadd` or
//! `bvmul` (`RING_COMMUTATIVE_OPERATORS`) whose positional operand pairs
//! disagree on a sampled assignment while its crossed pairs agree on every one.
//! `(f a b)` against `(f c d)` is then closed as `(f a b) = (f d c)` by
//! congruence over `(a, d)` and `(b, c)`. The operand swap `(f d c) = (f c d)`
//! follows, an `ArithClauseTautology` decided by the ring lane and printed
//! `poly_simp`, and `EufTransitive` joins the two (the walker's `crossed`
//! module docs give the measurement). A certificate with more swaps than the
//! printer promotes to `poly_simp` is declined, as in the crosswise walk.
//!
//! Nothing here is trusted. The strict checker re-derives each frontier lemma
//! with its bit-blast validator, each congruence clause with the
//! `EufCongruent` schema check, each operand swap with its ring lane, and each
//! join with the `EufTransitive` schema check. A pair that differs on a
//! sampled assignment is never offered to the recognizer.

use super::super::bvand_commutative_congruence::{
    add_ring_operand_swap, exceeds_printable_swaps, RING_COMMUTATIVE_OPERATORS,
};
use super::Executor;
use ay_core::{
    AletheRule, Proof, ProofId, Sort, Symbol, TermData, TermId, TermStore, TheoryLemmaKind,
};
use num_bigint::BigInt;

#[cfg(test)]
#[path = "frontier_tests.rs"]
mod tests;

/// Differing subterm pairs one identity may bit-blast.
const MAX_FRONTIER_PAIRS: usize = 8;
/// Skeleton application nodes walked per identity.
const MAX_SKELETON_NODES: usize = 256;
/// Sampled assignments a frontier pair must agree on before the bit-blast
/// recognizer is asked about it.
const SAMPLED_ASSIGNMENTS: u64 = 8;
/// Operand pairs one walk may sample to choose crosswise matching. Each
/// choice samples at most four. Once the allowance is spent, every remaining
/// node is matched by position. The frontier pairs are still sampled
/// afterwards, as before.
const MAX_CROSSING_SAMPLES: usize = 4 * MAX_FRONTIER_PAIRS;
/// Skeleton operators whose bit-blast circuit is quadratic in the width.
const QUADRATIC_OPERATORS: [&str; 6] = ["bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod"];

impl Executor {
    /// `(= lhs rhs)` proved in `candidate` by congruence over a checked
    /// frontier (module docs), or `None`.
    pub(super) fn bv_frontier_identity(
        &mut self,
        candidate: &mut Proof,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<ProofId> {
        let Frontier {
            pairs: frontier,
            crossed,
        } = congruence_frontier(&self.ctx.terms, lhs, rhs)?;
        if !frontier
            .iter()
            .all(|&(left, right)| samples_agree(&self.ctx.terms, left, right))
        {
            return None;
        }
        let equalities: Vec<TermId> = frontier
            .iter()
            .map(|&(left, right)| {
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [left, right], Sort::Bool)
            })
            .collect();
        // Raw `and`: `and_pos` projects by position, so the conjunction must
        // keep exactly this argument order. A skeleton that differs only by
        // operand swaps has no frontier and so no lemma.
        let lemma = match equalities.as_slice() {
            [] => None,
            [single] => Some(*single),
            _ => Some(
                self.ctx
                    .terms
                    .mk_app(Symbol::named("and"), equalities.clone(), Sort::Bool),
            ),
        };
        if lemma.is_some_and(|lemma| !self.recognize_bv_bitblast_until_stopped(&[lemma])) {
            return None;
        }
        let before = candidate.steps.len();
        let units = match lemma {
            Some(lemma) => self.project_frontier_lemma(candidate, lemma, &equalities),
            None => Some(Vec::new()),
        };
        let derived = units.and_then(|units| {
            let proved: Vec<_> = frontier.iter().copied().zip(units).collect();
            self.derive_skeleton_congruence(candidate, (lhs, rhs), &proved, &crossed)
        });
        // As in the crosswise walk: more swaps than the printer promotes to
        // `poly_simp` would print as holes.
        let derived = derived.filter(|_| !exceeds_printable_swaps(candidate, before));
        if derived.is_none() {
            candidate.steps.truncate(before);
        }
        derived.map(|(step, _)| step)
    }

    /// The single bit-blast lemma over the frontier, and one unit step
    /// `(cl (= s_i t_i))` per pair, in frontier order.
    pub(super) fn project_frontier_lemma(
        &mut self,
        candidate: &mut Proof,
        lemma: TermId,
        equalities: &[TermId],
    ) -> Option<Vec<ProofId>> {
        let lemma_step =
            candidate.add_theory_lemma_with_kind("bv", vec![lemma], TheoryLemmaKind::BvBitBlast);
        if let [_] = equalities {
            return Some(vec![lemma_step]);
        }
        let TermData::App(_, conjuncts) = self.ctx.terms.get(lemma).clone() else {
            return None;
        };
        if conjuncts != equalities {
            return None;
        }
        let not_lemma = self.ctx.terms.mk_not_raw(lemma);
        let mut units = Vec::with_capacity(equalities.len());
        for (position, &equality) in equalities.iter().enumerate() {
            // (cl (not (and e_1 .. e_n)) e_i), resolved against the lemma.
            let projection = candidate.add_rule_step(
                AletheRule::AndPos(u32::try_from(position).ok()?),
                vec![not_lemma, equality],
                Vec::new(),
                Vec::new(),
            );
            units.push(candidate.add_resolution(vec![equality], lemma, projection, lemma_step));
        }
        Some(units)
    }

    /// `(= lhs rhs)` derived in `candidate`: a frontier pair is its projected
    /// unit, anything else one congruence step over its arguments.
    pub(super) fn derive_frontier_congruence(
        &mut self,
        candidate: &mut Proof,
        lhs: TermId,
        rhs: TermId,
        proved: &[((TermId, TermId), ProofId)],
    ) -> Option<(ProofId, TermId)> {
        self.derive_skeleton_congruence(candidate, (lhs, rhs), proved, &[])
    }

    /// [`Self::derive_frontier_congruence`], where a node in `crossed` is
    /// closed crosswise (`derive_crossed_congruence`).
    fn derive_skeleton_congruence(
        &mut self,
        candidate: &mut Proof,
        (lhs, rhs): (TermId, TermId),
        proved: &[((TermId, TermId), ProofId)],
        crossed: &[(TermId, TermId)],
    ) -> Option<(ProofId, TermId)> {
        let equality = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
        if let Some(&(_, unit)) = proved.iter().find(|(pair, _)| *pair == (lhs, rhs)) {
            return Some((unit, equality));
        }
        if crossed.contains(&(lhs, rhs)) {
            return self.derive_crossed_congruence(candidate, (lhs, rhs), proved, crossed);
        }
        let (TermData::App(_, left_args), TermData::App(_, right_args)) = (
            self.ctx.terms.get(lhs).clone(),
            self.ctx.terms.get(rhs).clone(),
        ) else {
            return None;
        };
        let mut premises = Vec::with_capacity(left_args.len());
        for (&left, &right) in left_args.iter().zip(&right_args) {
            if left == right {
                let reflexive =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("="), [left, right], Sort::Bool);
                let step = candidate.add_theory_lemma_with_kind(
                    "euf",
                    vec![reflexive],
                    TheoryLemmaKind::EufReflexive,
                );
                premises.push((reflexive, step));
            } else {
                let (step, argument_equality) =
                    self.derive_skeleton_congruence(candidate, (left, right), proved, crossed)?;
                premises.push((argument_equality, step));
            }
        }
        // (cl (not (= a_1 b_1)) .. (not (= a_n b_n)) (= (f a) (f b)))
        let mut clause: Vec<TermId> = premises
            .iter()
            .map(|&(premise, _)| self.ctx.terms.mk_not_raw(premise))
            .collect();
        clause.push(equality);
        let mut current = candidate.add_theory_lemma_with_kind(
            "euf",
            clause.clone(),
            TheoryLemmaKind::EufCongruent,
        );
        let mut remaining = clause;
        for (premise, support) in premises {
            let negated = self.ctx.terms.mk_not_raw(premise);
            let position = remaining.iter().position(|&literal| literal == negated)?;
            let _ = remaining.remove(position);
            current = candidate.add_resolution(remaining.clone(), premise, current, support);
        }
        (remaining == [equality]).then_some((current, equality))
    }

    /// `(= lhs rhs)` for a node matched crosswise, `lhs = (f a b)` and
    /// `rhs = (f c d)`: congruence to `mirror = (f d c)`, the operand swap
    /// `(= mirror rhs)`, and one `EufTransitive` join. When `mirror` is `lhs`
    /// itself, the swap alone is the equality.
    fn derive_crossed_congruence(
        &mut self,
        candidate: &mut Proof,
        (lhs, rhs): (TermId, TermId),
        proved: &[((TermId, TermId), ProofId)],
        crossed: &[(TermId, TermId)],
    ) -> Option<(ProofId, TermId)> {
        let swap = add_ring_operand_swap(&mut self.ctx.terms, candidate, rhs)?;
        let terms = &mut self.ctx.terms;
        let equality = terms.mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
        if swap.mirror == lhs {
            return Some((swap.step, equality));
        }
        let not_swap = terms.mk_not_raw(swap.equality);
        let (congruent, forward) =
            self.derive_skeleton_congruence(candidate, (lhs, swap.mirror), proved, crossed)?;
        let not_forward = self.ctx.terms.mk_not_raw(forward);
        let join = candidate.add_theory_lemma_with_kind(
            "euf",
            vec![not_forward, not_swap, equality],
            TheoryLemmaKind::EufTransitive,
        );
        let joined = candidate.add_resolution(vec![not_swap, equality], forward, join, congruent);
        let closed = candidate.add_resolution(vec![equality], swap.equality, joined, swap.step);
        Some((closed, equality))
    }
}

/// What the skeleton walk found: the differing pairs, and the skeleton nodes
/// matched crosswise (module docs).
struct Frontier {
    pairs: Vec<(TermId, TermId)>,
    crossed: Vec<(TermId, TermId)>,
}

/// The pairs where `lhs` and `rhs` stop sharing one application skeleton
/// (a commutative node is walked crosswise when [`crosses`] says so, and
/// recorded), or `None` when there is no proper refinement to offer: the
/// roots themselves differ in head, the skeleton holds no quadratic operator,
/// a differing pair is not a bit-vector, or a bound is hit.
fn congruence_frontier(terms: &TermStore, lhs: TermId, rhs: TermId) -> Option<Frontier> {
    let mut frontier = Vec::new();
    let mut crossed = Vec::new();
    let mut pending = vec![(lhs, rhs)];
    let mut walked = 0usize;
    let mut sampled = 0usize;
    let mut quadratic = false;
    while let Some((left, right)) = pending.pop() {
        if left == right || frontier.contains(&(left, right)) {
            continue;
        }
        walked += 1;
        if walked > MAX_SKELETON_NODES {
            return None;
        }
        match (terms.get(left), terms.get(right)) {
            // Only a NAMED head is congruence-closed: an indexed operator
            // (`extract`, `zero_extend`, ...) has no `eq_congruent` spelling in
            // the consumer, so it stays inside a frontier pair.
            (
                TermData::App(left_symbol @ Symbol::Named(_), left_args),
                TermData::App(right_symbol, right_args),
            ) if left_symbol == right_symbol
                && left_args.len() == right_args.len()
                && !left_args.is_empty()
                && terms.sort(left) == terms.sort(right) =>
            {
                quadratic |= QUADRATIC_OPERATORS.contains(&left_symbol.name());
                match (left_args.as_slice(), right_args.as_slice()) {
                    (&[a, b], &[c, d])
                        if crosses(terms, left_symbol, [a, b], [c, d], &mut sampled) =>
                    {
                        if !crossed.contains(&(left, right)) {
                            crossed.push((left, right));
                        }
                        pending.extend([(a, d), (b, c)]);
                    }
                    _ => pending.extend(left_args.iter().copied().zip(right_args.iter().copied())),
                }
            }
            _ => {
                if (left, right) == (lhs, rhs)
                    || !matches!(terms.sort(left), Sort::BitVec(_))
                    || terms.sort(left) != terms.sort(right)
                {
                    return None;
                }
                frontier.push((left, right));
                if frontier.len() > MAX_FRONTIER_PAIRS {
                    return None;
                }
            }
        }
    }
    (quadratic && !(frontier.is_empty() && crossed.is_empty())).then_some(Frontier {
        pairs: frontier,
        crossed,
    })
}

/// Whether the binary ring node `(symbol a b)` against `(symbol c d)` is
/// matched crosswise: a positional pair disagrees on a sampled assignment and
/// both crossed pairs agree on every one. Identical terms agree without a
/// sample. A pair that would exceed [`MAX_CROSSING_SAMPLES`] is not sampled
/// and counts as disagreeing, so the node is matched by position.
fn crosses(
    terms: &TermStore,
    symbol: &Symbol,
    [a, b]: [TermId; 2],
    [c, d]: [TermId; 2],
    sampled: &mut usize,
) -> bool {
    let mut agree = |left: TermId, right: TermId| {
        if left == right {
            return true;
        }
        if *sampled >= MAX_CROSSING_SAMPLES {
            return false;
        }
        *sampled += 1;
        samples_agree(terms, left, right)
    };
    RING_COMMUTATIVE_OPERATORS.contains(&symbol.name())
        && !(agree(a, c) && agree(b, d))
        && agree(a, d)
        && agree(b, c)
}

/// Whether `left` and `right` evaluate equal on a few deterministic
/// assignments of their bit-vector variables. Any evaluation failure, or a
/// variable that is not a bit-vector, answers `false`: the sample is a cheap
/// necessary condition, never a proof.
pub(super) fn samples_agree(terms: &TermStore, left: TermId, right: TermId) -> bool {
    let Some(variables) = bv_variables(terms, &[left, right]) else {
        return false;
    };
    let mut state = 0x9E37_79B9_7F4A_7C15_u64;
    for round in 0..SAMPLED_ASSIGNMENTS {
        let mut values = ay_core::kani_compat::DetHashMap::default();
        for &(variable, width) in &variables {
            let value = match round {
                0 => BigInt::from(0u8),
                1 => (BigInt::from(1u8) << width) - 1u8,
                2 => BigInt::from(1u8) << (width - 1),
                _ => {
                    let mut value = BigInt::from(0u8);
                    for _ in 0..width.div_ceil(64) {
                        state = splitmix(state);
                        value = (value << 64u32) | BigInt::from(state);
                    }
                    value & ((BigInt::from(1u8) << width) - 1u8)
                }
            };
            values.insert(variable, value);
        }
        match (
            Executor::evaluate_bv_expr(terms, left, &values),
            Executor::evaluate_bv_expr(terms, right, &values),
        ) {
            (Some(left_value), Some(right_value)) if left_value == right_value => {}
            _ => return false,
        }
    }
    true
}

/// Every variable under `roots` with its width, or `None` when one is not a
/// bit-vector or the walk is too large.
fn bv_variables(terms: &TermStore, roots: &[TermId]) -> Option<Vec<(TermId, u32)>> {
    const MAX_NODES: usize = 4_096;
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let mut pending: Vec<TermId> = roots.to_vec();
    let mut variables = Vec::new();
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_NODES {
            return None;
        }
        match terms.get(term) {
            TermData::Var(..) => match terms.sort(term) {
                Sort::BitVec(bv) if bv.width > 0 => variables.push((term, bv.width)),
                _ => return None,
            },
            TermData::App(_, args) => pending.extend(args.iter().copied()),
            TermData::Ite(condition, then_term, else_term) => {
                pending.extend([*condition, *then_term, *else_term]);
            }
            TermData::Not(inner) => pending.push(*inner),
            TermData::Const(_) => {}
            _ => return None,
        }
    }
    Some(variables)
}

fn splitmix(state: u64) -> u64 {
    let mut z = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}
