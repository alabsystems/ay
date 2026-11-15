// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source negative modular-range facts and checked scalar store-miss proofs.

use num_traits::ToPrimitive;

use super::emit::ClosureEmitter;
use super::facts::FactBase;
use super::*;

#[derive(Clone, Copy)]
pub(super) struct NegativeRange {
    pub(super) fact: usize,
    pub(super) predicate: TermId,
    pub(super) delta: TermId,
    pub(super) point: TermId,
    pub(super) base: TermId,
    pub(super) bound: TermId,
    pub(super) width: u32,
    pub(super) length: u128,
    pub(super) constant_base: Option<u128>,
}

#[derive(Clone, Copy)]
pub(super) struct RangeMiss {
    pub(super) source: NegativeRange,
    pub(super) offset: u128,
}

fn constant(terms: &TermStore, term: TermId, width: u32) -> Option<u128> {
    let TermData::Const(Constant::BitVec {
        value,
        width: actual,
    }) = terms.get(term)
    else {
        return None;
    };
    if *actual != width
        || value.sign() == num_bigint::Sign::Minus
        || value.bits() > u64::from(width)
    {
        return None;
    }
    value.to_u128()
}

/// A fixed-size syntax/type probe; callers charge it before reading terms.
fn negative_range(terms: &TermStore, literal: TermId, fact: usize) -> Option<NegativeRange> {
    terms.entry_stamp(literal)?;
    if terms.sort(literal) != &Sort::Bool {
        return None;
    }
    let TermData::Not(predicate) = terms.get(literal) else {
        return None;
    };
    let predicate = *predicate;
    terms.entry_stamp(predicate)?;
    if terms.sort(predicate) != &Sort::Bool {
        return None;
    }
    let TermData::App(Symbol::Named(head), arguments) = terms.get(predicate) else {
        return None;
    };
    let &[delta, bound] = arguments.as_slice() else {
        return None;
    };
    if head != "bvult" || terms.is_declared_function(head) {
        return None;
    }
    for term in [delta, bound] {
        terms.entry_stamp(term)?;
    }
    let width = terms
        .sort(delta)
        .bitvec_width()
        .filter(|width| (1..=128).contains(width))?;
    if terms.sort(bound).bitvec_width() != Some(width) {
        return None;
    }
    let length = constant(terms, bound, width)?;
    if length == 0 {
        return None;
    }
    let TermData::App(Symbol::Named(head), arguments) = terms.get(delta) else {
        return None;
    };
    let &[point, base] = arguments.as_slice() else {
        return None;
    };
    if head != "bvsub" || terms.is_declared_function(head) {
        return None;
    }
    for term in [point, base] {
        terms.entry_stamp(term)?;
        if terms.sort(term).bitvec_width() != Some(width) {
            return None;
        }
    }
    // A symbolic start is an ACTUAL word leaf. Compound starts keep the
    // existing route; no fresh symbolic word abstracts their meaning.
    let constant_base = match terms.get(base) {
        TermData::Var(..) => None,
        TermData::App(_, arguments) if arguments.is_empty() => None,
        TermData::Const(Constant::BitVec { .. }) => Some(constant(terms, base, width)?),
        _ => return None,
    };
    Some(NegativeRange {
        fact,
        predicate,
        delta,
        point,
        base,
        bound,
        width,
        length,
        constant_base,
    })
}

#[cfg(test)]
mod namespace_tests {
    use super::*;

    #[test]
    fn registered_range_functions_do_not_supply_arithmetic_facts() {
        let mut terms = TermStore::new();
        let word = Sort::bitvec(8);
        let point = terms.mk_var("point", word.clone());
        let base = terms.mk_var("base", word.clone());
        let bound = terms.mk_bitvec(num_bigint::BigInt::from(4), 8);
        let delta = terms.mk_app(Symbol::named("bvsub"), [point, base], word);
        let predicate = terms.mk_app(Symbol::named("bvult"), [delta, bound], Sort::Bool);
        let literal = terms.mk_not_raw(predicate);
        assert!(negative_range(&terms, literal, 0).is_some());
        for identity in ["bvult", "bvsub"] {
            let mut declared = terms.clone();
            declared.register_declared_function(identity);
            assert!(
                negative_range(&declared, literal, 0).is_none(),
                "{identity}"
            );
            assert!(negative_range(&declared.clone(), literal, 0).is_none());
        }
    }
}

impl Executor {
    pub(super) fn ground_negative_ranges(
        &self,
        facts: &FactBase,
        work: &mut SharedGroundWork,
    ) -> Option<ay_core::kani_compat::DetHashMap<TermId, Vec<NegativeRange>>> {
        let mut ranges = ay_core::kani_compat::DetHashMap::default();
        let stop = self.make_proof_assembly_should_stop();
        for &index in facts.negative_bv_ranges() {
            work.spend(8)?;
            if stop() {
                return None;
            }
            let literal = facts.facts().get(index)?.literal;
            let Some(range) = negative_range(&self.ctx.terms, literal, index) else {
                continue;
            };
            ranges.try_reserve(1).ok()?;
            let candidates: &mut Vec<NegativeRange> = ranges.entry(range.point).or_default();
            candidates.try_reserve(1).ok()?;
            candidates.push(range);
        }
        Some(ranges)
    }

    /// Derive the exact guard from an earlier source fact. The conditional
    /// scalar relation is decomposed into ordinary congruence/transitivity,
    /// one bounded polynomial equality and a closed comparison. A direct
    /// conditional BV lemma currently has no complete wire lowering.
    pub(super) fn emit_ground_range_skip(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        point: TermId,
        index: TermId,
        equality: TermId,
        witness: RangeMiss,
        bases: Option<(TermId, TermId)>,
        limit: usize,
    ) -> Option<ProofId> {
        let source = self.emit_ground_fact(emitter, witness.source.fact)?;
        let range = negative_range(&self.ctx.terms, source.literal, witness.source.fact)?;
        self.ctx.terms.entry_stamp(index)?;
        self.ctx.terms.entry_stamp(equality)?;
        let (left, right) = decode_eq_local(&self.ctx.terms, equality)?;
        if range.predicate != witness.source.predicate
            || range.point != point
            || range.base != witness.source.base
            || range.bound != witness.source.bound
            || range.width != witness.source.width
            || witness.offset >= range.length
            || self.ctx.terms.sort(index).bitvec_width() != Some(range.width)
            || !((left == point && right == index) || (right == point && left == index))
        {
            return None;
        }
        let stop = self.make_proof_assembly_should_stop();
        if stop() {
            return None;
        }
        emitter.admit_steps(20)?;
        let sort = Sort::bitvec(range.width);
        let offset = self.ctx.terms.mk_bitvec(witness.offset.into(), range.width);
        let image_delta =
            self.ctx
                .terms
                .mk_app(Symbol::named("bvsub"), [index, range.base], sort.clone());
        let evaluation_delta = if let Some((base, expected)) = bases {
            self.ctx.terms.entry_stamp(base)?;
            if expected != range.base
                || self.ctx.terms.sort(base).bitvec_width() != Some(range.width)
            {
                return None;
            }
            self.ctx
                .terms
                .mk_app(Symbol::named("bvsub"), [index, base], sort)
        } else {
            image_delta
        };
        let evaluated =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [evaluation_delta, offset], Sort::Bool);
        let closed_range =
            self.ctx
                .terms
                .mk_app(Symbol::named("bvult"), [offset, range.bound], Sort::Bool);
        // The offset identity has exactly canceled integer coefficients.
        // Use the existing bounded polynomial owner, rather than spending a
        // whole-proof expensive bit-blast slot on each store. Both scalar
        // statements remain proposals independently reconstructed at final
        // strict replay; no fresh search/checker allowance is granted.
        let evaluated_step = emitter.proof.add_theory_lemma_with_kind(
            "arith",
            vec![evaluated],
            TheoryLemmaKind::ArithClauseTautology,
        );
        let arithmetic = if let Some((base, _)) = bases {
            let joined = self.ctx.terms.mk_app(
                Symbol::named("="),
                [image_delta, evaluation_delta],
                Sort::Bool,
            );
            let joined_step = self.emit_closure_cong(
                emitter,
                &[index, range.base],
                &[index, base],
                joined,
                limit,
            )?;
            emitter.admit_steps(3)?;
            let result =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [image_delta, offset], Sort::Bool);
            let clause = vec![
                self.ctx.terms.mk_not_raw(joined),
                self.ctx.terms.mk_not_raw(evaluated),
                result,
            ];
            let lemma = emitter.proof.add_theory_lemma_with_kind(
                "euf",
                clause.clone(),
                TheoryLemmaKind::EufTransitive,
            );
            let step = self.resolve_closure_units(
                emitter,
                lemma,
                clause,
                &[
                    DerivedUnit {
                        step: joined_step,
                        literal: joined,
                    },
                    DerivedUnit {
                        step: evaluated_step,
                        literal: evaluated,
                    },
                ],
                &[result],
            )?;
            DerivedUnit {
                step,
                literal: result,
            }
        } else {
            DerivedUnit {
                step: evaluated_step,
                literal: evaluated,
            }
        };
        // A wide closed comparison uses four ordinary steps instead of one
        // BB lemma. Reserve those actual slots within the unchanged ceiling.
        emitter.admit_steps(17 + 3 * usize::from(range.width > u64::BITS))?;
        let disequality = self.ctx.terms.mk_not_raw(equality);
        let joined =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [range.delta, image_delta], Sort::Bool);
        let constant_delta =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [range.delta, offset], Sort::Bool);
        let predicate_equality = self.ctx.terms.mk_app(
            Symbol::named("="),
            [range.predicate, closed_range],
            Sort::Bool,
        );
        // Spell every argument hypothesis explicitly. The effective surface
        // table may be present even when neither application is re-spelled;
        // its checked `eq_congruent` route requires the complete binary
        // argument list. Discharge the unchanged base with real reflexivity.
        let base_equal =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [range.base, range.base], Sort::Bool);
        let base_reflexive = emitter.proof.add_theory_lemma_with_kind(
            "euf",
            vec![base_equal],
            TheoryLemmaKind::EufReflexive,
        );
        let not_base_equal = self.ctx.terms.mk_not_raw(base_equal);
        let congruent = emitter.proof.add_theory_lemma_with_kind(
            "euf",
            vec![disequality, not_base_equal, joined],
            TheoryLemmaKind::EufCongruent,
        );
        let congruent = emitter.proof.add_resolution(
            vec![disequality, joined],
            base_equal,
            congruent,
            base_reflexive,
        );
        let not_joined = self.ctx.terms.mk_not_raw(joined);
        let not_arithmetic = self.ctx.terms.mk_not_raw(arithmetic.literal);
        let transitive = emitter.proof.add_theory_lemma_with_kind(
            "euf",
            vec![not_joined, not_arithmetic, constant_delta],
            TheoryLemmaKind::EufTransitive,
        );
        let transitive = emitter.proof.add_resolution(
            vec![not_joined, constant_delta],
            arithmetic.literal,
            transitive,
            arithmetic.step,
        );
        let conditional_delta = emitter.proof.add_resolution(
            vec![disequality, constant_delta],
            joined,
            congruent,
            transitive,
        );
        let closed = if range.width <= u64::BITS {
            // Preserve the bounded <=64-bit route, including its cheap census
            // and support for long chains without expensive-lemma entries.
            emitter.proof.add_theory_lemma_with_kind(
                "bv",
                vec![closed_range],
                TheoryLemmaKind::BvBitBlast,
            )
        } else {
            // Both operands are actual, same-width canonical literals: the
            // range probe checked the bound, and offset < length checked the
            // freshly constructed offset. The existing shared ground
            // evaluator checks exactly this unsigned literal comparison.
            // Propose its value, then derive the unit with stock Boolean
            // rules; final replay keeps the one original aggregate envelope.
            let truth = self.ctx.terms.true_term();
            let negative_truth = self.ctx.terms.mk_not_raw(truth);
            let claim =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [closed_range, truth], Sort::Bool);
            let negative_claim = self.ctx.terms.mk_not_raw(claim);
            let evaluated =
                emitter
                    .proof
                    .add_rule_step(AletheRule::Evaluate, vec![claim], vec![], vec![]);
            let logical = emitter.proof.add_rule_step(
                AletheRule::EquivPos1,
                vec![negative_claim, closed_range, negative_truth],
                vec![],
                vec![],
            );
            let constant = if let Some(step) = emitter.offset_constants[1] {
                step
            } else {
                let step =
                    emitter
                        .proof
                        .add_rule_step(AletheRule::True, vec![truth], vec![], vec![]);
                emitter.offset_constants[1] = Some(step);
                step
            };
            emitter.proof.add_rule_step(
                AletheRule::Resolution,
                vec![closed_range],
                vec![logical, evaluated, constant],
                vec![],
            )
        };
        let not_constant_delta = self.ctx.terms.mk_not_raw(constant_delta);
        let bound_equal =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [range.bound, range.bound], Sort::Bool);
        let bound_reflexive = emitter.proof.add_theory_lemma_with_kind(
            "euf",
            vec![bound_equal],
            TheoryLemmaKind::EufReflexive,
        );
        let not_bound_equal = self.ctx.terms.mk_not_raw(bound_equal);
        let predicate = emitter.proof.add_theory_lemma_with_kind(
            "euf",
            vec![not_constant_delta, not_bound_equal, predicate_equality],
            TheoryLemmaKind::EufCongruent,
        );
        let predicate = emitter.proof.add_resolution(
            vec![not_constant_delta, predicate_equality],
            bound_equal,
            predicate,
            bound_reflexive,
        );
        let not_predicate = self.ctx.terms.mk_not_raw(predicate_equality);
        let not_closed = self.ctx.terms.mk_not_raw(closed_range);
        let logical = emitter.proof.add_rule_step(
            AletheRule::EquivPos1,
            vec![not_predicate, range.predicate, not_closed],
            Vec::new(),
            Vec::new(),
        );
        let logical = emitter.proof.add_resolution(
            vec![not_predicate, range.predicate],
            closed_range,
            logical,
            closed,
        );
        let predicate = emitter.proof.add_resolution(
            vec![not_constant_delta, range.predicate],
            predicate_equality,
            predicate,
            logical,
        );
        let conditional_miss = emitter.proof.add_resolution(
            vec![disequality, range.predicate],
            constant_delta,
            conditional_delta,
            predicate,
        );
        let result = emitter.proof.add_resolution(
            vec![disequality],
            range.predicate,
            conditional_miss,
            source.step,
        );
        (!stop()).then_some(result)
    }
}
