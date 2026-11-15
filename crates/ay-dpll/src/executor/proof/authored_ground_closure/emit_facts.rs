// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Emission of the facts behind a closure refutation.
//!
//! Each fact becomes ONE unit clause `(cl literal)`, memoized:
//!
//! * `Root` — `assume` of the exact raw authored root;
//! * `Conjunct` — `and_pos` projection of the raw authored conjunction;
//! * `SubConjunct` — `and_pos` projection of a nested conjunction, resolved
//!   against its parent fact's unit;
//! * `Closed` — `BvBitBlast`, the checker's recognizer re-deciding it;
//! * `EqualityHolds` / `EqualityRefuted` — the closure's `EufTransitive`
//!   explanation, refuted against two constants by `BvBitBlast`;
//! * `PredCongruent` — `EufCongruentPred` over the explained arguments;
//! * `Propagated` — the shared `forall_inst` → `or` → `resolution` prologue,
//!   clausified by `or`/`implies`, with every other literal resolved away.

use super::emit::ClosureEmitter;
use super::facts::{literal_atom, FactReason};
use super::instances::InstanceShape;
use super::*;

impl Executor {
    /// The unit proving fact `index`, emitted once.
    pub(super) fn emit_ground_fact(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        index: usize,
    ) -> Option<DerivedUnit> {
        if let Some(&unit) = emitter.fact_units.get(&index) {
            return Some(unit);
        }
        emitter.within_budget()?;
        let fact = emitter.facts.facts().get(index)?.clone();
        let literal = fact.literal;
        let step = match fact.reason {
            FactReason::Root => emitter.assume(literal),
            FactReason::Conjunct { root, position } => {
                let assumed = emitter.assume(root);
                let negated = self.ctx.terms.mk_not_raw(root);
                let projection = emitter.proof.add_rule_step(
                    AletheRule::AndPos(position),
                    vec![negated, literal],
                    Vec::new(),
                    vec![root],
                );
                emitter
                    .proof
                    .add_resolution(vec![literal], root, projection, assumed)
            }
            FactReason::SubConjunct { parent, position } => {
                let conjunction = self.emit_ground_fact(emitter, parent)?;
                let negated = self.ctx.terms.mk_not_raw(conjunction.literal);
                let projection = emitter.proof.add_rule_step(
                    AletheRule::AndPos(position),
                    vec![negated, literal],
                    Vec::new(),
                    vec![conjunction.literal],
                );
                emitter.proof.add_resolution(
                    vec![literal],
                    conjunction.literal,
                    projection,
                    conjunction.step,
                )
            }
            FactReason::NegatedTrueEquality { parent } => {
                if parent >= index {
                    return None;
                }
                let source = self.emit_ground_fact(emitter, parent)?;
                let TermData::Not(equality) = *self.ctx.terms.get(source.literal) else {
                    return None;
                };
                let body = self.true_equality_body(equality)?;
                if self.ctx.terms.mk_not_raw(body) != literal {
                    return None;
                }
                let (left, right) = decode_eq_local(&self.ctx.terms, equality)?;
                let truth = self.ctx.terms.true_term();
                emitter.admit_steps(3 + usize::from(emitter.offset_constants[1].is_none()))?;
                let axiom = if let Some(step) = emitter.offset_constants[1] {
                    step
                } else {
                    let step = emitter.proof.add_rule_step(
                        AletheRule::True,
                        vec![truth],
                        Vec::new(),
                        Vec::new(),
                    );
                    emitter.offset_constants[1] = Some(step);
                    step
                };
                let clause = vec![
                    equality,
                    self.ctx.terms.mk_not_raw(left),
                    self.ctx.terms.mk_not_raw(right),
                ];
                let projection = emitter.proof.add_rule_step(
                    AletheRule::EquivNeg1,
                    clause.clone(),
                    Vec::new(),
                    Vec::new(),
                );
                // `source` is a negative unit. Resolve its atom directly;
                // the positive-unit helper intentionally retains raw `not`
                // shells and cannot turn `(not (not equality))` into it.
                let without_equality = vec![
                    self.ctx.terms.mk_not_raw(left),
                    self.ctx.terms.mk_not_raw(right),
                ];
                let projected = emitter.proof.add_resolution(
                    without_equality,
                    equality,
                    projection,
                    source.step,
                );
                emitter
                    .proof
                    .add_resolution(vec![literal], truth, projected, axiom)
            }
            FactReason::NegatedDisjunct { parent, position } => {
                if parent >= index {
                    return None;
                }
                let source = self.emit_ground_fact(emitter, parent)?;
                let TermData::Not(disjunction) = *self.ctx.terms.get(source.literal) else {
                    return None;
                };
                let TermData::App(Symbol::Named(head), arguments) = self.ctx.terms.get(disjunction)
                else {
                    return None;
                };
                if head != "or" {
                    return None;
                }
                let child = *arguments.get(usize::try_from(position).ok()?)?;
                if self.ctx.terms.mk_not_raw(child) != literal {
                    return None;
                }
                emitter.admit_steps(2)?;
                let projection = emitter.proof.add_rule_step(
                    AletheRule::OrNeg,
                    vec![disjunction, literal],
                    Vec::new(),
                    Vec::new(),
                );
                emitter
                    .proof
                    .add_resolution(vec![literal], disjunction, projection, source.step)
            }
            FactReason::Closed => emitter.proof.add_theory_lemma_with_kind(
                "bv",
                vec![literal],
                TheoryLemmaKind::BvBitBlast,
            ),
            FactReason::EqualityHolds => {
                let (lhs, rhs) = decode_eq_local(&self.ctx.terms, literal)?;
                let unit = self.emit_closure_path_unit(emitter, lhs, rhs, fact.edge_limit)?;
                (unit.literal == literal).then_some(unit.step)?
            }
            FactReason::EqualityRefuted => {
                let (atom, true) = literal_atom(&self.ctx.terms, literal) else {
                    return None;
                };
                let (lhs, rhs) = decode_eq_local(&self.ctx.terms, atom)?;
                let (step, equality) =
                    self.emit_closure_index_disequality(emitter, lhs, rhs, fact.edge_limit)?;
                (equality == atom).then_some(step)?
            }
            FactReason::PredCongruent { source } => {
                self.emit_pred_congruence(emitter, literal, source, fact.edge_limit)?
            }
            FactReason::Propagated { clause, refuting } => {
                self.emit_refuted_instance(emitter, clause, &refuting, &[literal])?
            }
        };
        let unit = DerivedUnit { step, literal };
        emitter.fact_units.insert(index, unit);
        Some(unit)
    }

    /// `EufCongruentPred` from fact `source`, `(p a..)` or `(not (p a..))`,
    /// to `literal`, `(p b..)` or `(not (p b..))` of the same polarity.
    fn emit_pred_congruence(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        literal: TermId,
        source: usize,
        limit: usize,
    ) -> Option<ProofId> {
        let source_unit = self.emit_ground_fact(emitter, source)?;
        let (target, negated) = literal_atom(&self.ctx.terms, literal);
        let (origin, source_negated) = literal_atom(&self.ctx.terms, source_unit.literal);
        if negated != source_negated {
            return None;
        }
        // The lemma concludes its LAST literal from its second-to-last: the
        // positive fact flows origin → target, the negative one back.
        let (from, to) = if negated {
            (target, origin)
        } else {
            (origin, target)
        };
        let (TermData::App(_, from_args), TermData::App(_, to_args)) = (
            self.ctx.terms.get(from).clone(),
            self.ctx.terms.get(to).clone(),
        ) else {
            return None;
        };
        let mut premises = Vec::with_capacity(from_args.len());
        for (&left, &right) in from_args.iter().zip(to_args.iter()) {
            premises.push(self.emit_closure_path_unit(emitter, left, right, limit)?);
        }
        let mut clause: Vec<TermId> = premises
            .iter()
            .map(|premise| self.ctx.terms.mk_not_raw(premise.literal))
            .collect();
        let not_from = self.ctx.terms.mk_not_raw(from);
        clause.extend([not_from, to]);
        let lemma = emitter.proof.add_theory_lemma_with_kind(
            "euf",
            clause.clone(),
            TheoryLemmaKind::EufCongruentPred,
        );
        let step =
            self.resolve_closure_units(emitter, lemma, clause, &premises, &[not_from, to])?;
        // Positive: resolve `(not from)` against the source unit `from`.
        // Negative: resolve `to` (= origin) against the source unit
        // `(not origin)`, leaving `(not target)`.
        let (remaining, pivot) = if negated { (not_from, to) } else { (to, from) };
        Some(
            emitter
                .proof
                .add_resolution(vec![remaining], pivot, step, source_unit.step),
        )
    }

    /// Instance clause `clause`, with the literals the `refuting` facts
    /// contradict resolved away; exactly `expected` must remain.
    pub(super) fn emit_refuted_instance(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        clause: usize,
        refuting: &[usize],
        expected: &[TermId],
    ) -> Option<ProofId> {
        let instance = emitter.facts.clauses().get(clause)?.clone();
        let mut step = self.add_forall_instance_prologue(
            &mut emitter.proof,
            instance.forall_root,
            instance.value,
            instance.instance,
        );
        match instance.shape {
            InstanceShape::Unit => {}
            InstanceShape::Or => {
                step = emitter.proof.add_rule_step(
                    AletheRule::Or,
                    instance.literals.clone(),
                    vec![step],
                    Vec::new(),
                );
            }
            InstanceShape::Implies => {
                step = emitter.proof.add_rule_step(
                    AletheRule::Implies,
                    instance.literals.clone(),
                    vec![step],
                    Vec::new(),
                );
            }
        }
        let mut remaining = instance.literals;
        for &fact in refuting {
            let unit = self.emit_ground_fact(emitter, fact)?;
            let (position, pivot) = remaining.iter().enumerate().find_map(|(position, &lit)| {
                self.resolution_pivot(unit.literal, lit)
                    .map(|pivot| (position, pivot))
            })?;
            let _ = remaining.remove(position);
            step = emitter
                .proof
                .add_resolution(remaining.clone(), pivot, step, unit.step);
        }
        (remaining == expected).then_some(step)
    }

    /// The pivot on which `unit` and the complementary clause literal `other`
    /// resolve: the one of the two that the other negates.
    fn resolution_pivot(&self, unit: TermId, other: TermId) -> Option<TermId> {
        match (self.ctx.terms.get(unit), self.ctx.terms.get(other)) {
            (TermData::Not(inner), _) if *inner == other => Some(other),
            (_, TermData::Not(inner)) if *inner == unit => Some(unit),
            _ => None,
        }
    }
}
