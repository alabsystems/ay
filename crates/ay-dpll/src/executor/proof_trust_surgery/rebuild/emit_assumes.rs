// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical derivations replacing normalized assumption leaves.

use super::super::*;
use super::model::RebuildWalk;

enum PlannedAssumeEmission {
    Distinct {
        raw: TermId,
        and_term: TermId,
    },
    AlreadyHoisted,
    AndDistinct {
        raw_and: TermId,
        and_term: TermId,
        units: Vec<AndDistinctUnit>,
        conjs: Vec<TermId>,
    },
    Literal {
        raw: TermId,
        atom: TermId,
        canonical: TermId,
    },
}

impl RebuildWalk<'_, '_> {
    pub(super) fn emit_assume_or_copy(&mut self, index: usize) -> bool {
        if !matches!(self.input.proof.steps[index], ProofStep::Assume(_)) {
            return self.copy_old_step(index);
        }
        let Some(plan) = self.plans.assume_plans.get(&index) else {
            return true;
        };
        let emission = match plan {
            AssumePlan::Distinct {
                raw,
                and_term,
                conjs: _,
            } => PlannedAssumeEmission::Distinct {
                raw: *raw,
                and_term: *and_term,
            },
            AssumePlan::AndBounds { .. } | AssumePlan::QuantExpansion { .. } => {
                PlannedAssumeEmission::AlreadyHoisted
            }
            AssumePlan::AndDistinct {
                raw_and,
                and_term,
                units,
                conjs,
            } => PlannedAssumeEmission::AndDistinct {
                raw_and: *raw_and,
                and_term: *and_term,
                units: units.clone(),
                conjs: conjs.clone(),
            },
            AssumePlan::Literal {
                raw,
                atom,
                canonical,
            } => PlannedAssumeEmission::Literal {
                raw: *raw,
                atom: *atom,
                canonical: *canonical,
            },
        };
        match emission {
            PlannedAssumeEmission::Distinct { raw, and_term } => {
                self.emit_distinct_assume(index, raw, and_term)
            }
            PlannedAssumeEmission::AlreadyHoisted => true,
            PlannedAssumeEmission::AndDistinct {
                raw_and,
                and_term,
                units,
                conjs,
            } => self.emit_and_distinct_assume(index, raw_and, and_term, &units, &conjs),
            PlannedAssumeEmission::Literal {
                raw,
                atom,
                canonical,
            } => self.emit_literal_assume(index, raw, atom, canonical),
        }
    }

    fn emit_distinct_assume(&mut self, index: usize, raw: TermId, and_term: TermId) -> bool {
        let Some(&assume) = self.state.assume_new_id.get(&index) else {
            return false;
        };
        let equivalence =
            self.executor
                .ctx
                .terms
                .mk_app(Symbol::named("="), [raw, and_term], Sort::Bool);
        let not_equivalence = self.executor.ctx.terms.mk_not_raw(equivalence);
        let not_raw = self.executor.ctx.terms.mk_not_raw(raw);
        let distinct_elim = self.state.new_proof.add_rule_step(
            AletheRule::DistinctElim,
            vec![equivalence],
            Vec::new(),
            Vec::new(),
        );
        let equiv_pos = self.state.new_proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_equivalence, not_raw, and_term],
            Vec::new(),
            Vec::new(),
        );
        let bridge = self.state.new_proof.add_resolution(
            vec![not_raw, and_term],
            equivalence,
            equiv_pos,
            distinct_elim,
        );
        let unit = self
            .state
            .new_proof
            .add_resolution(vec![and_term], raw, bridge, assume);
        self.state.distinct_unit.insert(index, unit);
        self.state.map[index] = Some(unit);
        true
    }

    fn emit_literal_assume(
        &mut self,
        index: usize,
        raw: TermId,
        atom: TermId,
        canonical: TermId,
    ) -> bool {
        let Some(&assume) = self.state.assume_new_id.get(&index) else {
            return false;
        };
        let raw_complement = complement_of(&mut self.executor.ctx.terms, raw);
        let lemma = Executor::add_pair_lemma(&mut self.state.new_proof, canonical, raw_complement);
        let unit = self
            .state
            .new_proof
            .add_resolution(vec![canonical], atom, lemma, assume);
        self.state.map[index] = Some(unit);
        true
    }

    fn emit_and_distinct_assume(
        &mut self,
        index: usize,
        raw_and: TermId,
        and_term: TermId,
        units: &[AndDistinctUnit],
        conjs: &[TermId],
    ) -> bool {
        let Some(&assume) = self.state.assume_new_id.get(&index) else {
            return false;
        };
        let not_raw_and = self.executor.ctx.terms.mk_not_raw(raw_and);
        let mut emitted = Vec::with_capacity(conjs.len());
        let mut position = 0usize;
        for unit in units {
            let extraction = self.state.new_proof.add_rule_step(
                AletheRule::AndPos(unit.pos),
                vec![not_raw_and, unit.raw],
                Vec::new(),
                Vec::new(),
            );
            let raw_unit =
                self.state
                    .new_proof
                    .add_resolution(vec![unit.raw], raw_and, extraction, assume);
            if !self.emit_and_distinct_contribution(
                unit,
                raw_unit,
                conjs,
                &mut position,
                &mut emitted,
            ) {
                return false;
            }
        }
        if position != conjs.len() || emitted.len() != conjs.len() {
            return false;
        }
        self.state.anddistinct_units.insert(index, emitted.clone());
        let conjunction = self.close_and_distinct_conjunction(and_term, conjs, &emitted);
        self.state.map[index] = Some(conjunction);
        true
    }

    fn emit_and_distinct_contribution(
        &mut self,
        unit: &AndDistinctUnit,
        raw_unit: ProofId,
        conjs: &[TermId],
        position: &mut usize,
        emitted: &mut Vec<ProofId>,
    ) -> bool {
        match &unit.kind {
            AndDistinctKind::Plain => emitted.push(raw_unit),
            AndDistinctKind::Arith { atom } => {
                let Some(&conjunct) = conjs.get(*position) else {
                    return false;
                };
                let complement = complement_of(&mut self.executor.ctx.terms, unit.raw);
                let lemma =
                    Executor::add_pair_lemma(&mut self.state.new_proof, conjunct, complement);
                emitted.push(self.state.new_proof.add_resolution(
                    vec![conjunct],
                    *atom,
                    lemma,
                    raw_unit,
                ));
            }
            AndDistinctKind::DistinctBinary => {
                let Some(&conjunct) = conjs.get(*position) else {
                    return false;
                };
                emitted.push(self.emit_binary_distinct_bridge(unit.raw, conjunct, raw_unit));
            }
            AndDistinctKind::DistinctNary { and_term, count } => {
                if !self.emit_nary_distinct_bridge(
                    unit.raw, *and_term, *count, raw_unit, conjs, position, emitted,
                ) {
                    return false;
                }
                return true;
            }
            AndDistinctKind::OrPerm { lits } => {
                let Some(&conjunct) = conjs.get(*position) else {
                    return false;
                };
                let Some(or_unit) =
                    self.emit_or_permutation_bridge(unit.raw, conjunct, lits, raw_unit)
                else {
                    return false;
                };
                emitted.push(or_unit);
            }
        }
        *position += 1;
        true
    }

    fn emit_binary_distinct_bridge(
        &mut self,
        raw: TermId,
        conjunct: TermId,
        raw_unit: ProofId,
    ) -> ProofId {
        let equivalence =
            self.executor
                .ctx
                .terms
                .mk_app(Symbol::named("="), [raw, conjunct], Sort::Bool);
        let not_equivalence = self.executor.ctx.terms.mk_not_raw(equivalence);
        let not_raw = self.executor.ctx.terms.mk_not_raw(raw);
        let distinct_elim = self.state.new_proof.add_rule_step(
            AletheRule::DistinctElim,
            vec![equivalence],
            Vec::new(),
            Vec::new(),
        );
        let equiv_pos = self.state.new_proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_equivalence, not_raw, conjunct],
            Vec::new(),
            Vec::new(),
        );
        let bridge = self.state.new_proof.add_resolution(
            vec![not_raw, conjunct],
            equivalence,
            equiv_pos,
            distinct_elim,
        );
        self.state
            .new_proof
            .add_resolution(vec![conjunct], raw, bridge, raw_unit)
    }

    fn emit_nary_distinct_bridge(
        &mut self,
        raw: TermId,
        block: TermId,
        count: u32,
        raw_unit: ProofId,
        conjs: &[TermId],
        position: &mut usize,
        emitted: &mut Vec<ProofId>,
    ) -> bool {
        let block_unit = self.emit_binary_distinct_bridge(raw, block, raw_unit);
        let not_block = self.executor.ctx.terms.mk_not_raw(block);
        for offset in 0..count {
            let Some(&conjunct) = conjs.get(*position) else {
                return false;
            };
            let extraction = self.state.new_proof.add_rule_step(
                AletheRule::AndPos(offset),
                vec![not_block, conjunct],
                Vec::new(),
                Vec::new(),
            );
            emitted.push(self.state.new_proof.add_resolution(
                vec![conjunct],
                block,
                extraction,
                block_unit,
            ));
            *position += 1;
        }
        true
    }

    fn emit_or_permutation_bridge(
        &mut self,
        raw: TermId,
        conjunct: TermId,
        lits: &[(TermId, TermId)],
        raw_unit: ProofId,
    ) -> Option<ProofId> {
        let TermData::App(_, full) = self.executor.ctx.terms.get(raw) else {
            return None;
        };
        let full = full.clone();
        let mut clause: Vec<TermId> = lits.iter().map(|&(source, _)| source).collect();
        let mut current = self.state.new_proof.add_rule_step(
            AletheRule::Or,
            full.clone(),
            vec![raw_unit],
            Vec::new(),
        );
        if full.len() != clause.len() {
            current = self.state.new_proof.add_rule_step(
                AletheRule::Contraction,
                clause.clone(),
                vec![current],
                Vec::new(),
            );
        }
        for (offset, &(source, canonical)) in lits.iter().enumerate() {
            if source == canonical {
                continue;
            }
            let (pivot, bridge) =
                self.executor
                    .add_eq_flip_bridge(&mut self.state.new_proof, source, canonical);
            clause[offset] = canonical;
            current = self
                .state
                .new_proof
                .add_resolution(clause.clone(), pivot, current, bridge);
        }
        for &(_, canonical) in lits {
            let not_canonical = self.executor.ctx.terms.mk_not_raw(canonical);
            let or_neg = self.state.new_proof.add_rule_step(
                AletheRule::OrNeg,
                vec![conjunct, not_canonical],
                Vec::new(),
                Vec::new(),
            );
            if let Some(position) = clause.iter().position(|&literal| literal == canonical) {
                let _ = clause.remove(position);
            }
            clause.push(conjunct);
            current =
                self.state
                    .new_proof
                    .add_resolution(clause.clone(), canonical, current, or_neg);
        }
        Some(self.state.new_proof.add_rule_step(
            AletheRule::Contraction,
            vec![conjunct],
            vec![current],
            Vec::new(),
        ))
    }

    fn close_and_distinct_conjunction(
        &mut self,
        and_term: TermId,
        conjs: &[TermId],
        units: &[ProofId],
    ) -> ProofId {
        let mut clause = Vec::with_capacity(conjs.len() + 1);
        clause.push(and_term);
        for &conjunct in conjs {
            clause.push(self.executor.ctx.terms.mk_not_raw(conjunct));
        }
        let mut current = self.state.new_proof.add_rule_step(
            AletheRule::AndNeg,
            clause.clone(),
            Vec::new(),
            Vec::new(),
        );
        for (&conjunct, &unit) in conjs.iter().zip(units) {
            let complement = self.executor.ctx.terms.mk_not_raw(conjunct);
            if let Some(position) = clause.iter().position(|&literal| literal == complement) {
                let _ = clause.remove(position);
            }
            current = self
                .state
                .new_proof
                .add_resolution(clause.clone(), conjunct, current, unit);
        }
        current
    }
}
