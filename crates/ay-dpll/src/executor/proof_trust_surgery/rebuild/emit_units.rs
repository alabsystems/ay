// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Re-derivation of recognized `and_pos` unit consumers.

use super::super::*;
use super::model::{EmitDecision, RebuildWalk};

enum UnitEmission {
    Distinct {
        and_term: TermId,
        conjunct: TermId,
    },
    AndBounds {
        raw_and: TermId,
        raw: TermId,
        bridge_atom: Option<TermId>,
        conjunct: TermId,
    },
    Existing(Option<ProofId>),
    QuantExpansion(TermId),
    Reject,
}

impl RebuildWalk<'_, '_> {
    pub(super) fn emit_unit_pattern(&mut self, index: usize) -> EmitDecision {
        let Some(&(assume_index, position)) = self.plans.unit_patterns.get(&index) else {
            return EmitDecision::NotApplicable;
        };
        let Some(&assume) = self.state.assume_new_id.get(&assume_index) else {
            return EmitDecision::Reject;
        };
        let emission = match &self.plans.assume_plans[&assume_index] {
            AssumePlan::Distinct {
                and_term, conjs, ..
            } => UnitEmission::Distinct {
                and_term: *and_term,
                conjunct: conjs[position],
            },
            AssumePlan::AndBounds {
                raw_and,
                raws,
                conjs,
            } => UnitEmission::AndBounds {
                raw_and: *raw_and,
                raw: raws[position].0,
                bridge_atom: raws[position].1,
                conjunct: conjs[position],
            },
            AssumePlan::AndDistinct { .. } => UnitEmission::Existing(
                self.state
                    .anddistinct_units
                    .get(&assume_index)
                    .and_then(|units| units.get(position))
                    .copied(),
            ),
            AssumePlan::QuantExpansion { forall_term, .. } => {
                UnitEmission::QuantExpansion(*forall_term)
            }
            AssumePlan::Literal { .. } => UnitEmission::Reject,
        };
        let unit = match emission {
            UnitEmission::Distinct { and_term, conjunct } => {
                self.emit_distinct_unit(assume_index, position, and_term, conjunct)
            }
            UnitEmission::AndBounds {
                raw_and,
                raw,
                bridge_atom,
                conjunct,
            } => self.emit_and_bounds_unit(assume, position, raw_and, raw, bridge_atom, conjunct),
            UnitEmission::Existing(unit) => unit,
            UnitEmission::QuantExpansion(forall_term) => {
                self.emit_quant_expansion_unit(assume_index, position, forall_term, assume)
            }
            UnitEmission::Reject => None,
        };
        let Some(unit) = unit else {
            return EmitDecision::Reject;
        };
        self.state.map[index] = Some(unit);
        EmitDecision::Emitted
    }

    fn emit_distinct_unit(
        &mut self,
        assume_index: usize,
        position: usize,
        and_term: TermId,
        conjunct: TermId,
    ) -> Option<ProofId> {
        let and_unit = *self.state.distinct_unit.get(&assume_index)?;
        let not_and = self.executor.ctx.terms.mk_not_raw(and_term);
        let position = u32::try_from(position).ok()?;
        let extraction = self.state.new_proof.add_rule_step(
            AletheRule::AndPos(position),
            vec![not_and, conjunct],
            Vec::new(),
            Vec::new(),
        );
        Some(
            self.state
                .new_proof
                .add_resolution(vec![conjunct], and_term, extraction, and_unit),
        )
    }

    fn emit_and_bounds_unit(
        &mut self,
        assume: ProofId,
        position: usize,
        raw_and: TermId,
        raw: TermId,
        bridge_atom: Option<TermId>,
        conjunct: TermId,
    ) -> Option<ProofId> {
        let not_raw_and = self.executor.ctx.terms.mk_not_raw(raw_and);
        let position = u32::try_from(position).ok()?;
        let extraction = self.state.new_proof.add_rule_step(
            AletheRule::AndPos(position),
            vec![not_raw_and, raw],
            Vec::new(),
            Vec::new(),
        );
        let raw_unit = self
            .state
            .new_proof
            .add_resolution(vec![raw], raw_and, extraction, assume);
        let Some(atom) = bridge_atom else {
            return Some(raw_unit);
        };
        let raw_complement = complement_of(&mut self.executor.ctx.terms, raw);
        let lemma = Executor::add_pair_lemma(&mut self.state.new_proof, conjunct, raw_complement);
        Some(
            self.state
                .new_proof
                .add_resolution(vec![conjunct], atom, lemma, raw_unit),
        )
    }

    fn emit_quant_expansion_unit(
        &mut self,
        assume_index: usize,
        position: usize,
        forall_term: TermId,
        assume: ProofId,
    ) -> Option<ProofId> {
        if let Some(&unit) = self
            .state
            .quant_units_emitted
            .get(&(assume_index, position))
        {
            return Some(unit);
        }
        let chain = self.plans.quant_chains.get(&(assume_index, position))?;
        let unit = self.executor.emit_quant_instance_chain(
            &mut self.state.new_proof,
            forall_term,
            assume,
            chain,
        );
        self.state
            .quant_units_emitted
            .insert((assume_index, position), unit);
        Some(unit)
    }
}
