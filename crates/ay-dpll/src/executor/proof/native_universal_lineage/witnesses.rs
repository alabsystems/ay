// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retained Skolem records select candidates only. The source is an exact
//! original negative universal, and the existing sko_forall checker verifies
//! actual typed witness metadata and freshness against the FULL query.

use super::NativeUniversalSource;
use crate::executor::Executor;
use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermData, TermId, TheoryLemmaKind};
use std::sync::Arc;

#[derive(Clone, Debug)]
pub(in crate::executor) struct NativeUniversalWitness {
    receipt: Arc<NativeUniversalSource>,
    source: TermId,
    quantified: TermId,
    witness: TermId,
    instance: TermId,
    pub(in crate::executor) asserted: TermId,
    conjunction: Option<(TermId, u32)>,
}

impl Executor {
    pub(in crate::executor) fn native_universal_witnesses(
        &mut self,
        source: &Arc<NativeUniversalSource>,
    ) -> Option<Vec<NativeUniversalWitness>> {
        if !source.is_current(self) || self.skolem_instance_records.len() > 64 {
            return None;
        }
        self.charge_native_universal(
            self.skolem_instance_records.len(),
            self.skolem_instance_records.len().checked_mul(128)?,
        )?;
        let records = self.skolem_instance_records.clone();
        let mut accepted = Vec::new();
        for record in records {
            if record.positive || !source.roots().contains(&record.source) {
                continue;
            }
            self.admit_native_universal_terms(&[
                record.source,
                record.quantified,
                record.witness,
                record.instance,
                record.asserted,
            ])?;
            if !matches!(self.ctx.terms.get(record.source), TermData::Not(q) if *q == record.quantified)
                || !matches!(self.ctx.terms.get(record.quantified), TermData::Forall(..))
                || !matches!(self.ctx.terms.get(record.witness), TermData::Var(name, _)
                    if self.ctx.terms.is_skolem_symbol(name))
            {
                continue;
            }
            let plan = NativeUniversalWitness {
                receipt: Arc::clone(source),
                source: record.source,
                quantified: record.quantified,
                witness: record.witness,
                instance: record.instance,
                asserted: record.asserted,
                conjunction: None,
            };
            self.charge_native_universal(512, 8192)?;
            let mut proof = Proof::new();
            self.emit_native_universal_witness(&mut proof, &plan)?;
            if ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
                &proof,
                &self.ctx.terms,
                None,
                None,
                source.roots(),
                &mut |w, b| self.charge_native_universal(w, b).is_some(),
            )
            .is_ok()
                && source.is_current(self)
            {
                if let TermData::App(symbol, args) = self.ctx.terms.get(plan.asserted) {
                    if symbol.name() == "and" {
                        self.charge_native_universal(args.len(), args.len().checked_mul(128)?)?;
                        if accepted.len().checked_add(args.len())? > 64 {
                            return None;
                        }
                        for (position, &child) in args.iter().enumerate() {
                            accepted.push(NativeUniversalWitness {
                                asserted: child,
                                conjunction: Some((plan.asserted, u32::try_from(position).ok()?)),
                                ..plan.clone()
                            });
                        }
                        continue;
                    }
                }
                if accepted.len() >= 64 {
                    return None;
                }
                accepted.push(plan);
            }
        }
        source.is_current(self).then_some(accepted)
    }

    pub(in crate::executor) fn emit_native_universal_witness(
        &mut self,
        proof: &mut Proof,
        plan: &NativeUniversalWitness,
    ) -> Option<ProofId> {
        if !plan.receipt.is_current(self) {
            return None;
        }
        let source = proof.add_assume(plan.source, None);
        let equality = self.ctx.terms.mk_app(
            Symbol::named("="),
            [plan.quantified, plan.instance],
            Sort::Bool,
        );
        let skolem = proof.add_rule_step(
            AletheRule::Skolem,
            vec![equality],
            Vec::new(),
            vec![plan.witness],
        );
        let neq = self.ctx.terms.mk_not_raw(equality);
        let ninstance = self.ctx.terms.mk_not_raw(plan.instance);
        let equiv = proof.add_rule_step(
            AletheRule::EquivPos1,
            vec![neq, plan.quantified, ninstance],
            Vec::new(),
            Vec::new(),
        );
        let implication =
            proof.add_resolution(vec![plan.quantified, ninstance], equality, skolem, equiv);
        let unit = proof.add_resolution(vec![ninstance], plan.quantified, source, implication);
        let base = plan.conjunction.map_or(plan.asserted, |(parent, _)| parent);
        let unit = if base == ninstance {
            unit
        } else {
            let positive = self.ctx.terms.mk_not_raw(ninstance);
            let bridge = proof.add_theory_lemma_with_kind(
                "bool",
                vec![positive, base],
                TheoryLemmaKind::BoolTautology,
            );
            proof.add_resolution(vec![base], ninstance, unit, bridge)
        };
        if let Some((parent, position)) = plan.conjunction {
            let negative = self.ctx.terms.mk_not_raw(parent);
            let projection = proof.add_rule_step(
                AletheRule::AndPos(position),
                vec![negative, plan.asserted],
                Vec::new(),
                vec![parent],
            );
            Some(proof.add_resolution(vec![plan.asserted], parent, projection, unit))
        } else {
            Some(unit)
        }
    }
}
