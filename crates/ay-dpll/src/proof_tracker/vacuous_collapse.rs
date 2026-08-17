// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict proof fragments for vacuous quantifier collapse.

use super::*;

/// What a vacuous-collapse proof certified for the checked sidecar.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct VacuousCollapseProof {
    pub(crate) unit: ProofId,
    pub(crate) quantified: TermId,
    pub(crate) witness: TermId,
    pub(crate) instance: TermId,
    pub(crate) positive: bool,
}

impl ProofTracker {
    /// Certify a top-level vacuous single-binder quantifier collapse.
    pub(crate) fn add_vacuous_quantifier_collapse(
        &mut self,
        terms: &mut TermStore,
        source: TermId,
        asserted: TermId,
    ) -> Option<VacuousCollapseProof> {
        if !self.enabled {
            return None;
        }
        let (quantified, positive) = match terms.get(source) {
            TermData::Forall(..) | TermData::Exists(..) => (source, true),
            TermData::Not(inner) => {
                let inner = *inner;
                matches!(terms.get(inner), TermData::Forall(..)).then_some((inner, false))?
            }
            _ => return None,
        };
        let (bindings, body, is_exists) = match terms.get(quantified).clone() {
            TermData::Forall(bindings, body, _) => (bindings, body, false),
            TermData::Exists(bindings, body, _) => (bindings, body, true),
            _ => return None,
        };
        let [(binder, sort)] = bindings.as_slice() else {
            return None;
        };
        let probe = terms.mk_fresh_var(&format!("vacprobe!{binder}"), sort.clone());
        let mut substitution: HashMap<String, TermId> = HashMap::default();
        substitution.insert(binder.clone(), probe);
        if crate::ematching::subst_vars_exact_qf(terms, body, &substitution)? != body {
            return None;
        }
        let expected = if positive { body } else { terms.mk_not(body) };
        if expected != asserted {
            return None;
        }

        let witness = terms.mk_fresh_var(&format!("sk!{binder}"), sort.clone());
        let TermData::Var(fresh_name, _) = terms.get(witness).clone() else {
            return None;
        };
        terms.mark_skolem_symbol(fresh_name);
        let choice_body = if is_exists { body } else { terms.mk_not(body) };
        terms.register_skolem_choice(
            witness,
            ay_core::SkolemChoice {
                binder: binder.clone(),
                sort: sort.clone(),
                body: choice_body,
            },
        );

        let (unit, literal) =
            self.add_vacuous_quantifier_unit(terms, source, quantified, body, witness, positive)?;
        let unit = self.bridge_vacuous_collapse_literal(terms, unit, literal, asserted);
        self.lemma_map.or_insert(
            LemmaKey::new(TheoryLemmaKind::Generic, &[asserted], None),
            unit,
        );
        Some(VacuousCollapseProof {
            unit,
            quantified,
            witness,
            instance: body,
            positive,
        })
    }

    pub(super) fn add_vacuous_quantifier_unit(
        &mut self,
        terms: &mut TermStore,
        source: TermId,
        quantified: TermId,
        body: TermId,
        witness: TermId,
        positive: bool,
    ) -> Option<(ProofId, TermId)> {
        let source_id = self.add_assumption(source, None)?;
        let equality = terms.mk_app(Symbol::named("="), [quantified, body], Sort::Bool);
        let sko = self.proof.add_rule_step(
            AletheRule::Skolem,
            vec![equality],
            Vec::new(),
            vec![witness],
        );
        let not_equality = terms.mk_not_raw(equality);
        if positive {
            let not_quantified = terms.mk_not_raw(quantified);
            let tautology = self.proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equality, not_quantified, body],
                Vec::new(),
                Vec::new(),
            );
            let elided =
                self.proof
                    .add_resolution(vec![not_quantified, body], equality, tautology, sko);
            let unit = self
                .proof
                .add_resolution(vec![body], quantified, elided, source_id);
            Some((unit, body))
        } else {
            let not_body = terms.mk_not_raw(body);
            let tautology = self.proof.add_rule_step(
                AletheRule::EquivPos1,
                vec![not_equality, quantified, not_body],
                Vec::new(),
                Vec::new(),
            );
            let elided =
                self.proof
                    .add_resolution(vec![quantified, not_body], equality, tautology, sko);
            let unit = self
                .proof
                .add_resolution(vec![not_body], quantified, source_id, elided);
            Some((unit, not_body))
        }
    }

    pub(super) fn bridge_vacuous_collapse_literal(
        &mut self,
        terms: &mut TermStore,
        unit: ProofId,
        literal: TermId,
        asserted: TermId,
    ) -> ProofId {
        if literal == asserted {
            return unit;
        }
        let bridge_equality = terms.mk_app(Symbol::named("="), [literal, asserted], Sort::Bool);
        let bridge = self.proof.add_rule_step(
            AletheRule::True,
            vec![bridge_equality],
            Vec::new(),
            Vec::new(),
        );
        let not_bridge_equality = terms.mk_not_raw(bridge_equality);
        let not_literal = terms.mk_not_raw(literal);
        let tautology = self.proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_bridge_equality, not_literal, asserted],
            Vec::new(),
            Vec::new(),
        );
        let elided = self.proof.add_resolution(
            vec![not_literal, asserted],
            bridge_equality,
            tautology,
            bridge,
        );
        self.proof
            .add_resolution(vec![asserted], literal, elided, unit)
    }
}
