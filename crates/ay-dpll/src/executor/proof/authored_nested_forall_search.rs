// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded search and checker-backed closure for nested authored universals.

use super::*;

const MAX_NESTED_FORALL_PROPOSALS: usize = 512;

impl Executor {
    pub(super) fn search_nested_forall_chain(
        &mut self,
        authored: &[TermId],
        quantified: TermId,
        quantified_unit: Option<ProofId>,
        mut base: Proof,
        depth: usize,
        proposals: &mut usize,
    ) -> Option<Proof> {
        const MAX_DEPTH: usize = 8;
        if depth >= MAX_DEPTH || *proposals >= MAX_NESTED_FORALL_PROPOSALS {
            return None;
        }
        let TermData::Forall(bindings, body, _) = self.ctx.terms.get(quantified).clone() else {
            return None;
        };
        if bindings.is_empty() {
            return None;
        }
        let quantified_unit = quantified_unit.unwrap_or_else(|| base.add_assume(quantified, None));
        for values in self.nested_instantiation_tuples(&bindings, authored) {
            *proposals += 1;
            if *proposals > MAX_NESTED_FORALL_PROPOSALS {
                return None;
            }
            let Some(instance) = Self::substitute_bindings_structurally(
                &mut self.ctx.terms,
                body,
                &bindings,
                &values,
            ) else {
                continue;
            };
            let mut candidate = base.clone();
            let instance_unit = self.add_forall_instance_from_unit(
                &mut candidate,
                quantified,
                quantified_unit,
                values,
                instance,
            );
            if let Some(done) = self.continue_nested_forall_instance(
                authored,
                instance,
                instance_unit,
                candidate,
                depth,
                proposals,
            ) {
                return Some(done);
            }
        }
        None
    }

    fn continue_nested_forall_instance(
        &mut self,
        authored: &[TermId],
        instance: TermId,
        instance_unit: ProofId,
        mut candidate: Proof,
        depth: usize,
        proposals: &mut usize,
    ) -> Option<Proof> {
        if matches!(self.ctx.terms.get(instance), TermData::Forall(..)) {
            return self.search_nested_forall_chain(
                authored,
                instance,
                Some(instance_unit),
                candidate,
                depth + 1,
                proposals,
            );
        }
        if let Some((antecedent, consequent)) =
            Self::decode_implication_local(&self.ctx.terms, instance)
        {
            let antecedent_unit =
                self.add_authored_entailment(&mut candidate, antecedent, authored)?;
            let consequent_unit = self.apply_implication_unit(
                &mut candidate,
                instance,
                instance_unit,
                antecedent,
                antecedent_unit,
                consequent,
            );
            if matches!(self.ctx.terms.get(consequent), TermData::Forall(..)) {
                return self.search_nested_forall_chain(
                    authored,
                    consequent,
                    Some(consequent_unit),
                    candidate,
                    depth + 1,
                    proposals,
                );
            }
            return self.close_authored_ground_unit(
                candidate,
                consequent,
                consequent_unit,
                authored,
            );
        }
        self.close_authored_ground_unit(candidate, instance, instance_unit, authored)
    }

    /// Emit `implies_pos` + two resolutions from an ALREADY-DERIVED
    /// `(cl implication)` and `(cl antecedent)`, leaving the unit
    /// `(cl consequent)`.
    ///
    /// Shared with the consequence-replay `ImpliedConsequent` plan
    /// (#implied-forall-ground-inst): one construction, one strict validator
    /// (`validate_implies_pos`), so the two lanes cannot drift.
    pub(super) fn apply_implication_unit(
        &mut self,
        candidate: &mut Proof,
        implication: TermId,
        implication_unit: ProofId,
        antecedent: TermId,
        antecedent_unit: ProofId,
        consequent: TermId,
    ) -> ProofId {
        let not_implication = self.ctx.terms.mk_not_raw(implication);
        let not_antecedent = self.ctx.terms.mk_not_raw(antecedent);
        let implication_clause = candidate.add_rule_step(
            AletheRule::ImpliesPos,
            vec![not_implication, not_antecedent, consequent],
            Vec::new(),
            Vec::new(),
        );
        let open = candidate.add_resolution(
            vec![not_antecedent, consequent],
            implication,
            implication_clause,
            implication_unit,
        );
        candidate.add_resolution(vec![consequent], antecedent, open, antecedent_unit)
    }

    pub(super) fn decode_implication_local(
        terms: &TermStore,
        term: TermId,
    ) -> Option<(TermId, TermId)> {
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            TermData::App(Symbol::Named(name), args) if name == "or" && args.len() == 2 => {
                if let TermData::Not(antecedent) = terms.get(args[0]) {
                    Some((*antecedent, args[1]))
                } else if let TermData::Not(antecedent) = terms.get(args[1]) {
                    Some((*antecedent, args[0]))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub(super) fn add_authored_entailment(
        &mut self,
        candidate: &mut Proof,
        target: TermId,
        authored: &[TermId],
    ) -> Option<ProofId> {
        if authored.contains(&target) {
            return Some(candidate.add_assume(target, None));
        }
        let trailing = vec![target];
        let (clause, farkas, kind, premises) =
            self.search_authored_farkas_conflict(&trailing, authored, 3)?;
        let mut current =
            candidate.add_theory_lemma_with_farkas_and_kind("LRA", clause.clone(), farkas, kind);
        let mut remaining = clause;
        for root in premises {
            let support = candidate.add_assume(root, None);
            let negated = Self::negated_root_literal(&mut self.ctx.terms, root);
            let position = remaining.iter().position(|&literal| literal == negated)?;
            let _ = remaining.remove(position);
            current = candidate.add_resolution(remaining.clone(), root, current, support);
        }
        (remaining == [target]).then_some(current)
    }

    pub(super) fn close_authored_ground_unit(
        &mut self,
        mut candidate: Proof,
        unit: TermId,
        unit_step: ProofId,
        authored: &[TermId],
    ) -> Option<Proof> {
        for &root in authored {
            let pivot = match (self.ctx.terms.get(root), self.ctx.terms.get(unit)) {
                (TermData::Not(inner), _) if *inner == unit => Some(unit),
                (_, TermData::Not(inner)) if *inner == root => Some(root),
                _ => None,
            };
            if let Some(pivot) = pivot {
                let root_step = candidate.add_assume(root, None);
                candidate.add_resolution(Vec::new(), pivot, unit_step, root_step);
                return Some(candidate);
            }
        }
        if let Some(done) =
            self.close_with_checked_farkas(candidate.clone(), unit, unit_step, authored)
        {
            return Some(done);
        }
        self.close_with_checked_nra(candidate, unit, unit_step, authored)
    }

    fn close_with_checked_farkas(
        &mut self,
        mut candidate: Proof,
        unit: TermId,
        unit_step: ProofId,
        authored: &[TermId],
    ) -> Option<Proof> {
        let trailing = vec![Self::negated_root_literal(&mut self.ctx.terms, unit)];
        let (clause, farkas, kind, premises) =
            self.search_authored_farkas_conflict(&trailing, authored, 4)?;
        let mut current =
            candidate.add_theory_lemma_with_farkas_and_kind("LRA", clause.clone(), farkas, kind);
        let mut remaining = clause;
        for root in premises {
            let support = candidate.add_assume(root, None);
            let negated = Self::negated_root_literal(&mut self.ctx.terms, root);
            let position = remaining.iter().position(|&literal| literal == negated)?;
            let _ = remaining.remove(position);
            current = candidate.add_resolution(remaining.clone(), root, current, support);
        }
        let negated_unit = Self::negated_root_literal(&mut self.ctx.terms, unit);
        let position = remaining
            .iter()
            .position(|&literal| literal == negated_unit)?;
        let _ = remaining.remove(position);
        candidate.add_resolution(remaining.clone(), unit, current, unit_step);
        remaining.is_empty().then_some(candidate)
    }

    fn close_with_checked_nra(
        &mut self,
        candidate: Proof,
        unit: TermId,
        unit_step: ProofId,
        authored: &[TermId],
    ) -> Option<Proof> {
        const MAX_NRA_TRIALS: usize = 128;
        let arithmetic_roots = self.arithmetic_authored_roots(authored);
        let mut trials = 0usize;
        for width in 1..=2 {
            let mut selections = Vec::new();
            Self::bounded_index_combinations(
                arithmetic_roots.len(),
                width,
                0,
                &mut Vec::new(),
                &mut selections,
                MAX_NRA_TRIALS,
            );
            for indices in selections {
                trials += 1;
                if trials > MAX_NRA_TRIALS {
                    return None;
                }
                let roots = indices
                    .iter()
                    .map(|&index| arithmetic_roots[index])
                    .collect::<Vec<_>>();
                if let Some(built) = self.try_nra_closure(&candidate, unit, unit_step, &roots) {
                    return Some(built);
                }
            }
        }
        None
    }

    fn arithmetic_authored_roots(&self, authored: &[TermId]) -> Vec<TermId> {
        authored
            .iter()
            .copied()
            .filter(|&root| {
                let atom = match self.ctx.terms.get(root) {
                    TermData::Not(inner) => *inner,
                    _ => root,
                };
                matches!(
                    self.ctx.terms.get(atom),
                    TermData::App(Symbol::Named(name), args)
                        if args.len() == 2
                            && matches!(name.as_str(), "=" | "<" | "<=" | ">" | ">=")
                )
            })
            .collect()
    }

    fn try_nra_closure(
        &mut self,
        candidate: &Proof,
        unit: TermId,
        unit_step: ProofId,
        roots: &[TermId],
    ) -> Option<Proof> {
        let mut clause = roots
            .iter()
            .map(|&root| Self::negated_root_literal(&mut self.ctx.terms, root))
            .collect::<Vec<_>>();
        clause.push(Self::negated_root_literal(&mut self.ctx.terms, unit));
        let kind = if ay_proof::recognize_nra_interval_unsat(&self.ctx.terms, &clause) {
            TheoryLemmaKind::NraIntervalUnsat
        } else if ay_proof::recognize_nra_univariate_unsat(&self.ctx.terms, &clause) {
            TheoryLemmaKind::NraUnivariateUnsat
        } else {
            return None;
        };
        let mut built = candidate.clone();
        let mut current = built.add_theory_lemma_with_kind("NRA", clause.clone(), kind);
        let mut remaining = clause;
        for &root in roots {
            let support = built.add_assume(root, None);
            let negated = Self::negated_root_literal(&mut self.ctx.terms, root);
            let position = remaining.iter().position(|&literal| literal == negated)?;
            let _ = remaining.remove(position);
            current = built.add_resolution(remaining.clone(), root, current, support);
        }
        let negated_unit = Self::negated_root_literal(&mut self.ctx.terms, unit);
        let position = remaining
            .iter()
            .position(|&literal| literal == negated_unit)?;
        let _ = remaining.remove(position);
        built.add_resolution(remaining.clone(), unit, current, unit_step);
        remaining.is_empty().then_some(built)
    }

    fn bounded_index_combinations(
        len: usize,
        width: usize,
        start: usize,
        current: &mut Vec<usize>,
        output: &mut Vec<Vec<usize>>,
        limit: usize,
    ) {
        if output.len() >= limit {
            return;
        }
        if current.len() == width {
            output.push(current.clone());
            return;
        }
        for index in start..len {
            current.push(index);
            Self::bounded_index_combinations(len, width, index + 1, current, output, limit);
            let _ = current.pop();
            if output.len() >= limit {
                return;
            }
        }
    }
}
