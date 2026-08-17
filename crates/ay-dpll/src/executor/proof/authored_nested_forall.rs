// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored-scope certificates for nested universal instantiation.

use super::*;

impl Executor {
    /// Rebuild the diagonal refutation of an authored `not (exists ...)` from
    /// its exact universal NNF dual.
    pub(super) fn replace_with_exact_authored_negated_exists_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        const MAX_AUTHORED_ROOTS: usize = 64;
        const MAX_PROPOSALS: usize = 128;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }
        let sources: Vec<(TermId, Vec<(String, Sort)>, TermId, Vec<Vec<TermId>>)> = authored
            .iter()
            .filter_map(|&source| {
                let TermData::Not(exists) = self.ctx.terms.get(source) else {
                    return None;
                };
                let TermData::Exists(bindings, body, triggers) = self.ctx.terms.get(*exists) else {
                    return None;
                };
                (!bindings.is_empty()).then_some((
                    source,
                    bindings.clone(),
                    *body,
                    triggers.clone(),
                ))
            })
            .collect();
        let mut proposals = 0usize;
        for (source, bindings, body, triggers) in sources {
            let dual_body = match self.ctx.terms.get(body) {
                TermData::Not(inner) => *inner,
                _ => self.ctx.terms.mk_not_raw(body),
            };
            let dual =
                self.ctx
                    .terms
                    .mk_forall_with_triggers(bindings.clone(), dual_body, triggers);
            let tuples = self.nested_instantiation_tuples(&bindings, &authored);
            for values in tuples {
                proposals += 1;
                if proposals > MAX_PROPOSALS {
                    return;
                }
                let Some(instance) = Self::substitute_bindings_structurally(
                    &mut self.ctx.terms,
                    dual_body,
                    &bindings,
                    &values,
                ) else {
                    continue;
                };
                let mut candidate = Proof::new();
                let source_unit = candidate.add_assume(source, None);
                let not_source = self.ctx.terms.mk_not_raw(source);
                let bridge = candidate.add_theory_lemma_with_kind(
                    "QUANT",
                    vec![not_source, dual],
                    TheoryLemmaKind::QuantifierNegatedExistsDual,
                );
                let dual_unit = candidate.add_resolution(vec![dual], source, bridge, source_unit);
                let instance_unit = self.add_forall_instance_from_unit(
                    &mut candidate,
                    dual,
                    dual_unit,
                    values,
                    instance,
                );
                let Some(candidate) =
                    self.close_authored_ground_unit(candidate, instance, instance_unit, &authored)
                else {
                    continue;
                };
                if self.commit_if_strictly_checked(proof, candidate, &authored) {
                    return;
                }
            }
        }
    }

    /// Rebuild a refutation that needs more than one `forall_inst` step.
    ///
    /// Each candidate begins at an exact authored universal and walks only a
    /// direct nested-universal chain, optionally through one implication whose
    /// antecedent is itself derived from exact authored arithmetic roots. The
    /// final ground literal must have an exact authored complement or form a
    /// checker-replayed arithmetic conflict with authored roots. Enumeration
    /// supplies hints only: the completed empty-clause proof is installed only
    /// through the ordinary authored-scope and strict-checker gate.
    pub(super) fn replace_with_exact_authored_nested_forall_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        const MAX_AUTHORED_ROOTS: usize = 64;
        const MAX_PROPOSALS: usize = 512;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }
        let roots: Vec<TermId> = authored
            .iter()
            .copied()
            .filter_map(|root| {
                if let TermData::Forall(_, body, _) = self.ctx.terms.get(root) {
                    return (Self::nested_forall_path_exists(&self.ctx.terms, *body)
                        || Self::contains_nonlinear_product(&self.ctx.terms, *body))
                    .then_some(root);
                }
                let (_, consequent) = Self::decode_implication_local(&self.ctx.terms, root)?;
                matches!(self.ctx.terms.get(consequent), TermData::Forall(..)).then_some(root)
            })
            .collect();
        let mut proposals = 0usize;
        for root in roots {
            let mut candidate = Proof::new();
            let (quantified, quantified_unit) = if let Some((antecedent, consequent)) =
                Self::decode_implication_local(&self.ctx.terms, root)
            {
                if !matches!(self.ctx.terms.get(consequent), TermData::Forall(..)) {
                    continue;
                }
                let source_unit = candidate.add_assume(root, None);
                let Some(antecedent_unit) =
                    self.add_authored_entailment(&mut candidate, antecedent, &authored)
                else {
                    continue;
                };
                let not_source = self.ctx.terms.mk_not_raw(root);
                let not_antecedent = self.ctx.terms.mk_not_raw(antecedent);
                let implication_clause = candidate.add_rule_step(
                    AletheRule::ImpliesPos,
                    vec![not_source, not_antecedent, consequent],
                    Vec::new(),
                    Vec::new(),
                );
                let open = candidate.add_resolution(
                    vec![not_antecedent, consequent],
                    root,
                    implication_clause,
                    source_unit,
                );
                let unit =
                    candidate.add_resolution(vec![consequent], antecedent, open, antecedent_unit);
                (consequent, Some(unit))
            } else {
                (root, None)
            };
            if let Some(candidate) = self.search_nested_forall_chain(
                &authored,
                quantified,
                quantified_unit,
                candidate,
                0,
                &mut proposals,
            ) {
                if self.commit_if_strictly_checked(proof, candidate, &authored) {
                    return;
                }
            }
            if proposals >= MAX_PROPOSALS {
                return;
            }
        }
    }

    fn nested_forall_path_exists(terms: &TermStore, root: TermId) -> bool {
        match terms.get(root) {
            TermData::Forall(..) => true,
            TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() == 2 => {
                matches!(terms.get(args[1]), TermData::Forall(..))
            }
            TermData::App(Symbol::Named(name), args) if name == "or" && args.len() == 2 => {
                matches!(terms.get(args[0]), TermData::Forall(..))
                    || matches!(terms.get(args[1]), TermData::Forall(..))
            }
            _ => false,
        }
    }

    fn contains_nonlinear_product(terms: &TermStore, root: TermId) -> bool {
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !seen.insert(term) || seen.len() > 20_000 {
                continue;
            }
            match terms.get(term) {
                TermData::App(Symbol::Named(name), _) if name == "*" => return true,
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                TermData::Let(..) => return false,
                _ => {}
            }
        }
        false
    }

    pub(super) fn nested_instantiation_tuples(
        &mut self,
        bindings: &[(String, Sort)],
        authored: &[TermId],
    ) -> Vec<Vec<TermId>> {
        const MAX_VALUES_PER_BINDER: usize = 8;
        const MAX_TUPLES: usize = 128;

        let mut tuples = vec![Vec::new()];
        for (_, sort) in bindings {
            let mut values = Self::ground_instantiation_candidates(
                &self.ctx.terms,
                authored,
                sort,
                MAX_VALUES_PER_BINDER,
            );
            let zero = match sort {
                Sort::Int => Some(self.ctx.terms.mk_int(BigInt::from(0))),
                Sort::Real => Some(
                    self.ctx
                        .terms
                        .mk_rational(num_rational::BigRational::from_integer(BigInt::from(0))),
                ),
                _ => None,
            };
            if let Some(zero) = zero {
                if !values.contains(&zero) {
                    values.push(zero);
                }
            }
            values.dedup();
            values.truncate(MAX_VALUES_PER_BINDER);
            if values.is_empty() {
                return Vec::new();
            }
            let mut next = Vec::new();
            'outer: for prefix in &tuples {
                for &value in &values {
                    let mut tuple = prefix.clone();
                    tuple.push(value);
                    next.push(tuple);
                    if next.len() >= MAX_TUPLES {
                        break 'outer;
                    }
                }
            }
            tuples = next;
        }
        tuples
    }

    pub(super) fn substitute_bindings_structurally(
        terms: &mut TermStore,
        body: TermId,
        bindings: &[(String, Sort)],
        values: &[TermId],
    ) -> Option<TermId> {
        if bindings.is_empty() || bindings.len() != values.len() {
            return None;
        }
        let mut seen = std::collections::HashSet::new();
        if !bindings.iter().all(|(name, _)| seen.insert(name.as_str())) {
            return None;
        }
        let mut instance = body;
        for ((name, sort), &value) in bindings.iter().zip(values) {
            if terms.sort(value) != sort {
                return None;
            }
            instance = Self::substitute_single_binder_structurally(terms, instance, name, value)?;
        }
        Some(instance)
    }

    pub(super) fn add_forall_instance_from_unit(
        &mut self,
        candidate: &mut Proof,
        quantified: TermId,
        quantified_unit: ProofId,
        values: Vec<TermId>,
        instance: TermId,
    ) -> ProofId {
        let not_quantified = self.ctx.terms.mk_not_raw(quantified);
        let implication =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), [not_quantified, instance], Sort::Bool);
        let instantiated = candidate.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            Vec::new(),
            values,
        );
        let clausified = candidate.add_rule_step(
            AletheRule::Or,
            vec![not_quantified, instance],
            vec![instantiated],
            Vec::new(),
        );
        candidate.add_resolution(vec![instance], quantified, clausified, quantified_unit)
    }
}
