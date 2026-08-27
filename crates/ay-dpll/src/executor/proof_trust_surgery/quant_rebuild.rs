// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Validated quantified-instance planning and emission.

use super::*;

impl Executor {
    /// Whether `(cl (not a1) .. (not an) concl)` is a valid all-ones
    /// `la_generic` lemma per the independent LINEAR Farkas checker (the
    /// antecedent literals asserted true, the conclusion asserted false).
    /// `_linear`, not `_full`: the lemma exports as `la_generic` and
    /// external checkers perform no congruence reasoning inside it.
    pub(super) fn quant_lemma_valid(&self, antecedents: &[TermId], conclusion: TermId) -> bool {
        let mut lits: Vec<TheoryLit> = antecedents
            .iter()
            .map(|&l| match self.ctx.terms.get(l) {
                TermData::Not(inner) => TheoryLit::new(*inner, false),
                _ => TheoryLit::new(l, true),
            })
            .collect();
        lits.push(match self.ctx.terms.get(conclusion) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(conclusion, false),
        });
        #[allow(clippy::cast_possible_truncation)]
        let coeffs = vec![1i64; lits.len()];
        ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &lits,
            &FarkasAnnotation::from_ints(&coeffs),
        )
        .is_ok()
    }

    /// Whether the asserted arithmetic literals are jointly infeasible under
    /// an all-ones Farkas combination.  This is the no-conclusion sibling of
    /// [`Self::quant_lemma_valid`], used when an E-matching instance and an
    /// authored equality directly contradict one another.
    pub(super) fn quant_conflict_valid(&self, antecedents: &[TermId]) -> bool {
        if antecedents.is_empty() {
            return false;
        }
        let lits: Vec<TheoryLit> = antecedents
            .iter()
            .map(|&literal| match self.ctx.terms.get(literal) {
                TermData::Not(inner) => TheoryLit::new(*inner, false),
                _ => TheoryLit::new(literal, true),
            })
            .collect();
        #[allow(clippy::cast_possible_truncation)]
        let coeffs = vec![1i64; lits.len()];
        ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &lits,
            &FarkasAnnotation::from_ints(&coeffs),
        )
        .is_ok()
    }

    /// Whether the unit clause `(cl atom)` is a ground arithmetic tautology
    /// per the independent Farkas checker (its negation is infeasible on its
    /// own — e.g. the instantiated guard bound `(<= 0 24)`).
    fn ground_arith_unit_valid(&self, atom: TermId) -> bool {
        let lit = match self.ctx.terms.get(atom) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(atom, false),
        };
        ay_core::proof_validation::verify_farkas_conflict_lits_full(
            &self.ctx.terms,
            &[lit],
            &FarkasAnnotation::from_ints(&[1]),
        )
        .is_ok()
    }

    /// Emit a `[1]` `la_generic` unit lemma `(cl atom)`. Only called for
    /// atoms already validated by [`Self::ground_arith_unit_valid`].
    fn add_unit_lemma(new_proof: &mut Proof, atom: TermId) -> ProofId {
        new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![atom],
            farkas: Some(FarkasAnnotation::from_ints(&[1])),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Build the certified derivation chain from the parsed `forall` premise
    /// to the unit `(cl target)` at binder values `values`
    /// (#quant-expansion-proof). Every ingredient is validated here, at plan
    /// time; emission ([`Self::emit_quant_instance_chain`]) is mechanical.
    /// Fail-closed `None` on: binder/value arity or sort mismatch, a body
    /// with any nested binding construct, a guard that is not a conjunction
    /// of distinct positive ground arithmetic truths, or a consequent that
    /// neither equals `target` nor bridges to it by a re-verified `[1, 1]`
    /// `la_generic` lemma.
    pub(super) fn build_quant_instance_chain(
        &mut self,
        parsed_forall: &FrontendTerm,
        values: &[TermId],
        target: TermId,
    ) -> Option<QuantInstanceChain> {
        if !surface_source_is_bounded(parsed_forall) {
            return None;
        }
        let stripped = strip_frontend_annotations(parsed_forall);
        let FrontendTerm::Forall(binders, body) = stripped else {
            return None;
        };
        if binders.len() != values.len() {
            return None;
        }
        let mut subst: HashMap<String, FrontendTerm> = HashMap::default();
        for ((name, _), &value) in binders.iter().zip(values.iter()) {
            subst.insert(name.clone(), value_to_surface(&self.ctx.terms, value)?);
        }
        let substituted = surface_subst_ground(body.as_ref(), &subst)?;
        let phi = self.raw_intern_surface(&substituted)?;
        let (guard, body_lit) = match &substituted {
            FrontendTerm::App(op, operands) if op == "=>" && operands.len() == 2 => {
                let guard_term = self.raw_intern_surface(&operands[0])?;
                let body_lit = self.raw_intern_surface(&operands[1])?;
                let atoms: Vec<TermId> = match strip_frontend_annotations(&operands[0]) {
                    FrontendTerm::App(gop, gargs) if gop == "and" && !gargs.is_empty() => gargs
                        .iter()
                        .map(|g| self.raw_intern_surface(g))
                        .collect::<Option<Vec<_>>>()?,
                    _ => vec![guard_term],
                };
                // Distinct positive atoms keep the and_neg resolution chain
                // unambiguous (a duplicated pivot would remove the wrong
                // number of literals; a negated conjunct would double-negate
                // in the and_neg clause).
                let mut seen = atoms.clone();
                seen.sort_unstable();
                seen.dedup();
                if seen.len() != atoms.len()
                    || atoms
                        .iter()
                        .any(|&a| matches!(self.ctx.terms.get(a), TermData::Not(_)))
                {
                    return None;
                }
                for &atom in &atoms {
                    if !self.ground_arith_unit_valid(atom) {
                        return None;
                    }
                }
                (Some((guard_term, atoms)), body_lit)
            }
            _ => (None, phi),
        };
        if body_lit != target {
            let body_complement = complement_of(&mut self.ctx.terms, body_lit);
            if !self.pair_lemma_valid(target, body_complement) {
                return None;
            }
        }
        Some(QuantInstanceChain {
            values: values.to_vec(),
            phi,
            guard,
            body_lit,
            target,
        })
    }

    /// Build an exact, unguarded direct-forall instance chain from either a
    /// parsed SMT-LIB forall or the native API's surface-placeholder.  The API
    /// path independently recomputes simultaneous substitution on the
    /// canonical authored term; it accepts only byte-identical ground bodies.
    pub(super) fn build_direct_ematching_instance_chain(
        &mut self,
        forall_term: TermId,
        parsed: &FrontendTerm,
        values: &[TermId],
        instance: TermId,
    ) -> Option<QuantInstanceChain> {
        if !surface_source_is_bounded(parsed) {
            return None;
        }
        if matches!(
            strip_frontend_annotations(parsed),
            FrontendTerm::Symbol(name) if name == NATIVE_API_ASSERTION_PLACEHOLDER
        ) {
            let (body, substitution) = {
                let TermData::Forall(bindings, body, _) = self.ctx.terms.get(forall_term) else {
                    return None;
                };
                if bindings.is_empty()
                    || bindings.len() != values.len()
                    || bindings.len() > MAX_PROVENANCE_REPAIR_TERMS
                {
                    return None;
                }
                let binder_bytes = bindings
                    .iter()
                    .try_fold(0usize, |bytes, (name, _)| bytes.checked_add(name.len()))?;
                if binder_bytes > 64 * 1024
                    || quant_canonical_term_work(&self.ctx.terms, *body).is_none()
                {
                    return None;
                }
                let mut substitution = HashMap::default();
                for ((name, sort), &value) in bindings.iter().zip(values) {
                    if self.ctx.terms.sort(value) != sort {
                        return None;
                    }
                    substitution.insert(name.clone(), value);
                }
                (*body, substitution)
            };
            let phi = crate::ematching::subst_vars(&mut self.ctx.terms, body, &substitution);
            if phi != instance {
                return None;
            }
            return Some(QuantInstanceChain {
                values: values.to_vec(),
                phi,
                guard: None,
                body_lit: phi,
                target: phi,
            });
        }

        let chain = self.build_quant_instance_chain(parsed, values, instance)?;
        // The negative-forall proof consumes the RAW surface instance
        // (`chain.phi`) directly in an arithmetic conflict. A comparison may
        // have a different canonical orientation than `instance`; the builder
        // above independently validated that bridge. Guard discharge, however,
        // would require the forall as a premise and would be circular here.
        chain.guard.is_none().then_some(chain)
    }

    /// Rebuild the exact authored surface forall around a raw ground instance.
    /// The returned quantifier is alpha-fresh but structurally faithful to the
    /// parsed source, so both AY's exact-substitution checker and an external
    /// Alethe checker see the same `forall_inst` body.
    pub(super) fn build_raw_ematching_forall_source(
        &mut self,
        canonical_forall: TermId,
        parsed: &FrontendTerm,
        values: &[TermId],
        ground_instance: TermId,
    ) -> Option<TermId> {
        if !surface_source_is_bounded(parsed) {
            return None;
        }
        if matches!(
            strip_frontend_annotations(parsed),
            FrontendTerm::Symbol(name) if name == NATIVE_API_ASSERTION_PLACEHOLDER
        ) {
            return Some(canonical_forall);
        }

        let FrontendTerm::Forall(parsed_bindings, parsed_body) = strip_frontend_annotations(parsed)
        else {
            return None;
        };
        let TermData::Forall(canonical_bindings, _, _) =
            self.ctx.terms.get(canonical_forall).clone()
        else {
            return None;
        };
        if parsed_bindings.is_empty()
            || parsed_bindings.len() != canonical_bindings.len()
            || parsed_bindings.len() != values.len()
        {
            return None;
        }

        let mut ground_substitution: HashMap<String, FrontendTerm> = HashMap::default();
        let mut bound_vars: HashMap<String, TermId> = HashMap::default();
        let mut raw_bindings = Vec::with_capacity(parsed_bindings.len());
        for (((parsed_name, _), (_, canonical_sort)), &value) in parsed_bindings
            .iter()
            .zip(canonical_bindings.iter())
            .zip(values)
        {
            if bound_vars.contains_key(parsed_name) || self.ctx.terms.sort(value) != canonical_sort
            {
                return None;
            }
            ground_substitution.insert(
                parsed_name.clone(),
                value_to_surface(&self.ctx.terms, value)?,
            );
            let variable = self
                .ctx
                .terms
                .mk_var(parsed_name.clone(), canonical_sort.clone());
            bound_vars.insert(parsed_name.clone(), variable);
            raw_bindings.push((parsed_name.clone(), canonical_sort.clone()));
        }

        let substituted = surface_subst_ground(parsed_body.as_ref(), &ground_substitution)?;
        let rebuilt_ground = self.raw_intern_surface(&substituted)?;
        if rebuilt_ground != ground_instance {
            return None;
        }
        let raw_body = lift_surface_binders_from_ground(
            &mut self.ctx.terms,
            parsed_body.as_ref(),
            &substituted,
            ground_instance,
            &bound_vars,
        )?;
        if self.ctx.terms.sort(raw_body) != &Sort::Bool {
            return None;
        }
        let raw_forall = self.ctx.terms.mk_forall(raw_bindings, raw_body);

        let exact_substitution: HashMap<String, TermId> = parsed_bindings
            .iter()
            .map(|(name, _)| name.clone())
            .zip(values.iter().copied())
            .collect();
        if !raw_instance_matches_substitution(
            &self.ctx.terms,
            raw_body,
            ground_instance,
            &exact_substitution,
        ) {
            return None;
        }
        Some(raw_forall)
    }

    /// Emit a plan-time-validated negative-forall derivation.  The forall is
    /// used only by the premiseless `forall_inst` rule; support assumptions
    /// close the checked arithmetic conflict to `(not instance)`, which then
    /// resolves the instantiation clause to `(not forall)`.
    pub(super) fn emit_ematching_quant_negation(
        &mut self,
        new_proof: &mut Proof,
        plan: &QuantNegationPlan,
        lift_assume: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let not_forall = self.ctx.terms.mk_not_raw(plan.forall_term);
        let inst_or = self.ctx.terms.mk_app(
            Symbol::named("or"),
            [not_forall, plan.chain.phi],
            Sort::Bool,
        );
        let forall_inst = new_proof.add_rule_step(
            AletheRule::ForallInst,
            vec![inst_or],
            Vec::new(),
            plan.chain.values.clone(),
        );
        let inst_clause = new_proof.add_rule_step(
            AletheRule::Or,
            vec![not_forall, plan.chain.phi],
            vec![forall_inst],
            Vec::new(),
        );

        #[allow(clippy::cast_possible_truncation)]
        let coeffs = vec![1i64; plan.lemma.len()];
        let mut conflict = new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: plan.lemma.clone(),
            farkas: Some(FarkasAnnotation::from_ints(&coeffs)),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        let mut remaining = plan.lemma.clone();
        for &support in &plan.supports {
            let support_id = *lift_assume.get(&support)?;
            let complement = complement_of(&mut self.ctx.terms, support);
            let position = remaining.iter().position(|&term| term == complement)?;
            let _ = remaining.remove(position);
            conflict = new_proof.add_resolution(
                remaining.clone(),
                atom_of(&self.ctx.terms, support),
                conflict,
                support_id,
            );
        }
        if remaining.len() != 1
            || remaining[0] != complement_of(&mut self.ctx.terms, plan.chain.phi)
        {
            return None;
        }
        Some(new_proof.add_resolution(
            vec![not_forall],
            atom_of(&self.ctx.terms, plan.chain.phi),
            inst_clause,
            conflict,
        ))
    }

    /// Emit the plan-time-validated instance derivation
    /// (#quant-expansion-proof): `forall_inst` (positional binder-value
    /// args) + `or` + resolution against the forall's assume yields the raw
    /// substituted body; `implies_pos` + per-atom `[1]` `la_generic` guard
    /// units + `and_neg` discharge the instantiated guard; the optional
    /// re-verified `[1, 1]` bridge lands on the canonical target unit.
    pub(super) fn emit_quant_instance_chain(
        &mut self,
        new_proof: &mut Proof,
        forall_term: TermId,
        assume_id: ProofId,
        chain: &QuantInstanceChain,
    ) -> ProofId {
        let not_forall = self.ctx.terms.mk_not_raw(forall_term);
        let inst_or =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), [not_forall, chain.phi], Sort::Bool);
        let fi = new_proof.add_rule_step(
            AletheRule::ForallInst,
            vec![inst_or],
            Vec::new(),
            chain.values.clone(),
        );
        let or_step = new_proof.add_rule_step(
            AletheRule::Or,
            vec![not_forall, chain.phi],
            vec![fi],
            Vec::new(),
        );
        let phi_unit = new_proof.add_resolution(vec![chain.phi], forall_term, or_step, assume_id);
        let body_unit = match &chain.guard {
            None => phi_unit,
            Some((guard_term, atoms)) => {
                let (guard_term, atoms) = (*guard_term, atoms.clone());
                let not_phi = self.ctx.terms.mk_not_raw(chain.phi);
                let not_guard = self.ctx.terms.mk_not_raw(guard_term);
                let ip = new_proof.add_rule_step(
                    AletheRule::ImpliesPos,
                    vec![not_phi, not_guard, chain.body_lit],
                    Vec::new(),
                    Vec::new(),
                );
                let guard_unit = if atoms.len() == 1 && atoms[0] == guard_term {
                    Self::add_unit_lemma(new_proof, guard_term)
                } else {
                    let not_atoms: Vec<TermId> = atoms
                        .iter()
                        .map(|&a| self.ctx.terms.mk_not_raw(a))
                        .collect();
                    let mut working = vec![guard_term];
                    working.extend(not_atoms.iter().copied());
                    let mut cur = new_proof.add_rule_step(
                        AletheRule::AndNeg,
                        working.clone(),
                        Vec::new(),
                        Vec::new(),
                    );
                    for (&atom, &not_atom) in atoms.iter().zip(not_atoms.iter()) {
                        let unit = Self::add_unit_lemma(new_proof, atom);
                        if let Some(p) = working.iter().position(|&l| l == not_atom) {
                            let _ = working.remove(p);
                        }
                        cur = new_proof.add_resolution(working.clone(), atom, cur, unit);
                    }
                    cur
                };
                let r1 = new_proof.add_resolution(
                    vec![not_guard, chain.body_lit],
                    chain.phi,
                    ip,
                    phi_unit,
                );
                new_proof.add_resolution(vec![chain.body_lit], guard_term, r1, guard_unit)
            }
        };
        if chain.target == chain.body_lit {
            body_unit
        } else {
            let body_pivot = atom_of(&self.ctx.terms, chain.body_lit);
            let body_complement = complement_of(&mut self.ctx.terms, chain.body_lit);
            let lemma = Self::add_pair_lemma(new_proof, chain.target, body_complement);
            new_proof.add_resolution(vec![chain.target], body_pivot, lemma, body_unit)
        }
    }
}
