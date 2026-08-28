// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Rebuild a bounded composed integer-divisibility contradiction.
    ///
    /// Some linear integer systems are satisfiable over the rationals, so no
    /// Farkas contradiction exists over their original roots. A small integer
    /// combination can nevertheless imply an impossible equality such as
    /// `16*c1 + 16*c2 - 1 = 0`. Derive both orderings of that equality with
    /// ordinary Farkas certificates, combine them with `la_disequality`, then
    /// close against the strict checker's exact GCD/divisibility theorem.
    pub(super) fn replace_with_exact_authored_divisibility_refutation(
        &mut self,
        proof: &mut Proof,
        entry: RepairEntry,
    ) {
        const MAX_EQUALITY_ROOTS: usize = 6;

        if entry == RepairEntry::Check && self.authored_cascade_publishable(proof) {
            return;
        }

        let authored = self.exact_concrete_authored_scope();
        let equality_roots: Vec<(TermId, TermId, TermId)> = authored
            .iter()
            .filter_map(|&root| {
                let (lhs, rhs) = decode_eq_local(&self.ctx.terms, root)?;
                (matches!(self.ctx.terms.sort(lhs), Sort::Int)
                    && matches!(self.ctx.terms.sort(rhs), Sort::Int))
                .then_some((root, lhs, rhs))
            })
            .collect();
        if equality_roots.len() < 2 || equality_roots.len() > MAX_EQUALITY_ROOTS {
            return;
        }

        // Ternary digits select coefficient 0, +1, or -1. The bounded lane is
        // intentionally small; exhausting it leaves the original proof and
        // therefore fails closed at publication.
        let combination_count = 3_usize.pow(equality_roots.len() as u32);
        let mut chosen: Option<(Vec<TermId>, TermId)> = None;
        for mut code in 1..combination_count {
            let mut selected = Vec::new();
            let mut summands = Vec::new();
            for &(root, lhs, rhs) in &equality_roots {
                let digit = code % 3;
                code /= 3;
                let (positive, negative) = match digit {
                    1 => (lhs, rhs),
                    2 => (rhs, lhs),
                    _ => continue,
                };
                selected.push(root);
                summands.push(positive);
                let minus_one = self.ctx.terms.mk_int(BigInt::from(-1));
                let negated =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("*"), [minus_one, negative], Sort::Int);
                summands.push(negated);
            }
            if selected.len() < 2 {
                continue;
            }
            let combined = if summands.len() == 1 {
                summands[0]
            } else {
                self.ctx
                    .terms
                    .mk_app(Symbol::named("+"), summands, Sort::Int)
            };
            let zero = self.ctx.terms.mk_int(BigInt::from(0));
            let equality = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [combined, zero], Sort::Bool);
            let disequality = self.ctx.terms.mk_not_raw(equality);
            if ay_core::proof_validation::recognize_lia_divisibility(
                &self.ctx.terms,
                &[disequality],
            ) {
                chosen = Some((selected, equality));
                break;
            }
        }
        let Some((selected, equality)) = chosen else {
            return;
        };

        fn derive_bound(
            terms: &mut TermStore,
            candidate: &mut Proof,
            roots: &[TermId],
            premise_ids: &[ProofId],
            conclusion: TermId,
        ) -> Option<ProofId> {
            let mut clause: Vec<TermId> =
                roots.iter().map(|&root| terms.mk_not_raw(root)).collect();
            clause.push(conclusion);
            let mut farkas = None;
            let mut inferred = TheoryLemmaKind::Generic;
            if !super::super::proof_farkas::try_lra_farkas_reconstruction(
                terms,
                &clause,
                &mut farkas,
                &mut inferred,
            ) {
                return None;
            }
            let mut current = candidate.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: clause.clone(),
                farkas,
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            });
            let mut residual = clause;
            for (&root, &premise) in roots.iter().zip(premise_ids.iter()) {
                let complement = terms.mk_not_raw(root);
                let position = residual.iter().position(|&lit| lit == complement)?;
                let _ = residual.remove(position);
                current = candidate.add_resolution(residual.clone(), root, current, premise);
            }
            (residual == [conclusion]).then_some(current)
        }

        let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, equality) else {
            return;
        };
        let forward = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [lhs, rhs], Sort::Bool);
        let reverse = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [rhs, lhs], Sort::Bool);
        let mut candidate = Proof::new();
        let premise_ids: Vec<ProofId> = selected
            .iter()
            .map(|&root| candidate.add_assume(root, None))
            .collect();
        let Some(forward_unit) = derive_bound(
            &mut self.ctx.terms,
            &mut candidate,
            &selected,
            &premise_ids,
            forward,
        ) else {
            return;
        };
        let Some(reverse_unit) = derive_bound(
            &mut self.ctx.terms,
            &mut candidate,
            &selected,
            &premise_ids,
            reverse,
        ) else {
            return;
        };

        let not_forward = self.ctx.terms.mk_not_raw(forward);
        let not_reverse = self.ctx.terms.mk_not_raw(reverse);
        let split = self.ctx.terms.mk_app(
            Symbol::named("or"),
            [equality, not_forward, not_reverse],
            Sort::Bool,
        );
        let split_unit = candidate.add_rule_step(
            AletheRule::LaDisequality,
            vec![split],
            Vec::new(),
            Vec::new(),
        );
        let split_clause = candidate.add_rule_step(
            AletheRule::Or,
            vec![equality, not_forward, not_reverse],
            vec![split_unit],
            Vec::new(),
        );
        let forward_resolved = candidate.add_resolution(
            vec![equality, not_reverse],
            forward,
            split_clause,
            forward_unit,
        );
        let equality_unit =
            candidate.add_resolution(vec![equality], reverse, forward_resolved, reverse_unit);
        let disequality = self.ctx.terms.mk_not_raw(equality);
        let divisibility = candidate.add_step(ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![disequality],
            farkas: Some(FarkasAnnotation::new(vec![num_rational::Rational64::from(
                1,
            )])),
            kind: TheoryLemmaKind::LiaGeneric,
            lia: Some(ay_core::LiaAnnotation::Divisibility),
        });
        candidate.add_resolution(Vec::new(), equality, equality_unit, divisibility);

        if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok()
            && Self::proof_derives_empty_clause(&candidate)
            && self.check_proof_strict_with_datatypes(&candidate).is_ok()
        {
            // Keep source spellings only where the problem checker needs
            // them: the exact authored assumptions. Every synthesized
            // arithmetic term must reach the external checker in the same
            // canonical spelling the native witness validated.
            self.purge_surface_overrides_for_certified_proof(&candidate);
            *proof = candidate;
        }
    }
}
