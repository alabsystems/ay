// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authenticated implication/or planning and emission.

use super::*;

impl Executor {
    /// Recognize a singleton trust clause as the packed canonical `or` of an
    /// exact authored right-associated implication chain.
    ///
    /// Authority comes from the immutable `(canonical, parsed)` original pair.
    /// The canonical half is the exact internal premise; the parsed half must
    /// still be a right-associated implication chain of the same width.  This
    /// separation is intentional: the strict checker sees the canonical
    /// packed `or`, while the Alethe printer replays its decomposition through
    /// `implies_pos` so the external premise retains the authored spelling.
    /// Only an exact comparison dual may differ between source and target, and
    /// that two-literal bridge is independently Farkas-validated.
    pub(super) fn plan_normalized_authored_or(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
    ) -> Option<NormalizedAuthoredOrPlan> {
        let [target_or] = clause else {
            return None;
        };
        let target_or = *target_or;
        let TermData::App(Symbol::Named(op), target_disjuncts) = self.ctx.terms.get(target_or)
        else {
            return None;
        };
        if op != "or" || target_disjuncts.len() < 2 {
            return None;
        }
        let target_disjuncts = target_disjuncts.clone();
        if !matches!(self.ctx.terms.sort(target_or), Sort::Bool)
            || target_disjuncts
                .iter()
                .any(|&term| !matches!(self.ctx.terms.sort(term), Sort::Bool))
        {
            return None;
        }
        let mut distinct = target_disjuncts.clone();
        distinct.sort_unstable();
        distinct.dedup();
        if distinct.len() != target_disjuncts.len() {
            return None;
        }

        // Removing the target's whole-term surface override is necessary for
        // the derived packed `or` to print as an `or`.  Never do that when the
        // same term is itself an authored premise: a shared TermId would make
        // the surviving assume print differently from the input assertion.
        if originals
            .iter()
            .any(|(canonical, _)| *canonical == target_or)
        {
            return None;
        }

        for (source_or, parsed) in originals {
            // Re-authenticate the pair locally.  The caller already assembled
            // it from the immutable parsed/original stacks, but this check
            // prevents a forged `(TermId, surface)` tuple from granting premise
            // authority to the plan.
            if self.ctx.elaborate_surface_subterm(parsed) != Some(*source_or) {
                continue;
            }
            let Some(plan) = self.plan_normalized_authored_or_from_source(
                *source_or,
                target_or,
                &target_disjuncts,
                parsed,
            ) else {
                continue;
            };
            return Some(plan);
        }
        None
    }

    fn plan_normalized_authored_or_from_source(
        &mut self,
        source_or: TermId,
        target_or: TermId,
        target_disjuncts: &[TermId],
        parsed: &FrontendTerm,
    ) -> Option<NormalizedAuthoredOrPlan> {
        if source_or == target_or {
            return None;
        }

        let TermData::App(Symbol::Named(source_op), source_disjuncts) =
            self.ctx.terms.get(source_or)
        else {
            return None;
        };
        if source_op != "or" || source_disjuncts.len() != target_disjuncts.len() {
            return None;
        }
        let source_disjuncts = source_disjuncts.clone();
        if source_disjuncts.len() < 2
            || !matches!(self.ctx.terms.sort(source_or), Sort::Bool)
            || source_disjuncts
                .iter()
                .any(|&term| !matches!(self.ctx.terms.sort(term), Sort::Bool))
        {
            return None;
        }
        let mut distinct_source = source_disjuncts.clone();
        distinct_source.sort_unstable();
        distinct_source.dedup();
        if distinct_source.len() != source_disjuncts.len() {
            return None;
        }

        // Retain the source-language guard: an arbitrary authored `or` with
        // the same canonical term must not enter the implication-specific
        // printer bridge.  The final consequent accounts for the last
        // disjunct, hence links + 1 must equal the flat canonical width.
        let mut current_surface = strip_frontend_annotations(parsed);
        let mut implication_links = 0usize;
        while let FrontendTerm::App(head, operands) = current_surface {
            if head != "=>" || operands.len() != 2 {
                break;
            }
            implication_links = implication_links.checked_add(1)?;
            current_surface = strip_frontend_annotations(&operands[1]);
        }
        if implication_links == 0 || implication_links + 1 != source_disjuncts.len() {
            return None;
        }

        let mut used_target = vec![false; target_disjuncts.len()];
        let mut aligned: Vec<Option<(TermId, Option<TermId>)>> = vec![None; source_disjuncts.len()];

        // Exact identities always win.  Doing this as a separate pass prevents
        // an earlier arithmetic literal from consuming a target that a later
        // source literal shares exactly.
        for (source_position, &source) in source_disjuncts.iter().enumerate() {
            if let Some(position) = target_disjuncts
                .iter()
                .enumerate()
                .position(|(position, &target)| !used_target[position] && target == source)
            {
                used_target[position] = true;
                aligned[source_position] = Some((source, None));
            }
        }

        // The sole non-exact alignment is an exact syntactic comparison dual
        // (`not (< a b)` versus `(<= b a)`, and the seven polarity/head
        // variants).  No general arithmetic-equivalence search is admitted.
        for (source_position, &source) in source_disjuncts.iter().enumerate() {
            if aligned[source_position].is_some() {
                continue;
            }
            let mut bridged = None;
            for (position, &target) in target_disjuncts.iter().enumerate() {
                if used_target[position] {
                    continue;
                }
                let Some(bridge_atom) = self.comparison_dual_source_literal(source, target) else {
                    continue;
                };
                bridged = Some((position, target, bridge_atom));
                break;
            }
            let (position, canonical, bridge_atom) = bridged?;
            used_target[position] = true;
            aligned[source_position] = Some((canonical, Some(bridge_atom)));
        }
        if used_target.iter().any(|used| !*used) {
            return None;
        }
        let literals: Option<Vec<NormalizedAuthoredOrLiteral>> = source_disjuncts
            .iter()
            .copied()
            .zip(aligned)
            .map(|(source, alignment)| {
                alignment.map(|(canonical, bridge_atom)| NormalizedAuthoredOrLiteral {
                    source,
                    canonical,
                    bridge_atom,
                })
            })
            .collect();

        Some(NormalizedAuthoredOrPlan {
            source_or,
            source_disjuncts,
            target_or,
            target_disjuncts: target_disjuncts.to_vec(),
            literals: literals?,
        })
    }

    /// Emit a [`NormalizedAuthoredOrPlan`], returning the exact singleton
    /// `(cl target_or)` unit consumed by the old trust step's users.
    pub(super) fn emit_normalized_authored_or(
        &mut self,
        new_proof: &mut Proof,
        plan: &NormalizedAuthoredOrPlan,
        source_assume: ProofId,
    ) -> Option<ProofId> {
        let mut clause = plan.source_disjuncts.clone();
        let mut current = new_proof.add_rule_step(
            AletheRule::Or,
            clause.clone(),
            vec![source_assume],
            Vec::new(),
        );

        // Normalize only the comparison literals whose pair certificates were
        // independently checked during planning.
        for literal in &plan.literals {
            let Some(bridge_atom) = literal.bridge_atom else {
                continue;
            };
            let position = clause.iter().position(|&term| term == literal.source)?;
            let _ = clause.remove(position);
            if !clause.contains(&literal.canonical) {
                clause.push(literal.canonical);
            }
            let source_complement = complement_of(&mut self.ctx.terms, literal.source);
            let bridge = Self::add_pair_lemma(new_proof, literal.canonical, source_complement);
            current = new_proof.add_resolution(clause.clone(), bridge_atom, current, bridge);
        }
        if clause.len() != plan.target_disjuncts.len()
            || clause
                .iter()
                .any(|term| !plan.target_disjuncts.contains(term))
        {
            return None;
        }

        // Pack the exact flat clause back into the singleton or-term.  This is
        // the same checked `or_neg` + contraction recipe used by the existing
        // or-wrapped EUF tautology emitter.
        for &disjunct in &plan.target_disjuncts {
            let position = clause.iter().position(|&term| term == disjunct)?;
            let _ = clause.remove(position);
            let not_disjunct = self.ctx.terms.mk_not_raw(disjunct);
            let or_neg = new_proof.add_rule_step(
                AletheRule::OrNeg,
                vec![plan.target_or, not_disjunct],
                Vec::new(),
                Vec::new(),
            );
            clause.push(plan.target_or);
            current = new_proof.add_resolution(clause.clone(), disjunct, current, or_neg);
        }
        let unit = new_proof.add_rule_step(
            AletheRule::Contraction,
            vec![plan.target_or],
            vec![current],
            Vec::new(),
        );
        Some(unit)
    }
}
