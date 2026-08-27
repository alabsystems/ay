// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Original-disjunction and substituted-equality unit repair.

use super::*;

impl Executor {
    /// Recognize a preprocessor-derived unit trust step `(cl L)`: an
    /// original disjunctive assertion contains `L`, and every OTHER disjunct
    /// is the syntactic complement of another original assertion (so plain
    /// resolutions against their assumes derive the unit). Fail-closed: the
    /// disjunct atoms must be pairwise distinct (unambiguous pivots) with
    /// `L` among them exactly once.
    pub(super) fn plan_or_unit(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<OrUnitPlan> {
        if clause.len() != 1 {
            return None;
        }
        let lit = clause[0];
        'orig: for (orig, parsed) in originals {
            if !planning.spend_work(1) {
                return None;
            }
            let orig = *orig;
            if !source_index.contains(orig) {
                continue;
            }
            let TermData::App(Symbol::Named(op), ds) = self.ctx.terms.get(orig) else {
                continue;
            };
            if op != "or"
                || ds.len() < 2
                || ds.len() > MAX_PROVENANCE_REPAIR_TERMS
                || !ds.contains(&lit)
            {
                continue;
            }
            if !planning.spend_surface(orig, parsed)
                || !planning.spend_terms(&self.ctx.terms, &[orig])
            {
                return None;
            }
            let disjuncts = ds.clone();
            if !surface_or_decomposition_matches(&mut self.ctx, parsed, &disjuncts) {
                continue;
            }
            let mut atoms: Vec<TermId> = disjuncts
                .iter()
                .map(|&d| atom_of(&self.ctx.terms, d))
                .collect();
            atoms.sort_unstable();
            atoms.dedup();
            if atoms.len() != disjuncts.len() {
                continue;
            }
            let mut eliminations: Vec<(TermId, TermId)> = Vec::new();
            for &d in &disjuncts {
                if d == lit {
                    continue;
                }
                let comp = complement_of(&mut self.ctx.terms, d);
                if !source_index.contains(comp) {
                    continue 'orig;
                }
                eliminations.push((atom_of(&self.ctx.terms, d), comp));
            }
            return Some(OrUnitPlan {
                orig,
                disjuncts,
                eliminations,
            });
        }
        None
    }

    /// Recognize a PREPROCESSING-COLLAPSE equality unit `(cl (= L R))` and
    /// plan its re-derivation from the problem's ORIGINAL equality assertions
    /// (see [`SubstEqPlan`]).
    ///
    /// The substitute-and-simplify preprocessor eliminates a defined constant
    /// (`(assert (= v0 t))` -> `v0 := t`), so the assertions that justify the
    /// equality never reach the exported proof as `assume` steps and the
    /// equality itself is exported as a premiseless `trust` unit. Every
    /// premise the repair introduces is an assertion of the input file, and
    /// the derivation is the existing EUF toolkit's `eq_transitive` /
    /// `eq_congruent` recipe plus one resolution per re-introduced premise —
    /// no invented premise, no weakened clause.
    ///
    /// Fail-closed: the conclusion must be a binary equality, the hypotheses
    /// must be top-level positive binary-equality ORIGINALS, and the whole
    /// derivation must be plannable by [`Self::plan_euf_lemma`], which only
    /// admits a conclusion its own congruence closure actually entails.
    pub(super) fn plan_substituted_equality(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<SubstEqPlan> {
        if clause.len() != 1 {
            return None;
        }
        let target = clause[0];
        let (lhs, rhs) = decode_binary_equality(&self.ctx.terms, target)?;
        if lhs == rhs {
            // A reflexive conclusion needs no premise at all; that is a
            // different (and unobserved) shape. Decline.
            return None;
        }
        // Hypothesis candidates: the problem's own top-level positive binary
        // equalities, deduplicated so one assertion cannot supply two clause
        // literals (the EUF planner rejects duplicated literals anyway).
        let mut hyps: Vec<TermId> = Vec::new();
        let mut seen = HashSet::default();
        for (canonical, parsed) in originals {
            if !planning.spend_work(1) {
                return None;
            }
            if *canonical == target
                || !source_index.contains(*canonical)
                || !seen.insert(*canonical)
            {
                continue;
            }
            let Some((a, b)) = decode_binary_equality(&self.ctx.terms, *canonical) else {
                continue;
            };
            if a == b {
                continue;
            }
            if !planning.spend_surface(*canonical, parsed)
                || !planning.spend_terms(&self.ctx.terms, &[*canonical])
            {
                return None;
            }
            if !self.surface_equality_source_is_print_faithful(*canonical, parsed) {
                continue;
            }
            if hyps.len() >= MAX_PROVENANCE_REPAIR_TERMS {
                return None;
            }
            hyps.push(*canonical);
        }
        if hyps.is_empty() {
            return None;
        }
        let plan = self.plan_substituted_equality_over(target, &hyps, planning)?;
        // Second pass over only the hypotheses the recipe actually used: it
        // keeps the emitted lemma minimal (no `weakening` over unrelated
        // assertions) and avoids re-introducing assumes the derivation never
        // reads. Falls back to the full-hypothesis plan if the narrowed set
        // no longer entails the conclusion.
        let EufTarget::Bare { extras } = &plan.euf.target else {
            return Some(plan);
        };
        if extras.is_empty() {
            return Some(plan);
        }
        let used: Vec<TermId> = plan
            .hyps
            .iter()
            .copied()
            .zip(plan.lemma[1..].iter())
            .filter(|(_, neg)| !extras.contains(neg))
            .map(|(h, _)| h)
            .collect();
        if used.is_empty() || used.len() == plan.hyps.len() {
            return Some(plan);
        }
        Some(
            self.plan_substituted_equality_over(target, &used, planning)
                .unwrap_or(plan),
        )
    }

    /// Plan `(cl target)` against exactly `hyps`: synthesize the lemma clause
    /// `[target, (not h1), .., (not hk)]` and hand it to the EUF planner.
    fn plan_substituted_equality_over(
        &mut self,
        target: TermId,
        hyps: &[TermId],
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<SubstEqPlan> {
        let mut lemma = Vec::with_capacity(hyps.len() + 1);
        lemma.push(target);
        for &h in hyps {
            let neg = self.ctx.terms.mk_not_raw(h);
            // `mk_not_raw` must give back a literal negation: a folded result
            // would make the resolution pivots disagree with the lemma.
            if atom_of(&self.ctx.terms, neg) != h || neg == h {
                return None;
            }
            if lemma.contains(&neg) {
                return None;
            }
            lemma.push(neg);
        }
        let euf = self.plan_euf_lemma_with_budget(&lemma, planning)?;
        // Only the bare (flat-clause) target reproduces the synthesized clause
        // literal-for-literal; an `OrUnit` plan would derive a different term.
        if !matches!(euf.target, EufTarget::Bare { .. }) {
            return None;
        }
        Some(SubstEqPlan {
            lemma,
            hyps: hyps.to_vec(),
            euf,
        })
    }

    /// Emit a [`SubstEqPlan`]'s derivation, returning the id of the derived
    /// unit `(cl (= L R))`. `assume_of` must resolve every hypothesis to its
    /// hoisted `assume` step.
    pub(super) fn emit_substituted_equality(
        &mut self,
        new_proof: &mut Proof,
        plan: &SubstEqPlan,
        assume_of: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let mut cur = self.emit_euf_lemma(new_proof, &plan.euf);
        let mut remaining: Vec<TermId> = plan.lemma.clone();
        for (i, &h) in plan.hyps.iter().enumerate() {
            let assume_id = *assume_of.get(&h)?;
            let neg = plan.lemma[i + 1];
            remaining.retain(|&l| l != neg);
            cur = new_proof.add_resolution(remaining.clone(), h, cur, assume_id);
        }
        (remaining == vec![plan.lemma[0]]).then_some(cur)
    }
}
