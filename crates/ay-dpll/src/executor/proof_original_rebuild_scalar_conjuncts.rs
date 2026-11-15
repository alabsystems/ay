// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recover scalar consequences of mixed-theory positive conjunctions.
//!
//! Every selected leaf is DERIVED from an unchanged authored root. No leaf
//! becomes an assumption, and neither disjunction nor negation is split.

use super::*;

impl Executor {
    pub(super) fn build_authenticated_scalar_conjunct_refutation(
        &mut self,
        authenticated_scope: &[TermId],
    ) -> Option<Proof> {
        let mut candidate = Proof::new();
        let mut pending = Vec::new();
        let mut remaining = ay_proof::MAX_BV_LIA_QUERY_ROOTS;
        for &root in authenticated_scope {
            remaining = remaining.checked_sub(1)?;
            if self.ctx.terms.entry_stamp(root).is_none()
                || self.ctx.terms.sort(root) != &Sort::Bool
            {
                return None;
            }
            pending.push((root, candidate.add_assume(root, None)));
        }
        let mut seen = HashSet::default();
        let mut scalar = Vec::new();
        let mut projected = false;
        while let Some((term, unit)) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            if self.should_abort_theory_loop() {
                return None;
            }
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) {
                if name == "and" && !args.is_empty() {
                    // Bound all pending work before allocating or deriving it.
                    // This reuses the existing root ceiling, never widens it.
                    remaining = remaining.checked_sub(args.len())?;
                    let children = args.clone();
                    let not_parent = self.ctx.terms.mk_not_raw(term);
                    for (index, child) in children.into_iter().enumerate() {
                        let position = u32::try_from(index).ok()?;
                        let projection = candidate.add_rule_step(
                            AletheRule::AndPos(position),
                            vec![not_parent, child],
                            Vec::new(),
                            vec![term],
                        );
                        let derived = candidate.add_resolution(vec![child], term, projection, unit);
                        pending.push((child, derived));
                    }
                    projected = true;
                    continue;
                }
            }
            if !matches!(
                self.ctx.terms.get(term),
                TermData::Const(Constant::Bool(true))
            ) && bv_lia_scalar_sorted_root(&self.ctx.terms, term)
            {
                scalar.push((term, unit));
            }
        }
        if !projected || scalar.is_empty() {
            return None;
        }
        let roots: Vec<TermId> = scalar.iter().map(|&(term, _)| term).collect();
        // A subset is useful only if the unchanged checker proves that exact
        // subset UNSAT. A satisfiable or unsupported subset grants nothing.
        ay_proof::authenticate_bv_lia_unsat_query(
            &self.ctx.terms,
            &roots,
            self.current_solve_deadline(),
        )
        .ok()?;
        let mut residual: Vec<TermId> = roots
            .iter()
            .map(|&term| self.ctx.terms.mk_not_raw(term))
            .collect();
        let mut current = candidate.add_theory_lemma_with_kind(
            "BV_LIA",
            residual.clone(),
            TheoryLemmaKind::BvLiaTautology,
        );
        for (term, unit) in scalar {
            let complement = self.ctx.terms.mk_not_raw(term);
            let position = residual.iter().position(|&literal| literal == complement)?;
            let _ = residual.remove(position);
            current = candidate.add_resolution(residual.clone(), term, current, unit);
        }
        if !residual.is_empty()
            || !crate::executor::proof_resolution::prune_to_empty_clause_derivation_at(
                &mut candidate,
                current.0 as usize,
            )
        {
            return None;
        }
        ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, authenticated_scope)
            .ok()?;
        let quality = self.check_proof_strict_until_stopped(&candidate).ok()?;
        (quality.is_complete() && Self::proof_derives_empty_clause(&candidate)).then_some(candidate)
    }
}
