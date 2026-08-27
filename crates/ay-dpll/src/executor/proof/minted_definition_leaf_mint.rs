// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Choosing the definitions the MINTED-DEFINITION leaf lane would write.
//!
//! Split out of `minted_definition_leaf.rs` so each file stays inside the
//! repository's 500-line ceiling. That file owns the lane, the alignment and
//! the module-level soundness argument; this one owns Guards 4-8 — the vetting
//! that decides FRESH, SORT, SINGLE DEFINIENS and INDEPENDENT before any
//! definition may enter a pool.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::proof_validation::recognize_fresh_def_eq;
use ay_core::{AletheRule, Proof, ProofStep, TermData, TermId};

use super::super::Executor;
use super::minted_definition_leaf::{
    align, collect_symbol_names, Minted, MAX_ALIGN_NODES, MAX_MINTED_PER_LEAF,
};

impl Executor {
    /// Every symbol NAME the problem constrains or the proof assumes.
    pub(super) fn minted_constrained_names(
        &self,
        proof: &Proof,
        problem_assertions: &[TermId],
    ) -> DetHashSet<String> {
        let mut names: DetHashSet<String> = DetHashSet::default();
        let mut visited: DetHashSet<TermId> = DetHashSet::default();
        for &assertion in problem_assertions {
            collect_symbol_names(&self.ctx.terms, assertion, &mut names, &mut visited);
        }
        for assertion in self.complete_problem_assertions_for_strict_proof() {
            collect_symbol_names(&self.ctx.terms, assertion, &mut names, &mut visited);
        }
        for step in &proof.steps {
            if let ProofStep::Assume(term) = step {
                collect_symbol_names(&self.ctx.terms, *term, &mut names, &mut visited);
            }
        }
        names
    }

    /// The `name -> definiens` bindings the proof already carries, across BOTH
    /// fresh-definition rules — the population `FreshDefRegistry` will see.
    pub(super) fn existing_fresh_definitions(&self, proof: &Proof) -> DetHashMap<String, TermId> {
        let mut bindings: DetHashMap<String, TermId> = DetHashMap::default();
        for step in &proof.steps {
            let ProofStep::Step {
                rule: rule @ (AletheRule::FreshDefEq | AletheRule::FreshDefBound),
                clause,
                premises,
                args,
            } = step
            else {
                continue;
            };
            if !premises.is_empty() {
                continue;
            }
            let Some(&definiendum) = args.first() else {
                continue;
            };
            let TermData::Var(name, _) = self.ctx.terms.get(definiendum) else {
                continue;
            };
            let Some(&atom) = clause.first() else {
                continue;
            };
            let definiens = match rule {
                AletheRule::FreshDefEq => recognize_fresh_def_eq(&self.ctx.terms, &[atom], 0, args)
                    .ok()
                    .map(|shape| shape.definiens),
                _ => ay_core::proof_validation::recognize_fresh_def_bound(
                    &self.ctx.terms,
                    &[atom],
                    0,
                    args,
                )
                .ok()
                .map(|shape| shape.definiens),
            };
            if let Some(definiens) = definiens {
                bindings.insert(name.clone(), definiens);
            }
        }
        bindings
    }

    /// The definitions the leaf would need, or `None` when any condition of
    /// Guards 4-8 fails.
    pub(super) fn mint_definitions_for(
        &mut self,
        atom: TermId,
        root: TermId,
        constrained: &DetHashSet<String>,
        existing: &DetHashMap<String, TermId>,
    ) -> Option<Vec<Minted>> {
        let mut pairs: Vec<(TermId, TermId)> = Vec::new();
        let mut budget = MAX_ALIGN_NODES;
        if !align(&self.ctx.terms, atom, root, &mut pairs, &mut budget) {
            return None;
        }
        if pairs.is_empty() || pairs.len() > MAX_MINTED_PER_LEAF {
            return None;
        }
        self.mint_definitions_from_pairs(&pairs, constrained, existing)
    }

    /// Guards 4-8 over an ALREADY COMPUTED alignment. Extracted verbatim from
    /// [`Self::mint_definitions_for`] so the conjunct-decomposition lane, whose
    /// alignment additionally descends `Not`, is vetted by exactly this code
    /// rather than a second copy of it.
    pub(super) fn mint_definitions_from_pairs(
        &mut self,
        pairs: &[(TermId, TermId)],
        constrained: &DetHashSet<String>,
        existing: &DetHashMap<String, TermId>,
    ) -> Option<Vec<Minted>> {
        if pairs.is_empty() || pairs.len() > MAX_MINTED_PER_LEAF {
            return None;
        }
        // Guards 4, 5 and 6: every differing position is a FRESH atomic
        // variable at the same sort, with ONE definiens per name.
        let mut chosen: DetHashMap<String, (TermId, TermId)> = DetHashMap::default();
        for &(definiendum, definiens) in pairs {
            let TermData::Var(name, _) = self.ctx.terms.get(definiendum) else {
                return None;
            };
            let name = name.clone();
            if constrained.contains(&name) {
                return None;
            }
            if self.ctx.terms.sort(definiendum) != self.ctx.terms.sort(definiens) {
                return None;
            }
            if let Some(&bound) = existing.get(&name) {
                if bound != definiens {
                    return None;
                }
            }
            match chosen.get(&name) {
                Some(&(_, prior)) if prior != definiens => return None,
                Some(_) => {}
                None => {
                    chosen.insert(name, (definiendum, definiens));
                }
            }
        }
        // Guard 7 (INDEPENDENT): no minted or existing definiendum name may
        // occur inside any minted or existing definiens.
        let mut definiens_names: DetHashSet<String> = DetHashSet::default();
        let mut visited: DetHashSet<TermId> = DetHashSet::default();
        for &(_, definiens) in chosen.values() {
            collect_symbol_names(
                &self.ctx.terms,
                definiens,
                &mut definiens_names,
                &mut visited,
            );
        }
        for &definiens in existing.values() {
            collect_symbol_names(
                &self.ctx.terms,
                definiens,
                &mut definiens_names,
                &mut visited,
            );
        }
        if chosen.keys().any(|name| definiens_names.contains(name))
            || existing.keys().any(|name| definiens_names.contains(name))
        {
            return None;
        }
        // Guard 8: the CHECKER's own recognizer decides whether the node this
        // lane built is a fresh definitional equality at all.
        let mut ordered: Vec<(String, (TermId, TermId))> = chosen.into_iter().collect();
        ordered.sort_by(|left, right| left.0.cmp(&right.0));
        let mut minted: Vec<Minted> = Vec::with_capacity(ordered.len());
        for (_, (definiendum, definiens)) in ordered {
            let definition = self.ctx.terms.mk_eq(definiendum, definiens);
            if recognize_fresh_def_eq(&self.ctx.terms, &[definition], 0, &[definiendum]).is_err() {
                return None;
            }
            minted.push(Minted {
                definiendum,
                definition,
            });
        }
        Some(minted)
    }
}
