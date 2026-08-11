// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact rendered roles for generated Boolean connective projections.

use ay_core::term::TermData;
use ay_core::{Sort, Symbol, TermId, TermStore};

use super::{ProvenanceSurfaceAudit, MAX_AUDITED_FARKAS_LEMMAS};

const MAX_CONNECTIVE_ARITY: usize =
    crate::executor::proof_trust_surgery_provenance::MAX_PROVENANCE_REPAIR_TERMS;
const MAX_GENERATED_AND_PROJECTION_USES: usize = 512;
const LINEAR_CONNECTIVE_RENDER_FACTOR: usize = 24;

impl ProvenanceSurfaceAudit {
    fn record_generated_connective_render_use(&mut self, root: TermId, factor: usize) -> bool {
        let previous = self
            .generated_connective_render_uses
            .get(&root)
            .copied()
            .unwrap_or(0);
        let Some(next) = previous.checked_add(factor.max(1)) else {
            self.overflowed = true;
            return false;
        };
        if next > super::MAX_AUDITED_RENDER_WORK as usize {
            self.overflowed = true;
            return false;
        }
        self.generated_connective_render_uses.insert(root, next);
        true
    }

    /// Register an emitted `or` decomposition whose authored immediate
    /// operands must remain an exact duplicate-preserving permutation.
    pub(in crate::executor) fn protect_or_decomposition_permutation_role(
        &mut self,
        terms: &mut TermStore,
        root: TermId,
        disjuncts: &[TermId],
    ) -> bool {
        let canonical = match terms.get(root) {
            TermData::App(Symbol::Named(head), canonical)
                if head == "or"
                    && *terms.sort(root) == Sort::Bool
                    && (2..=MAX_CONNECTIVE_ARITY).contains(&canonical.len())
                    && canonical.as_slice() == disjuncts
                    && canonical
                        .iter()
                        .all(|&term| *terms.sort(term) == Sort::Bool) =>
            {
                canonical.clone()
            }
            _ => {
                self.overflowed = true;
                return false;
            }
        };
        let role = (root, canonical);
        if self.or_decomposition_roles.len() >= MAX_AUDITED_FARKAS_LEMMAS
            && !self.or_decomposition_roles.contains(&role)
        {
            self.overflowed = true;
            return false;
        }
        self.protect_operand(terms, root);
        for &disjunct in disjuncts {
            self.protect_operand(terms, disjunct);
        }
        self.or_decomposition_roles.insert(role);
        let _ = self.record_generated_connective_render_use(root, LINEAR_CONNECTIVE_RENDER_FACTOR);
        !self.overflowed
    }

    /// Register the exact positive flat-`and` operand selected by a generated
    /// `and_pos(index)` step.
    pub(in crate::executor) fn protect_and_projection_role(
        &mut self,
        terms: &mut TermStore,
        root: TermId,
        index: u32,
        conjunct: TermId,
    ) -> bool {
        let index_usize = index as usize;
        let valid = matches!(
            terms.get(root),
            TermData::App(Symbol::Named(head), conjuncts)
                if head == "and"
                    && *terms.sort(root) == Sort::Bool
                    && (2..=MAX_CONNECTIVE_ARITY).contains(&conjuncts.len())
                    && conjuncts.get(index_usize) == Some(&conjunct)
                    && conjuncts.iter().filter(|&&term| term == conjunct).count() == 1
                    && conjuncts
                        .iter()
                        .all(|&term| *terms.sort(term) == Sort::Bool)
        );
        if !valid {
            self.overflowed = true;
            return false;
        }
        self.generated_and_projection_uses = match self.generated_and_projection_uses.checked_add(1)
        {
            Some(uses) if uses <= MAX_GENERATED_AND_PROJECTION_USES => uses,
            _ => {
                self.overflowed = true;
                return false;
            }
        };
        let role = (root, index, conjunct);
        if self.and_projection_roles.len() >= MAX_AUDITED_FARKAS_LEMMAS
            && !self.and_projection_roles.contains(&role)
        {
            self.overflowed = true;
            return false;
        }
        self.protect_operand(terms, root);
        self.protect_operand(terms, conjunct);
        self.and_projection_roles.insert(role);
        let _ = self.record_generated_connective_render_use(root, LINEAR_CONNECTIVE_RENDER_FACTOR);
        !self.overflowed
    }

    /// Register one generated `and_neg` against the exact canonical children
    /// whose rendered multiplicity must be preserved.
    pub(in crate::executor) fn protect_and_introduction_role(
        &mut self,
        terms: &mut TermStore,
        root: TermId,
    ) -> bool {
        let children = match terms.get(root) {
            TermData::App(Symbol::Named(head), children)
                if head == "and"
                    && *terms.sort(root) == Sort::Bool
                    && (2..=MAX_CONNECTIVE_ARITY).contains(&children.len())
                    && children.iter().all(|&term| *terms.sort(term) == Sort::Bool) =>
            {
                children.clone()
            }
            _ => {
                self.overflowed = true;
                return false;
            }
        };
        let role = (root, children.clone());
        if self.and_introduction_roles.len() >= MAX_AUDITED_FARKAS_LEMMAS
            && !self.and_introduction_roles.contains(&role)
        {
            self.overflowed = true;
            return false;
        }
        self.protect_operand(terms, root);
        for child in children {
            self.protect_operand(terms, child);
        }
        self.and_introduction_roles.insert(role);
        let _ = self.record_generated_connective_render_use(root, LINEAR_CONNECTIVE_RENDER_FACTOR);
        !self.overflowed
    }

    /// Register all generated `or_neg` links from distinct selected target
    /// disjuncts into one rendered goal OR.
    pub(in crate::executor) fn protect_or_projection_roles(
        &mut self,
        terms: &mut TermStore,
        root: TermId,
        disjuncts: &[TermId],
        uses: usize,
    ) -> bool {
        if uses == 0 || uses > disjuncts.len() {
            self.overflowed = true;
            return false;
        }
        if !self.protect_or_decomposition_permutation_role(terms, root, disjuncts) {
            return false;
        }
        let Some(factor) = disjuncts
            .len()
            .checked_add(LINEAR_CONNECTIVE_RENDER_FACTOR)
            .and_then(|factor| factor.checked_mul(uses))
        else {
            self.overflowed = true;
            return false;
        };
        let _ = self.record_generated_connective_render_use(root, factor);
        !self.overflowed
    }
}
