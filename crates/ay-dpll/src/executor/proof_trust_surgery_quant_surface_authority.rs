// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deduplicated, work-budgeted authority for quantifier surface sources.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::TermId;
use ay_frontend::command::Term as FrontendTerm;

use crate::executor::proof_surface_syntax::strip_frontend_annotations;
use crate::executor::proof_trust_surgery_provenance::{
    surface_source_is_bounded, OriginalSourceIndex, ProvenanceSurfaceAudit, SurgeryPlanningBudget,
};
use crate::executor::Executor;

fn native_api_placeholder(parsed: &FrontendTerm) -> bool {
    surface_source_is_bounded(parsed)
        && matches!(
            strip_frontend_annotations(parsed),
            FrontendTerm::Symbol(name)
                if name == crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER
        )
}

pub(in super::super) struct QuantSurfaceAuthority<'a> {
    authenticated: HashSet<(TermId, TermId, bool)>,
    authenticated_assume_roots: HashSet<TermId>,
    nonquant_supports: Option<Vec<TermId>>,
    source_index: &'a OriginalSourceIndex,
    planning: SurgeryPlanningBudget,
}

impl<'a> QuantSurfaceAuthority<'a> {
    pub(in super::super) fn new(source_index: &'a OriginalSourceIndex) -> Self {
        Self {
            authenticated: HashSet::default(),
            authenticated_assume_roots: HashSet::default(),
            nonquant_supports: None,
            source_index,
            planning: SurgeryPlanningBudget::new(),
        }
    }

    pub(in super::super) fn original<'source>(
        &self,
        originals: &'source [(TermId, FrontendTerm)],
        canonical: TermId,
    ) -> Option<&'source FrontendTerm> {
        self.source_index
            .get(originals, canonical)
            .map(|(_, parsed)| parsed)
    }

    pub(in super::super) fn is_valid(&self) -> bool {
        self.source_index.is_valid()
    }

    pub(in super::super) fn authenticated_assume_roots(&self) -> &HashSet<TermId> {
        &self.authenticated_assume_roots
    }

    /// Cache the bounded exact-original support prefix shared by every
    /// quantifier candidate instead of rescanning all assertions per plan.
    pub(in super::super) fn nonquant_supports(
        &mut self,
        terms: &ay_core::TermStore,
        originals: &[(TermId, FrontendTerm)],
    ) -> Option<Vec<TermId>> {
        if self.nonquant_supports.is_none() {
            if !self.is_valid() {
                return None;
            }
            self.nonquant_supports = Some(
                originals
                    .iter()
                    .map(|(term, _)| *term)
                    .filter(|&term| {
                        !matches!(
                            terms.get(term),
                            ay_core::term::TermData::Forall(..)
                                | ay_core::term::TermData::Exists(..)
                        )
                    })
                    .take(12)
                    .collect(),
            );
        }
        self.nonquant_supports.clone()
    }

    fn spend_source(&mut self, canonical: TermId, parsed: &FrontendTerm) -> bool {
        self.is_valid() && self.planning.spend_surface(canonical, parsed)
    }

    pub(in super::super) fn spend_chain_source(
        &mut self,
        canonical: TermId,
        parsed: &FrontendTerm,
    ) -> bool {
        self.spend_source(canonical, parsed)
    }

    pub(in super::super) fn spend_canonical_work(&mut self, work: usize) -> bool {
        self.is_valid() && self.planning.spend_work(work)
    }

    pub(in super::super) fn spend_classification_work(&mut self, work: usize) -> bool {
        self.is_valid() && self.planning.spend_work(work)
    }

    pub(in super::super) fn spend_solver_attempt(
        &mut self,
        terms: &ay_core::TermStore,
        operands: &[TermId],
    ) -> bool {
        self.is_valid()
            && operands.len()
                <= crate::executor::proof_trust_surgery_provenance::MAX_PROVENANCE_REPAIR_TERMS
            && self.planning.spend_terms(terms, operands)
    }

    pub(in super::super) fn planning_budget(&mut self) -> &mut SurgeryPlanningBudget {
        &mut self.planning
    }

    pub(super) fn authenticate(
        &mut self,
        executor: &mut Executor,
        audit: &mut ProvenanceSurfaceAudit,
        originals: &[(TermId, FrontendTerm)],
        canonical: TermId,
        alias: TermId,
        alias_is_live: bool,
    ) -> bool {
        let key = (canonical, alias, alias_is_live);
        if self.authenticated.contains(&key) {
            return true;
        }
        let Some(parsed) = self.original(originals, canonical) else {
            return false;
        };
        let canonical_root = match executor.ctx.terms.get(canonical) {
            ay_core::term::TermData::Forall(_, body, _)
            | ay_core::term::TermData::Exists(_, body, _) => *body,
            _ => canonical,
        };
        if !self.spend_solver_attempt(&executor.ctx.terms, &[canonical_root]) {
            return false;
        }
        let authenticated = if native_api_placeholder(parsed) {
            if alias != canonical {
                return false;
            }
            audit.protect_rigid_operand(&mut executor.ctx.terms, canonical);
            true
        } else {
            if !self.spend_source(canonical, parsed) {
                return false;
            }
            audit.require_parsed_original_as(
                &mut executor.ctx,
                parsed,
                canonical,
                alias,
                !alias_is_live,
            )
        };
        if authenticated {
            audit.protect_operand(&mut executor.ctx.terms, canonical);
            audit.protect_operand(&mut executor.ctx.terms, alias);
            self.authenticated_assume_roots.insert(canonical);
            self.authenticated_assume_roots.insert(alias);
            self.authenticated.insert(key);
        }
        authenticated
    }
}

#[cfg(test)]
mod tests {
    use ay_core::{Sort, TermId, TermStore};
    use ay_frontend::command::Term as FrontendTerm;

    use super::{OriginalSourceIndex, QuantSurfaceAuthority};

    #[test]
    fn repeated_large_source_work_is_aggregate_bounded() {
        let source = FrontendTerm::Symbol("q".repeat(2 * 1024 * 1024));
        let originals = vec![(TermId(0), source.clone())];
        let index = OriginalSourceIndex::new(&originals);
        let mut authority = QuantSurfaceAuthority::new(&index);
        for _ in 0..4 {
            assert!(authority.spend_chain_source(TermId(0), &source));
        }
        assert!(!authority.spend_chain_source(TermId(0), &source));
    }

    #[test]
    fn duplicate_canonical_sources_have_no_authority() {
        let originals = vec![
            (TermId(7), FrontendTerm::Symbol("first_q".to_string())),
            (TermId(7), FrontendTerm::Symbol("second_q".to_string())),
        ];
        let index = OriginalSourceIndex::new(&originals);
        let authority = QuantSurfaceAuthority::new(&index);
        assert!(authority.original(&originals, TermId(7)).is_none());
    }

    #[test]
    fn canonical_work_shares_the_quant_source_budget() {
        let originals = vec![(TermId(0), FrontendTerm::Symbol("q".to_string()))];
        let index = OriginalSourceIndex::new(&originals);
        let mut authority = QuantSurfaceAuthority::new(&index);
        assert!(authority.spend_canonical_work(16 * 1024 * 1024));
        assert!(authority.spend_canonical_work(16 * 1024 * 1024));
        assert!(!authority.spend_canonical_work(1));
    }

    #[test]
    fn repeated_solver_attempts_charge_cached_operand_work() {
        let originals = vec![(TermId(0), FrontendTerm::Symbol("q".to_string()))];
        let index = OriginalSourceIndex::new(&originals);
        let mut authority = QuantSurfaceAuthority::new(&index);
        let mut terms = TermStore::new();
        let operand = terms.mk_var("quant_attempt_operand", Sort::Bool);
        let work = super::super::super::quant_canonical_term_work(&terms, operand)
            .expect("small operand is bounded");
        authority.planning.set_remaining_work_for_test(work * 2);
        assert!(authority.spend_solver_attempt(&terms, &[operand]));
        assert!(authority.spend_solver_attempt(&terms, &[operand]));
        assert!(!authority.spend_solver_attempt(&terms, &[operand]));
    }

    #[test]
    fn canonical_source_preflight_rejects_excess_arity() {
        let originals = vec![(TermId(0), FrontendTerm::Symbol("q".to_string()))];
        let index = OriginalSourceIndex::new(&originals);
        let mut authority = QuantSurfaceAuthority::new(&index);
        let mut terms = TermStore::new();
        let atom = terms.mk_bool(true);
        let body = terms.mk_app(
            ay_core::Symbol::named("quant_surface_wide"),
            vec![atom; 100_001],
            Sort::Bool,
        );
        assert!(!authority.spend_solver_attempt(&terms, &[body]));
    }
}
