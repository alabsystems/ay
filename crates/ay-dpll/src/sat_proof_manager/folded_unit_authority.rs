// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded discovery of strict-authenticated proof plans for folded SAT units.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Symbol, TermData, TermId};
use ay_sat::{ResolutionValidationError, ResolutionValidationResource};

use super::exact_fragment::{exact_checked_mul, OrFoldUnitPlan};
use super::SatProofManager;

impl SatProofManager<'_> {
    /// Build the authored-conjunct closure and folded-`or` plans in one walk.
    ///
    /// Transitive `and`-conjuncts mirror the exact closure the strict checker's
    /// own premise validator computes. The resulting plans remain hints only:
    /// every emitted proof step is independently re-derived downstream.
    pub(super) fn build_folded_unit_authority(
        &self,
        authored_problem_terms: &[TermId],
        unit_authority: bool,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<(HashSet<TermId>, HashMap<TermId, OrFoldUnitPlan>), ResolutionValidationError> {
        let mut authored_conjunct_closure = HashSet::default();
        let mut or_fold_candidates = Vec::new();
        if unit_authority {
            let mut stack: Vec<TermId> = authored_problem_terms.to_vec();
            let mut expanded = HashSet::default();
            let mut pending_pops = 0usize;
            while let Some(term) = stack.pop() {
                pending_pops += 1;
                if pending_pops == 256 {
                    progress(pending_pops, 0)?;
                    pending_pops = 0;
                }
                if !expanded.insert(term) {
                    continue;
                }
                // Authored roots are not yet validated against the term store
                // here. A stale root must fail closed later, never panic here.
                if term.index() >= self.terms.len() {
                    continue;
                }
                let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
                    continue;
                };
                if name == "or" && Self::or_fold_survivor(self.terms, term).is_some() {
                    or_fold_candidates.push(term);
                    continue;
                }
                if name != "and" {
                    continue;
                }
                let args = args.clone();
                progress(
                    args.len(),
                    exact_checked_mul(args.len(), 192, ResolutionValidationResource::Bytes)?,
                )?;
                for &arg in &args {
                    authored_conjunct_closure.insert(arg);
                    stack.push(arg);
                }
            }
            progress(pending_pops, 0)?;
        }
        let or_fold_unit_plans = self.build_or_fold_unit_plans(&or_fold_candidates, progress)?;
        Ok((authored_conjunct_closure, or_fold_unit_plans))
    }
}
