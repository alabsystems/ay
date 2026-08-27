// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certified ITE lifting after an additional authored bound substitution.

use super::proof_trust_surgery_ite_plan::IteLiftPlan;
use super::Executor;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{FarkasAnnotation, Sort, TermId};
use ay_frontend::command::Term as FrontendTerm;

impl Executor {
    /// Recognize a lifted branch after preprocessing applied both the ITE
    /// substitution and a second authored equality. Both transfer lemmas are
    /// accepted only when the independent Farkas checker certifies the exact
    /// coefficients subsequently emitted.
    pub(super) fn plan_ite_lift_over_substituted_bound(
        &mut self,
        originals: &[(TermId, FrontendTerm)],
        cond: TermId,
        lifted_then: TermId,
        lifted_else: TermId,
        goal: TermId,
    ) -> Option<IteLiftPlan> {
        const TRIPLE_BUDGET: usize = 512;
        const GRID: i64 = 8;

        let mut budget = TRIPLE_BUDGET;
        for &(orig, _) in originals {
            for (ite_term, u, v) in self.term_ite_candidates_with_cond(orig, cond) {
                let Some((eq_then, eq_else, ite_def, and_term, intro_eq)) =
                    self.build_ite_lift_connectives(orig, cond, ite_term, u, v)
                else {
                    continue;
                };
                for &(bound, _) in originals {
                    if bound == orig {
                        continue;
                    }
                    if budget == 0 {
                        return None;
                    }
                    budget -= 1;
                    let Some(then_coeffs) =
                        self.search_quad_transfer_coeffs(eq_then, orig, bound, lifted_then, GRID)
                    else {
                        continue;
                    };
                    let Some(else_coeffs) =
                        self.search_quad_transfer_coeffs(eq_else, orig, bound, lifted_else, GRID)
                    else {
                        continue;
                    };
                    return Some(IteLiftPlan {
                        guarded_then_or: false,
                        orig,
                        defining_source: None,
                        bound: Some(bound),
                        cond,
                        lifted_then,
                        lifted_else,
                        goal,
                        ite_term,
                        eq_then,
                        eq_else,
                        ite_def,
                        and_term,
                        intro_eq,
                        then_coeffs,
                        else_coeffs,
                    });
                }
            }
        }
        None
    }

    /// Search a bounded coefficient grid, with premise and conclusion weights
    /// pinned to one so the result remains a transfer rather than an arbitrary
    /// arithmetic consequence.
    fn search_quad_transfer_coeffs(
        &self,
        eq: TermId,
        premise: TermId,
        bound: TermId,
        conclusion: TermId,
        grid: i64,
    ) -> Option<FarkasAnnotation> {
        for eq_coefficient in 1..=grid {
            for bound_coefficient in 1..=grid {
                let annotation =
                    FarkasAnnotation::from_ints(&[eq_coefficient, 1, bound_coefficient, 1]);
                if self.quad_lemma_valid_with(eq, premise, bound, conclusion, &annotation) {
                    return Some(annotation);
                }
            }
        }
        None
    }

    /// Non-Boolean ITE subterms of `root` using exactly `condition`.
    pub(super) fn term_ite_candidates_with_cond(
        &self,
        root: TermId,
        condition: TermId,
    ) -> Vec<(TermId, TermId, TermId)> {
        let mut candidates = Vec::new();
        let mut stack = vec![root];
        let mut seen = HashSet::default();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(cond, then_term, else_term) => {
                    if *cond == condition && *self.ctx.terms.sort(term) != Sort::Bool {
                        candidates.push((term, *then_term, *else_term));
                    }
                    stack.extend([*cond, *then_term, *else_term]);
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                _ => {}
            }
        }
        candidates
    }
}
