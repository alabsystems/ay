// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The exact finite-expansion UNSAT route of the quantified result mapper.
//!
//! [`Executor::finite_expansion_unsat_route`] records, before the solve-time
//! assertions are restored, which theorem may certify the verdict.
//! [`Executor::certify_finite_expansion_unsat_route`] consults that theorem
//! after restoration. The record is only a routing fact: the theorem
//! (`unsat_cert/finite_expansion_evidence.rs`) re-expands the immutable public
//! roots itself.

use ay_core::TermId;

use crate::executor::quantifier_loop::ExactFiniteExpansionEvidence;
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};

/// Which finite-expansion UNSAT theorem the post-restoration gate consults.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FiniteExpansionUnsatRoute {
    /// The classified verdict was `Unsat`: the literal-bound theorem.
    Literal,
    /// (#withheld-finite-expansion-refutation) The ground solve refuted the
    /// exact expansion and the mandatory-artifact gate withheld the verdict:
    /// the source-derived theorem.
    WithheldRefutation,
}

impl FiniteExpansionUnsatRoute {
    fn select(routed: bool, withheld_ground_refutation: bool) -> Option<Self> {
        match (routed, withheld_ground_refutation) {
            (false, _) => None,
            (true, true) => Some(Self::WithheldRefutation),
            (true, false) => Some(Self::Literal),
        }
    }

    /// `Some(source_derived)` when the restored verdict consults a theorem.
    fn theorem_for(route: Option<Self>, restored: &Result<SolveResult>) -> Option<bool> {
        match (route, restored) {
            (Some(Self::WithheldRefutation), Ok(SolveResult::Unknown)) => Some(true),
            (Some(_), Ok(SolveResult::Unsat(_))) => Some(false),
            _ => None,
        }
    }
}

impl Executor {
    /// Preserve only a routing fact here: before restoration, authenticate
    /// that the ground UNSAT was obtained after the exact recorded
    /// finite-domain replacement of every solve-time quantified root.  The
    /// record is never retargeted to authored roots.  After restoration the
    /// semantic certificate below independently re-expands the immutable
    /// public roots and checks their complete ground vector itself.
    ///
    /// (#withheld-finite-expansion-refutation) The same route also owns a
    /// refutation of that exact expansion which the mandatory-artifact gate
    /// WITHHELD. A derived-bound expansion grounds the problem only after
    /// E-matching, so an earlier instance without a strict `forall_inst`
    /// translation (typically the diagonal pass's) has already marked the
    /// translation incomplete, and the downgrade ran before this theorem
    /// could be consulted. The theorem re-derives its contradiction from the
    /// public roots alone and uses nothing that solve produced, so it can
    /// only turn the withheld `unknown` into a certified `unsat`; when it
    /// declines, the withheld `unknown` stands. Proof-artifact modes skip it:
    /// the theorem declines there anyway.
    pub(super) fn finite_expansion_unsat_route(
        &mut self,
        ground_solve_was_unsat: bool,
        final_result: &Result<SolveResult>,
        full_ematching_coverage: bool,
        original: Option<&[TermId]>,
        expansion: Option<&ExactFiniteExpansionEvidence>,
    ) -> Option<FiniteExpansionUnsatRoute> {
        let withheld_ground_refutation = ground_solve_was_unsat
            && self.quantified_refutation_withheld
            && matches!(final_result, Ok(SolveResult::Unknown))
            && !self.strict_unsat_presentation_required();
        let routed = (matches!(final_result, Ok(SolveResult::Unsat(_)))
            || withheld_ground_refutation)
            && full_ematching_coverage
            && match (original, expansion) {
                (Some(original), Some(expansion)) => self
                    .exact_finite_expansion_model_roots(original, expansion)
                    .is_some(),
                _ => false,
            };
        FiniteExpansionUnsatRoute::select(routed, withheld_ground_refutation)
    }

    /// Exact finite-expansion UNSAT theorem.  This is deliberately after
    /// restoration: its private constructor sees only the current public
    /// query epoch, canonical-expands those roots afresh, and accepts a
    /// model-independent `false` conjunct or distinct-scalar assignment
    /// clash.  A failed theorem leaves the ordinary mandatory strict-proof
    /// gate in charge; explicit proof/self-check modes decline this lane.
    ///
    /// A withheld refutation is consulted only while restoration left the
    /// verdict `unknown`; either route is consulted on an `Unsat`, and then by
    /// the literal-bound theorem.
    pub(super) fn certify_finite_expansion_unsat_route(
        &mut self,
        route: Option<FiniteExpansionUnsatRoute>,
        final_result: &mut Result<SolveResult>,
    ) {
        let Some(source_derived) = FiniteExpansionUnsatRoute::theorem_for(route, final_result)
        else {
            return;
        };
        // `original_assertions` is the solve-time preprocessing snapshot,
        // which can differ from the always-on gate's authored vector. The
        // outer transaction restores this same vector on return; install it
        // now so the source theorem binds to the immutable public epoch,
        // never to the record's transformed root identity.
        let public_roots = match self.independent_gate_query_roots() {
            Ok(roots) => roots,
            Err(_) => {
                *final_result = Ok(SolveResult::Unknown);
                return;
            }
        };
        let prior_roots = std::mem::replace(&mut self.ctx.assertions, public_roots);
        let evidence = if source_derived {
            self.try_authorize_current_query_source_derived_finite_expansion_unsat()
        } else {
            self.try_authorize_current_query_exact_finite_expansion_unsat()
        };
        if let Some(evidence) = evidence {
            if ay_core::misc_cli_flags().debug_cert {
                eprintln!("CERT/exact-finite-expansion-unsat: public theorem accepted");
            }
            let emitted = self.emit_checked_exact_finite_expansion_unsat(evidence);
            if !emitted.is_unsat() {
                // A stop or strict-presentation request can arrive between
                // authorization and emission. It must not leave the failed
                // semantic lane's temporary public-root window installed
                // for later strict reconstruction.
                self.ctx.assertions = prior_roots;
            }
            *final_result = Ok(emitted);
        } else if ay_core::misc_cli_flags().debug_cert {
            self.ctx.assertions = prior_roots;
            eprintln!("CERT/exact-finite-expansion-unsat: public theorem declined");
        } else {
            self.ctx.assertions = prior_roots;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The route and the theorem choice against the booleans the inlined gate
    /// computed before this extraction: `withheld_route = withheld && routed
    /// && unknown`, entered on `withheld_route || (routed && unsat)`, and the
    /// source-derived theorem exactly on `withheld_route`.
    #[test]
    fn the_route_selects_exactly_what_the_inlined_gate_selected() {
        let verdicts = [
            Ok(SolveResult::Unknown),
            Ok(SolveResult::unsat()),
            Ok(SolveResult::Sat),
        ];
        for routed in [false, true] {
            for withheld in [false, true] {
                let route = FiniteExpansionUnsatRoute::select(routed, withheld);
                for restored in &verdicts {
                    let unknown = matches!(restored, Ok(SolveResult::Unknown));
                    let unsat = matches!(restored, Ok(SolveResult::Unsat(_)));
                    let withheld_route = withheld && routed && unknown;
                    let inlined = (withheld_route || (routed && unsat)).then_some(withheld_route);
                    assert_eq!(
                        FiniteExpansionUnsatRoute::theorem_for(route, restored),
                        inlined,
                        "routed={routed} withheld={withheld} restored={restored:?}"
                    );
                }
            }
        }
    }
}
