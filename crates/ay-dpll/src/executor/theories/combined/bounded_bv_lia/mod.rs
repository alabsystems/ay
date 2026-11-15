// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-exact bounded Bool/BV/LIA refutation lane.
//!
//! This is intentionally not another theory bridge. The independent proof
//! checker interprets the exact live assertion-plus-assumption roots and
//! returns an opaque snapshot-bound witness only when that source query is
//! UNSAT. The witness is consumed here only as a decision bit: the ordinary
//! public UNSAT funnel re-authenticates the immutable public source roots and
//! remains the sole authority for publication. No transformed proof, model,
//! or solver state exists to leak into the enclosing solve.

use crate::executor::Executor;
use crate::executor_types::{SolveResult, UnknownOrigin, UnknownReason};
use crate::features::StaticFeatures;
use crate::logic_detection::LogicCategory;
use ay_core::TermId;

impl Executor {
    /// Plain integer mod queries need the same exact-source handoff as the BV
    /// combiner. This predicate only selects a candidate; the existing checker
    /// owns fragment admission and the unchanged public funnel owns its proof.
    pub(in crate::executor) fn try_solve_via_bounded_scalar_mod(
        &mut self,
        category: LogicCategory,
        features: &StaticFeatures,
        assumptions: &[TermId],
    ) -> Option<SolveResult> {
        if !matches!(
            category,
            LogicCategory::QfLia | LogicCategory::QfNia | LogicCategory::QfEia
        ) || !features.has_int_div_mod
            || !features.within_dt_uf_nia_theories()
            || features.has_uf
            || features.has_quantifiers
            || features.has_bv_int_conversion
            || features.has_seq
            || features.has_rounding_mode
            || features.has_is_int_real
        {
            return None;
        }
        self.try_solve_via_bounded_bv_lia(assumptions)
    }

    /// Return a provisional BV/LIA refutation with a conservative assumption
    /// core. Bridge assertions may be consequences of any active assumption,
    /// so a core harvested after those consequences become base assertions is
    /// not source-valid unless it retains every assumption.
    pub(super) fn bv_lia_unsat_candidate(&mut self, assumptions: &[TermId]) -> SolveResult {
        if !assumptions.is_empty() {
            self.last_assumption_core = Some(assumptions.to_vec());
        }
        SolveResult::unsat()
    }

    pub(super) fn try_solve_via_bounded_bv_lia(
        &mut self,
        assumptions: &[TermId],
    ) -> Option<SolveResult> {
        if self.should_abort_theory_loop() {
            return Some(SolveResult::Unknown);
        }

        let mut exact_roots = self.ctx.assertions.clone();
        exact_roots.extend_from_slice(assumptions);
        let authenticated = ay_proof::authenticate_bv_lia_unsat_query(
            &self.ctx.terms,
            &exact_roots,
            self.current_solve_deadline(),
        )
        .ok()
        .is_some_and(|evidence| evidence.is_current_for(&self.ctx.terms, &exact_roots));

        if self.should_abort_theory_loop() {
            return Some(SolveResult::Unknown);
        }

        self.last_statistics.set_string(
            "solver.bv_lia_bounded_source",
            if authenticated { "unsat" } else { "declined" },
        );
        if !authenticated {
            return None;
        }
        // Disposable internal solves have no public query epoch. Their exact
        // working-set decision remains useful, but cannot mint publication
        // authority or a source-bound export token.
        if self.unsat_query_epoch.is_none() {
            self.pending_bounded_bv_lia_unsat = None;
            self.last_unknown_reason = None;
            return Some(self.bv_lia_unsat_candidate(assumptions));
        }
        // The combined route may be solving a transient working set. Mint the
        // affine W7 handoff only after independently re-authenticating the
        // immutable public epoch's complete ordered assertions+assumptions.
        // Unsupported/resource-bounded exact source shapes decline this fast
        // route. A SAT or structurally invalid exact source is contradictory
        // evidence and hard-vetoes the working-set refutation.
        match self.authenticate_and_prepare_pending_bounded_bv_lia_unsat(assumptions) {
            Ok(true) => {}
            Ok(false) => {
                self.last_statistics
                    .set_string("solver.bv_lia_bounded_source", "declined-exact-source");
                return None;
            }
            Err(error) => {
                self.last_statistics
                    .set_string("solver.bv_lia_bounded_source", "rejected-exact-source");
                self.record_unknown_from_origin(UnknownOrigin::VerdictCertification);
                self.last_unknown_reason = Some(UnknownReason::SelfCheckRejected);
                self.record_unknown_diagnostic(UnknownReason::SelfCheckRejected, error.to_string());
                return Some(SolveResult::Unknown);
            }
        }
        self.last_unknown_reason = None;
        Some(self.bv_lia_unsat_candidate(assumptions))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_frontend::parse;

    #[test]
    fn internal_working_set_refutation_does_not_mint_public_authority() {
        let mut executor = Executor::new();
        executor.ctx.assertions = vec![executor.ctx.terms.false_term()];
        assert!(executor.unsat_query_epoch.is_none());

        assert!(executor
            .try_solve_via_bounded_bv_lia(&[])
            .is_some_and(|result| result.is_unsat()));
        assert!(executor.pending_bounded_bv_lia_unsat.is_none());
        assert!(executor.last_unsat_certificate.is_none());
        assert!(!executor.has_strict_native_bv_lia_bundle_state());
    }

    #[test]
    fn exact_source_sat_hard_vetoes_transient_working_set_refutation() {
        let commands = parse(
            r#"
            (set-option :produce-proofs true)
            (set-logic QF_UFBVLIA)
            (declare-const b (_ BitVec 8))
            (assert (= b #x02))
            (assert (= (bv2nat b) 2))
            "#,
        )
        .expect("valid exact SAT query");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("install exact SAT query");
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);

        // The production route may decide a transformed working set, but that
        // result cannot override the immutable public epoch. Make the working
        // set trivially UNSAT while leaving the exact epoch/source SAT.
        executor.ctx.assertions = vec![executor.ctx.terms.false_term()];
        let result = executor.try_solve_via_bounded_bv_lia(&[]);

        assert!(result.is_some_and(|result| result.is_unknown()));
        assert_eq!(
            executor
                .statistics()
                .get_string("solver.bv_lia_bounded_source"),
            Some("rejected-exact-source")
        );
        // This unit exercises the private route directly, before the outer
        // check-sat boundary installs `last_result`; inspect the route's
        // internal reason slot instead of the public last-result accessor.
        assert_eq!(
            executor.last_unknown_reason,
            Some(UnknownReason::SelfCheckRejected)
        );
        assert!(executor.pending_bounded_bv_lia_unsat.is_none());
    }
}
