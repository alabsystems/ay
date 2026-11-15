// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Private ground-candidate ownership before the full datatype certificate.

use super::{CheckedDtSatAuthority, Executor, Result, SolveResult, TermId};
use crate::ematching::contains_quantifier;
use crate::executor::qsat_route::ProofStateSnapshot;
use crate::executor::quantifier_loop::result_mapping::CheckedModelInstallSnapshot;
use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;

mod outputs;
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use outputs::{GroundModelAuthority, GroundProofOutputs};

#[cfg(test)]
mod producer_tests;
#[cfg(test)]
mod tests;

impl Executor {
    /// Solve only the exact ground subquery, then restore outer query/proof
    /// authority before certifying the complete original obligation. The old
    /// model and its sidecars remain parked until that full certificate grants.
    pub(super) fn with_dt_ground_candidate_scope(
        &mut self,
        ground: Vec<TermId>,
        certification_roots: &[TermId],
        solve: impl FnOnce(&mut Self) -> Result<SolveResult>,
        certify: impl FnOnce(&mut Self) -> Option<CheckedDtSatAuthority>,
    ) -> Option<CheckedDtSatAuthority> {
        const MAX_SOURCE_TERMS: usize = 16_384;
        let root_count = certification_roots
            .len()
            .checked_add(self.last_assumptions.as_ref().map_or(0, Vec::len))?;
        if root_count > MAX_SOURCE_TERMS
            || ground.len() > MAX_SOURCE_TERMS
            || self.ctx.terms.len() > MAX_SOURCE_TERMS
            || self.recorded_var_substitutions.len() > MAX_SOURCE_TERMS
        {
            return None;
        }
        // These are current-query preprocessing equations, unlike delegated
        // assertion grants owned by the predecessor model. Copy only live
        // entries into a bounded fresh map, not its historical capacity.
        let candidate_substitutions = self
            .recorded_var_substitutions
            .iter()
            .map(|(&from, &to)| (from, to))
            .collect();
        let mut classifications = DetHashMap::default();
        let mut is_ground = |root| {
            if self.external_stop_reason().is_some() || self.evaluation_stop_origin().is_some() {
                return None;
            }
            Some(
                *classifications
                    .entry(root)
                    .or_insert_with(|| !contains_quantifier(&self.ctx.terms, root)),
            )
        };
        let mut authored_ground = Vec::new();
        for &root in certification_roots {
            if is_ground(root)? {
                authored_ground.push(root);
            }
        }
        let mut ground_assumptions = self.last_assumptions.as_ref().map(|_| Vec::new());
        if let (Some(original), Some(ground)) = (&self.last_assumptions, &mut ground_assumptions) {
            for &root in original {
                if is_ground(root)? {
                    ground.push(root);
                }
            }
        }
        let mut present: DetHashSet<_> = authored_ground.iter().copied().collect();
        if let Some(assumptions) = &ground_assumptions {
            for &root in assumptions {
                if present.insert(root) {
                    authored_ground.push(root);
                }
            }
        }
        let saved_model_authority = GroundModelAuthority::take(self);
        let saved_model = CheckedModelInstallSnapshot::take(self);
        self.recorded_var_substitutions = candidate_substitutions;
        let saved_lane_pins = std::mem::take(&mut self.lane_model_pin_roots);
        let saved_pending_pins = std::mem::take(&mut self.pending_lane_model_pin_roots);
        let saved_lane_model = self.lane_ground_model.take();
        let saved_producer_outputs = GroundProofOutputs::take(self);
        let saved_interpolation = (
            self.interpolation.last_proof.take(),
            self.interpolation.leaf_sources.take(),
        );
        let saved_proof = ProofStateSnapshot::take_owned(self);
        let tracker = self.proof_tracker.fresh_window();
        let saved_tracker = std::mem::replace(&mut self.proof_tracker, tracker);
        let provenance = ProofProblemAssertionProvenance::passthrough(&authored_ground, &ground);
        let saved_provenance = self.proof_problem_assertion_provenance.replace(provenance);
        let saved_independent = self
            .independent_gate_authored_assertions
            .replace(authored_ground.clone());
        let saved_self_check = std::mem::replace(
            &mut self.self_check_authored_assertions,
            self.self_check.then_some(authored_ground),
        );
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, ground);
        let saved_assumptions = std::mem::replace(&mut self.last_assumptions, ground_assumptions);
        let saved_incr = self.incr_theory_state.take();
        let saved_bv = self.incr_bv_state.take();
        let saved_fp = self.incr_fp_state.take();
        let saved_fp_armed = std::mem::replace(&mut self.fp_persistent_armed, false);
        let saved_scoped_lanes = self.scoped_window_lanes.take();
        let saved_defer = std::mem::replace(&mut self.defer_model_validation, false);
        let saved_deadline = self.solve_deadline.get();
        let saved_lazy = self.dt_lazy_lane_suppressed_for_scoped_probe;
        self.last_result = None;
        self.last_model_validated = false;
        self.last_unknown_reason = None;
        self.last_unknown_origin = None;
        let solved = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| solve(self)));

        self.ctx.assertions = saved_assertions;
        self.last_assumptions = saved_assumptions;
        self.incr_theory_state = saved_incr;
        self.incr_bv_state = saved_bv;
        self.incr_fp_state = saved_fp;
        self.fp_persistent_armed = saved_fp_armed;
        self.scoped_window_lanes = saved_scoped_lanes;
        self.defer_model_validation = saved_defer;
        self.solve_deadline.set(saved_deadline);
        self.dt_lazy_lane_suppressed_for_scoped_probe = saved_lazy;
        self.independent_gate_authored_assertions = saved_independent;
        self.self_check_authored_assertions = saved_self_check;
        self.proof_problem_assertion_provenance = saved_provenance;
        self.proof_tracker = saved_tracker;
        saved_producer_outputs.restore(self);
        self.interpolation.last_proof = saved_interpolation.0;
        self.interpolation.leaf_sources = saved_interpolation.1;
        saved_proof.restore(self);
        // Ground-model grants cannot substitute for the original quantified
        // theorem. Keep candidate interpretation data, discard private grants.
        drop(GroundModelAuthority::take(self));
        // A ground model is only a candidate for the outer quantified query.
        self.last_sat_certificate = None;
        self.last_model_validated = false;
        let certified = match solved {
            Ok(Ok(SolveResult::Sat)) => {
                self.last_result = Some(SolveResult::Sat);
                self.last_unknown_reason = None;
                self.last_unknown_origin = None;
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| certify(self)))
            }
            Ok(_) => Ok(None),
            Err(payload) => Err(payload),
        };
        let declined = match certified {
            Ok(Some(evidence)) => return Some(evidence),
            outcome => outcome,
        };
        saved_model.restore(self);
        saved_model_authority.restore(self);
        self.lane_model_pin_roots = saved_lane_pins;
        self.pending_lane_model_pin_roots = saved_pending_pins;
        self.lane_ground_model = saved_lane_model;
        match declined {
            Ok(evidence) => evidence,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }
}
