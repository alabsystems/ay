// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Objective lower-bound reasoning and objective-guided search seeding for
//! `PbCdclSolver` (optimization mode): lower-bound cut plans, phase/activity
//! seeding from the objective, and LP/root bound estimation. Extracted from
//! `cdcl.rs`; these remain methods on [`super::PbCdclSolver`].

use super::*;
use crate::proof::ProofStep;
use crate::propagation::{Lit, PbPropagator, PropResult};
use crate::types::{PbConstraint, PbObjective};

impl PbCdclSolver {
    pub(super) fn log_objective_bound_update(&mut self, incumbent_model: &[bool]) -> bool {
        if self.proof_writer.is_none() {
            return true;
        }

        // Snapshot the soli id about to be superseded BEFORE it is overwritten
        // (ConstraintId is Copy). Only the LATEST soli id is ever read (by
        // try_log_objective_lower_bound_cut_proof at conclusion), so the
        // previous id has no remaining use once a tighter incumbent lands.
        let superseded_bound_id = self.last_objective_bound_proof_id;

        let mut assignment = String::new();
        for (index, &value) in incumbent_model.iter().enumerate() {
            if !assignment.is_empty() {
                assignment.push(' ');
            }
            if !value {
                assignment.push('~');
            }
            assignment.push('x');
            assignment.push_str(&(index + 1).to_string());
        }

        match self.log_proof_step(ProofStep::SolutionImproving(assignment.clone())) {
            Some(id) => {
                self.last_objective_bound_proof_id = Some(id);
                // Keep the witness for the `conclusion BOUNDS` upper-bound
                // hint: in unchecked-deletion mode the checker discounts
                // `soli`-logged solutions, so the conclusion must carry the
                // incumbent inline.
                self.last_objective_bound_witness = Some(assignment);
                // Superseded soli row: the new incumbent is STRICTLY tighter, so
                // `obj <= v_new-1` implies the previous `obj <= v_old-1` and the
                // checked deletion verifies. Only the latest soli id is read (at
                // conclusion), so the previous id is del-after-last-use; the DEL
                // follows the new soli line, so the implying constraint is in the
                // database when the checker verifies the deletion.
                if let Some(previous_id) = superseded_bound_id {
                    self.log_proof_step(ProofStep::Delete(previous_id));
                }
                true
            }
            None => {
                self.last_objective_bound_proof_id = None;
                self.last_objective_bound_witness = None;
                false
            }
        }
    }

    /// Emits the cutting-planes derivation of `objective >= optimum` into the
    /// proof stream.
    ///
    /// Returns [`ObjectiveFloorCutOutcome::Derived`] ONLY when every step of the
    /// plan was written, carrying the id of the closing contradiction row that
    /// the `conclusion BOUNDS` footer hints at. Any failure is reported
    /// distinctly so the caller fails closed instead of asserting a conclusion
    /// it cannot back up: [`ObjectiveFloorCutOutcome::Inexpressible`] when the
    /// planner declined (no positive combination of input rows proves the
    /// floor), [`ObjectiveFloorCutOutcome::EmissionFailed`] when a `pol` step or
    /// the closing addition against the incumbent bound could not be logged.
    /// Reporting success after a failed step is exactly the defect this guards
    /// against.
    pub(super) fn try_log_objective_lower_bound_cut_proof(
        &mut self,
        objective: &PbObjective,
        optimum: i128,
    ) -> ObjectiveFloorCutOutcome {
        if self.proof_writer.is_none() || optimum <= 0 {
            return ObjectiveFloorCutOutcome::Inexpressible;
        }
        let Some(upper_bound_id) = self.last_objective_bound_proof_id else {
            return ObjectiveFloorCutOutcome::Inexpressible;
        };
        let Some(plan) = self.build_objective_lower_bound_cut_plan(objective, optimum) else {
            return ObjectiveFloorCutOutcome::Inexpressible;
        };

        let mut lower_bound_id = None;
        for step in plan.steps {
            let step_id = match step {
                ObjectiveLowerBoundCutStep::Constraint {
                    constraint_id,
                    multiplier,
                } => {
                    let mut step_id = constraint_id;
                    if multiplier > 1 {
                        let Some(multiplied_id) =
                            self.log_proof_step(ProofStep::Multiply(step_id, multiplier))
                        else {
                            return ObjectiveFloorCutOutcome::EmissionFailed;
                        };
                        step_id = multiplied_id;
                    }
                    step_id
                }
                ObjectiveLowerBoundCutStep::Polynomial(expression) => {
                    let Some(polynomial_id) =
                        self.log_proof_step(ProofStep::Polynomial(expression))
                    else {
                        return ObjectiveFloorCutOutcome::EmissionFailed;
                    };
                    polynomial_id
                }
            };

            lower_bound_id = match lower_bound_id {
                Some(accumulated_id) => {
                    let Some(sum_id) =
                        self.log_proof_step(ProofStep::Addition(accumulated_id, step_id))
                    else {
                        return ObjectiveFloorCutOutcome::EmissionFailed;
                    };
                    Some(sum_id)
                }
                None => Some(step_id),
            };
        }

        let Some(lower_bound_id) = lower_bound_id else {
            return ObjectiveFloorCutOutcome::Inexpressible;
        };
        // floor (`obj >= optimum`) + soli row (`obj <= optimum-1`) sums to a
        // contradiction; its id is the conclusion's lower-bound hint (a
        // contradiction syntactically implies any bound).
        match self.log_proof_step(ProofStep::Addition(lower_bound_id, upper_bound_id)) {
            Some(contradiction_id) => ObjectiveFloorCutOutcome::Derived(contradiction_id),
            None => ObjectiveFloorCutOutcome::EmissionFailed,
        }
    }

    fn build_objective_lower_bound_cut_plan(
        &self,
        objective: &PbObjective,
        optimum: i128,
    ) -> Option<ObjectiveLowerBoundCutPlan> {
        if let Some(plan) = self.build_direct_objective_lower_bound_cut_plan(objective, optimum) {
            return Some(plan);
        }
        self.build_cardinality_objective_lower_bound_cut_plan(objective, optimum)
    }

    fn build_direct_objective_lower_bound_cut_plan(
        &self,
        objective: &PbObjective,
        optimum: i128,
    ) -> Option<ObjectiveLowerBoundCutPlan> {
        let mut remaining_coefficients = objective_positive_linear_coefficients(objective)?;
        let mut selected_steps = Vec::new();
        let mut proven_lower_bound = 0i128;

        for (constraint, &constraint_id) in self
            .constraints
            .iter()
            .take(self.proof_input_constraint_count)
            .zip(
                self.constraint_ids
                    .iter()
                    .take(self.proof_input_constraint_count),
            )
        {
            if proven_lower_bound >= optimum {
                break;
            }

            let Some(candidate) =
                objective_lower_bound_candidate(constraint, &remaining_coefficients)
            else {
                continue;
            };

            let required = optimum.checked_sub(proven_lower_bound)?;
            let desired_multiplier = ceil_div_positive(required, candidate.degree)?;
            let multiplier = candidate.max_multiplier.min(desired_multiplier);
            if multiplier <= 0 {
                continue;
            }

            for (lit, coeff) in candidate.coefficients {
                let remaining = remaining_coefficients.get_mut(&lit)?;
                *remaining = remaining.checked_sub(coeff.checked_mul(multiplier)?)?;
            }
            proven_lower_bound =
                proven_lower_bound.checked_add(candidate.degree.checked_mul(multiplier)?)?;
            selected_steps.push(ObjectiveLowerBoundCutStep::Constraint {
                constraint_id,
                multiplier,
            });
        }

        (proven_lower_bound >= optimum).then_some(ObjectiveLowerBoundCutPlan {
            steps: selected_steps,
        })
    }

    fn build_cardinality_objective_lower_bound_cut_plan(
        &self,
        objective: &PbObjective,
        optimum: i128,
    ) -> Option<ObjectiveLowerBoundCutPlan> {
        let objective_coefficients = objective_positive_linear_coefficients(objective)?;

        for (constraint, &constraint_id) in self
            .constraints
            .iter()
            .take(self.proof_input_constraint_count)
            .zip(
                self.constraint_ids
                    .iter()
                    .take(self.proof_input_constraint_count),
            )
        {
            let Some(candidate) = cardinality_objective_lower_bound_candidate(
                constraint,
                constraint_id,
                &objective_coefficients,
            ) else {
                continue;
            };
            if candidate.degree < optimum {
                continue;
            }

            return Some(ObjectiveLowerBoundCutPlan {
                steps: vec![ObjectiveLowerBoundCutStep::Polynomial(candidate.expression)],
            });
        }

        None
    }

    pub(super) fn install_root_assignments(&mut self) {
        let mut pending: Vec<Lit> = self
            .fixed_literals
            .iter()
            .map(|(&var, &value)| if value { var as Lit } else { -(var as Lit) })
            .collect();
        pending.sort_unstable_by_key(|lit| lit.unsigned_abs());
        pending.reverse();

        while let Some(lit) = pending.pop() {
            match self.propagator.assign_literal(lit, 0) {
                PropResult::Ok => {}
                PropResult::Propagated(next_lit, _, _) => {
                    let var = next_lit.unsigned_abs();
                    let value = next_lit > 0;
                    if let Some(previous) = self.fixed_literals.insert(var, value) {
                        debug_assert_eq!(
                            previous, value,
                            "root assignment propagation must not contradict a fixed literal"
                        );
                    } else {
                        pending.push(next_lit);
                    }
                }
                PropResult::Conflict(_, _) => {
                    debug_assert!(
                        false,
                        "preprocessed instance must not conflict on root assignments"
                    );
                    self.interrupted = true;
                    return;
                }
                PropResult::Interrupted => unreachable!(
                    "non-interruptible root assignment installation must not interrupt"
                ),
            }
        }
    }

    pub(super) fn seed_saved_phase_from_objective(&mut self, objective: &PbObjective) {
        let mut net_coeff_by_var: HashMap<u32, i128> = HashMap::new();
        for term in &objective.terms {
            let [lit] = term.lits.as_slice() else {
                continue;
            };
            let contribution = if lit.negated { -term.coeff } else { term.coeff };
            *net_coeff_by_var.entry(lit.var).or_insert(0) += contribution;
        }

        for (var, net_coeff) in net_coeff_by_var {
            let idx = var as usize;
            if idx >= self.saved_phase.len() {
                continue;
            }
            if net_coeff < 0 {
                self.saved_phase[idx] = true;
            } else if net_coeff > 0 {
                self.saved_phase[idx] = false;
            }
        }
    }

    pub(super) fn seed_activity_from_objective(&mut self, objective: &PbObjective) {
        let mut objective_activity = vec![0.0f64; self.activity.len()];
        let mut max_activity = 0.0f64;

        for term in &objective.terms {
            let [lit] = term.lits.as_slice() else {
                continue;
            };
            let idx = lit.var as usize;
            if idx >= objective_activity.len() || term.coeff == 0 {
                continue;
            }

            objective_activity[idx] += (term.coeff as f64).abs();
            max_activity = max_activity.max(objective_activity[idx]);
        }

        if max_activity <= 0.0 {
            return;
        }

        for (idx, objective_score) in objective_activity.into_iter().enumerate().skip(1) {
            if objective_score > 0.0 {
                self.activity[idx] += objective_score / max_activity;
            }
        }
        self.rebuild_heap();
    }

    pub(super) fn seed_search_from_objective_bound_constraint(
        &mut self,
        constraint: &PbConstraint,
    ) {
        if constraint.rel != PbRel::Ge {
            return;
        }

        let mut truth_pressure_by_var: HashMap<u32, i128> = HashMap::new();
        let mut activity_by_var = vec![0.0f64; self.activity.len()];
        let mut max_activity = 0.0f64;

        for term in &constraint.terms {
            let [lit] = term.lits.as_slice() else {
                return;
            };
            if term.coeff == 0 {
                continue;
            }

            let idx = lit.var as usize;
            if idx >= self.activity.len() {
                continue;
            }

            let variable_true_delta = if lit.negated { -term.coeff } else { term.coeff };
            *truth_pressure_by_var.entry(lit.var).or_insert(0) += variable_true_delta;

            let activity = (term.coeff.abs() as f64).max(0.0);
            activity_by_var[idx] += activity;
            max_activity = max_activity.max(activity_by_var[idx]);
        }

        if truth_pressure_by_var.is_empty() || max_activity <= 0.0 {
            return;
        }

        for (var, truth_pressure) in truth_pressure_by_var {
            let idx = var as usize;
            if idx >= self.saved_phase.len() {
                continue;
            }
            if truth_pressure > 0 {
                self.saved_phase[idx] = true;
            } else if truth_pressure < 0 {
                self.saved_phase[idx] = false;
            }
        }

        for (idx, bound_activity) in activity_by_var.into_iter().enumerate().skip(1) {
            if bound_activity > 0.0 {
                self.activity[idx] += bound_activity / max_activity;
            }
        }
        self.rebuild_heap();
    }

    pub(super) fn seed_activity_from_objective_bound_neighborhood(
        &mut self,
        bound_constraint: &PbConstraint,
    ) {
        if bound_constraint.rel != PbRel::Ge {
            return;
        }

        let mut bound_vars = HashSet::new();
        for term in &bound_constraint.terms {
            let [lit] = term.lits.as_slice() else {
                return;
            };
            if term.coeff != 0 && (lit.var as usize) < self.activity.len() {
                bound_vars.insert(lit.var);
            }
        }
        if bound_vars.is_empty() {
            return;
        }

        let mut activity_by_var = vec![0.0f64; self.activity.len()];
        let mut max_activity = 0.0f64;
        for constraint in &self.constraints {
            if constraint.terms.is_empty()
                || constraint.terms.len() > OBJECTIVE_BOUND_NEIGHBOR_MAX_ROW_TERMS
            {
                continue;
            }

            let mut touches_bound = false;
            for term in &constraint.terms {
                let [lit] = term.lits.as_slice() else {
                    touches_bound = false;
                    break;
                };
                if bound_vars.contains(&lit.var) {
                    touches_bound = true;
                }
            }
            if !touches_bound {
                continue;
            }

            for term in &constraint.terms {
                let [lit] = term.lits.as_slice() else {
                    continue;
                };
                let idx = lit.var as usize;
                if idx >= activity_by_var.len() || term.coeff == 0 {
                    continue;
                }

                activity_by_var[idx] += term.coeff.abs() as f64;
                max_activity = max_activity.max(activity_by_var[idx]);
            }
        }

        if max_activity <= 0.0 {
            return;
        }

        for (idx, neighbor_activity) in activity_by_var.into_iter().enumerate().skip(1) {
            if neighbor_activity > 0.0 {
                self.activity[idx] +=
                    OBJECTIVE_BOUND_NEIGHBOR_ACTIVITY_SCALE * neighbor_activity / max_activity;
            }
        }
        self.rebuild_heap();
    }

    pub(super) fn objective_lower_bound_from_solver_state(
        &self,
        objective: &PbObjective,
        should_stop: &dyn Fn() -> bool,
    ) -> Option<i128> {
        objective_lower_bound_with_fixed_literals(
            &self.constraints,
            objective,
            &self.fixed_literals,
            should_stop,
        )
    }

    /// Sound LP-relaxation lower bound on `objective` over the solver's
    /// preprocessed `>=` rows ([`Self::constraints`]), residualized for the
    /// preprocessing-fixed literals exactly as
    /// [`objective_lower_bound_with_fixed_literals`] does.
    ///
    /// Returns `Some(lb)` with the guarantee `lb <= IntOpt` (the integer optimum
    /// of the full instance) or `None` when no sound LP bound could be produced
    /// (empty residual objective, non-linear/negative objective terms, size or
    /// arithmetic guard, or interrupted). A `None` is always safe — it merely
    /// fails to tighten the optimality floor.
    ///
    /// # Soundness of the residualization
    ///
    /// Let `F` be the set of preprocessing-fixed literals (forced in *every*
    /// model of the instance) and `fixed_bound` the sum of objective coeffs
    /// already paid by `F`. Splitting the objective as
    /// `objective = fixed_bound + residual_objective`, any integer-feasible `x*`
    /// of the full instance agrees with `F` and satisfies the preprocessed rows
    /// (preprocessing is satisfiability-preserving), so it is feasible for the LP
    /// over [`Self::constraints`] restricted to `[0,1]^n`. Hence
    /// `objective(x*) = fixed_bound + residual_objective(x*)
    ///               >= fixed_bound + ceil(LP*_residual)`,
    /// because `ceil(LP*_residual) <= residual_objective(x*)` by LP weak duality
    /// (`lp_lower_bound` returns `ceil(LP*)`). Therefore
    /// `fixed_bound + lp_lower_bound(residual_objective)` is a valid lower bound.
    /// This mirrors the structural bound's `fixed_bound + residual_bound` exactly,
    /// reusing the same `residual_positive_objective_after_fixed_literals` helper
    /// so the residual can never be computed inconsistently.
    ///
    /// `should_stop` is polled by the LP so the outer deadline can abort it; an
    /// interrupted/partial LP bound is still sound (it comes from a dual-feasible
    /// vertex), just possibly looser. In addition to the caller's `should_stop`, an
    /// internal wall-clock backstop ([`ROOT_LP_BOUND_TIME_BUDGET`]) bounds the LP
    /// even when the caller passes a no-op stop (e.g. the non-interruptible
    /// `solve_optimize` path used in tests), so a single root LP bound can never
    /// monopolize the solver on a pathological instance whose exact-rational
    /// simplex grows large.
    /// `incumbent_value` (the best objective value in hand, when known) is an
    /// **early-exit target**: the LP stops tightening (skips remaining cut
    /// rounds) the moment its sound floor reaches it, because `floor <= IntOpt
    /// <= incumbent` means such a floor already proves the incumbent optimal
    /// and no larger floor can matter to the caller's `floor >= best_value`
    /// check (see [`crate::optimize::lp_bound::lp_lower_bound_with_target`]).
    /// Passing `None` keeps the full tightening behaviour.
    pub(super) fn lp_objective_lower_bound_at_root(
        &self,
        objective: &PbObjective,
        incumbent_value: Option<i128>,
        should_stop: &dyn Fn() -> bool,
    ) -> Option<i128> {
        // Match the structural-bound gating: skip while a proof is being written
        // so the proof path is unchanged.
        if self.proof_writer.is_some() {
            return None;
        }

        // Combine the caller's stop with an internal wall-clock backstop. Aborting
        // the LP at any point is sound (it returns the bound from the last
        // dual-feasible vertex, possibly looser), so the backstop only affects
        // tightness, never soundness. The backstop is DEADLINE-PROPORTIONAL when
        // the caller threaded a solve deadline ([`PbCdclSolver::set_solve_deadline`]):
        // `min(ROOT_LP_BOUND_TIME_BUDGET, remaining / ROOT_LP_BOUND_DEADLINE_FRACTION)`,
        // so a short-budget optimize call no longer spends a flat 5s on the LP floor.
        let started = std::time::Instant::now();
        let budget = self.root_lp_budget(started);
        let stop =
            || should_stop() || started.elapsed() >= budget || ay_sys::process_memory_exceeded();

        if self.fixed_literals.is_empty() {
            return crate::optimize::lp_bound::lp_lower_bound_with_target(
                objective,
                &self.constraints,
                self.num_vars,
                incumbent_value,
                &stop,
            );
        }

        let (fixed_bound, residual_objective) =
            residual_positive_objective_after_fixed_literals(objective, &self.fixed_literals)?;
        // The caller's target is on the FULL objective; the residual LP proves
        // `fixed_bound + residual_lb`, so its share of the target is
        // `incumbent - fixed_bound`. On subtraction overflow just drop the
        // target (full tightening; never a wrong exit).
        let residual_target =
            incumbent_value.and_then(|incumbent| incumbent.checked_sub(fixed_bound));
        let residual_lb = crate::optimize::lp_bound::lp_lower_bound_with_target(
            &residual_objective,
            &self.constraints,
            self.num_vars,
            residual_target,
            &stop,
        )?;
        fixed_bound.checked_add(residual_lb)
    }

    pub(super) fn replace_active_optimization_bound(&mut self, start: usize, end: usize) {
        if let Some((old_start, old_end)) = self.active_optimization_bound_range.take() {
            for cid in old_start..old_end {
                self.propagator.deactivate_constraint_lazy(cid);
                // Mirror the deactivation into the learned region (bound rows
                // live there — flat-cid convention) so constraint_by_index,
                // reduce_db, and the SAT-side model-validity gates all stop
                // seeing the superseded bound row. The proof-side `del` of the
                // superseded soli row was already emitted by
                // log_objective_bound_update.
                if let Some(learned_idx) = cid.checked_sub(self.constraints.len()) {
                    if learned_idx < self.learned_active.len() {
                        self.learned_active[learned_idx] = false;
                    }
                }
            }
        }

        if start < end {
            self.active_optimization_bound_range = Some((start, end));
        }
    }

    /// Replays VeriPB's own check for the `rup >= 1 ;` step that closes an
    /// optimality proof: does unit propagation from the empty assignment reach a
    /// conflict on the constraint database VeriPB will hold at that point?
    ///
    /// That database is the imported input rows (`f N ;`) plus the
    /// objective-improving row `objective <= optimum - 1` that VeriPB derives
    /// from the `soli` step — the intermediate search steps are suppressed in
    /// optimization mode ([`PbCdclSolver::suppress_optimization_intermediate_proof_steps`]),
    /// so nothing else is in it. This method rebuilds exactly that set in a
    /// *fresh* propagator (never the solver's own, which also holds learned
    /// lemmas VeriPB has never seen and which would make the replay stronger
    /// than the checker) and propagates to fixpoint.
    ///
    /// Deliberately conservative, since a wrong `true` here is a proof VeriPB
    /// rejects:
    ///
    /// * the whole input formula must have been linear
    ///   ([`PbCdclSolver::proof_input_rows_are_linear`]), because the rows in
    ///   `self.constraints` are already normalized and a product term dropped by
    ///   that normalization would leave a row strictly stronger than the one
    ///   VeriPB imported;
    /// * a row whose magnitudes could saturate the normalizer's arithmetic is
    ///   skipped;
    /// * the objective must be linear, and the improving row must be a real
    ///   (non-trivial) constraint;
    /// * running out of the propagation budget answers `false`.
    ///
    /// Dropping rows only ever weakens propagation, and propagation is monotone:
    /// a conflict found from a subset of VeriPB's database is a conflict VeriPB
    /// finds too. Answering `false` only ever makes the caller
    /// ([`PbCdclSolver::conclude_opt_proof`]) fail closed onto the certified
    /// OPT-LIN route, so every error direction is the safe one.
    pub(super) fn objective_improvement_unit_propagates_to_conflict(
        &self,
        objective: &PbObjective,
        optimum: i128,
    ) -> bool {
        if !self.proof_input_rows_are_linear {
            return false;
        }
        if !objective.terms.iter().all(|term| term.lits.len() == 1) {
            return false;
        }
        let Some(improvement_row) = build_upper_bound_constraint(objective, optimum) else {
            return false;
        };
        if !is_replayable_linear_row(&improvement_row) {
            return false;
        }

        let mut propagator = PbPropagator::new();
        for constraint in self
            .constraints
            .iter()
            .take(self.proof_input_constraint_count)
            .filter(|constraint| is_replayable_linear_row(constraint))
        {
            propagator.add_from_pb_constraint(constraint);
        }
        if propagator
            .add_from_pb_constraint(&improvement_row)
            .is_none()
        {
            // Trivially satisfied improving row: it cannot participate in a
            // conflict, and the input rows alone are satisfiable (we have an
            // incumbent), so there is nothing to find.
            return false;
        }

        propagation_reaches_conflict(&mut propagator)
    }
}

/// Work budget, in constraint visits, for the RUP replay
/// ([`PbCdclSolver::objective_improvement_unit_propagates_to_conflict`]).
/// Running out answers "no conflict", which only ever makes the caller fail
/// closed.
const RUP_REPLAY_WORK_BUDGET: u64 = 50_000_000;

/// Whether `constraint` can be handed to the linear propagator for the RUP
/// replay without changing its meaning.
///
/// Rejects non-linear (product) terms — the normalizer silently *drops* those,
/// which strengthens a `>=` row and could manufacture a conflict VeriPB does not
/// see — and magnitudes large enough for the normalizer's saturating degree
/// arithmetic to lose information.
fn is_replayable_linear_row(constraint: &PbConstraint) -> bool {
    let mut magnitude: i128 = constraint.rhs.checked_abs().unwrap_or(i128::MAX);
    for term in &constraint.terms {
        if term.lits.len() != 1 {
            return false;
        }
        let Some(coeff_magnitude) = term.coeff.checked_abs() else {
            return false;
        };
        let Some(next) = magnitude.checked_add(coeff_magnitude) else {
            return false;
        };
        magnitude = next;
    }
    true
}

/// Propagates `propagator` to fixpoint from its current (empty) assignment and
/// reports whether a conflict is reached.
///
/// Uses [`PbPropagator::propagate`], the full-scan form documented as the one
/// that finds *all* implications, and re-scans after every assignment until a
/// complete pass is quiet. The solver's own `propagate_all` is the faster
/// event-driven form, but an event-driven pass may stop short of the fixpoint —
/// harmless for search (it just means more decisions) and not harmless here,
/// where a missed implication turns a genuinely checkable `rup >= 1 ;` into an
/// unnecessary fail-closed UNKNOWN.
///
/// The scan is charged against [`RUP_REPLAY_WORK_BUDGET`]; exhausting it reports
/// "no conflict", the fail-closed answer.
fn propagation_reaches_conflict(propagator: &mut PbPropagator) -> bool {
    let mut budget = RUP_REPLAY_WORK_BUDGET;

    loop {
        let scan_cost = propagator.num_constraints() as u64;
        let Some(remaining) = budget.checked_sub(scan_cost.max(1)) else {
            return false;
        };
        budget = remaining;

        match propagator.propagate() {
            PropResult::Conflict(_, _) => return true,
            PropResult::Interrupted | PropResult::Ok => return false,
            PropResult::Propagated(lit, _, _) => match propagator.assign_literal(lit, 0) {
                PropResult::Conflict(_, _) => return true,
                PropResult::Interrupted => return false,
                // Any further implication this assignment triggered is re-found
                // by the next full scan; nothing is lost by ignoring it here.
                PropResult::Ok | PropResult::Propagated(_, _, _) => {}
            },
        }
    }
}

#[cfg(test)]
mod rup_replay_tests;
