// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transitive Relation Projection (TRP)
//!
//! TRP combines Model-Based Projection (MBP) with recurrence analysis to compute
//! transitive projections of loop bodies. This enables TRL to learn relations
//! that summarize multiple loop iterations.
//!
//! # Algorithm reference (LoAT `trp.cpp:276-297`)
//!
//! ```text
//! TRP::compute(loop, model):
//!   // Check if loop is trivially transitive
//!   if SAT(intermediate(loop) ∧ intermediate(loop) ∧ ¬loop) == UNSAT:
//!     return loop  // Identity transition
//!
//!   pre = MBP(loop, model, keep_pre_vars)    // Project out post-vars
//!   step = recurrent(loop, model)            // Recurrence analysis
//!   post = MBP(loop, model, keep_post_vars)  // Project out pre-vars
//!   return simplify(pre ∧ step ∧ post)
//! ```
//!
//! # Recurrence Analysis
//!
//! For each variable update pattern, emit constraints for n iterations:
//!
//! - **Constant delta**: `x' = x + c` → `x_n - x_0 = c*n`
//! - **Bounds**: Upper/lower bounds scale with n
//! - **Divisibility**: `x mod d = 0` preserved across iterations
//!
//! # References
//!
//! - LoAT implementation: `reference/loat-src/src/lib/trp/trp.cpp`
//! - TRL paper: `papers/CADE2025-Infinite-State-Model-Checking-by-Learning-Transitive-Relations.pdf`
//! - Issue: #1176

mod recurrence_helpers;

use crate::mbp::Mbp;
use crate::recurrence::{analyze_transition, ClosedForm, TriangularSystem};
use crate::{ChcExpr, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use num_rational::Rational64;
use std::sync::atomic::{AtomicUsize, Ordering};
#[cfg(test)]
use std::sync::Mutex;

/// TRP configuration options.
///
/// Internal technique toggles — not exposed to callers.
#[derive(Debug, Clone)]
pub(crate) struct TrpConfig {
    pub(crate) recurrent_bounds: bool,
    pub(crate) recurrent_exps: bool,
}

impl Default for TrpConfig {
    fn default() -> Self {
        Self {
            recurrent_bounds: true,
            recurrent_exps: true,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AcceleratedSummaryAcceleratedRowKind {
    ConstantDelta,
    PolynomialClosedForm,
    PreservedDifference,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AcceleratedSummaryFamilySummaryKind {
    AffineConstantDelta,
    PolynomialClosedForm,
    AffinePreservedDifference,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct AcceleratedSummaryTrpFamilySummaryStatistics {
    pub(crate) family_summary_candidates: u64,
    pub(crate) affine_constant_delta_family_summaries: u64,
    pub(crate) polynomial_closed_form_family_summaries: u64,
    pub(crate) affine_preserved_difference_family_summaries: u64,
}

#[cfg(test)]
pub(crate) const ACCELERATED_SUMMARY_TRP_ACCELERATED_ROW_CANDIDATE_SCHEMA: &str =
    "trp-accelerated-summary-accelerated-row-candidate-v1";

#[cfg(test)]
pub(crate) const ACCELERATED_SUMMARY_TRP_FAMILY_SUMMARY_CANDIDATE_SCHEMA: &str =
    "trp-accelerated-summary-family-summary-candidate-v1";

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AcceleratedSummaryTrpAcceleratedRowCandidate {
    pub(crate) schema: &'static str,
    pub(crate) local_index: usize,
    pub(crate) kind: AcceleratedSummaryAcceleratedRowKind,
    pub(crate) row: ChcExpr,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AcceleratedSummaryTrpFamilySummaryCandidate {
    pub(crate) schema: &'static str,
    pub(crate) local_index: usize,
    pub(crate) kind: AcceleratedSummaryFamilySummaryKind,
    pub(crate) source_row: ChcExpr,
}

#[derive(Debug, Default)]
struct AcceleratedSummaryArtifactHookCounters {
    accelerated_row_candidates: AtomicUsize,
    family_summary_candidates: AtomicUsize,
    affine_constant_delta_family_summaries: AtomicUsize,
    polynomial_closed_form_family_summaries: AtomicUsize,
    affine_preserved_difference_family_summaries: AtomicUsize,
    #[cfg(test)]
    accelerated_row_candidate_records: Mutex<Vec<AcceleratedSummaryTrpAcceleratedRowCandidate>>,
    #[cfg(test)]
    family_summary_candidate_records: Mutex<Vec<AcceleratedSummaryTrpFamilySummaryCandidate>>,
}

impl AcceleratedSummaryArtifactHookCounters {
    fn record_accelerated_row_candidate(
        &self,
        kind: AcceleratedSummaryAcceleratedRowKind,
        row: &ChcExpr,
    ) {
        #[cfg(test)]
        {
            let mut records = self
                .accelerated_row_candidate_records
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());

            let local_index = records.len();
            records.push(AcceleratedSummaryTrpAcceleratedRowCandidate {
                schema: ACCELERATED_SUMMARY_TRP_ACCELERATED_ROW_CANDIDATE_SCHEMA,
                local_index,
                kind,
                row: row.clone(),
            });

            self.accelerated_row_candidates
                .store(records.len(), Ordering::Relaxed);
        }

        #[cfg(not(test))]
        {
            let _ = kind;
            let _ = row;
            self.accelerated_row_candidates
                .fetch_add(1, Ordering::Relaxed);
        }
    }

    fn record_family_summary_candidate(
        &self,
        kind: AcceleratedSummaryFamilySummaryKind,
        source_row: &ChcExpr,
    ) {
        self.family_summary_candidates
            .fetch_add(1, Ordering::Relaxed);
        match kind {
            AcceleratedSummaryFamilySummaryKind::AffineConstantDelta => {
                self.affine_constant_delta_family_summaries
                    .fetch_add(1, Ordering::Relaxed);
            }
            AcceleratedSummaryFamilySummaryKind::PolynomialClosedForm => {
                self.polynomial_closed_form_family_summaries
                    .fetch_add(1, Ordering::Relaxed);
            }
            AcceleratedSummaryFamilySummaryKind::AffinePreservedDifference => {
                self.affine_preserved_difference_family_summaries
                    .fetch_add(1, Ordering::Relaxed);
            }
        }

        #[cfg(test)]
        {
            let mut records = self
                .family_summary_candidate_records
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());

            let local_index = records.len();
            records.push(AcceleratedSummaryTrpFamilySummaryCandidate {
                schema: ACCELERATED_SUMMARY_TRP_FAMILY_SUMMARY_CANDIDATE_SCHEMA,
                local_index,
                kind,
                source_row: source_row.clone(),
            });
        }

        #[cfg(not(test))]
        {
            let _ = source_row;
        }
    }

    #[cfg(test)]
    fn family_summary_statistics(&self) -> AcceleratedSummaryTrpFamilySummaryStatistics {
        AcceleratedSummaryTrpFamilySummaryStatistics {
            family_summary_candidates: self.family_summary_candidates.load(Ordering::Relaxed)
                as u64,
            affine_constant_delta_family_summaries: self
                .affine_constant_delta_family_summaries
                .load(Ordering::Relaxed) as u64,
            polynomial_closed_form_family_summaries: self
                .polynomial_closed_form_family_summaries
                .load(Ordering::Relaxed)
                as u64,
            affine_preserved_difference_family_summaries: self
                .affine_preserved_difference_family_summaries
                .load(Ordering::Relaxed)
                as u64,
        }
    }

    #[cfg(test)]
    fn accelerated_row_candidates(&self) -> usize {
        self.accelerated_row_candidates.load(Ordering::Relaxed)
    }

    #[cfg(test)]
    fn family_summary_candidates(&self) -> usize {
        self.family_summary_candidates.load(Ordering::Relaxed)
    }

    #[cfg(test)]
    fn family_summary_kind_candidates(&self, kind: AcceleratedSummaryFamilySummaryKind) -> usize {
        match kind {
            AcceleratedSummaryFamilySummaryKind::AffineConstantDelta => self
                .affine_constant_delta_family_summaries
                .load(Ordering::Relaxed),
            AcceleratedSummaryFamilySummaryKind::PolynomialClosedForm => self
                .polynomial_closed_form_family_summaries
                .load(Ordering::Relaxed),
            AcceleratedSummaryFamilySummaryKind::AffinePreservedDifference => self
                .affine_preserved_difference_family_summaries
                .load(Ordering::Relaxed),
        }
    }

    #[cfg(test)]
    fn accelerated_row_candidate_records(
        &self,
    ) -> Vec<AcceleratedSummaryTrpAcceleratedRowCandidate> {
        self.accelerated_row_candidate_records
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
    }

    #[cfg(test)]
    fn family_summary_candidate_records(&self) -> Vec<AcceleratedSummaryTrpFamilySummaryCandidate> {
        self.family_summary_candidate_records
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
    }
}

/// Transitive Relation Projection engine
pub(crate) struct Trp {
    /// MBP engine for projection
    mbp: Mbp,
    /// Configuration
    config: TrpConfig,
    /// State variables (pre-state form)
    state_vars: Vec<ChcVar>,
    /// Iteration count variable for closed forms
    n_var: ChcVar,
    /// Private accelerated-summary artifact hook counters for closed-form accelerated rows.
    accelerated_summary_artifact_hooks: AcceleratedSummaryArtifactHookCounters,
}

impl Trp {
    /// Create a new TRP engine for the given state variables.
    ///
    /// # Arguments
    /// * `state_vars` - The state variables (pre-state form, without `_next` suffix)
    pub(crate) fn new(state_vars: Vec<ChcVar>) -> Self {
        Self {
            mbp: Mbp::new(),
            config: TrpConfig::default(),
            state_vars,
            n_var: ChcVar::new("__trp_n", ChcSort::Int),
            accelerated_summary_artifact_hooks: AcceleratedSummaryArtifactHookCounters::default(),
        }
    }

    fn record_accelerated_summary_accelerated_row_candidate(
        &self,
        kind: AcceleratedSummaryAcceleratedRowKind,
        row: &ChcExpr,
    ) {
        self.accelerated_summary_artifact_hooks
            .record_accelerated_row_candidate(kind, row);
    }

    fn record_accelerated_summary_family_summary_candidate(
        &self,
        kind: AcceleratedSummaryFamilySummaryKind,
        source_row: &ChcExpr,
    ) {
        self.accelerated_summary_artifact_hooks
            .record_family_summary_candidate(kind, source_row);
    }

    #[cfg(test)]
    pub(crate) fn accelerated_summary_family_summary_statistics(
        &self,
    ) -> AcceleratedSummaryTrpFamilySummaryStatistics {
        self.accelerated_summary_artifact_hooks
            .family_summary_statistics()
    }

    #[cfg(test)]
    fn accelerated_summary_accelerated_row_candidates(&self) -> usize {
        self.accelerated_summary_artifact_hooks
            .accelerated_row_candidates()
    }

    #[cfg(test)]
    fn accelerated_summary_family_summary_candidates(&self) -> usize {
        self.accelerated_summary_artifact_hooks
            .family_summary_candidates()
    }

    #[cfg(test)]
    fn accelerated_summary_family_summary_kind_candidates(
        &self,
        kind: AcceleratedSummaryFamilySummaryKind,
    ) -> usize {
        self.accelerated_summary_artifact_hooks
            .family_summary_kind_candidates(kind)
    }

    #[cfg(test)]
    fn accelerated_summary_accelerated_row_candidate_records(
        &self,
    ) -> Vec<AcceleratedSummaryTrpAcceleratedRowCandidate> {
        self.accelerated_summary_artifact_hooks
            .accelerated_row_candidate_records()
    }

    #[cfg(test)]
    fn accelerated_summary_family_summary_candidate_records(
        &self,
    ) -> Vec<AcceleratedSummaryTrpFamilySummaryCandidate> {
        self.accelerated_summary_artifact_hooks
            .family_summary_candidate_records()
    }

    /// Compute transitive projection of a loop body.
    ///
    /// Given a loop body formula and a satisfying model, computes a formula
    /// that summarizes the effect of multiple iterations.
    ///
    /// # Arguments
    /// * `loop_body` - The loop body as a transition relation (pre → post)
    /// * `model` - A model satisfying the loop body
    ///
    /// # Returns
    /// * `Some(formula)` - A transitive projection formula
    /// * `None` - If TRP cannot be computed (e.g., non-linear recurrence)
    pub(crate) fn compute(
        &self,
        loop_body: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        // Step 1: Check if loop is trivially transitive (identity)
        // This would require SMT check which is expensive; skip for now
        // and always attempt full TRP

        // Step 2: Project to keep only pre-vars (eliminate post-vars)
        let pre_vars: FxHashSet<ChcVar> = self.state_vars.iter().cloned().collect();
        let post_vars: Vec<ChcVar> = self
            .state_vars
            .iter()
            .map(|v| ChcVar::new(format!("{}_next", v.name), v.sort.clone()))
            .collect();

        // MBP to eliminate post-vars, keeping pre-vars
        let pre_formula = self.mbp.project(loop_body, &post_vars, model);

        // Step 3: Recurrence analysis
        let step_formula = self.recurrent(loop_body, model);

        // Step 4: Project to keep only post-vars (eliminate pre-vars)
        let pre_vars_vec: Vec<ChcVar> = pre_vars.into_iter().collect();
        let post_formula = self.mbp.project(loop_body, &pre_vars_vec, model);

        // Step 5: Combine: pre ∧ step ∧ post
        let mut conjuncts = Vec::new();

        // Only add non-trivial formulas
        if !matches!(pre_formula, ChcExpr::Bool(true)) {
            conjuncts.push(pre_formula);
        }
        if !matches!(step_formula, ChcExpr::Bool(true)) {
            conjuncts.push(step_formula);
        }
        if !matches!(post_formula, ChcExpr::Bool(true)) {
            conjuncts.push(post_formula);
        }

        // If we have useful constraints, return them
        if conjuncts.is_empty() {
            // Nothing learned - return None to indicate TRP couldn't help
            None
        } else {
            // Keep n as a free variable (Golem TRL.cc:296-351).
            // The iteration count n parameterizes the learned relation so a single
            // use can represent n > 0 loop iterations. Without this, the learned
            // relation degenerates to a single-step transition (n=1) and TRL
            // provides no acceleration over plain BMC.
            let n_positive = ChcExpr::gt(ChcExpr::var(self.n_var.clone()), ChcExpr::int(0));
            conjuncts.push(n_positive);
            let combined = ChcExpr::and_all(conjuncts);

            // Only return if we got something meaningful
            if matches!(combined, ChcExpr::Bool(true)) {
                None
            } else {
                Some(combined)
            }
        }
    }

    /// Perform recurrence analysis on the loop body.
    ///
    /// Analyzes update patterns and emits constraints for n iterations.
    fn recurrent(&self, loop_body: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> ChcExpr {
        let mut result_lits: Vec<ChcExpr> = Vec::new();

        // Try to analyze the transition as a triangular system
        let var_names: Vec<String> = self.state_vars.iter().map(|v| v.name.clone()).collect();

        // Track which variables have closed-form solutions to avoid duplicate constraints
        let mut handled_vars: FxHashSet<String> = FxHashSet::default();

        if let Some(system) = analyze_transition(loop_body, &var_names) {
            // We have closed-form solutions - emit recurrence constraints
            self.emit_recurrence_constraints(&system, model, &mut result_lits, &mut handled_vars);
        }

        // Apply LoAT-style recurrence handlers for variables not handled by closed-form analysis
        if self.config.recurrent_bounds {
            self.recurrent_bounds(loop_body, model, &mut result_lits, &handled_vars);
        }

        if self.config.recurrent_exps {
            self.recurrent_exps(loop_body, model, &mut result_lits);
        }

        // Build result formula
        if result_lits.is_empty() {
            ChcExpr::Bool(true)
        } else {
            // Add constraint: n > 0 (at least one iteration)
            result_lits.push(ChcExpr::gt(
                ChcExpr::var(self.n_var.clone()),
                ChcExpr::int(0),
            ));
            ChcExpr::and_all(result_lits)
        }
    }

    /// Emit constraints from closed-form solutions.
    ///
    /// Includes:
    /// 1. Individual delta constraints: `x' - x = delta * n`
    /// 2. Preserved differences: when delta(A) = delta(B), emit `A' - B' = A - B`
    ///
    /// Part of #1347 (loop acceleration).
    fn emit_recurrence_constraints(
        &self,
        system: &TriangularSystem,
        model: &FxHashMap<String, SmtValue>,
        result: &mut Vec<ChcExpr>,
        handled_vars: &mut FxHashSet<String>,
    ) {
        // Group variables by delta to find preserved differences
        let mut delta_groups: FxHashMap<i64, Vec<(String, ChcVar)>> = FxHashMap::default();

        for (var_name, closed_form) in &system.solutions {
            if let ClosedForm::ConstantDelta { delta, .. } = closed_form {
                if let Some(v) = self
                    .state_vars
                    .iter()
                    .find(|v| v.name == *var_name)
                    .cloned()
                {
                    handled_vars.insert(var_name.clone());
                    delta_groups
                        .entry(*delta)
                        .or_default()
                        .push((var_name.clone(), v.clone()));

                    // Emit individual delta constraint
                    let next_var = ChcVar::new(format!("{}_next", v.name), v.sort.clone());
                    if *delta == 0 {
                        // Identity: x_next = x (Part of #1394)
                        let row = ChcExpr::eq(ChcExpr::var(next_var), ChcExpr::var(v.clone()));
                        self.record_accelerated_summary_accelerated_row_candidate(
                            AcceleratedSummaryAcceleratedRowKind::ConstantDelta,
                            &row,
                        );
                        self.record_accelerated_summary_family_summary_candidate(
                            AcceleratedSummaryFamilySummaryKind::AffineConstantDelta,
                            &row,
                        );
                        result.push(row);
                    } else {
                        // Non-trivial delta: x_next - x = delta * n
                        let delta_expr =
                            ChcExpr::sub(ChcExpr::var(next_var), ChcExpr::var(v.clone()));
                        let n_times_delta = if *delta == 1 {
                            ChcExpr::var(self.n_var.clone())
                        } else {
                            ChcExpr::mul(ChcExpr::int(*delta), ChcExpr::var(self.n_var.clone()))
                        };
                        let row = ChcExpr::eq(delta_expr, n_times_delta);
                        self.record_accelerated_summary_accelerated_row_candidate(
                            AcceleratedSummaryAcceleratedRowKind::ConstantDelta,
                            &row,
                        );
                        self.record_accelerated_summary_family_summary_candidate(
                            AcceleratedSummaryFamilySummaryKind::AffineConstantDelta,
                            &row,
                        );
                        result.push(row);
                    }
                }
            }
        }

        // Emit polynomial closed-form constraints (Part of #7335).
        //
        // For ClosedForm::Polynomial { coeffs }, where coeffs[k] maps variable
        // names to Rational64 coefficients of n^k:
        //   x_next = sum_{k=0}^{deg} (sum_{v} coeffs[k][v] * v_0) * n^k
        //
        // To stay in integer arithmetic, multiply through by the LCM of all
        // coefficient denominators:
        //   lcm * x_next = lcm * polynomial(pre_vars, n)
        for (var_name, closed_form) in &system.solutions {
            if let ClosedForm::Polynomial { coeffs } = closed_form {
                if let Some(v) = self
                    .state_vars
                    .iter()
                    .find(|v| v.name == *var_name)
                    .cloned()
                {
                    if let Some(constraint) = self.lower_polynomial_constraint(&v, coeffs) {
                        handled_vars.insert(var_name.clone());
                        self.record_accelerated_summary_accelerated_row_candidate(
                            AcceleratedSummaryAcceleratedRowKind::PolynomialClosedForm,
                            &constraint,
                        );
                        self.record_accelerated_summary_family_summary_candidate(
                            AcceleratedSummaryFamilySummaryKind::PolynomialClosedForm,
                            &constraint,
                        );
                        result.push(constraint);
                    }
                }
            }
        }

        // Emit preserved difference constraints for pairs with same delta
        // Sort groups by delta for deterministic constraint ordering (#3060)
        let mut sorted_groups: Vec<_> = delta_groups.iter().collect();
        sorted_groups.sort_unstable_by_key(|(delta, _)| **delta);
        for (_, vars) in &sorted_groups {
            if vars.len() >= 2 {
                for i in 0..vars.len() {
                    for j in (i + 1)..vars.len() {
                        let (name_a, var_a) = &vars[i];
                        let (name_b, var_b) = &vars[j];
                        let val_a = model
                            .get(name_a)
                            .and_then(|v| match v {
                                SmtValue::Int(n) => Some(*n),
                                _ => None,
                            })
                            .unwrap_or(0);
                        let val_b = model
                            .get(name_b)
                            .and_then(|v| match v {
                                SmtValue::Int(n) => Some(*n),
                                _ => None,
                            })
                            .unwrap_or(0);
                        let next_a =
                            ChcVar::new(format!("{}_next", var_a.name), var_a.sort.clone());
                        let next_b =
                            ChcVar::new(format!("{}_next", var_b.name), var_b.sort.clone());
                        // A' - B' = A - B (preserved difference)
                        let row = ChcExpr::eq(
                            ChcExpr::sub(ChcExpr::var(next_a), ChcExpr::var(next_b)),
                            ChcExpr::sub(ChcExpr::var(var_a.clone()), ChcExpr::var(var_b.clone())),
                        );
                        self.record_accelerated_summary_accelerated_row_candidate(
                            AcceleratedSummaryAcceleratedRowKind::PreservedDifference,
                            &row,
                        );
                        self.record_accelerated_summary_family_summary_candidate(
                            AcceleratedSummaryFamilySummaryKind::AffinePreservedDifference,
                            &row,
                        );
                        result.push(row);
                        // If model shows A = B, emit equality hint
                        if val_a - val_b == 0 {
                            result.push(ChcExpr::eq(
                                ChcExpr::var(var_a.clone()),
                                ChcExpr::var(var_b.clone()),
                            ));
                        }
                    }
                }
            }
        }
    }

    /// Lower a `ClosedForm::Polynomial` into an integer equality constraint.
    ///
    /// Given polynomial coefficients for variable `var`, builds:
    ///   lcm * var_next = sum of lcm-scaled monomials in (pre_vars, __trp_n)
    ///
    /// Returns `None` if the polynomial is trivially empty or constant-only
    /// (degree 0 with a single self-reference, i.e., identity).
    ///
    /// Part of #7335.
    fn lower_polynomial_constraint(
        &self,
        var: &ChcVar,
        coeffs: &[FxHashMap<String, Rational64>],
    ) -> Option<ChcExpr> {
        if coeffs.is_empty() {
            return None;
        }

        // Compute the LCM of all coefficient denominators to clear fractions.
        let mut lcm: i64 = 1;
        for coeff_map in coeffs {
            for rational in coeff_map.values() {
                lcm = lcm_i64(lcm, *rational.denom());
            }
        }
        if lcm == 0 {
            return None;
        }

        // Build the RHS: sum_{k=0}^{degree} (sum_{v} (lcm * coeffs[k][v]) * v_0) * n^k
        let mut rhs_terms: Vec<ChcExpr> = Vec::new();
        for (power, coeff_map) in coeffs.iter().enumerate() {
            for (var_name, rational) in coeff_map {
                let scaled_numer = rational.numer() * (lcm / rational.denom());
                if scaled_numer == 0 {
                    continue;
                }

                // Build the base term: either a constant or a variable reference
                let base = if var_name.is_empty() {
                    // Pure constant term
                    ChcExpr::int(scaled_numer)
                } else {
                    // Variable reference: scaled_numer * var_0
                    let ref_var = self
                        .state_vars
                        .iter()
                        .find(|v| v.name == *var_name)
                        .cloned();
                    match ref_var {
                        Some(rv) => {
                            if scaled_numer == 1 {
                                ChcExpr::var(rv)
                            } else {
                                ChcExpr::mul(ChcExpr::int(scaled_numer), ChcExpr::var(rv))
                            }
                        }
                        None => {
                            // Variable not in state vars — skip this term
                            continue;
                        }
                    }
                };

                // Multiply by n^power
                let monomial = if power == 0 {
                    base
                } else {
                    let n_pow = self.n_power(power);
                    ChcExpr::mul(base, n_pow)
                };

                rhs_terms.push(monomial);
            }
        }

        if rhs_terms.is_empty() {
            return None;
        }

        let rhs = rhs_terms
            .into_iter()
            .reduce(ChcExpr::add)
            .unwrap_or_else(|| ChcExpr::int(0));

        // Build LHS: lcm * var_next
        let next_var = ChcVar::new(format!("{}_next", var.name), var.sort.clone());
        let lhs = if lcm == 1 {
            ChcExpr::var(next_var)
        } else {
            ChcExpr::mul(ChcExpr::int(lcm), ChcExpr::var(next_var))
        };

        Some(ChcExpr::eq(lhs, rhs))
    }

    /// Build __trp_n^power as a ChcExpr.
    fn n_power(&self, power: usize) -> ChcExpr {
        match power {
            0 => ChcExpr::int(1),
            1 => ChcExpr::var(self.n_var.clone()),
            _ => {
                let mut expr = ChcExpr::var(self.n_var.clone());
                for _ in 1..power {
                    expr = ChcExpr::mul(expr, ChcExpr::var(self.n_var.clone()));
                }
                expr
            }
        }
    }
}

/// Integer LCM for denominator clearing.
fn lcm_i64(a: i64, b: i64) -> i64 {
    if a == 0 || b == 0 {
        return 0;
    }
    let a = a.abs();
    let b = b.abs();
    a / gcd_i64(a, b) * b
}

fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;
