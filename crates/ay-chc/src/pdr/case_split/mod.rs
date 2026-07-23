// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Case-splitting preprocessing for unconstrained constant arguments.

mod candidates;

use crate::cancellation::{CancellationGuard, CancellationToken};
use crate::{ChcExpr, ChcProblem, ChcVar, PredicateId};
use ay_core::time::Instant;
use std::time::Duration;

use super::frame::PdrResult;
use super::model::{InvariantModel, PredicateInterpretation};
use super::solver::PdrSolver;
use super::PdrConfig;

const DEFAULT_BRANCH_BUDGET: Duration = Duration::from_secs(4);
const FUTURE_BRANCH_RESERVE: Duration = Duration::from_secs(2);
const MERGE_VERIFY_RESERVE: Duration = Duration::from_millis(500);

/// A case constraint for case-splitting on constant arguments.
///
/// Case constraints partition the state space based on equality/disequality
/// conditions on an unconstrained constant argument. For example, if a mode
/// argument is compared only against `1` in the transition, the cases are:
/// - `mode = 1` (equality case)
/// - `mode ≠ 1` (other case, ensures exhaustive partition)
#[derive(Debug, Clone, PartialEq, Eq)]
struct CaseConstraint {
    /// Human-readable name for logging (e.g., "mode = 1" or "mode ∉ {1, 2}")
    name: String,
    kind: CaseConstraintKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CaseConstraintKind {
    Eq(i128),
    NeAll(Vec<i128>),
}

impl CaseConstraint {
    /// Create an equality case: `var = value`
    fn eq(var_name: &str, value: i128) -> Self {
        Self {
            name: format!("{var_name} = {value}"),
            kind: CaseConstraintKind::Eq(value),
        }
    }

    /// Create a disequality for all given values: `var ≠ v1 ∧ var ≠ v2 ∧ ...`
    fn ne_all(var_name: &str, values: &[i128]) -> Self {
        let mut values: Vec<i128> = values.to_vec();
        values.sort_unstable();
        values.dedup();

        Self {
            name: format!(
                "{} ∉ {{{}}}",
                var_name,
                values
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            kind: CaseConstraintKind::NeAll(values),
        }
    }

    fn constraint_for_var(&self, var: ChcVar) -> ChcExpr {
        match &self.kind {
            CaseConstraintKind::Eq(value) => ChcExpr::eq(ChcExpr::var(var), ChcExpr::int(*value)),
            CaseConstraintKind::NeAll(values) => ChcExpr::and_vec(
                values
                    .iter()
                    .map(|v| ChcExpr::not(ChcExpr::eq(ChcExpr::var(var.clone()), ChcExpr::int(*v))))
                    .collect(),
            ),
        }
    }
}

impl PdrSolver {
    /// Attempt to solve via case-split on unconstrained constant arguments.
    ///
    /// Returns Some(result) if case-split was applied and yielded a definitive result,
    /// None if case-split doesn't apply or all cases returned Unknown.
    ///
    /// # When to use directly
    ///
    /// This function is called automatically by `solve_problem()`. Call it directly only
    /// when you need case-split as a standalone preprocessing step with dedicated limits
    /// (e.g., at the adaptive layer before portfolio with higher iteration budget).
    ///
    /// Reference: #1306 - Constant-argument case-splitting for dillig-style benchmarks.
    pub(crate) fn try_case_split_solve(
        problem: &ChcProblem,
        config: PdrConfig,
    ) -> Option<PdrResult> {
        // Find candidates: predicates with constant arguments that are unconstrained at init
        let candidates = Self::find_case_split_candidates(problem, config.verbose);

        if candidates.is_empty() {
            return None;
        }

        // Take the first candidate - typically there's at most one
        let (pred_id, arg_idx, var_name, cases) = &candidates[0];

        if config.verbose {
            let case_names: Vec<&str> = cases.iter().map(|c| c.name.as_str()).collect();
            safe_eprintln!(
                "PDR: Attempting case-split on pred {} arg {} ({}) with cases {:?}",
                pred_id.index(),
                arg_idx,
                var_name,
                case_names
            );
        }

        // Wall-clock deadline for the entire case-split attempt.
        // This ensures case-split cannot consume more than its allocated budget,
        // even if individual branches take longer than expected.
        let case_split_deadline = config.solve_timeout.map(|t| Instant::now() + t);

        // Solve for each case
        let mut safe_models: Vec<(CaseConstraint, InvariantModel)> = Vec::new();
        let mut had_unknown = false;

        for (case_index, case) in cases.iter().enumerate() {
            // Check wall-clock deadline before starting each branch
            if Self::case_split_deadline_expired(case_split_deadline) {
                if config.verbose {
                    safe_eprintln!("PDR: Case-split: wall-clock deadline expired, returning None");
                }
                return None;
            }
            let constrained_problem =
                Self::add_init_constraint_expr(problem, *pred_id, *arg_idx, case);

            if config.verbose {
                safe_eprintln!("PDR: Case-split: solving with {}", case.name);
            }

            let mut sub_config = config.clone();
            sub_config.verbose = config.verbose;
            // Case-split is a preprocessing optimization. Keep every branch
            // bounded, but make the allocation work-conserving within the
            // unchanged stage deadline: reserve two seconds for every sibling
            // still to run and 500ms for merged-model strict verification,
            // then let the current branch use the remaining slack. This avoids
            // discarding stage budget when a hard explicit-value case needs a
            // final certificate recheck and the complement case is cheap
            // (dillig12_m E=1 / E!=1).
            let remaining = case_split_deadline
                .map(|d| d.saturating_duration_since(ay_core::time::Instant::now()));
            let future_branches = cases.len().saturating_sub(case_index + 1);
            let branch_budget = Self::case_split_branch_budget(remaining, future_branches);
            if config.verbose {
                safe_eprintln!(
                    "PDR: Case-split: branch budget {:.3}s ({} future case(s), stage remaining {:.3}s)",
                    branch_budget.as_secs_f64(),
                    future_branches,
                    remaining.unwrap_or(branch_budget).as_secs_f64()
                );
            }
            sub_config.solve_timeout = Some(branch_budget);
            let _branch_cancel_guard =
                Self::install_case_split_branch_cancellation(&mut sub_config, branch_budget);

            let mut solver = Self::new(constrained_problem, sub_config);
            let result = solver.solve();

            if config.verbose {
                safe_eprintln!(
                    "PDR: Case-split: {} -> {:?}",
                    case.name,
                    match &result {
                        PdrResult::Safe(_) => "Safe",
                        PdrResult::Unsafe(_) => "Unsafe",
                        PdrResult::Unknown | PdrResult::NotApplicable => "Unknown",
                    }
                );
            }

            match result {
                PdrResult::Safe(model) => {
                    safe_models.push((case.clone(), model));
                }
                PdrResult::Unsafe(cex) => {
                    // Early termination: any Unsafe case means the whole problem is Unsafe
                    if config.verbose {
                        safe_eprintln!(
                            "PDR: Case-split: early termination - {} is Unsafe",
                            case.name
                        );
                    }
                    return Some(PdrResult::Unsafe(cex));
                }
                PdrResult::Unknown | PdrResult::NotApplicable => {
                    had_unknown = true;
                    if Self::case_split_deadline_expired(case_split_deadline) {
                        if config.verbose {
                            safe_eprintln!(
                                "PDR: Case-split: branch exhausted wall-clock deadline, returning None"
                            );
                        }
                        return None;
                    }
                }
            }
        }

        if had_unknown || safe_models.is_empty() {
            // Some cases Unknown - don't claim a result
            if config.verbose {
                safe_eprintln!("PDR: Case-split: Some cases Unknown, returning None");
            }
            return None;
        }

        // All cases returned Safe - merge models and verify on the original problem.
        if Self::case_split_deadline_expired(case_split_deadline) {
            if config.verbose {
                safe_eprintln!(
                    "PDR: Case-split: deadline expired before merge/verify, returning None"
                );
            }
            return None;
        }
        if config.verbose {
            safe_eprintln!(
                "PDR: Case-split: All {} cases safe, attempting merge + verify",
                safe_models.len()
            );
        }

        let merged = Self::merge_case_split_safe_models(&safe_models, *arg_idx);
        if Self::case_split_deadline_expired(case_split_deadline) {
            if config.verbose {
                safe_eprintln!(
                    "PDR: Case-split: deadline expired before strict verification, returning None"
                );
            }
            return None;
        }
        let mut verifier = Self::case_split_strict_verifier(problem, &config, case_split_deadline);
        if verifier.verify_model_fresh(&merged) {
            if config.verbose {
                safe_eprintln!("PDR: Case-split: merged model verified, returning Safe");
            }
            return Some(PdrResult::Safe(merged));
        }

        // #9227: If the merged model cannot be strictly re-validated against the
        // original problem, do not mark it Safe with a trust flag. Let callers
        // continue with the normal portfolio fallback instead.
        if config.verbose {
            safe_eprintln!(
                "PDR: Case-split: merged model failed strict validation, returning None (#9227)"
            );
        }
        None
    }

    fn case_split_deadline_expired(deadline: Option<Instant>) -> bool {
        deadline.is_some_and(|d| Instant::now() >= d)
    }

    fn case_split_branch_budget(remaining: Option<Duration>, future_branches: usize) -> Duration {
        let Some(remaining) = remaining else {
            return DEFAULT_BRANCH_BUDGET;
        };

        let future_count = u32::try_from(future_branches).unwrap_or(u32::MAX);
        let reserve = FUTURE_BRANCH_RESERVE
            .saturating_mul(future_count)
            .saturating_add(MERGE_VERIFY_RESERVE);
        if let Some(slack) = remaining.checked_sub(reserve) {
            if !slack.is_zero() {
                return slack;
            }
        }

        // If the advertised reserves no longer fit, split the remaining
        // envelope fairly. The enclosing stage deadline is still authoritative.
        let branch_count = u32::try_from(future_branches.saturating_add(1)).unwrap_or(u32::MAX);
        remaining / branch_count.max(1)
    }

    fn install_case_split_branch_cancellation(
        config: &mut PdrConfig,
        branch_budget: Duration,
    ) -> Option<CancellationGuard> {
        if config.cancellation_token.is_some() {
            return None;
        }

        let branch_cancellation = CancellationToken::new();
        let guard = branch_cancellation.cancel_after(branch_budget);
        config.cancellation_token = Some(branch_cancellation);
        Some(guard)
    }

    fn case_split_strict_verifier(
        problem: &ChcProblem,
        config: &PdrConfig,
        case_split_deadline: Option<Instant>,
    ) -> Self {
        let mut verifier_config = config.clone();
        verifier_config.strict_proofs = true;
        verifier_config.disable_array_scalarization = true;
        let mut verifier = Self::new(problem.clone(), verifier_config);
        verifier.solve_deadline = case_split_deadline;
        verifier
    }

    fn merge_case_split_safe_models(
        safe_models: &[(CaseConstraint, InvariantModel)],
        split_arg_idx: usize,
    ) -> InvariantModel {
        debug_assert!(!safe_models.is_empty(), "merge requires at least one model");

        let first_model = &safe_models[0].1;
        let mut pred_ids: Vec<PredicateId> = first_model.iter().map(|(id, _)| *id).collect();
        pred_ids.sort_by_key(|p| p.index());

        let mut merged = InvariantModel::new();
        for pred_id in pred_ids {
            let first_interp = first_model
                .get(&pred_id)
                .expect("InvariantModel::iter must match get()");
            let vars = first_interp.vars.clone();

            let mut case_interps: Vec<(&CaseConstraint, &PredicateInterpretation)> = Vec::new();
            for (case, model) in safe_models {
                let interp = model
                    .get(&pred_id)
                    .expect("case-split model missing predicate interpretation");
                debug_assert_eq!(
                    interp.vars, vars,
                    "case-split models disagree on predicate vars"
                );
                case_interps.push((case, interp));
            }

            // For predicates that DO have the split argument, use guarded implications
            // (implies guard interp). For predicates that DON'T (e.g., SAD in dillig12_m
            // where the split was on FUN's arg 4), use or_vec — the split variable doesn't
            // exist in this predicate so both case interpretations are valid. (#1306)
            let formula = if vars.len() > split_arg_idx {
                let mode_var = vars[split_arg_idx].clone();
                ChcExpr::and_vec(
                    case_interps
                        .iter()
                        .map(|(case, interp)| {
                            let guard = case.constraint_for_var(mode_var.clone());
                            ChcExpr::implies(guard, interp.formula.clone())
                        })
                        .collect(),
                )
            } else {
                ChcExpr::or_vec(
                    case_interps
                        .iter()
                        .map(|(_, interp)| interp.formula.clone())
                        .collect(),
                )
            };

            merged.set(pred_id, PredicateInterpretation::new(vars, formula));
        }

        merged
    }

    /// Create a new problem with an additional constraint expression on init.
    ///
    /// The constraint expression should be over the variable at arg_idx in the fact clause.
    /// Accepts arbitrary ChcExpr (e.g., disequalities or conjunctions for the "other" case).
    fn add_init_constraint_expr(
        problem: &ChcProblem,
        pred_id: PredicateId,
        arg_idx: usize,
        case: &CaseConstraint,
    ) -> ChcProblem {
        let mut new_problem = problem.clone();

        for clause in new_problem.clauses_mut() {
            if clause.head.predicate_id() != Some(pred_id) {
                continue;
            }

            if clause.is_fact() {
                // Fact clause: guard on the head variable at arg_idx.
                let var = match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => {
                        if arg_idx >= args.len() {
                            continue;
                        }
                        match &args[arg_idx] {
                            ChcExpr::Var(v) => v.clone(),
                            _ => continue,
                        }
                    }
                    crate::ClauseHead::False => continue,
                };

                let case_constraint = case.constraint_for_var(var);
                let combined = match &clause.body.constraint {
                    Some(existing) => ChcExpr::and(existing.clone(), case_constraint),
                    None => case_constraint,
                };
                clause.body.constraint = Some(combined);
            } else if clause.body.predicates.len() == 1 && clause.body.predicates[0].0 == pred_id {
                // D13 (#1306): Self-loop clause — thread the case guard into the
                // transition constraint. The arg is constant (head == body), so
                // the guard on the body-side variable is equivalent. This makes
                // preservation queries (e.g., is_scaled_diff_preserved) branch-aware.
                let body_args = &clause.body.predicates[0].1;
                if arg_idx >= body_args.len() {
                    continue;
                }
                let var = match &body_args[arg_idx] {
                    ChcExpr::Var(v) => v.clone(),
                    _ => continue,
                };

                let case_constraint = case.constraint_for_var(var);
                let combined = match &clause.body.constraint {
                    Some(existing) => ChcExpr::and(existing.clone(), case_constraint),
                    None => case_constraint,
                };
                clause.body.constraint = Some(combined);
            }
        }

        new_problem
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
