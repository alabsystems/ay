// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Utility functions for blocking: model projection, integer minimization,
//! bounds extraction, and hyperedge derivation allocation.

use super::super::*;
use crate::pdr::derivation::{Derivation, DerivationId, Premise, PremiseSummary};

/// Default per-query timeout for array-containing SMT queries (#8660).
///
/// Array theory queries can be extremely expensive (especially with >=2 array-sorted
/// parameters). Cap individual queries to prevent a single blocking check from consuming
/// the entire solve budget. If the query times out, the caller gets Unknown and falls
/// back to scalar-only blocking or returns Unknown to the obligation queue.
///
/// The actual cap scales inversely with the number of array params:
/// - 1 array param: 2000ms (full budget)
/// - 2 array params: 1000ms
/// - 3+ array params: 500ms
///   This prevents problems with many array params from burning budget on queries that
///   are unlikely to terminate quickly.
const ARRAY_QUERY_TIMEOUT_BASE: std::time::Duration = std::time::Duration::from_secs(2);

/// Compute the per-query timeout cap based on the number of array parameters.
///
/// The more array parameters a problem has, the tighter the timeout should be:
/// - 0-1 array params: base timeout (2000ms)
/// - 2 array params: 1000ms
/// - 3+ array params: 500ms
fn scaled_array_timeout(max_array_params: usize) -> std::time::Duration {
    match max_array_params {
        0..=1 => ARRAY_QUERY_TIMEOUT_BASE,
        2 => std::time::Duration::from_secs(1),
        _ => std::time::Duration::from_millis(500),
    }
}

impl PdrSolver {
    pub(super) fn check_array_clause_query(
        smt: &mut SmtContext,
        array_clause_sessions: &mut caches::LruSolverMap<
            ArraySessionKey,
            PersistentExecutorSmtContext,
        >,
        session_key: ArraySessionKey,
        background: &ChcExpr,
        query_delta: &ChcExpr,
        full_query: &ChcExpr,
        max_array_params: usize,
    ) -> SmtResult {
        debug_assert!(
            full_query.contains_array_ops(),
            "persistent array query helper requires an array-containing query"
        );

        // #8660: Cap per-query timeout to prevent single array queries from exhausting
        // the solve budget. With >=2 array params, queries can easily take >10s each,
        // leaving no budget for actual invariant convergence.
        // Scale the cap inversely with array param count for tighter control.
        let timeout_cap = scaled_array_timeout(max_array_params);
        let base_timeout = smt.current_timeout().unwrap_or_default();
        let timeout = if base_timeout.is_zero() {
            timeout_cap
        } else {
            base_timeout.min(timeout_cap)
        };
        let mut propagated_model = FxHashMap::default();
        Self::extract_equalities_from_formula(full_query, &mut propagated_model);

        let result = {
            let session = array_clause_sessions
                .get_or_insert_with(session_key, PersistentExecutorSmtContext::default);
            if !session.ensure_background(background, timeout) {
                SmtResult::Unknown
            } else {
                session.check_query(query_delta, &propagated_model, timeout)
            }
        };

        // Keep the scratch SMT context fresh for follow-up minimization queries.
        smt.reset();
        result
    }

    pub(super) fn projection_vars_for_args(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
    ) -> Vec<ChcVar> {
        let mut vars = Vec::new();
        let mut seen_names: FxHashSet<String> = FxHashSet::default();

        for arg in args {
            for var in arg.vars() {
                if seen_names.insert(var.name.clone()) {
                    vars.push(var);
                }
            }
        }

        if let Some(canonical_vars) = self.canonical_vars(pred) {
            for var in canonical_vars {
                if seen_names.insert(var.name.clone()) {
                    vars.push(var.clone());
                }
            }
        }

        vars
    }

    pub(super) fn int_minimize_candidates(
        var: &ChcVar,
        query: &ChcExpr,
        current: i128,
    ) -> Vec<i128> {
        let (lower, upper) = Self::extract_int_bounds_for_var(query, &var.name);
        let mut candidates: Vec<i128> = Vec::new();

        match (lower, upper) {
            (Some(lb), Some(ub)) if lb <= ub => {
                // Try the in-range value with smallest absolute value first.
                let closest_to_zero = if lb <= 0 && 0 <= ub {
                    0
                } else if lb > 0 {
                    lb
                } else {
                    ub
                };
                candidates.push(closest_to_zero);
                candidates.push(lb);
                candidates.push(ub);
                candidates.push(lb.saturating_add(1));
                candidates.push(ub.saturating_sub(1));
            }
            (Some(lb), None) if lb > 0 => {
                candidates.push(lb);
                candidates.push(lb.saturating_add(1));
            }
            (None, Some(ub)) if ub < 0 => {
                candidates.push(ub);
                candidates.push(ub.saturating_sub(1));
            }
            _ => {}
        }

        // Stable fallback set.
        candidates.extend([0, 1, -1, current]);

        let mut seen: FxHashSet<i128> = FxHashSet::default();
        candidates.retain(|v| seen.insert(*v));
        candidates
    }

    pub(super) fn extract_int_bounds_for_var(
        query: &ChcExpr,
        var_name: &str,
    ) -> (Option<i128>, Option<i128>) {
        let mut lower: Option<i128> = None;
        let mut upper: Option<i128> = None;

        for conjunct in query.collect_conjuncts() {
            let Some((op, constant)) = Self::var_const_relation(&conjunct, var_name) else {
                continue;
            };
            Self::tighten_int_bounds(&mut lower, &mut upper, op, constant);
        }

        (lower, upper)
    }

    pub(super) fn tighten_int_bounds(
        lower: &mut Option<i128>,
        upper: &mut Option<i128>,
        op: ChcOp,
        c: i128,
    ) {
        let mut tighten_lower = |candidate: i128| {
            *lower = Some(match *lower {
                Some(existing) => existing.max(candidate),
                None => candidate,
            });
        };
        let mut tighten_upper = |candidate: i128| {
            *upper = Some(match *upper {
                Some(existing) => existing.min(candidate),
                None => candidate,
            });
        };

        match op {
            ChcOp::Eq => {
                tighten_lower(c);
                tighten_upper(c);
            }
            ChcOp::Ge => tighten_lower(c),
            ChcOp::Gt => tighten_lower(c.saturating_add(1)),
            ChcOp::Le => tighten_upper(c),
            ChcOp::Lt => tighten_upper(c.saturating_sub(1)),
            _ => {}
        }
    }

    pub(super) fn var_const_relation(expr: &ChcExpr, var_name: &str) -> Option<(ChcOp, i128)> {
        let ChcExpr::Op(op, args) = expr else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let lhs = args[0].as_ref();
        let rhs = args[1].as_ref();

        match (lhs, rhs) {
            (ChcExpr::Var(v), ChcExpr::Int(c)) if v.name == var_name => Some((*op, *c)),
            (ChcExpr::Int(c), ChcExpr::Var(v)) if v.name == var_name => {
                let flipped = match op {
                    ChcOp::Eq => ChcOp::Eq,
                    ChcOp::Ge => ChcOp::Le,
                    ChcOp::Gt => ChcOp::Lt,
                    ChcOp::Le => ChcOp::Ge,
                    ChcOp::Lt => ChcOp::Gt,
                    _ => return None,
                };
                Some((flipped, *c))
            }
            _ => None,
        }
    }

    pub(super) fn minimize_projection_model_with_context(
        smt: &mut SmtContext,
        projection_vars: &[ChcVar],
        query: &ChcExpr,
        model: FxHashMap<String, SmtValue>,
    ) -> FxHashMap<String, SmtValue> {
        const MAX_TARGET_VARS: usize = 4;
        const MAX_ATTEMPTS: usize = 8;
        const ATTEMPT_TIMEOUT: std::time::Duration = std::time::Duration::from_millis(50);

        let mut minimized = model;
        let mut attempts = 0usize;

        for var in projection_vars.iter().take(MAX_TARGET_VARS) {
            let Some(current_value) = minimized.get(&var.name).cloned() else {
                continue;
            };

            let candidates: Vec<SmtValue> = match (&var.sort, current_value.clone()) {
                (ChcSort::Bool, SmtValue::Bool(_)) => {
                    vec![SmtValue::Bool(false), SmtValue::Bool(true)]
                }
                (ChcSort::Int, SmtValue::Int(current)) => {
                    Self::int_minimize_candidates(var, query, current)
                        .into_iter()
                        .map(SmtValue::Int)
                        .collect()
                }
                _ => continue,
            };

            for candidate in candidates {
                if attempts >= MAX_ATTEMPTS {
                    return minimized;
                }
                if candidate == current_value {
                    continue;
                }
                attempts += 1;

                let binding = match (&var.sort, candidate) {
                    (ChcSort::Bool, SmtValue::Bool(true)) => ChcExpr::var(var.clone()),
                    (ChcSort::Bool, SmtValue::Bool(false)) => {
                        ChcExpr::not(ChcExpr::var(var.clone()))
                    }
                    (ChcSort::Int, SmtValue::Int(value)) => {
                        ChcExpr::eq(ChcExpr::var(var.clone()), ChcExpr::int(value))
                    }
                    _ => continue,
                };

                let constrained_query = ChcExpr::and(query.clone(), binding);
                let sat_result = smt.with_phase_seed_model(Some(&minimized), |inner| {
                    inner.check_sat_with_timeout(&constrained_query, ATTEMPT_TIMEOUT)
                });
                if let SmtResult::Sat(new_model) = sat_result {
                    minimized = new_model;
                    break;
                }
            }
        }

        minimized
    }

    /// Allocate a derivation for a hyperedge (multi-body clause) predecessor.
    ///
    /// Creates a Derivation that tracks progress through all body predicates
    /// of the clause. The may predicate at last_may_index becomes the active
    /// premise to be proven reachable first.
    ///
    /// Takes pre-cloned body predicates to avoid borrow checker issues at the call site
    /// (where clause is borrowed from self.problem.clauses()).
    ///
    /// #1275: Implements derivation tracking for hyperedge clauses.
    #[allow(clippy::too_many_arguments)] // params map 1:1 to Derivation fields; a wrapper struct would duplicate them
    pub(in crate::pdr::solver) fn allocate_hyperedge_derivation_from_preds(
        &mut self,
        body_predicates: &[(PredicateId, Vec<ChcExpr>)],
        clause_index: usize,
        last_may_index: usize,
        head_predicate: PredicateId,
        head_level: usize,
        head_state: ChcExpr,
        query_clause: Option<usize>,
        prev_level: usize,
    ) -> DerivationId {
        let mut premises: Vec<Premise> = Vec::with_capacity(body_predicates.len());

        for (i, (pred_id, _args)) in body_predicates.iter().enumerate() {
            let summary = if i < last_may_index {
                // Predicates before last_may_index used must-summaries in the SAT check
                if let Some(must) = self.reachability.must_summaries.get(prev_level, *pred_id) {
                    PremiseSummary::May(must)
                } else {
                    PremiseSummary::May(ChcExpr::Bool(true))
                }
            } else {
                // The may predicate and those after use frame constraints
                let may = self
                    .cumulative_frame_constraint(prev_level, *pred_id)
                    .unwrap_or(ChcExpr::Bool(true));
                PremiseSummary::May(may)
            };

            premises.push(Premise {
                predicate: *pred_id,
                summary,
            });
        }

        let derivation = Derivation {
            clause_index,
            head_predicate,
            head_level,
            head_state,
            query_clause,
            premises,
            active: last_may_index,
            premise_rfs: Vec::new(),
        };

        self.reachability.derivations.alloc(derivation)
    }
}
