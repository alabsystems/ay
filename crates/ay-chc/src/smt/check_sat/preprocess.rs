// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocessing stage of check_sat: feature scanning, constant propagation,
//! normalization, bound promotion, executor dispatch, and conjunction flattening.

use ay_core::time::Instant;
use std::time::Duration;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::super::context::SmtContext;
use super::super::executor_sort_guard::unsupported_executor_expr_reason;
use super::super::types::{SmtResult, SmtValue, UnsatCore};
use super::PreparedQuery;
use crate::{ChcExpr, ChcSort, ChcVar};

impl SmtContext {
    /// Preprocess a check_sat query: scan features, propagate constants,
    /// normalize, promote bounds, dispatch to executor if needed, and
    /// flatten top-level conjunctions.
    ///
    /// Returns `Ok(PreparedQuery)` for the CNF + theory-loop stages,
    /// or `Err(SmtResult)` for early exits (budget, timeout, trivial,
    /// executor-resolved).
    pub(super) fn prepare_check_sat_query(
        &mut self,
        expr: &ChcExpr,
        start: Instant,
        timeout: Option<Duration>,
    ) -> Result<PreparedQuery, SmtResult> {
        // Track consecutive budget exceedances (#2472). Check the flag from
        // the PREVIOUS call before reset clears it.
        if self.conversion_budget_exceeded {
            self.conversion_budget_strikes = self.conversion_budget_strikes.saturating_add(1);
        } else {
            self.conversion_budget_strikes = 0;
        }

        // Reset per-check conversion budget (#2771).
        self.reset_conversion_budget();

        // If too many consecutive calls exceeded the budget, short-circuit.
        if self.conversion_budget_strikes >= super::super::context::MAX_CONVERSION_STRIKES {
            return Err(SmtResult::Unknown);
        }

        // #6360: Single-pass feature scan replaces repeated `contains_*` walks.
        // #8664: Run bounded symbolic read-over-write expansion before feature
        // routing so short store chains can become scalar ITEs instead of being
        // sent to the Array executor solely because of the original syntax.
        let initial_features = expr.scan_features();
        let preprocessed_expr = if initial_features.has_array_ops {
            expr.simplify_array_ops().expand_select_store_symbolic()
        } else {
            expr.clone()
        };

        // Detect array ops, BV usage, UF apps, mixed-sort eq, ITE, mod/div,
        // negation, and strict comparisons in the expression actually solved.
        let features = preprocessed_expr.scan_features();
        let has_array_ops = features.has_array_ops;
        let has_dt = features.has_dt;
        let has_uf_apps = features.has_uf_apps;
        let needs_euf = has_array_ops || has_uf_apps;
        let needs_executor = has_array_ops || has_dt;

        // #5877: Early timeout check before any expression processing.
        if let Some(t) = timeout {
            if start.elapsed() >= t {
                return Err(SmtResult::Unknown);
            }
        }

        // Step 1: Apply constant propagation to enable folding of mod expressions
        // e.g., (A = 0) ∧ (mod A 2) != 0 becomes (A = 0) ∧ (0 != 0) = false
        let mut propagated_equalities: FxHashMap<String, i128> = FxHashMap::default();
        Self::collect_int_var_const_equalities(&preprocessed_expr, &mut propagated_equalities);
        // #5877: Also collect BV var=const equalities for BV-native PDR mode.
        let mut propagated_bv_equalities: FxHashMap<String, (u128, u32)> = FxHashMap::default();
        if features.has_bv {
            Self::collect_bv_var_const_equalities(
                &preprocessed_expr,
                &mut propagated_bv_equalities,
            );
        }
        let simplified = preprocessed_expr.propagate_constants();

        // Propagation can discover new bindings (e.g. `(+ 1 A) = 4` ⇒ `A = 3`).
        Self::collect_int_var_const_equalities(&simplified, &mut propagated_equalities);
        if features.has_bv {
            Self::collect_bv_var_const_equalities(&simplified, &mut propagated_bv_equalities);
        }

        let mut propagated_model: FxHashMap<String, SmtValue> = FxHashMap::default();
        for (name, value) in &propagated_equalities {
            propagated_model.insert(name.clone(), SmtValue::Int(*value));
        }
        for (name, (value, width)) in &propagated_bv_equalities {
            propagated_model.insert(name.clone(), SmtValue::bitvec_from_u128(*value, *width));
        }

        // Check if simplified to a constant.
        if let ChcExpr::Bool(b) = &simplified {
            return if *b {
                Err(Self::sat_or_unknown(
                    expr,
                    propagated_model,
                    "constant propagation",
                ))
            } else {
                Err(SmtResult::Unsat)
            };
        }

        // #5877: Check timeout after constant propagation.
        if let Some(t) = timeout {
            if start.elapsed() >= t {
                return Err(SmtResult::Unknown);
            }
        }

        // #6360: shared core normalization chain.
        let mut normalized = features.core_normalize(simplified);

        // Step 6: Promote singleton bounds to equalities.
        let mut lower_bounds: FxHashMap<String, i128> = FxHashMap::default();
        let mut upper_bounds: FxHashMap<String, i128> = FxHashMap::default();
        Self::collect_int_var_bounds(&normalized, &mut lower_bounds, &mut upper_bounds);

        let mut bound_subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for (name, lb) in &lower_bounds {
            let Some(ub) = upper_bounds.get(name) else {
                continue;
            };
            if lb == ub {
                propagated_equalities.entry(name.clone()).or_insert(*lb);
                bound_subst.push((ChcVar::new(name, ChcSort::Int), ChcExpr::Int(*lb)));
            }
        }
        if !bound_subst.is_empty() {
            normalized = normalized.substitute(&bound_subst).simplify_constants();
            propagated_model.clear();
            for (name, value) in &propagated_equalities {
                propagated_model.insert(name.clone(), SmtValue::Int(*value));
            }
        }

        // #6047/#7016: When the formula contains array operations or datatype
        // sorts, dispatch to ay-dpll's Executor.
        if needs_executor {
            if unsupported_executor_expr_reason(&normalized).is_some() {
                return Err(SmtResult::Unknown);
            }
            let remaining_timeout = timeout
                .map(|t| {
                    t.checked_sub(start.elapsed())
                        .unwrap_or(Duration::from_millis(100))
                })
                .unwrap_or(Duration::from_secs(10));
            let executor_result =
                self.check_sat_via_executor(&normalized, &propagated_model, remaining_timeout);
            if !matches!(executor_result, SmtResult::Unknown) {
                return Err(executor_result);
            }
            // Fall through to the internal DPLL(T) path if executor also returns Unknown.
        }

        // Try assumption-based solving for conjunction-shaped queries.
        let mut top_conjuncts = Vec::new();
        Self::flatten_top_level_and(&normalized, &mut top_conjuncts);

        // Trivial conjunctions.
        if top_conjuncts.is_empty() {
            return Err(Self::sat_or_unknown(
                expr,
                propagated_model,
                "empty conjuncts",
            ));
        }
        if top_conjuncts
            .iter()
            .any(|c| matches!(c, ChcExpr::Bool(false)))
        {
            return Err(SmtResult::UnsatWithCore(UnsatCore {
                conjuncts: vec![ChcExpr::Bool(false)],
                ..Default::default()
            }));
        }
        top_conjuncts.retain(|c| !matches!(c, ChcExpr::Bool(true)));
        if top_conjuncts.is_empty() {
            return Err(Self::sat_or_unknown(
                expr,
                propagated_model,
                "all-true conjuncts",
            ));
        }

        Ok(PreparedQuery {
            features,
            normalized,
            propagated_model,
            top_conjuncts,
            needs_euf,
            _needs_executor: needs_executor,
        })
    }
}
