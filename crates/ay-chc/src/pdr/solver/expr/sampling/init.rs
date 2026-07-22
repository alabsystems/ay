// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::super::PdrSolver;
use super::{with_blocking_clauses, with_int_presence_tautologies};
use crate::smt::{SmtResult, SmtValue};
use crate::{ChcExpr, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

impl PdrSolver {
    /// Sample N models from the fact constraint for a predicate.
    ///
    /// Returns a vector of models, each mapping canonical variable names to i128 values.
    /// Used when init bounds aren't constant but we still want to discover affine relations.
    ///
    /// Implements blocking-based diversity: each model blocks itself from subsequent queries
    /// to ensure we get different points in the init region.
    pub(in crate::pdr::solver) fn sample_init_models(
        &mut self,
        predicate: PredicateId,
        n: usize,
    ) -> Vec<FxHashMap<String, i128>> {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return Vec::new(),
        };

        // We only sample integer assignments (used for affine/divisibility synthesis).
        // If there are no integer vars, there's nothing useful to extract.
        let int_vars: Vec<ChcVar> = canonical_vars
            .iter()
            .filter(|v| matches!(v.sort, ChcSort::Int))
            .cloned()
            .collect();
        if int_vars.is_empty() {
            return Vec::new();
        }

        // Build the fact constraint for this predicate
        let mut fact_constraint: Option<ChcExpr> = None;
        for fact in self
            .problem
            .facts()
            .filter(|f| f.head.predicate_id() == Some(predicate))
        {
            let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let head_args = match &fact.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                continue;
            }

            // Build substitution from head args to canonical vars
            let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
            for (arg, canon) in head_args.iter().zip(canonical_vars.iter()) {
                if let ChcExpr::Var(v) = arg {
                    if v.name != canon.name {
                        subst.push((v.clone(), ChcExpr::var(canon.clone())));
                    }
                }
            }

            let renamed_constraint = if subst.is_empty() {
                constraint
            } else {
                constraint.substitute(&subst)
            };

            // Also constrain canonical variables to equal the fact head arguments.
            //
            // Without this, facts like `(P x (+ x 1))` only contribute `constraint` to the
            // sampled init region, and sampling can miss the head relation entirely.
            let mut parts: Vec<ChcExpr> = Vec::with_capacity(1 + head_args.len());
            parts.push(renamed_constraint);
            for (arg, canon) in head_args.iter().zip(canonical_vars.iter()) {
                let renamed_arg = if subst.is_empty() {
                    arg.clone()
                } else {
                    arg.substitute(&subst)
                };
                parts.push(ChcExpr::eq(ChcExpr::var(canon.clone()), renamed_arg));
            }

            let renamed = ChcExpr::and_all(parts);

            fact_constraint = Some(match fact_constraint {
                None => renamed,
                Some(existing) => ChcExpr::or(existing, renamed),
            });
        }

        let Some(base_constraint) = fact_constraint else {
            return Vec::new();
        };
        let base_constraint = with_int_presence_tautologies(base_constraint, &int_vars);

        // Ensure integer canonical vars appear in the query even if the init region is unconstrained.
        //
        // `SmtContext::reset()` means only variables syntactically present in the formula
        // are eligible to show up in extracted models. If the init condition simplifies to
        // `true` (or doesn't mention all vars), we can end up with empty/partial models,
        // which is unsound for sampling-based invariant discovery (defaults to 0s).
        //
        // Use a tautology over integers: (v <= 0) OR (v > 0), which keeps `v` in the query
        // without adding any semantic restriction.
        // Extract var-var equalities from the constraint. The SMT layer's constant propagation
        // substitutes unified variables (e.g., x = y becomes just x), so the returned model may
        // be missing some canonical vars. We use these equalities to recover missing values.
        let var_equalities = base_constraint.extract_var_var_equalities();
        let mut var_eq_map: FxHashMap<String, String> = FxHashMap::default();
        for (v1, v2) in &var_equalities {
            // Map second var to first (consistent with propagate_var_equalities)
            var_eq_map.insert(v2.name.clone(), v1.name.clone());
        }

        // Extract var = constant equalities to recover variables eliminated by
        // constant propagation in the SMT layer. When all init vars are determined
        // to specific constants (e.g., init = (P 0 0 0 0)), the SMT solver may
        // eliminate ALL variables and return an empty model. (#7138)
        //
        // After extracting direct var=const equalities, propagate them through
        // var=var equalities to get the full set. Example: a1=0 + a0=a1 => a0=0.
        let var_const_equalities = base_constraint.extract_var_const_equalities();
        let mut var_const_map: FxHashMap<String, i128> = var_const_equalities
            .into_iter()
            .map(|(v, c)| (v.name, c))
            .collect();
        if !var_const_map.is_empty() && !var_eq_map.is_empty() {
            // Propagate: if var_eq_map[v2] = v1 and var_const_map[v1] = c, then v2 = c.
            // Also reverse: if var_eq_map[v2] = v1 and var_const_map[v2] = c, then v1 = c.
            // Iterate to fixed point for chains.
            loop {
                let mut added = false;
                for (v2, v1) in &var_eq_map {
                    if let Some(&c) = var_const_map.get(v1) {
                        if !var_const_map.contains_key(v2) {
                            var_const_map.insert(v2.clone(), c);
                            added = true;
                        }
                    }
                    if let Some(&c) = var_const_map.get(v2) {
                        if !var_const_map.contains_key(v1) {
                            var_const_map.insert(v1.clone(), c);
                            added = true;
                        }
                    }
                }
                if !added {
                    break;
                }
            }
        }

        let mut models = Vec::with_capacity(n);
        let mut blocking_clauses: Vec<ChcExpr> = Vec::new();

        for _ in 0..n {
            // Combine base constraint with blocking clauses
            let query = with_blocking_clauses(base_constraint.clone(), &blocking_clauses);

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
            {
                SmtResult::Sat(model) => {
                    // Extract integer values for canonical variables
                    let mut values: FxHashMap<String, i128> = FxHashMap::default();
                    let mut all_values = true;
                    for var in &int_vars {
                        if let Some(SmtValue::Int(v)) = model.get(&var.name) {
                            values.insert(var.name.clone(), *v);
                        } else if let Some(eq_name) = var_eq_map.get(&var.name) {
                            // Var was substituted away by var-equality propagation; use unified var's value
                            if let Some(SmtValue::Int(v)) = model.get(eq_name) {
                                values.insert(var.name.clone(), *v);
                            } else if let Some(&c) = var_const_map.get(eq_name) {
                                values.insert(var.name.clone(), c);
                            } else {
                                all_values = false;
                                break;
                            }
                        } else if let Some(&c) = var_const_map.get(&var.name) {
                            // Var was eliminated by constant propagation (#7138);
                            // recover from the init constraint's var = const equalities.
                            values.insert(var.name.clone(), c);
                        } else {
                            all_values = false;
                            break;
                        }
                    }

                    // If we can't extract a complete integer assignment, give up on sampling.
                    if !all_values {
                        break;
                    }

                    // Build blocking clause: NOT(all vars equal this model)
                    let mut diseqs: Vec<ChcExpr> = Vec::new();
                    for var in &int_vars {
                        let Some(value) = values.get(&var.name) else {
                            continue;
                        };
                        diseqs.push(ChcExpr::ne(ChcExpr::var(var.clone()), ChcExpr::Int(*value)));
                    }
                    if !diseqs.is_empty() {
                        let blocking = diseqs
                            .into_iter()
                            .reduce(ChcExpr::or)
                            .unwrap_or(ChcExpr::Bool(true));
                        blocking_clauses.push(blocking);
                    }

                    models.push(values);
                }
                _ => break, // No more models or timeout
            }
        }

        // Magnitude-diversity init sampling (AY_CHC_FWDSIM_FIX). The SMT returns
        // MINIMAL models (free init vars at 0/negative). For relational transitions
        // whose guards require positive differences (e.g. 003-horn's a_i - a_j >= 1),
        // those degenerate init states enable NO transition, so forward simulation
        // produces 0 samples and affine discovery sees only the degenerate init cloud
        // (var=0 equalities). Add a bounded set of init states with larger/positive
        // free-var values so transitions become enabled and forward-sim can advance.
        // SOUND: these extra points only feed the UNCHANGED affine kernel + admission
        // oracle, which rejects any non-inductive relation.
        if std::env::var("AY_CHC_FWDSIM_FIX").ok().as_deref() != Some("0") {
            const MAX_EXTRA: usize = 16;
            'outer: for var in int_vars.iter().take(8) {
                for &threshold in &[1i128, 3, 8] {
                    if models.len() >= n + MAX_EXTRA {
                        break 'outer;
                    }
                    let bias = ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(threshold));
                    let query = ChcExpr::and(
                        with_blocking_clauses(base_constraint.clone(), &blocking_clauses),
                        bias,
                    );
                    self.smt.reset();
                    let SmtResult::Sat(model) = self
                        .smt
                        .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
                    else {
                        continue;
                    };
                    let mut values: FxHashMap<String, i128> = FxHashMap::default();
                    let mut ok = true;
                    for v in &int_vars {
                        if let Some(SmtValue::Int(val)) = model.get(&v.name) {
                            values.insert(v.name.clone(), *val);
                        } else if let Some(eq_name) = var_eq_map.get(&v.name) {
                            if let Some(SmtValue::Int(val)) = model.get(eq_name) {
                                values.insert(v.name.clone(), *val);
                            } else if let Some(&c) = var_const_map.get(eq_name) {
                                values.insert(v.name.clone(), c);
                            } else {
                                ok = false;
                                break;
                            }
                        } else if let Some(&c) = var_const_map.get(&v.name) {
                            values.insert(v.name.clone(), c);
                        } else {
                            ok = false;
                            break;
                        }
                    }
                    if !ok {
                        continue;
                    }
                    let diseqs: Vec<ChcExpr> = int_vars
                        .iter()
                        .filter_map(|v| {
                            values.get(&v.name).map(|value| {
                                ChcExpr::ne(ChcExpr::var(v.clone()), ChcExpr::Int(*value))
                            })
                        })
                        .collect();
                    if let Some(blocking) = diseqs.into_iter().reduce(ChcExpr::or) {
                        blocking_clauses.push(blocking);
                    }
                    models.push(values);
                }
            }
        }

        models
    }
}
