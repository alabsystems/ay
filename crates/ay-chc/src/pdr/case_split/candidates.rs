// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Case-split candidate detection: find predicates with constant arguments
//! that are unconstrained at init and identify equality test constants.

use crate::expr_vars::expr_var_names;
use crate::pdr::expr_utils::extract_equality_constants;
use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcProblem, ChcSort, PredicateId};
use ay_core::kani_compat::DetHashSet as FxHashSet;

use super::CaseConstraint;

impl PdrSolver {
    /// Find predicates with constant arguments that are unconstrained at init.
    ///
    /// Returns: Vec of (predicate_id, arg_index, var_name, case_constraints)
    /// where case_constraints is derived from observed equality tests against the mode variable.
    pub(super) fn find_case_split_candidates(
        problem: &ChcProblem,
        verbose: bool,
    ) -> Vec<(PredicateId, usize, String, Vec<CaseConstraint>)> {
        let mut candidates = Vec::new();

        for pred in problem.predicates() {
            let pred_id = pred.id;

            // Case splitting is only sound when the predicate is defined by facts + 1-body
            // self-loops. Otherwise, "constant argument" is not well-defined syntactically.
            let mut has_non_fact_clause = false;
            let mut self_loop_only = true;
            for clause in problem.clauses_defining(pred_id) {
                if clause.body.predicates.is_empty() {
                    continue;
                }
                has_non_fact_clause = true;
                if clause.body.predicates.len() != 1 {
                    self_loop_only = false;
                    break;
                }
                let (body_pred, _) = &clause.body.predicates[0];
                if *body_pred != pred_id {
                    self_loop_only = false;
                    break;
                }
            }
            if !has_non_fact_clause || !self_loop_only {
                continue;
            }

            // Find constant arguments (unchanged in self-loops)
            let constant_args_set = Self::detect_constant_arguments_static(problem, pred_id);
            if constant_args_set.is_empty() {
                continue;
            }
            // Sort for deterministic iteration
            let mut constant_args: Vec<usize> = constant_args_set.into_iter().collect();
            constant_args.sort_unstable();

            let fact_clauses: Vec<_> = problem
                .facts()
                .filter(|f| f.head.predicate_id() == Some(pred_id))
                .collect();
            if fact_clauses.is_empty() {
                continue;
            }

            for &arg_idx in &constant_args {
                // Require "unconstrained at init" across all facts for this predicate.
                let mut var_name_for_log: Option<String> = None;
                let mut unconstrained_in_all_facts = true;

                for clause in &fact_clauses {
                    let head_args = match &clause.head {
                        crate::ClauseHead::Predicate(_, args) => args,
                        crate::ClauseHead::False => {
                            unconstrained_in_all_facts = false;
                            break;
                        }
                    };
                    let Some(ChcExpr::Var(v)) = head_args.get(arg_idx) else {
                        unconstrained_in_all_facts = false;
                        break;
                    };
                    if v.sort != ChcSort::Int {
                        unconstrained_in_all_facts = false;
                        break;
                    }
                    var_name_for_log.get_or_insert_with(|| v.name.clone());

                    let constraint = clause
                        .body
                        .constraint
                        .clone()
                        .unwrap_or(ChcExpr::Bool(true));
                    let constraint_vars: FxHashSet<String> = expr_var_names(&constraint);
                    if constraint_vars.contains(&v.name) {
                        unconstrained_in_all_facts = false;
                        break;
                    }
                }

                if !unconstrained_in_all_facts {
                    continue;
                }

                let var_name = var_name_for_log.unwrap_or_else(|| format!("arg{arg_idx}"));

                // Scan relevant clauses to discover the constants compared against this argument.
                //
                // IMPORTANT: variable names are local to each forall binder, so we must scan per
                // clause using the variable that occurs at `arg_idx` for `pred_id` *in that clause*.
                // Scanning the whole problem for a single var_name would produce false positives
                // (or miss constants) when different clauses use different names (e.g., E vs J vs C
                // in `dillig12_m_000.smt2`).
                let mut observed_constants: FxHashSet<i128> = FxHashSet::default();
                for c in problem.clauses() {
                    let mut mode_vars: FxHashSet<String> = FxHashSet::default();

                    // Head occurrence
                    if c.head.predicate_id() == Some(pred_id) {
                        if let crate::ClauseHead::Predicate(_, args) = &c.head {
                            if let Some(ChcExpr::Var(v)) = args.get(arg_idx) {
                                if v.sort == ChcSort::Int {
                                    mode_vars.insert(v.name.clone());
                                }
                            }
                        }
                    }

                    // Body occurrences
                    for (body_pred, args) in &c.body.predicates {
                        if *body_pred != pred_id {
                            continue;
                        }
                        if let Some(ChcExpr::Var(v)) = args.get(arg_idx) {
                            if v.sort == ChcSort::Int {
                                mode_vars.insert(v.name.clone());
                            }
                        }
                    }

                    if mode_vars.is_empty() {
                        continue;
                    }

                    for mode_var in mode_vars {
                        // Scan constraint
                        if let Some(ref cexpr) = c.body.constraint {
                            observed_constants.extend(extract_equality_constants(cexpr, &mode_var));
                        }
                        // Scan body predicate arguments
                        for (_, args) in &c.body.predicates {
                            for arg_expr in args {
                                observed_constants
                                    .extend(extract_equality_constants(arg_expr, &mode_var));
                            }
                        }
                        // Scan head arguments
                        if let crate::ClauseHead::Predicate(_, hargs) = &c.head {
                            for arg_expr in hargs {
                                observed_constants
                                    .extend(extract_equality_constants(arg_expr, &mode_var));
                            }
                        }
                    }
                }

                if observed_constants.is_empty() {
                    continue;
                }

                let mut sorted_constants: Vec<i128> = observed_constants.into_iter().collect();
                sorted_constants.sort_unstable();

                let mut cases = Vec::new();
                for &k in &sorted_constants {
                    cases.push(CaseConstraint::eq(&var_name, k));
                }
                cases.push(CaseConstraint::ne_all(&var_name, &sorted_constants));

                if verbose {
                    let case_names: Vec<&str> = cases.iter().map(|c| c.name.as_str()).collect();
                    safe_eprintln!(
                        "PDR: Found case-split candidate: pred {} arg {} ({}) with cases {:?}",
                        pred_id.index(),
                        arg_idx,
                        var_name,
                        case_names
                    );
                }

                candidates.push((pred_id, arg_idx, var_name.clone(), cases));
            }
        }

        candidates
    }

    /// Static version of detect_constant_arguments that works without a PdrSolver instance.
    ///
    /// Check all self-loop clauses for this predicate.
    /// If no self-loops exist (e.g., multi-predicate SCC where transitions go through
    /// other predicates), we cannot conclude any argument is constant.
    fn detect_constant_arguments_static(
        problem: &ChcProblem,
        pred_id: PredicateId,
    ) -> FxHashSet<usize> {
        let pred = match problem.get_predicate(pred_id) {
            Some(p) => p,
            None => return FxHashSet::default(),
        };
        let arity = pred.arity();

        // Start with all positions as potentially constant
        let mut constant_positions: FxHashSet<usize> = (0..arity).collect();
        let mut found_self_loop = false;

        for clause in problem.clauses_defining(pred_id) {
            // Skip fact clauses (no body predicates)
            if clause.body.predicates.is_empty() {
                continue;
            }

            // Only check self-loops
            if clause.body.predicates.len() != 1 {
                continue;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != pred_id {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != body_args.len() || head_args.len() != arity {
                continue;
            }

            found_self_loop = true;

            // For each position, check if head_arg == body_arg (just a copy)
            for i in 0..head_args.len() {
                if !constant_positions.contains(&i) {
                    continue;
                }

                let head_arg = &head_args[i];
                let body_arg = &body_args[i];

                // Check if head_arg is exactly the same variable as body_arg
                let is_identity = match (head_arg, body_arg) {
                    (ChcExpr::Var(hv), ChcExpr::Var(bv)) => hv.name == bv.name,
                    _ => false,
                };

                if !is_identity {
                    constant_positions.remove(&i);
                }
            }
        }

        if !found_self_loop {
            return FxHashSet::default();
        }

        constant_positions
    }
}
