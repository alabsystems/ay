// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Edge Summary computation for inter-predicate invariant propagation.
//!
//! This module implements Golem-style edge may-summaries for deriving entry
//! constraints on predicates. For a clause `P(body_args) ∧ c ⇒ Q(head_args)`:
//!
//! - Build: `F := Frame[level](P)[body_args] ∧ c`
//! - Project: `Σ := MBP_project(F, vars(head_args))`
//! - Use `Σ` as entry constraint for Q's proactive invariant discovery
//!
//! See: #1429, the development design notes
//!
//! Reference: Golem's `getEdgeMaySummary` in `reference/golem/src/engine/Spacer.cc:634-651`

use super::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashSet as FxHashSet;

impl PdrSolver {
    /// Compute the edge may-summary for a clause at a given level.
    ///
    /// For clause `P(body_args) ∧ c ⇒ Q(head_args)`:
    /// Returns `MBP_project(Frame[level](P)[body_args] ∧ c, vars(head_args))`
    ///
    /// Returns `Some(Bool(true))` if feasibility is undecided (Unknown) — conservative
    /// over-approximation since we lack a model for MBP.
    ///
    /// Returns None if:
    /// - No frame lemmas exist for body predicates
    /// - The clause has no body predicates (fact clause)
    /// - The edge is provably infeasible (SMT returns Unsat)
    pub(in crate::pdr::solver) fn compute_edge_may_summary(
        &mut self,
        clause_index: usize,
        level: usize,
    ) -> Option<ChcExpr> {
        let clause = self.problem.clauses().get(clause_index)?.clone();

        // Fact clauses have no edge summary (they ARE the summary)
        if clause.body.predicates.is_empty() {
            return None;
        }

        // Get head predicate and args
        let (head_pred, head_args) = match &clause.head {
            crate::ClauseHead::Predicate(pred, args) => (*pred, args.clone()),
            crate::ClauseHead::False => return None, // Query clause
        };

        // #2492: Normalize expression head args by introducing fresh proxy variables.
        // For clause `P(body) ∧ c ⇒ Q(x+1, y)`, introduce `_head_0 = x+1` and retain
        // `_head_0` instead of trying to project directly on expression args.
        let canonical_vars = self.canonical_vars(head_pred)?.to_vec();
        let mut proxy_equalities: Vec<ChcExpr> = Vec::new();
        let mut proxy_vars: Vec<ChcVar> = Vec::new();

        for (i, head_arg) in head_args.iter().enumerate() {
            let proxy = match head_arg {
                ChcExpr::Var(v) => v.clone(),
                expr => {
                    // Create a proxy variable that stands in for the expression.
                    let sort = canonical_vars
                        .get(i)
                        .map_or(ChcSort::Int, |cv| cv.sort.clone());
                    let pv = ChcVar::new(format!("_head_{i}"), sort);
                    proxy_equalities.push(ChcExpr::eq(ChcExpr::var(pv.clone()), expr.clone()));
                    pv
                }
            };
            proxy_vars.push(proxy);
        }

        // Build: transition constraint ∧ ⋀_{source} frame_lemmas(source, level) ∧ proxy_eqs
        let mut conjuncts = Vec::new();

        // Add clause body constraint
        if let Some(ref constraint) = clause.body.constraint {
            conjuncts.push(constraint.clone());
        }

        // Add frame lemmas for each body predicate
        for (body_pred, body_args) in &clause.body.predicates {
            if let Some(frame_lemmas) = self.cumulative_frame_constraint(level, *body_pred) {
                // Apply frame lemmas to body arguments
                if let Some(applied) = self.apply_to_args(*body_pred, &frame_lemmas, body_args) {
                    conjuncts.push(applied);
                }
            }
            // If no frame lemmas, the body predicate is unconstrained at this level
        }

        // Add proxy equalities for expression head args
        conjuncts.extend(proxy_equalities);

        // If no constraints on edge, return None (unconstrained edge = true, provides no bounds)
        if conjuncts.is_empty() {
            return None;
        }

        let edge_formula = ChcExpr::and_all(conjuncts);

        // Get model for MBP projection
        // #7984: Use persistent executor backend for integer arithmetic.
        let sat_result = self.check_sat_via_executor_backend(&edge_formula);

        let model = match sat_result {
            SmtResult::Sat(model) => model,
            // #2491: Distinguish genuinely infeasible edges from undecided ones.
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // Edge is provably infeasible — no reachable states flow through it.
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Edge clause {} at level {} is infeasible (UNSAT)",
                        clause_index,
                        level
                    );
                }
                return None;
            }
            SmtResult::Unknown => {
                // #7165: Try executor fallback before giving up. The internal
                // DPLL(T) is incomplete on disequality-heavy QF_LIA and mod/div
                // queries. The full ay-dpll executor handles these via theory
                // propagation + CEGQI.
                if !self.problem.has_bv_sorts() && !edge_formula.contains_array_ops() {
                    self.smt.reset();
                    let fallback = self.smt.check_sat_with_executor_fallback_timeout(
                        &edge_formula,
                        std::time::Duration::from_secs(2),
                    );
                    match fallback {
                        SmtResult::Sat(m) => m,
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Edge clause {} at level {} infeasible via executor fallback",
                                    clause_index,
                                    level
                                );
                            }
                            return None;
                        }
                        SmtResult::Unknown => {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Edge clause {} at level {} returned Unknown (executor also) — \
                                     treating as unconstrained",
                                    clause_index,
                                    level
                                );
                            }
                            return Some(ChcExpr::Bool(true));
                        }
                    }
                } else {
                    // Unknown != Unsat: we cannot prove infeasibility, so return a
                    // conservative may-summary (true = any head-arg assignment is
                    // possible through this edge). This prevents falsely dropping
                    // feasible edges from the entry-constraint disjunction (#2491).
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Edge clause {} at level {} returned Unknown — \
                             treating as unconstrained",
                            clause_index,
                            level
                        );
                    }
                    return Some(ChcExpr::Bool(true));
                }
            }
        };

        // #2492: Retain vars from full head-arg expressions, not only direct vars.
        let retained_var_names: FxHashSet<String> =
            proxy_vars.iter().map(|v| v.name.clone()).collect();

        let all_vars = edge_formula.vars();
        let vars_to_eliminate: Vec<ChcVar> = all_vars
            .into_iter()
            .filter(|v| !retained_var_names.contains(&v.name))
            .collect();

        // Project using MBP
        let projected = self.mbp.project(&edge_formula, &vars_to_eliminate, &model);

        // Map proxy/head vars to canonical head predicate variables
        let mut result = projected;

        let subst: Vec<(ChcVar, ChcExpr)> = proxy_vars
            .iter()
            .zip(canonical_vars.iter())
            .filter(|(pv, cv)| pv.name != cv.name)
            .map(|(pv, cv)| (pv.clone(), ChcExpr::var(cv.clone())))
            .collect();
        if !subst.is_empty() {
            result = result.substitute(&subst);
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: Edge summary for clause {} at level {}: {}",
                clause_index,
                level,
                result
            );
        }

        Some(result)
    }

    /// Get entry constraints for a predicate via all incoming edges.
    ///
    /// Returns the disjunction of edge may-summaries from all clauses
    /// that define this predicate.
    pub(in crate::pdr::solver) fn get_entry_constraints(
        &mut self,
        pred: PredicateId,
        level: usize,
    ) -> Option<ChcExpr> {
        // Find all clauses that define this predicate
        let defining_clauses: Vec<usize> = self
            .problem
            .clauses()
            .iter()
            .enumerate()
            .filter_map(|(i, c)| {
                if c.head.predicate_id() == Some(pred) && !c.body.predicates.is_empty() {
                    Some(i)
                } else {
                    None
                }
            })
            .collect();

        if defining_clauses.is_empty() {
            return None;
        }

        // Compute edge summary for each incoming clause
        let mut summaries = Vec::new();
        for clause_idx in defining_clauses {
            if let Some(summary) = self.compute_edge_may_summary(clause_idx, level) {
                // #2491: if any edge is unconstrained (true), the whole disjunction is true.
                if matches!(summary, ChcExpr::Bool(true)) {
                    return Some(ChcExpr::Bool(true));
                }
                summaries.push(summary);
            }
        }

        if summaries.is_empty() {
            return None;
        }

        // Return disjunction over all entry paths
        if summaries.len() == 1 {
            Some(summaries.swap_remove(0))
        } else {
            Some(ChcExpr::or_all(summaries))
        }
    }

    /// Discover bound invariants for derived predicates using edge summaries.
    ///
    /// For predicates without fact clauses, compute entry constraints from
    /// incoming edges and extract bounds that are self-inductive.
    ///
    /// #1429: MBP edge-entry summaries for derived predicates.
    pub(in crate::pdr::solver) fn discover_edge_summary_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            // Only process predicates without facts (derived predicates)
            if self.predicate_has_facts(pred.id) {
                continue;
            }

            // Skip unreachable predicates
            if !self.predicate_is_reachable(pred.id) {
                continue;
            }

            // Get entry constraints at level 1 (using frame[1] lemmas from source predicates)
            let entry_constraint = match self.get_entry_constraints(pred.id, 1) {
                Some(c) => c,
                None => continue,
            };

            // #2491: Bool(true) means all edges were Unknown — no useful bounds.
            if matches!(entry_constraint, ChcExpr::Bool(true)) {
                continue;
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Entry constraint for derived pred {}: {}",
                    pred.id.index(),
                    entry_constraint
                );
            }

            // Extract atomic bounds from the entry constraint
            let bounds = Self::extract_bounds_from_constraint(&entry_constraint);

            // Verify predicate has canonical vars (needed for bounds to be meaningful)
            if self.canonical_vars(pred.id).is_none() {
                continue;
            }

            // Try each bound as a potential invariant
            // add_discovered_invariant handles all validation (init-validity, self-inductiveness,
            // entry-inductiveness) so we just submit candidates and let it filter.
            for bound in bounds {
                if self.add_discovered_invariant(pred.id, bound.clone(), 1) && self.config.verbose {
                    safe_eprintln!(
                        "PDR: Edge-derived invariant for pred {}: {}",
                        pred.id.index(),
                        bound
                    );
                }
            }
        }
    }

    /// Extract atomic bounds (var >= c, var <= c) from a constraint formula.
    fn extract_bounds_from_constraint(constraint: &ChcExpr) -> Vec<ChcExpr> {
        let mut bounds = Vec::new();
        Self::collect_bounds_recursive(constraint, &mut bounds);
        bounds
    }

    fn supports_arithmetic_bound(var_expr: &ChcExpr, bound_expr: &ChcExpr) -> bool {
        matches!(var_expr.sort(), ChcSort::Int | ChcSort::Real)
            && var_expr.sort() == bound_expr.sort()
    }

    fn collect_bounds_recursive(expr: &ChcExpr, bounds: &mut Vec<ChcExpr>) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            // Equality: var = c implies both var >= c and var <= c
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let (var_expr, const_expr) = if matches!(&*args[0], ChcExpr::Var(_)) {
                    (Some((*args[0]).clone()), Some((*args[1]).clone()))
                } else if matches!(&*args[1], ChcExpr::Var(_)) {
                    (Some((*args[1]).clone()), Some((*args[0]).clone()))
                } else {
                    (None, None)
                };
                if let (Some(v), Some(c)) = (var_expr, const_expr) {
                    if Self::supports_arithmetic_bound(&v, &c) {
                        // Add both bounds implied by equality
                        bounds.push(ChcExpr::ge(v.clone(), c.clone()));
                        bounds.push(ChcExpr::le(v, c));
                    }
                }
            }
            // Atomic bounds: var >= c or var > c
            ChcExpr::Op(ChcOp::Ge | ChcOp::Gt, args) if args.len() == 2 => {
                // Handle both `var >= c` and `c <= var` (reversed form)
                if matches!(&*args[0], ChcExpr::Var(_))
                    && Self::supports_arithmetic_bound(args[0].as_ref(), args[1].as_ref())
                {
                    bounds.push(expr.clone());
                } else if matches!(&*args[1], ChcExpr::Var(_))
                    && Self::supports_arithmetic_bound(args[1].as_ref(), args[0].as_ref())
                {
                    // c >= var means var <= c - convert
                    let var = args[1].clone();
                    let c = args[0].clone();
                    bounds.push(ChcExpr::le((*var).clone(), (*c).clone()));
                }
            }
            // Atomic bounds: var <= c or var < c
            ChcExpr::Op(ChcOp::Le | ChcOp::Lt, args) if args.len() == 2 => {
                // Handle both `var <= c` and `c >= var` (reversed form)
                if matches!(&*args[0], ChcExpr::Var(_))
                    && Self::supports_arithmetic_bound(args[0].as_ref(), args[1].as_ref())
                {
                    bounds.push(expr.clone());
                } else if matches!(&*args[1], ChcExpr::Var(_))
                    && Self::supports_arithmetic_bound(args[1].as_ref(), args[0].as_ref())
                {
                    // c <= var means var >= c - convert
                    let var = args[1].clone();
                    let c = args[0].clone();
                    bounds.push(ChcExpr::ge((*var).clone(), (*c).clone()));
                }
            }
            // Recurse into conjunctions
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    Self::collect_bounds_recursive(arg, bounds);
                }
            }
            // For disjunctions, we can only extract bounds that appear in ALL disjuncts
            // For now, skip disjunctions (conservative) - a bound must hold on all paths
            // to be safe as an invariant
            _ => {}
        })
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
