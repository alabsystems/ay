// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SingleLoopTransformation: Encode multi-predicate CHC as single-predicate transition system
//!
//! This module implements the transformation from a general linear CHC system to a transition
//! system (init, transition, query), following the algorithm in:
//!
//! "Horn2VMT: Translating Horn Reachability into Transition Systems" (HCVS 2020)
//!
//! The key insight is:
//! 1. Introduce an Int location variable `.loc_N` for each predicate (0=inactive, 1=active)
//! 2. Introduce typed argument variables `.arg_N_M` for each predicate argument
//! 3. Initial state: all locations 0 (no predicate holds yet)
//! 4. Each non-query clause becomes a transition disjunct
//! 5. Query: disjunction of the query clause conditions (source loc = 1 + constraint)
//!
//! Reference: Golem's SingleLoopTransformation.cc (MIT licensed)

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;

/// A transformed transition system ready for PDKIND
#[derive(Debug, Clone)]
pub(crate) struct TransformedSystem {
    /// State variables (location vars + argument vars)
    pub state_vars: Vec<ChcVar>,
    /// Initial state constraint
    pub init: ChcExpr,
    /// Transition relation
    pub transition: ChcExpr,
    /// Query/bad state constraint
    pub query: ChcExpr,
    /// Mapping from predicate to location variable
    pub _location_vars: FxHashMap<PredicateId, ChcVar>,
    /// Mapping from (predicate, arg_index) to argument variable
    pub _arg_vars: FxHashMap<(PredicateId, usize), ChcVar>,
}

impl TransformedSystem {
    /// Build a synthetic single-predicate CHcProblem from the transformed system.
    ///
    /// Creates a predicate `__sloop` with canonical vars `v0, v1, ...` matching
    /// the state variables. The init/transition/query are pre-canonicalized so
    /// that PdkindSolver's `extract_transition_system()` recovers the exact
    /// same constraints.
    pub(crate) fn to_chc_problem(&self) -> ChcProblem {
        let mut problem = ChcProblem::new();

        // Arg sorts from state vars
        let arg_sorts: Vec<ChcSort> = self.state_vars.iter().map(|v| v.sort.clone()).collect();
        let pred_id = problem.declare_predicate("__sloop", arg_sorts);

        // Canonical vars: v0, v1, ...
        let canonical: Vec<ChcVar> = self
            .state_vars
            .iter()
            .enumerate()
            .map(|(i, v)| ChcVar::new(format!("v{i}"), v.sort.clone()))
            .collect();
        let canonical_next: Vec<ChcVar> = canonical
            .iter()
            .map(|v| ChcVar::new(format!("{}_next", v.name), v.sort.clone()))
            .collect();

        // Substitution: state_var -> v_i
        let to_canonical: Vec<(ChcVar, ChcExpr)> = self
            .state_vars
            .iter()
            .zip(canonical.iter())
            .map(|(sv, cv)| (sv.clone(), ChcExpr::var(cv.clone())))
            .collect();

        // Substitution: state_var_next -> v_i_next
        let next_vars: Vec<ChcVar> = self
            .state_vars
            .iter()
            .map(|v| ChcVar::new(format!("{}_next", v.name), v.sort.clone()))
            .collect();
        let next_to_canonical: Vec<(ChcVar, ChcExpr)> = next_vars
            .iter()
            .zip(canonical_next.iter())
            .map(|(nv, cn)| (nv.clone(), ChcExpr::var(cn.clone())))
            .collect();

        let canonical_exprs: Vec<ChcExpr> =
            canonical.iter().map(|v| ChcExpr::var(v.clone())).collect();
        let canonical_next_exprs: Vec<ChcExpr> = canonical_next
            .iter()
            .map(|v| ChcExpr::var(v.clone()))
            .collect();

        // Fact clause: init[state_vars -> v_i] => __sloop(v0, v1, ...)
        let init_canonical = self.init.substitute(&to_canonical);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(init_canonical),
            ClauseHead::Predicate(pred_id, canonical_exprs.clone()),
        ));

        // Transition clause: __sloop(v0, ...) /\ transition[sv->v, sv_next->v_next]
        //                     => __sloop(v0_next, ...)
        let mut all_subs = to_canonical.clone();
        all_subs.extend(next_to_canonical);
        let trans_canonical = self.transition.substitute(&all_subs);
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(pred_id, canonical_exprs.clone())],
                Some(trans_canonical),
            ),
            ClauseHead::Predicate(pred_id, canonical_next_exprs),
        ));

        // Query clause: __sloop(v0, ...) /\ query[sv -> v] => false
        let query_canonical = self.query.substitute(&to_canonical);
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(pred_id, canonical_exprs)], Some(query_canonical)),
            ClauseHead::False,
        ));

        problem
    }
}

/// SingleLoopTransformation transforms multi-predicate CHC to single-predicate TS
pub(crate) struct SingleLoopTransformation {
    /// The CHC problem
    problem: ChcProblem,
    /// Location variables for each predicate
    location_vars: FxHashMap<PredicateId, ChcVar>,
    /// Argument variables for each (predicate, arg_index)
    arg_vars: FxHashMap<(PredicateId, usize), ChcVar>,
}

impl SingleLoopTransformation {
    /// Create a new transformation for the given CHC problem
    pub(crate) fn new(problem: ChcProblem) -> Self {
        Self {
            problem,
            location_vars: FxHashMap::default(),
            arg_vars: FxHashMap::default(),
        }
    }

    /// Check if the problem is linear (each clause body has at most one predicate)
    pub(crate) fn is_linear(&self) -> bool {
        self.problem
            .clauses()
            .iter()
            .all(|c| c.body.predicates.len() <= 1)
    }

    /// Transform the CHC problem to a transition system
    pub(crate) fn transform(&mut self) -> Option<TransformedSystem> {
        if !self.is_linear() {
            return None;
        }

        // Create location and argument variables
        self.create_variables();

        // Build initial state: all location variables false
        let init = self.build_init();

        // Build transition relation: disjunction over non-query clauses
        let transition = self.build_transition();

        // Build query: disjunction over query clause conditions
        let query = self.build_query()?;

        // Collect state variables in deterministic order (#3060)
        let mut sorted_locs: Vec<_> = self.location_vars.iter().collect();
        sorted_locs.sort_unstable_by_key(|(pid, _)| pid.index());
        let mut state_vars: Vec<ChcVar> = sorted_locs.into_iter().map(|(_, v)| v.clone()).collect();
        let mut sorted_args: Vec<_> = self.arg_vars.iter().collect();
        sorted_args.sort_unstable_by_key(|((pid, idx), _)| (pid.index(), *idx));
        for (_, var) in sorted_args {
            state_vars.push(var.clone());
        }

        Some(TransformedSystem {
            state_vars,
            init,
            transition,
            query,
            _location_vars: self.location_vars.clone(),
            _arg_vars: self.arg_vars.clone(),
        })
    }

    /// Create location and argument variables for each predicate
    fn create_variables(&mut self) {
        for pred in self.problem.predicates() {
            // Location variable: .loc_N
            let loc_var = ChcVar::new(format!(".loc_{}", pred.id.index()), ChcSort::Int);
            self.location_vars.insert(pred.id, loc_var);

            // Argument variables: .arg_N_M
            for (i, sort) in pred.arg_sorts.iter().enumerate() {
                let arg_var = ChcVar::new(format!(".arg_{}_{}", pred.id.index(), i), sort.clone());
                self.arg_vars.insert((pred.id, i), arg_var);
            }
        }
    }

    /// Build initial state: all location variables = 0
    fn build_init(&self) -> ChcExpr {
        let mut conjuncts = Vec::new();

        // Sort for deterministic formula ordering (#3060)
        let mut sorted_locs: Vec<_> = self.location_vars.iter().collect();
        sorted_locs.sort_unstable_by_key(|(pid, _)| pid.index());
        for (_, loc_var) in &sorted_locs {
            conjuncts.push(ChcExpr::eq(
                ChcExpr::var((*loc_var).clone()),
                ChcExpr::int(0),
            ));
        }

        if conjuncts.is_empty() {
            ChcExpr::Bool(true)
        } else {
            conjuncts
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true))
        }
    }

    /// Build transition relation as disjunction of NON-QUERY clause translations
    fn build_transition(&self) -> ChcExpr {
        let mut disjuncts = Vec::new();

        for clause in self.problem.clauses() {
            // Skip query clauses - they define the query, not the transition
            if clause.is_query() {
                continue;
            }

            if let Some(translated) = self.translate_clause(clause) {
                disjuncts.push(translated);
            }
        }

        if disjuncts.is_empty() {
            ChcExpr::Bool(false)
        } else {
            disjuncts
                .into_iter()
                .reduce(ChcExpr::or)
                .unwrap_or(ChcExpr::Bool(false))
        }
    }

    /// Build a substitution map from clause-local variables to state variables.
    ///
    /// When a predicate argument is a simple variable (like `x`), we substitute
    /// `x -> arg_var` in the clause constraint to eliminate the free variable.
    /// When the argument is a complex expression (like `x - 1`), we need an
    /// explicit equality constraint instead.
    ///
    /// This prevents free clause-local variables from leaking into the
    /// transition system, which would make PDKind's verification fail (#2690).
    ///
    /// `substitutions` accumulates across the body and head passes of one
    /// clause. When the SAME clause variable appears in several predicate
    /// argument positions (the ubiquitous passthrough `P(x) => Q(x)`, or a
    /// duplicated argument `P(x, x)`), only the FIRST occurrence becomes a
    /// substitution; every later occurrence emits a linking equality
    /// `later_slot = first_slot`. Previously each occurrence pushed its own
    /// substitution pair and `substitute` applied only one of them, silently
    /// DROPPING the linkage between the state slots (inc-9): the encoding
    /// over-approximated (head slots became unconstrained), which is sound
    /// for Safe verdicts but produced spurious shallow counterexamples in
    /// every Unsafe-side consumer of this transformation.
    fn build_clause_var_substitution(
        &self,
        pred: &PredicateId,
        args: &[ChcExpr],
        use_next: bool,
        substitutions: &mut Vec<(ChcVar, ChcExpr)>,
    ) -> Vec<ChcExpr> {
        let mut equality_constraints = Vec::new();

        for (i, arg) in args.iter().enumerate() {
            if let Some(arg_var) = self.arg_vars.get(&(*pred, i)) {
                let target_var = if use_next {
                    ChcVar::new(format!("{}_next", arg_var.name), arg_var.sort.clone())
                } else {
                    arg_var.clone()
                };
                if let ChcExpr::Var(clause_var) = arg {
                    if let Some((_, mapped)) = substitutions
                        .iter()
                        .find(|(existing, _)| existing == clause_var)
                    {
                        // Same clause variable already bound to another state
                        // slot: link the two slots instead of shadowing the
                        // earlier substitution.
                        equality_constraints
                            .push(ChcExpr::eq(ChcExpr::var(target_var), mapped.clone()));
                    } else {
                        substitutions.push((clause_var.clone(), ChcExpr::var(target_var)));
                    }
                } else {
                    equality_constraints.push(ChcExpr::eq(ChcExpr::var(target_var), arg.clone()));
                }
            }
        }

        equality_constraints
    }

    /// Translate a single non-query clause to a transition disjunct
    fn translate_clause(&self, clause: &HornClause) -> Option<ChcExpr> {
        let mut conjuncts = Vec::new();
        let mut substitutions: Vec<(ChcVar, ChcExpr)> = Vec::new();

        // Source location handling
        // Sort location_vars for deterministic formula ordering (#3060)
        let mut sorted_locs: Vec<_> = self.location_vars.iter().collect();
        sorted_locs.sort_unstable_by_key(|(pid, _)| pid.index());
        if clause.body.predicates.is_empty() {
            // Fact clause: coming from initial state (all locations = 0)
            for (_, loc_var) in &sorted_locs {
                conjuncts.push(ChcExpr::eq(
                    ChcExpr::var((*loc_var).clone()),
                    ChcExpr::int(0),
                ));
            }
        } else {
            let (source_pred, source_args) = &clause.body.predicates[0];
            let source_loc_var = self.location_vars.get(source_pred)?;

            conjuncts.push(ChcExpr::eq(
                ChcExpr::var(source_loc_var.clone()),
                ChcExpr::int(1),
            ));

            for (pred, loc_var) in &sorted_locs {
                if **pred != *source_pred {
                    conjuncts.push(ChcExpr::eq(
                        ChcExpr::var((*loc_var).clone()),
                        ChcExpr::int(0),
                    ));
                }
            }

            let eqs = self.build_clause_var_substitution(
                source_pred,
                source_args,
                false,
                &mut substitutions,
            );
            conjuncts.extend(eqs);
        }

        // Target location and arguments
        if let ClauseHead::Predicate(target_pred, target_args) = &clause.head {
            let target_loc_var = self.location_vars.get(target_pred)?;
            let next_target = ChcVar::new(format!("{}_next", target_loc_var.name), ChcSort::Int);
            conjuncts.push(ChcExpr::eq(ChcExpr::var(next_target), ChcExpr::int(1)));

            for (pred, loc_var) in &self.location_vars {
                if *pred != *target_pred {
                    let next_var = ChcVar::new(format!("{}_next", loc_var.name), ChcSort::Int);
                    conjuncts.push(ChcExpr::eq(ChcExpr::var(next_var), ChcExpr::int(0)));
                }
            }

            let eqs = self.build_clause_var_substitution(
                target_pred,
                target_args,
                true,
                &mut substitutions,
            );
            conjuncts.extend(eqs);
        } else {
            return None;
        }

        // Apply substitutions to the constraint to eliminate clause-local variables
        if let Some(constraint) = &clause.body.constraint {
            let substituted = if substitutions.is_empty() {
                constraint.clone()
            } else {
                constraint.substitute(&substitutions)
            };
            conjuncts.push(substituted);
        }

        // Apply substitutions to equality constraints that reference clause-local vars
        if !substitutions.is_empty() {
            conjuncts = conjuncts
                .into_iter()
                .map(|c| c.substitute(&substitutions))
                .collect();
        }

        if conjuncts.is_empty() {
            Some(ChcExpr::Bool(true))
        } else {
            Some(
                conjuncts
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .unwrap_or(ChcExpr::Bool(true)),
            )
        }
    }

    /// Build query from query clauses
    /// A query clause is: P(x) /\ constraint => false
    /// This means: if we're at P with constraint satisfied, we have a bug
    /// Query = (P's location is true) AND constraint
    fn build_query(&self) -> Option<ChcExpr> {
        let mut query_disjuncts = Vec::new();

        for clause in self.problem.queries() {
            let mut query_conjuncts = Vec::new();
            let mut substitutions: Vec<(ChcVar, ChcExpr)> = Vec::new();

            // The source predicate's location must be active (= 1)
            if !clause.body.predicates.is_empty() {
                let (source_pred, source_args) = &clause.body.predicates[0];
                let source_loc_var = self.location_vars.get(source_pred)?;
                query_conjuncts.push(ChcExpr::eq(
                    ChcExpr::var(source_loc_var.clone()),
                    ChcExpr::int(1),
                ));

                let eqs = self.build_clause_var_substitution(
                    source_pred,
                    source_args,
                    false,
                    &mut substitutions,
                );
                query_conjuncts.extend(eqs);
            }

            // Add the query's constraint (with substitutions applied)
            if let Some(constraint) = &clause.body.constraint {
                let substituted = if substitutions.is_empty() {
                    constraint.clone()
                } else {
                    constraint.substitute(&substitutions)
                };
                query_conjuncts.push(substituted);
            }

            // Apply substitutions to equality constraints
            if !substitutions.is_empty() {
                query_conjuncts = query_conjuncts
                    .into_iter()
                    .map(|c| c.substitute(&substitutions))
                    .collect();
            }

            if !query_conjuncts.is_empty() {
                let query_part = query_conjuncts
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .unwrap_or(ChcExpr::Bool(true));
                query_disjuncts.push(query_part);
            }
        }

        if query_disjuncts.is_empty() {
            None
        } else if query_disjuncts.len() == 1 {
            Some(query_disjuncts.swap_remove(0))
        } else {
            Some(ChcExpr::or_all(query_disjuncts))
        }
    }

    /// Back-translate an invariant from the transformed system to predicate interpretations
    pub(crate) fn back_translate_invariant(
        &self,
        invariant: &ChcExpr,
    ) -> FxHashMap<PredicateId, ChcExpr> {
        let mut interpretations = FxHashMap::default();

        for pred in self.problem.predicates() {
            // For each predicate, substitute:
            // - Its location variable with true
            // - All other location variables with false
            // - Then extract the constraint on its argument variables

            let mut substitutions = Vec::new();

            for (p, loc_var) in &self.location_vars {
                let value = if *p == pred.id {
                    ChcExpr::int(1)
                } else {
                    ChcExpr::int(0)
                };
                substitutions.push((loc_var.clone(), value));
            }

            let pred_invariant = invariant.substitute(&substitutions);

            // Now translate argument variables back to the predicate's canonical variables
            let mut arg_subs = Vec::new();
            for (i, sort) in pred.arg_sorts.iter().enumerate() {
                if let Some(arg_var) = self.arg_vars.get(&(pred.id, i)) {
                    // Create canonical variable name (v0, v1, etc.)
                    let canonical = ChcVar::new(format!("v{i}"), sort.clone());
                    arg_subs.push((arg_var.clone(), ChcExpr::var(canonical)));
                }
            }

            let final_invariant = pred_invariant.substitute(&arg_subs);
            interpretations.insert(pred.id, final_invariant);
        }

        interpretations
    }
}
