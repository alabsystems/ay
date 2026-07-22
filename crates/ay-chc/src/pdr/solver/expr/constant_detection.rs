// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constant argument detection and variable substitution.
//!
//! Detects which predicate arguments remain constant across all transitions,
//! and provides canonical variable substitution for applying frame invariants
//! to clause contexts.

use super::super::PdrSolver;
use crate::{ChcExpr, ChcOp, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

impl PdrSolver {
    /// Check if an expression consists only of a single constant argument variable.
    pub(in crate::pdr::solver) fn expr_is_pure_constant_arg(
        expr: &ChcExpr,
        canonical_vars: &[ChcVar],
        constant_positions: &FxHashSet<usize>,
    ) -> bool {
        if let ChcExpr::Var(v) = expr {
            // Check if this variable corresponds to a constant position
            for (idx, canon) in canonical_vars.iter().enumerate() {
                if canon.name == v.name && constant_positions.contains(&idx) {
                    return true;
                }
            }
        }
        false
    }

    /// Detect which argument positions are constant across all self-transitions.
    ///
    /// A position is constant if for all self-loop clauses (head_pred = body_pred),
    /// the head argument at that position equals the body argument (i.e., the value
    /// is just copied, not modified).
    ///
    /// This is useful for benchmarks like dillig12_m where the 5th argument (E) is
    /// constant throughout execution - it's unconstrained at init but never changes.
    ///
    /// Returns a set of constant argument indices for the given predicate.
    pub(in crate::pdr::solver) fn detect_constant_arguments(
        &self,
        pred_id: PredicateId,
    ) -> FxHashSet<usize> {
        let canonical_vars = match self.canonical_vars(pred_id) {
            Some(v) => v.to_vec(),
            None => return FxHashSet::default(),
        };

        // Start with all positions as potentially constant
        let mut constant_positions: FxHashSet<usize> = (0..canonical_vars.len()).collect();

        // Track whether we found any self-loop clauses. If a predicate has no self-loops
        // (e.g., in a multi-predicate SCC where transitions go through other predicates),
        // we cannot conclude any argument is constant from self-loop analysis alone.
        // Returning all positions as "constant" would be unsound — it would suppress
        // parity invariant discovery for variables that DO change through the SCC cycle.
        // Bug: #3121 regression — dillig02_m parity discovery was skipped because inv
        // has no self-loops, causing detect_constant_arguments to return all positions.
        let mut found_self_loop = false;

        // Check all self-loop clauses for this predicate
        for clause in self.problem.clauses_defining(pred_id) {
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

            if head_args.len() != body_args.len() || head_args.len() != canonical_vars.len() {
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

        // No self-loop clauses: cannot conclude any argument is constant.
        if !found_self_loop {
            return FxHashSet::default();
        }

        if self.config.verbose && !constant_positions.is_empty() {
            let const_names: Vec<_> = constant_positions
                .iter()
                .filter_map(|&i| canonical_vars.get(i).map(|v| v.name.clone()))
                .collect();
            safe_eprintln!(
                "PDR: Constant arguments for pred {}: {:?}",
                pred_id.index(),
                const_names
            );
        }

        constant_positions
    }

    /// Detect variables with tight inductive bounds in frame[1].
    ///
    /// Returns indices of variables where frame[1] has both `var >= c` and `var <= c`
    /// for the same constant c (same predicate). These variables are effectively
    /// constant — they have a proven-inductive exact value.
    ///
    /// This supplements `detect_constant_arguments` (which only works for self-loop
    /// predicates) for multi-predicate problems where there are no self-loops
    /// but the init bounds are inductive through the SCC cycle.
    pub(in crate::pdr::solver) fn detect_frame_tight_bound_vars(
        &self,
        pred_id: PredicateId,
    ) -> FxHashSet<usize> {
        let canonical_vars = match self.canonical_vars(pred_id) {
            Some(v) => v,
            None => return FxHashSet::default(),
        };
        if self.frames.len() < 2 {
            return FxHashSet::default();
        }

        // Collect lower and upper bounds from frame[1] lemmas for this predicate
        let mut lower_bounds: FxHashMap<usize, i128> = FxHashMap::default();
        let mut upper_bounds: FxHashMap<usize, i128> = FxHashMap::default();

        for lemma in &self.frames[1].lemmas {
            if lemma.predicate != pred_id {
                continue;
            }
            // Match (>= var c) pattern
            if let ChcExpr::Op(ChcOp::Ge, ref args) = lemma.formula {
                if args.len() == 2 {
                    if let (ChcExpr::Var(ref v), ChcExpr::Int(c)) =
                        (args[0].as_ref(), args[1].as_ref())
                    {
                        if let Some(idx) = canonical_vars.iter().position(|cv| cv.name == v.name) {
                            // Keep the tightest (highest) lower bound
                            lower_bounds
                                .entry(idx)
                                .and_modify(|e| *e = (*e).max(*c))
                                .or_insert(*c);
                        }
                    }
                }
            }
            // Match (<= var c) pattern
            if let ChcExpr::Op(ChcOp::Le, ref args) = lemma.formula {
                if args.len() == 2 {
                    if let (ChcExpr::Var(ref v), ChcExpr::Int(c)) =
                        (args[0].as_ref(), args[1].as_ref())
                    {
                        if let Some(idx) = canonical_vars.iter().position(|cv| cv.name == v.name) {
                            // Keep the tightest (lowest) upper bound
                            upper_bounds
                                .entry(idx)
                                .and_modify(|e| *e = (*e).min(*c))
                                .or_insert(*c);
                        }
                    }
                }
            }
        }

        // Variables where lower == upper are frame-constant
        let mut tight: FxHashSet<usize> = FxHashSet::default();
        for (&idx, &lb) in &lower_bounds {
            if upper_bounds.get(&idx) == Some(&lb) {
                tight.insert(idx);
            }
        }
        tight
    }

    /// Substitute canonical variable names in an expression with body args.
    /// This is used to apply frame invariants (which use canonical names like __p0_a3)
    /// to clause contexts (which use local variable names like C).
    pub(in crate::pdr::solver) fn substitute_canonical_vars(
        expr: &ChcExpr,
        canonical_vars: &[ChcVar],
        body_args: &[ChcExpr],
    ) -> ChcExpr {
        if canonical_vars.len() != body_args.len() {
            return expr.clone();
        }
        let map: FxHashMap<String, ChcExpr> = canonical_vars
            .iter()
            .zip(body_args.iter())
            .map(|(cv, ba)| (cv.name.clone(), ba.clone()))
            .collect();
        expr.substitute_name_map(&map)
    }
}
