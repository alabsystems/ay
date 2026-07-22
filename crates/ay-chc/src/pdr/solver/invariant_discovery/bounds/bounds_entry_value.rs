// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Entry-value constant bounds for derived predicates (#4751).
//!
//! For a derived predicate (no fact clauses) whose argument at position `i` is
//! UNCHANGED by every self-loop clause, any bound on the values that flow into
//! position `i` through the entry edges is an invariant: the entry edges
//! establish it and the self-loops preserve it trivially.
//!
//! The candidate constants are harvested from the problem's integer literals
//! (plus a small default range), and every candidate is admitted through
//! `add_discovered_invariant`, i.e. it is SMT-checked to be entry-inductive
//! against the CURRENT source-predicate frame and self-inductive over the
//! predicate's own transitions. Nothing is assumed: a candidate that the
//! frames cannot justify is simply rejected.
//!
//! This pass is only useful AFTER the source-predicate frames carry their
//! relational invariants (e.g. dillig12_m's FUN kernel equality D = 2*C makes
//! the FUN→SAD entry value `F = ite(C=1, 2+D-2E, 1)` provably <= 2), so the
//! orchestrator runs it in the nonfixpoint phase after affine-kernel
//! discovery.
//!
//! Motivation: dillig12_m's SAD predicate needs `first_arg <= 2` — without it
//! the error clause `SAD(A,B) ∧ B >= A ∧ B >= 5 → false` cannot be blocked by
//! any difference bound alone.

use super::*;

/// Per-predicate wall-clock budget for the entry-value bound pass.
const ENTRY_VALUE_BOUND_PRED_BUDGET: std::time::Duration = std::time::Duration::from_secs(2);

/// Cap on the harvested candidate-constant magnitude. Large literals (array
/// offsets, bitmasks) produce useless bound candidates and waste SMT budget.
const ENTRY_VALUE_BOUND_MAX_CONST: i128 = 64;

impl PdrSolver {
    /// Discover constant bounds `arg <= c` / `arg >= c` for self-loop-constant
    /// arguments of derived predicates. See module docs.
    pub(in crate::pdr::solver) fn discover_derived_entry_value_bounds(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Harvest candidate constants once per problem.
        let mut consts: Vec<i128> = vec![-2, -1, 0, 1, 2];
        {
            let mut literals: Vec<i128> = Vec::new();
            for clause in self.problem.clauses() {
                if let Some(ref c) = clause.body.constraint {
                    Self::collect_int_literals(c, &mut literals);
                }
                if let crate::ClauseHead::Predicate(_, ref args) = clause.head {
                    for arg in args {
                        Self::collect_int_literals(arg, &mut literals);
                    }
                }
            }
            for k in literals {
                if k.abs() <= ENTRY_VALUE_BOUND_MAX_CONST && !consts.contains(&k) {
                    consts.push(k);
                }
            }
        }
        // Ascending order: for upper bounds the FIRST admissible `arg <= c` is
        // the tightest; for lower bounds we iterate the same list descending.
        consts.sort_unstable();

        for pred in &predicates {
            if self.is_cancelled() {
                return;
            }
            if self.predicate_has_facts(pred.id) || !self.predicate_is_reachable(pred.id) {
                continue;
            }
            // Need at least one self-loop: detect_constant_arguments only
            // reasons over self-loop clauses and returns nothing otherwise.
            let has_self_loop = self.problem.clauses_defining(pred.id).any(|clause| {
                clause.body.predicates.len() == 1 && clause.body.predicates[0].0 == pred.id
            });
            if !has_self_loop {
                continue;
            }
            let constant_args = self.detect_constant_arguments(pred.id);
            if constant_args.is_empty() {
                continue;
            }
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let pred_start = ay_core::time::Instant::now();
            for &idx in &constant_args {
                let Some(var) = canonical_vars.get(idx) else {
                    continue;
                };
                if !matches!(var.sort, ChcSort::Int) {
                    continue;
                }

                // Tightest upper bound: ascending scan, stop at first success.
                for &c in &consts {
                    if self.is_cancelled() || pred_start.elapsed() >= ENTRY_VALUE_BOUND_PRED_BUDGET
                    {
                        break;
                    }
                    let cand = ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(c));
                    if self.add_discovered_invariant(pred.id, cand, 1) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: entry-value bound for derived pred {}: {} <= {} (#4751)",
                                pred.id.index(),
                                var.name,
                                c
                            );
                        }
                        break;
                    }
                }

                // Tightest lower bound: descending scan, stop at first success.
                for &c in consts.iter().rev() {
                    if self.is_cancelled() || pred_start.elapsed() >= ENTRY_VALUE_BOUND_PRED_BUDGET
                    {
                        break;
                    }
                    let cand = ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(c));
                    if self.add_discovered_invariant(pred.id, cand, 1) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: entry-value bound for derived pred {}: {} >= {} (#4751)",
                                pred.id.index(),
                                var.name,
                                c
                            );
                        }
                        break;
                    }
                }
            }
        }
    }

    /// Collect all integer literals appearing in an expression.
    fn collect_int_literals(expr: &ChcExpr, out: &mut Vec<i128>) {
        match expr {
            ChcExpr::Int(k) => out.push(*k),
            ChcExpr::Op(_, args) => {
                for arg in args {
                    Self::collect_int_literals(arg, out);
                }
            }
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    Self::collect_int_literals(arg, out);
                }
            }
            _ => {}
        }
    }
}
