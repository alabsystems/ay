// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Range threshold search, delegated helpers, and interpolant weakening.

use super::super::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, PredicateId};
use std::sync::Arc;

impl PdrSolver {
    /// Binary search to find the optimal threshold for a range lemma.
    ///
    /// For `is_ge=true`: Find smallest K in [lo, hi] such that (x >= K) is inductive
    /// For `is_ge=false`: Find largest K in [lo, hi] such that (x <= K) is inductive
    ///
    /// Returns the best threshold found, or the starting bound if nothing better works.
    ///
    /// Given conjuncts like (D=1, E=1, F=2), tries to discover relational equalities:
    /// - D = E (both have value 1)
    /// - D = F - 1 (or F = D + 1)
    ///
    /// If a relational equality is inductive, it can replace multiple point constraints
    /// with a single, more powerful relational constraint.
    ///
    /// This implements a key insight from Spacer: when blocking states like (D=0,E=0)
    /// and (D=1,E=1), we should discover that D=E is an invariant, not just block
    /// each point individually.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::pdr::solver) fn binary_search_threshold(
        &mut self,
        conjuncts: &[ChcExpr],
        idx: usize,
        var: &crate::ChcVar,
        lo: i128,
        hi: i128,
        predicate: PredicateId,
        level: usize,
        is_ge: bool,
    ) -> i128 {
        // Limit search iterations for performance
        const MAX_SEARCH_ITERS: usize = 10;

        if lo >= hi {
            return if is_ge { hi } else { lo };
        }

        let mut best = if is_ge { hi } else { lo };
        let mut search_lo = lo;
        let mut search_hi = hi;

        for _ in 0..MAX_SEARCH_ITERS {
            if search_lo >= search_hi {
                break;
            }

            let mid = search_lo + (search_hi - search_lo) / 2;

            let test_formula = if is_ge {
                ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(mid))
            } else {
                ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(mid))
            };

            let mut test_conjuncts = conjuncts.to_vec();
            test_conjuncts[idx] = test_formula;
            let generalized = Self::build_conjunction(&test_conjuncts);

            if self.is_inductive_blocking(&generalized, predicate, level) {
                // This threshold works
                best = mid;
                if is_ge {
                    // Search for smaller threshold
                    search_hi = mid;
                } else {
                    // Search for larger threshold
                    search_lo = mid + 1;
                }
            } else {
                // This threshold doesn't work
                if is_ge {
                    // Need larger threshold
                    search_lo = mid + 1;
                } else {
                    // Need smaller threshold
                    search_hi = mid;
                }
            }
        }

        best
    }

    /// Extract all disequalities (not (= a b)) from an expression.
    /// Returns Vec<(lhs, rhs)> for each disequality found.
    /// Delegated to generalization module.
    pub(in crate::pdr::solver) fn extract_disequalities(expr: &ChcExpr) -> Vec<(ChcExpr, ChcExpr)> {
        crate::pdr::generalization::extract_disequalities(expr)
    }

    /// Build a conjunction from a list of formulas.
    /// Delegated to generalization module.
    pub(in crate::pdr::solver) fn build_conjunction(conjuncts: &[ChcExpr]) -> ChcExpr {
        crate::pdr::generalization::build_conjunction(conjuncts)
    }

    /// Try to weaken an interpolant by replacing equalities with inequalities (#1346).
    ///
    /// When interpolation produces `x = c` (where x is a variable and c is a constant),
    /// the equality may be too strong to be an inductive invariant. This function tries
    /// to weaken it to `x >= c` or `x <= c` while still blocking the bad state.
    ///
    /// The weakening is sound because:
    /// - If `x = c` implies `NOT(bad_state)`, then both `x >= c` and `x <= c` might also
    ///   imply `NOT(bad_state)` depending on the structure of `bad_state`.
    /// - A weaker constraint is more likely to be inductive across transitions.
    ///
    /// Example: If bad_state = `x < 0` and interpolant = `x = 0`:
    /// - `x >= 0` also blocks `x < 0` and is more likely to be preserved by `x' = x + 1`
    ///
    /// # Arguments
    /// - `interpolant`: The interpolant to weaken
    /// - `bad_state`: The bad state that the interpolant should block
    ///
    /// Uses `self.smt` for checking implications internally.
    ///
    /// # Returns
    /// A potentially weakened interpolant, or the original if no weakening is valid.
    pub(in crate::pdr::solver) fn try_weaken_interpolant_equalities(
        &mut self,
        interpolant: &ChcExpr,
        bad_state: &ChcExpr,
    ) -> ChcExpr {
        // inc-12: spacer-mode admits interpolants raw (one interpolating
        // query per pob, golem-style) — skip the per-equality SMT ladder.
        if self.config.interpolant_first_blocking {
            return interpolant.clone();
        }
        self.try_weaken_interpolant_equalities_inner(interpolant, bad_state, 0)
    }

    fn try_weaken_interpolant_equalities_inner(
        &mut self,
        interpolant: &ChcExpr,
        bad_state: &ChcExpr,
        depth: usize,
    ) -> ChcExpr {
        // Depth bound (#2988): prevent unbounded stacker heap allocation.
        // Crash report showed depth 3636 = 7.2 GB heap from stacker segments.
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
            return interpolant.clone();
        }
        // Find equalities of the form `x = c` where x is a variable and c is a constant
        crate::expr::maybe_grow_expr_stack(|| match interpolant {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let (var, constant) = match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(c)) => (v.clone(), ChcExpr::Int(*c)),
                    (ChcExpr::Int(c), ChcExpr::Var(v)) => (v.clone(), ChcExpr::Int(*c)),
                    (ChcExpr::Var(v), ChcExpr::Real(n, d)) => (v.clone(), ChcExpr::Real(*n, *d)),
                    (ChcExpr::Real(n, d), ChcExpr::Var(v)) => (v.clone(), ChcExpr::Real(*n, *d)),
                    _ => return interpolant.clone(),
                };

                // Try x >= c first
                let ge_candidate = ChcExpr::ge(ChcExpr::var(var.clone()), constant.clone());
                if self.check_blocks_bad_state(&ge_candidate, bad_state) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Weakened interpolant {} to {} (#1346)",
                            interpolant,
                            ge_candidate
                        );
                    }
                    return ge_candidate;
                }

                // Try x <= c next
                let le_candidate = ChcExpr::le(ChcExpr::var(var), constant);
                if self.check_blocks_bad_state(&le_candidate, bad_state) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Weakened interpolant {} to {} (#1346)",
                            interpolant,
                            le_candidate
                        );
                    }
                    return le_candidate;
                }

                // Neither inequality works, keep the equality
                interpolant.clone()
            }
            ChcExpr::Op(ChcOp::And, args) => {
                // Recursively try to weaken conjuncts
                let weakened: Vec<Arc<ChcExpr>> = args
                    .iter()
                    .map(|arg| {
                        Arc::new(self.try_weaken_interpolant_equalities_inner(
                            arg,
                            bad_state,
                            depth + 1,
                        ))
                    })
                    .collect();
                ChcExpr::Op(ChcOp::And, weakened)
            }
            ChcExpr::Op(ChcOp::Or, args) => {
                // Recursively try to weaken disjuncts
                // Note: Weakening within a disjunct is sound because we only weaken
                // individual equalities, and each weaker disjunct still blocks bad_state.
                let weakened: Vec<Arc<ChcExpr>> = args
                    .iter()
                    .map(|arg| {
                        Arc::new(self.try_weaken_interpolant_equalities_inner(
                            arg,
                            bad_state,
                            depth + 1,
                        ))
                    })
                    .collect();
                ChcExpr::Op(ChcOp::Or, weakened)
            }
            _ => interpolant.clone(),
        })
    }

    /// Check if a constraint implies NOT(bad_state).
    ///
    /// Returns true if `constraint AND bad_state` is UNSAT.
    ///
    /// # Side Effects
    /// Uses `check_sat_via_executor_backend` which either uses the persistent
    /// executor (for integer arithmetic) or falls back to `self.smt.reset()` +
    /// `self.smt.check_sat()` (for non-integer problems).
    fn check_blocks_bad_state(&mut self, constraint: &ChcExpr, bad_state: &ChcExpr) -> bool {
        let query = ChcExpr::and(constraint.clone(), bad_state.clone());
        // #7984: Use persistent executor backend for integer arithmetic.
        matches!(
            self.check_sat_via_executor_backend(&query),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        )
    }
}
