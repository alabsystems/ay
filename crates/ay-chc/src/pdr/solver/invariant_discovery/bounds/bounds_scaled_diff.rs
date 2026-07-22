// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scaled difference bound invariant discovery: invariants of the form B - k*A >= c.
//!
//! For transitions like A' = A + 1, B' = B + 2, if the init constraint gives
//! B > A (i.e., B >= A + 1), then B - 2*A is non-decreasing with a lower bound.
//! This enables solving benchmarks like s_mutants_05.
//!
//! Validation helpers (init/preservation checks, coefficient extraction) are in
//! `bounds_scaled_diff_verify.rs`.

use super::super::super::PdrSolver;
use super::SCALED_DIFF_BOUND_CANDIDATES;
use crate::{ChcExpr, ChcSort};

impl PdrSolver {
    /// Discover scaled difference bound invariants of the form B - k*A >= c.
    ///
    /// For transitions like A' = A + 1, B' = B + 2, if the init constraint gives
    /// B > A (i.e., B >= A + 1), then B - 2*A is non-decreasing with a lower bound.
    /// This enables solving benchmarks like s_mutants_05.
    pub(in crate::pdr::solver) fn discover_scaled_difference_bounds(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Extract multiplication coefficients from the problem's clauses.
        // gj2007_m_1 uses (* 5 C) which requires k=5 as a scale factor.
        // k=1 handles simple difference bounds (B - A >= c) for predicates without
        // fact clauses. discover_difference_invariants only runs for predicates WITH
        // facts, so k=1 here covers downstream predicates like query predicates
        // reached via inter-predicate transitions. (#1306: dillig12_m SAD predicate)
        let mut problem_scale_factors = vec![1i128, 2, 3, 4];
        {
            let mut coeffs = Vec::new();
            for clause in self.problem.clauses() {
                if let Some(ref c) = clause.body.constraint {
                    Self::collect_mul_coefficients(c, &mut coeffs);
                }
                if let crate::ClauseHead::Predicate(_, ref args) = clause.head {
                    for arg in args {
                        Self::collect_mul_coefficients(arg, &mut coeffs);
                    }
                }
            }
            // Also extract equality constants from fact clauses (#5480).
            // dillig21_m has `(= 10 v_0)` in init — the value 10 is the minimum
            // per-step increment for the accumulator, needed as a scale factor.
            for clause in self.problem.facts() {
                if let Some(ref c) = clause.body.constraint {
                    Self::collect_equality_constants(c, &mut coeffs);
                }
            }
            for k in coeffs {
                // checked_abs: i128::MIN has no absolute value; such a constant
                // can never be a valid small scale factor anyway.
                let Some(abs_k) = k.checked_abs() else {
                    continue;
                };
                if (2..=20).contains(&abs_k) && !problem_scale_factors.contains(&abs_k) {
                    problem_scale_factors.push(abs_k);
                }
            }
        }

        for pred in &predicates {
            // Need at least one self-loop for preservation check (#1388).
            // For predicates with facts: check init via facts.
            // For derived predicates (no facts, with incoming transitions):
            // check init via incoming transitions + source invariants (#5480).
            let has_facts = self.predicate_has_facts(pred.id);
            let has_self_loop = self.problem.clauses_defining(pred.id).any(|clause| {
                clause.body.predicates.len() == 1 && clause.body.predicates[0].0 == pred.id
            });
            if !has_self_loop {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: scaled-diff: skipping pred {} (no self-loop)",
                        pred.id.index()
                    );
                }
                continue;
            }

            // Skip predicates with unrestricted incoming transitions (identity-like
            // mappings with no constraint — init bounds don't hold for injected states).
            if self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: scaled-diff: skipping pred {} (unrestricted incoming)",
                        pred.id.index()
                    );
                }
                continue;
            }
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: scaled-diff: entering pred {} (has_facts={}, vars={})",
                    pred.id.index(),
                    has_facts,
                    self.canonical_vars(pred.id).map(<[_]>::len).unwrap_or(0),
                );
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Pre-compute init values for algebraic fast-path (#2833).
            // For derived predicates without facts, init_values will be empty;
            // we fall back to SMT-based incoming transition checks.
            let init_values = if has_facts {
                self.get_init_values(pred.id)
            } else {
                Default::default()
            };

            // #7048: Pre-compute constant arguments to skip redundant scaled-diff bounds.
            // When both vars in a pair are constant (e.g., A=1, B=0 in dillig02_m),
            // bounds like B - 2*A >= -2 are trivially implied by the tight bounds
            // A >= 1 AND A <= 1, B >= 0 AND B <= 0. These bloat the frame without
            // adding information, making push queries slow.
            //
            // detect_constant_arguments checks self-loop structure (works for single-pred).
            // detect_frame_tight_bound_vars checks frame[1] for var >= c AND var <= c
            // (works for multi-predicate problems where constant bounds are inductive
            // through the SCC cycle but no self-loops exist).
            let mut constant_args = self.detect_constant_arguments(pred.id);
            let frame_constants = self.detect_frame_tight_bound_vars(pred.id);
            constant_args.extend(frame_constants.iter());

            // Try scaled differences B - k*A for pairs of integer variables.
            // Per-variable time budget prevents expensive outer variables (e.g.,
            // constants paired with accumulators in mod/ite transitions causing
            // SMT Unknown) from starving later variable pairs (#5480).
            for (i, var_a) in canonical_vars.iter().enumerate() {
                // Check cancellation to support solve_timeout / portfolio solving
                if self.is_cancelled() {
                    return;
                }
                if !matches!(var_a.sort, ChcSort::Int) {
                    continue;
                }
                let var_a_start = ay_core::time::Instant::now();
                let var_a_budget = std::time::Duration::from_secs(2);

                for (j, var_b) in canonical_vars.iter().enumerate() {
                    if i == j {
                        continue;
                    }
                    if !matches!(var_b.sort, ChcSort::Int) {
                        continue;
                    }
                    // #7048: Skip pairs where BOTH variables are constant. When both
                    // have fixed values, the bound is trivially determined. When only
                    // one is constant, the affine bound reduces to a useful simple bound
                    // on the non-constant variable (e.g., a0 - 128 <= 0 → a0 <= 128).
                    // Using && instead of || recovers count_by_2 upper bound discovery.
                    if constant_args.contains(&i) && constant_args.contains(&j) {
                        continue;
                    }
                    if var_a_start.elapsed() >= var_a_budget {
                        break;
                    }

                    // Try problem-derived and standard scale factors
                    for &k in &problem_scale_factors {
                        if var_a_start.elapsed() >= var_a_budget {
                            break;
                        }
                        // Find the tightest valid bound. Higher c is tighter.
                        // These cover common cases like B >= 2*A + 1 (from B > A and A=0).
                        let mut tightest_valid: Option<i128> = None;

                        // Algebraic fast-path: if both vars have constant init values,
                        // compute the exact init difference once instead of calling SMT
                        // for each candidate bound (#2833).
                        let a_init = init_values
                            .get(&var_a.name)
                            .filter(|b| b.min == b.max)
                            .map(|b| b.min);
                        let b_init = init_values
                            .get(&var_b.name)
                            .filter(|b| b.min == b.max)
                            .map(|b| b.min);
                        let init_diff = match (a_init, b_init) {
                            (Some(a), Some(b)) => Some(b - k * a),
                            _ => None,
                        };

                        for c in SCALED_DIFF_BOUND_CANDIDATES {
                            if var_a_start.elapsed() >= var_a_budget {
                                break;
                            }
                            // First check if B - k*A >= c holds at init
                            let init_valid = if let Some(diff) = init_diff {
                                diff >= c
                            } else if has_facts {
                                self.is_scaled_diff_bound_init_valid(pred.id, var_a, var_b, k, c)
                            } else {
                                // Derived predicate: check incoming transitions (#5480)
                                self.is_scaled_diff_bound_incoming_valid(
                                    pred.id, var_a, var_b, k, c,
                                )
                            };
                            if !init_valid {
                                continue;
                            }

                            // Check if B - k*A >= c is preserved
                            let preserved =
                                self.is_scaled_diff_bound_preserved(pred.id, var_a, var_b, k, c);
                            if !preserved {
                                continue;
                            }

                            // Found the tightest valid bound - stop searching.
                            tightest_valid = Some(c);
                            break;
                        }

                        if let Some(c) = tightest_valid {
                            let diff_expr = ChcExpr::sub(
                                ChcExpr::var(var_b.clone()),
                                ChcExpr::mul(ChcExpr::Int(k), ChcExpr::var(var_a.clone())),
                            );
                            let bound_invariant = ChcExpr::ge(diff_expr, ChcExpr::Int(c));

                            // Check if already known
                            let already_known = self.frames.len() > 1
                                && self.frames[1].contains_lemma(pred.id, &bound_invariant);

                            if already_known {
                                continue;
                            }

                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered scaled diff bound for pred {}: {} - {}*{} >= {}",
                                    pred.id.index(),
                                    var_b.name,
                                    k,
                                    var_a.name,
                                    c
                                );
                            }

                            self.add_discovered_invariant(pred.id, bound_invariant, 1);
                        }
                    }
                }
            }
        }
    }
}
