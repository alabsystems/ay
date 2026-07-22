// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA two-variable Diophantine equation solver.
//!
//! Extracted from `lib.rs` (#2998 code-health, design #6859 Packet 6).
//! Handles the special case of equalities with exactly two integer variables,
//! using extended GCD to find solutions and detect infeasibility.

use super::*;

impl LiaSolver<'_> {
    /// Try to solve 2-variable integer equalities directly using extended GCD.
    ///
    /// For equations of the form `a*x + b*y = c`, this:
    /// 1. Checks GCD infeasibility: if gcd(a,b) does not divide c, UNSAT.
    /// 2. Uses extended GCD to find a parametric solution: x = x0 + k*step_x, y = y0 + k*step_y.
    /// 3. Computes bounds on the parameter k from variable bounds.
    /// 4. If k bounds are contradictory, UNSAT.
    /// 5. If k has exactly one value (unique solution), sets hard bounds.
    ///
    /// This handles the case where the original equation may have more variables,
    /// but some are "fixed" (equal lower/upper bounds), reducing to 2 free variables.
    ///
    /// Example: `4*x1 + 4*x2 + 4*x3 + 2*x4 = 49` with x3, x4 fixed.
    /// After folding: `4*x1 + 4*x2 = 49 - 4*x3_val - 2*x4_val`.
    /// GCD(4, 4, 4, 2) = 2, but 2 does not divide 49, so UNSAT.
    ///
    /// Returns a `TheoryConflict` with Farkas coefficient 1 for the failing equality.
    /// For interpolation purposes, the equality itself serves as the interpolant.
    pub(crate) fn try_two_variable_solve(&mut self) -> Option<Vec<TheoryLit>> {
        let debug = self.debug_dioph;

        // Count total equalities - we can only safely set hard bounds when there's
        // exactly one equality (otherwise bounds from one equation may conflict with others)
        let total_equalities = self.count_equalities();

        let (term_to_idx, idx_to_term) = self.build_var_index();

        // Collect candidates for 2-variable equations
        // We need to do this in two phases to avoid borrow conflicts
        struct TwoVarCandidate {
            literal: TermId,
            coeffs: HashMap<usize, BigInt>,
            constant: BigInt,
            /// Bound reasons from folded variables (#8012). Must be included
            /// in any conflict derived from this equation.
            fold_reasons: Vec<TheoryLit>,
        }

        let mut candidates: Vec<TwoVarCandidate> = Vec::new();

        for &(literal, value) in &self.asserted {
            if !value {
                continue;
            }

            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };

            if name != "=" || args.len() != 2 {
                continue;
            }

            // Parse the equality
            let Some((var_coeffs, constant)) =
                self.parse_equality_for_dioph(args[0], args[1], &term_to_idx)
            else {
                continue;
            };

            // Fold fixed variables: an equation with 3+ vars may reduce to 2
            // when some variables have equal lower/upper bounds.
            let (folded_coeffs, folded_constant, fold_reasons) =
                self.fold_fixed_vars_in_equation(&var_coeffs, constant, &idx_to_term);

            // Must have exactly 2 variables after folding
            if folded_coeffs.len() != 2 {
                continue;
            }

            // Build the equation
            let mut coeffs_map: HashMap<usize, BigInt> = HashMap::default();
            for (idx, coeff) in folded_coeffs {
                coeffs_map.insert(idx, coeff);
            }

            candidates.push(TwoVarCandidate {
                literal,
                coeffs: coeffs_map,
                constant: folded_constant,
                fold_reasons,
            });
        }

        // Now process candidates (we've dropped the borrow on self.asserted)
        for candidate in candidates {
            let eq = dioph::IntEquation::new(candidate.coeffs, candidate.constant);

            // GCD infeasibility check
            if eq.gcd_infeasible() {
                if debug {
                    safe_eprintln!("[DIOPH] 2-var GCD infeasibility");
                }
                // Include fold_reasons: the GCD test operates on the folded
                // equation, so the bound reasons that justified folding are
                // part of the infeasibility (#8012).
                let mut conflict = vec![TheoryLit::new(candidate.literal, true)];
                let mut seen: HashSet<TheoryLit> = conflict.iter().copied().collect();
                for reason in &candidate.fold_reasons {
                    if seen.insert(*reason) {
                        conflict.push(*reason);
                    }
                }
                return Some(conflict);
            }

            // Try extended GCD solution
            let Some(sol) = eq.solve_two_variable() else {
                continue;
            };

            if debug {
                safe_eprintln!(
                    "[DIOPH] 2-var solution: var_x={}, var_y={}, x0={}, y0={}, step_x={}, step_y={}",
                    sol.var_x, sol.var_y, sol.x0, sol.y0, sol.step_x, sol.step_y
                );
            }

            // Get bounds for both variables from LRA
            let term_x = idx_to_term.get(sol.var_x).copied();
            let term_y = idx_to_term.get(sol.var_y).copied();

            let (x_lo, x_hi) = self.get_integer_bounds_for_term(term_x);
            let (y_lo, y_hi) = self.get_integer_bounds_for_term(term_y);

            if debug {
                safe_eprintln!(
                    "[DIOPH] Bounds: x in [{:?}, {:?}], y in [{:?}, {:?}]",
                    x_lo,
                    x_hi,
                    y_lo,
                    y_hi
                );
            }

            // Compute k bounds from x bounds
            let (k_min_x, k_max_x) = sol.k_bounds_from_x(x_lo.as_ref(), x_hi.as_ref());
            // Compute k bounds from y bounds
            let (k_min_y, k_max_y) = sol.k_bounds_from_y(y_lo.as_ref(), y_hi.as_ref());

            // Intersect k bounds
            let k_min = match (k_min_x, k_min_y) {
                (Some(a), Some(b)) => Some(a.max(b)),
                (Some(a), None) => Some(a),
                (None, Some(b)) => Some(b),
                (None, None) => None,
            };
            let k_max = match (k_max_x, k_max_y) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (Some(a), None) => Some(a),
                (None, Some(b)) => Some(b),
                (None, None) => None,
            };

            if debug {
                safe_eprintln!("[DIOPH] k bounds: [{:?}, {:?}]", k_min, k_max);
            }

            // Check if bounds are contradictory
            if let (Some(ref lo), Some(ref hi)) = (&k_min, &k_max) {
                if lo > hi {
                    if debug {
                        safe_eprintln!("[DIOPH] k bounds contradictory - infeasible");
                    }
                    // Infeasible - gather all bound assertions
                    let mut conflict = vec![TheoryLit::new(candidate.literal, true)];
                    // Add bounds that contributed to the conflict
                    conflict.extend(self.get_bound_reasons_for_term(term_x));
                    conflict.extend(self.get_bound_reasons_for_term(term_y));
                    // Include fold_reasons: tight bounds used during folding
                    // are part of the infeasibility (#8012).
                    conflict.extend(candidate.fold_reasons.iter().copied());
                    debug_assert!(
                        !conflict.is_empty(),
                        "BUG: try_two_variable_solve: k-bounds infeasible (lo={lo}, hi={hi}) \
                         but conflict clause is empty"
                    );
                    return Some(conflict);
                }

                // If k has exactly ONE valid value (range == 0), set hard bounds.
                // This means there's truly only one solution.
                //
                // FIX for #938: Previously we set bounds when range <= 10, which incorrectly
                // restricted to a single solution when multiple existed (breaking ALL-SAT).
                // Now we only set bounds when range == 0 (unique solution).
                //
                // IMPORTANT: Only do this when there's exactly one equality in the system.
                // If there are multiple equalities, setting hard bounds based on one equation
                // may conflict with constraints from other equations.
                let range = hi - lo;
                if range.is_zero() && total_equalities == 1 {
                    // Exactly one valid k - unique solution
                    let k = lo.clone();
                    let (x_val, y_val) = sol.evaluate(&k);

                    if debug {
                        safe_eprintln!(
                            "[DIOPH] Unique solution (range=0): x={}, y={}",
                            x_val,
                            y_val
                        );
                    }

                    // Include the equality AND all bound atoms that constrained
                    // k to a unique value. Without bound reasons, cross-sort
                    // propagation produces over-strong conflict clauses →
                    // false-UNSAT (#6198).
                    let mut reasons = vec![(candidate.literal, true)];
                    for r in self.get_bound_reasons_for_term(term_x) {
                        reasons.push((r.term, r.value));
                    }
                    for r in self.get_bound_reasons_for_term(term_y) {
                        reasons.push((r.term, r.value));
                    }

                    if let Some(tid) = term_x {
                        self.add_integer_bound(tid, &x_val, &reasons);
                    }
                    if let Some(tid) = term_y {
                        self.add_integer_bound(tid, &y_val, &reasons);
                    }
                    // #8147: Mark that Dioph has modified LRA bounds.
                    self.dioph_modified_bounds = true;
                } else if debug && range <= BigInt::from(10) {
                    safe_eprintln!(
                        "[DIOPH] Multiple solutions exist (range={}), NOT setting bounds",
                        range
                    );
                }
            } else if k_min.is_none()
                && k_max.is_none()
                && total_equalities == 1
                && self.integer_vars.len() == 2
                && self.count_arith_atoms() == 1
                && sol.step_x.abs() > BigInt::one()
                && sol.step_y.abs() > BigInt::one()
            {
                // Completeness (#wrong-unsat): the ONLY constraint in the system
                // is this single 2-variable equality `a*x + b*y = c`, both
                // variables are unbounded (k is fully free), and `gcd(a,b) | c`
                // (otherwise gcd_infeasible would have returned above), so the
                // equation has infinitely many integer solutions and the problem
                // is SAT.
                //
                // The `step_x,step_y > 1` guard restricts this to the case where
                // NEITHER variable has a unit coefficient (`step_y = a/g`,
                // `step_x = b/g`). With a unit coefficient the general
                // Diophantine substitution path resolves the system directly and
                // the LP relaxation is already integer-feasible (no B&B drift), so
                // we leave that path untouched (it populates the substitution
                // caches other code depends on). Without a unit coefficient the LP
                // relaxation is fractional and branch-and-bound walks the line
                // forever, never landing on an integer point near the origin;
                // the unbounded-drift guard then bails to Unknown.
                //
                // Since nothing else constrains x or y, we may soundly pin ANY
                // concrete witness. Pin k = 0 -> (x0, y0); this makes the LRA
                // model integer-feasible so LIA reports SAT. The equality literal
                // is the sole reason (no bounds participated).
                let k = BigInt::zero();
                let (x_val, y_val) = sol.evaluate(&k);

                if debug {
                    safe_eprintln!(
                        "[DIOPH] Unbounded single-equation witness: x={}, y={}",
                        x_val,
                        y_val
                    );
                }

                let reasons = vec![(candidate.literal, true)];
                if let Some(tid) = term_x {
                    self.add_integer_bound(tid, &x_val, &reasons);
                }
                if let Some(tid) = term_y {
                    self.add_integer_bound(tid, &y_val, &reasons);
                }
                // #8147: Mark that Dioph has modified LRA bounds.
                self.dioph_modified_bounds = true;
            }
        }

        None
    }
}
