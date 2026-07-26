// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LP optimization (simplex-based objective minimization/maximization).
//!
//! Expression analysis and linear equality assertion live in sibling
//! `expression_forced.rs`.

use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::rational::Rational;
use ay_core::{DebugChannel, TheoryResult, TheorySolver};

use crate::types::InfRational;
use crate::{
    LinearExpr, LraSolver, OptimizationResult, OptimizationSense, TableauRow, VarInfo, VarStatus,
};

// Cached `--debug lra` channel (checked once per process). #8858
cached_debug_channel!(debug_lra, DebugChannel::Lra);

impl LraSolver {
    /// Optimize a linear expression subject to the currently asserted constraints.
    ///
    /// This method first ensures the constraint system is feasible, then uses
    /// primal simplex to find the optimal value of the given objective.
    ///
    /// # Arguments
    /// * `objective` - The linear expression to optimize
    /// * `sense` - Whether to minimize or maximize
    ///
    /// # Returns
    /// * `OptimizationResult::Optimal(value)` - The optimal value found
    /// * `OptimizationResult::Unbounded` - The objective is unbounded
    /// * `OptimizationResult::Infeasible` - The constraints are unsatisfiable
    /// * `OptimizationResult::Unknown` - Iteration limit reached without conclusion
    ///
    /// # Example
    /// ```
    /// use ay_lra::{LraSolver, LinearExpr, OptimizationSense, OptimizationResult};
    /// use ay_core::{Sort, TermStore, TheoryResult, TheorySolver};
    /// use num_bigint::BigInt;
    /// use num_rational::BigRational;
    ///
    /// let mut terms = TermStore::new();
    /// let x = terms.mk_var("x", Sort::Real);
    /// let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    /// let le_5 = terms.mk_le(x, five); // x <= 5
    ///
    /// let mut solver = LraSolver::new(&terms);
    /// solver.assert_literal(le_5, true);
    ///
    /// // Register variables and parse asserted constraints.
    /// assert!(matches!(solver.check(), TheoryResult::Sat));
    ///
    /// let x_var = *solver.term_to_var().get(&x).expect("x should be interned");
    /// let objective = LinearExpr::var(x_var);
    ///
    /// // Maximize x subject to x <= 5 => optimal = 5.
    /// let result = solver.optimize(&objective, OptimizationSense::Maximize);
    /// assert!(matches!(
    ///     result,
    ///     OptimizationResult::Optimal(val) if val == BigRational::from(BigInt::from(5))
    /// ));
    /// ```
    pub fn optimize(
        &mut self,
        objective: &LinearExpr,
        sense: OptimizationSense,
    ) -> OptimizationResult {
        self.optimize_with_max_iters(objective, sense, 10_000)
    }

    /// Like [`optimize`], but with a configurable iteration limit for testing.
    pub(crate) fn optimize_with_max_iters(
        &mut self,
        objective: &LinearExpr,
        sense: OptimizationSense,
        max_iters: usize,
    ) -> OptimizationResult {
        self.optimize_impl(objective, sense, max_iters, false).0
    }

    /// Shared implementation for [`optimize`] and
    /// [`LraSolver::optimize_with_certificate`]. When `want_certificate` is
    /// set and a finite optimum is reached, the dual (Farkas) certificate is
    /// extracted from the terminal objective row before it is popped (see
    /// `optimality_certificate.rs`).
    pub(crate) fn optimize_impl(
        &mut self,
        objective: &LinearExpr,
        sense: OptimizationSense,
        max_iters: usize,
        want_certificate: bool,
    ) -> (OptimizationResult, Option<crate::OptimalityCertificate>) {
        let debug = debug_lra();

        if debug {
            safe_eprintln!(
                "[LRA] optimize() called, sense={:?}, objective vars={}",
                sense,
                objective.coeffs.len()
            );
        }

        // First, check feasibility (this parses atoms and sets bounds)
        let feasibility = self.check();
        match feasibility {
            TheoryResult::Sat => {
                // Continue to optimization
            }
            // A model-equality request is a theory-COMBINATION obligation
            // (#4906): the arithmetic assignment is complete and feasible, and
            // LRA is asking the DPLL layer to case-split an equality that the
            // OTHER theories can observe. Optimization reasons about arithmetic
            // alone, so the request carries no information for it — the tableau
            // is primal feasible, which is the whole precondition here.
            //
            // Rejecting it silently disabled the simplex lane (and with it every
            // optimality certificate) whenever three or more variables were
            // pinned to the same value — the shape a fixed column takes in
            // ay-milp's lowering, and thus the shape of essentially every real
            // MILP. The optimum stays honest regardless: the caller confirms it
            // against the FULL solver before reporting it.
            TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_) => {
                // Continue to optimization
            }
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                return (OptimizationResult::Infeasible, None);
            }
            TheoryResult::Unknown
            | TheoryResult::NeedSplit(_)
            | TheoryResult::NeedDisequalitySplit(_)
            | TheoryResult::NeedExpressionSplit(_)
            | TheoryResult::NeedStringLemma(_) => {
                // #6166: These indicate incomplete feasibility checking, NOT infeasibility.
                // Unknown means the theory solver cannot determine satisfiability (e.g.,
                // unsupported atoms with ITE, non-linear terms, or variable-divisor div/mod).
                // NeedSplit variants mean the DPLL(T) loop needs case splits to determine SAT.
                return (OptimizationResult::Unknown, None);
            }
            _ => unreachable!("unexpected TheoryResult variant"),
        }

        // Disequalities are non-convex: a feasibility model can satisfy one
        // before optimization and then move onto the excluded point, so the
        // convex objective tableau below cannot see them. Fail closed.
        //
        // Strict bounds, by contrast, ARE handled exactly: the whole objective
        // loop below runs in delta-rational space (`InfRational`, x + y·ε,
        // Dutertre–de Moura CAV'06), where a strict bound is the closed bound
        // `value ± ε`. The terminal objective value's ε-part classifies
        // attainment exactly: k = 0 ⟺ the optimum is attained (a delta-point
        // with nonzero objective ε-part would materialize (δ→0⁺) to real
        // feasible points beyond the sup — impossible), and the finite part is
        // the true sup/inf (the closure of a nonempty {Ax≤b, Cx<d} is
        // {Ax≤b, Cx≤d}).
        let has_disequality =
            !self.disequality_trail.is_empty() || !self.shared_disequality_trail.is_empty();
        if has_disequality {
            return (OptimizationResult::Unknown, None);
        }

        // If the objective is constant, return it directly. The certificate is
        // the empty multiplier set: `objective >= bound` is the tautology
        // `c >= c`, entailed by no atoms at all.
        if objective.coeffs.is_empty() {
            let value = objective.constant.to_big();
            let certificate = want_certificate.then(|| crate::OptimalityCertificate {
                sense,
                bound: value.clone(),
                strict: false,
                atoms: Vec::new(),
            });
            return (OptimizationResult::Optimal(value), certificate);
        }

        // For maximization, negate the objective (minimize -f(x) == maximize f(x))
        let mut obj = objective.clone();
        if sense == OptimizationSense::Maximize {
            obj.negate();
        }

        // Create a fresh variable for the objective: obj_var = objective_expr
        // This allows us to apply bounds and pivoting to minimize obj_var
        let obj_var = self.next_var;
        self.next_var += 1;
        while self.vars.len() <= obj_var as usize {
            self.vars.push(VarInfo::default());
        }

        // Compute the initial value of the objective from current assignment.
        // Delta-rational: carry the FULL value including the ε-part, so strict
        // bounds participate exactly (#opt-epsilon).
        let mut obj_value = InfRational::from_rat(obj.constant.clone());
        for &(var, ref coeff) in &obj.coeffs {
            if (var as usize) < self.vars.len() {
                obj_value += &self.vars[var as usize].value.mul_rat(coeff);
            }
        }
        // #inc-guard-memo: direct value write — invalidate the guard memo and
        // break the tracked-only chain (#inc-guard-chain).
        self.guard_clean_valid = false;
        self.guard_tracked_only = false;
        // #warm-simplex: untracked value write (and a new row below).
        self.warm_invalidate();
        self.vars[obj_var as usize].value = obj_value;
        self.vars[obj_var as usize].status = Some(VarStatus::Basic(self.rows.len()));

        // Substitute basic variables in the objective expression (#4842).
        let mut new_obj_coeffs: Vec<(u32, Rational)> = Vec::new();
        let mut new_obj_constant = obj.constant.clone();
        for &(v, ref c) in &obj.coeffs {
            if let Some(VarStatus::Basic(basic_row_idx)) =
                self.vars.get(v as usize).and_then(|info| info.status)
            {
                let basic_row = &self.rows[basic_row_idx];
                for &(rv, ref rc) in &basic_row.coeffs {
                    crate::types::add_sparse_term_rat(&mut new_obj_coeffs, rv, c * rc);
                }
                new_obj_constant = &new_obj_constant + &(c * &basic_row.constant);
            } else {
                crate::types::add_sparse_term_rat(&mut new_obj_coeffs, v, c.clone());
            }
        }
        let obj_row = TableauRow::new_rat(obj_var, new_obj_coeffs, new_obj_constant);
        let obj_row_idx_for_col = self.rows.len();
        self.rows.push(obj_row);
        self.heap_stale = true; // #8782: new row → full heap rebuild needed

        // Register objective row in column index (#4919 Phase 1)
        {
            let obj_vars: Vec<u32> = self.rows[obj_row_idx_for_col]
                .coeffs
                .iter()
                .map(|&(v, _)| v)
                .collect();
            for v in obj_vars {
                self.col_index_add(v, obj_row_idx_for_col);
            }
        }

        // Primal simplex: minimize obj_var
        // At each iteration, find a non-basic variable that can reduce obj_var
        for iter in 0..max_iters {
            if debug && iter < 20 {
                safe_eprintln!(
                    "[LRA] primal simplex iter {}, obj_var={}, obj_value={}",
                    iter,
                    obj_var,
                    self.vars[obj_var as usize].value
                );
            }

            // Find the objective row
            let obj_row_idx = self.rows.len() - 1;
            let obj_row = &self.rows[obj_row_idx];

            // For minimization: look for a non-basic variable x_j with positive coefficient
            // (increasing x_j would increase obj, so we want to decrease x_j if possible)
            // Or a non-basic variable with negative coefficient that we can increase
            //
            // Standard primal: look for a variable that can reduce the
            // objective. ENTERING choice uses Bland's rule (smallest variable
            // index among improving candidates, not first-in-sparse-order):
            // with the ratio test bounding each move, degenerate vertices
            // produce zero-length pivots, and an arbitrary entering order
            // cycles forever (#R1: the 5-var ny repro cycled to the iteration
            // cap). Bland's rule guarantees termination.
            let mut best_pivot: Option<(u32, bool)> = None; // (var, increase)

            for &(var, ref coeff) in &obj_row.coeffs {
                if matches!(
                    self.vars.get(var as usize).and_then(|v| v.status.as_ref()),
                    Some(VarStatus::NonBasic)
                ) {
                    let info = &self.vars[var as usize];

                    // Positive coeff in objective row: decreasing var reduces
                    // the objective (only if var sits above its lower bound).
                    // Comparisons are DELTA-AWARE (`cmp_bound` maps a strict
                    // lower bound to value+ε, a strict upper to value−ε); the
                    // previous rational-only compare was latently wrong for
                    // strict bounds and only masked by the pre-#opt-epsilon
                    // strict-bound gate.
                    let candidate = if coeff.is_positive() {
                        let can_decrease = info.lower.as_ref().is_none_or(|lb| {
                            info.value
                                .cmp_bound(&lb.value, lb.strict, crate::BoundType::Lower)
                                == std::cmp::Ordering::Greater
                        });
                        can_decrease.then_some((var, false))
                    }
                    // Negative coeff: increasing var reduces the objective.
                    else if coeff.is_negative() {
                        let can_increase = info.upper.as_ref().is_none_or(|ub| {
                            info.value
                                .cmp_bound(&ub.value, ub.strict, crate::BoundType::Upper)
                                == std::cmp::Ordering::Less
                        });
                        can_increase.then_some((var, true))
                    } else {
                        None
                    };
                    if let Some((v, dir)) = candidate {
                        if best_pivot.is_none_or(|(bv, _)| v < bv) {
                            best_pivot = Some((v, dir));
                        }
                    }
                }
            }

            let Some((pivot_var, increase)) = best_pivot else {
                // No improving pivot found - we're at the delta-optimum.
                let opt_inf = self.vars[obj_var as usize].value.clone();
                let opt_value = opt_inf.rational();

                // Extract the dual certificate while the objective row is
                // still the last tableau row (fails closed to None). Only an
                // ATTAINED optimum (ε-part zero) gets one; unattained optima
                // carry no certificate in Phase A (#opt-epsilon).
                let certificate = if want_certificate && opt_inf.epsilon_is_zero() {
                    self.extract_optimality_certificate(sense, &opt_value)
                } else {
                    None
                };

                // Clean up: remove the objective row
                self.pop_row_with_col_cleanup();
                self.vars[obj_var as usize].status = None;

                // If we were maximizing, negate the result
                let (final_value, eps_coeff) = if sense == OptimizationSense::Maximize {
                    (-opt_value, -opt_inf.epsilon())
                } else {
                    (opt_value, opt_inf.epsilon())
                };

                if eps_coeff.is_zero() {
                    if debug {
                        safe_eprintln!("[LRA] Found optimal: {}", final_value);
                    }
                    return (OptimizationResult::Optimal(final_value), certificate);
                }

                // Unattained optimum: the delta-max carries a nonzero ε-part.
                // Sign theorem (no ε-cancellation: every binding strict bound
                // contributes one ε of the sense's sign): minimize ⇒ k > 0,
                // maximize ⇒ k < 0. A violation means an implementation bug;
                // fail closed rather than publish a wrong shape.
                let sign_ok = match sense {
                    OptimizationSense::Minimize => eps_coeff.is_positive(),
                    OptimizationSense::Maximize => eps_coeff.is_negative(),
                };
                debug_assert!(
                    sign_ok,
                    "delta-optimum ε-sign violates the sense theorem: {sense:?} k={eps_coeff}"
                );
                if !sign_ok {
                    return (OptimizationResult::Unknown, None);
                }
                if debug {
                    safe_eprintln!(
                        "[LRA] Found unattained optimum: {} + {}*eps",
                        final_value,
                        eps_coeff
                    );
                }
                return (
                    OptimizationResult::OptimalInf {
                        value: final_value,
                        eps_coeff,
                    },
                    None,
                );
            };

            // Determine how far we can move pivot_var. The move distance is
            // the MINIMUM of (a) the entering variable's own bound distance
            // and (b) the ratio test — the distance until the first basic
            // variable hits one of its bounds. Jumping straight to the
            // entering variable's own bound without the ratio test loses
            // primal feasibility (basic variables overshoot their bounds) and
            // terminates at a super-optimal, INFEASIBLE "optimum" — observed
            // as `maximize z` reporting 3/2 where the true maximum is 1/2
            // (#R1, the development design notes P0 findings).
            let info = &self.vars[pivot_var as usize];
            let current_val = info.value.clone();

            // (a) Distance to the entering variable's own bound in the move
            // direction (None = unbounded that way). Delta-rational: a strict
            // bound is `value ± ε` (`Bound::as_inf`), so the distance carries
            // the ε-part exactly (#opt-epsilon).
            let own_bound_dist: Option<InfRational> = if increase {
                info.upper
                    .as_ref()
                    .map(|ub| &ub.as_inf(crate::BoundType::Upper) - &current_val)
            } else {
                info.lower
                    .as_ref()
                    .map(|lb| &current_val - &lb.as_inf(crate::BoundType::Lower))
            };

            // (b) The ratio test: the distance until the first basic variable
            // hits a bound, and WHICH basic variable that is. Carrying the
            // blocker out of the ratio test is what makes the pivot legal —
            // see the leaving-variable choice below.
            let blocking = self.find_pivot_limit(pivot_var, increase);

            // The move is limited by whichever binds first. When the entering
            // variable reaches its own bound first (or ties), it simply flips
            // to that bound and stays non-basic — no basis change. Only a
            // blocking basic variable causes a pivot, and only that variable
            // may leave.
            let (move_dist, leaving) = match (own_bound_dist, blocking) {
                (Some(own), Some((ratio, blocker))) => {
                    if ratio < own {
                        (ratio, Some(blocker))
                    } else {
                        (own, None)
                    }
                }
                (Some(own), None) => (own, None),
                (None, Some((ratio, blocker))) => (ratio, Some(blocker)),
                (None, None) => {
                    // Nothing bounds the improving direction: the objective is
                    // genuinely unbounded.
                    self.pop_row_with_col_cleanup();
                    self.vars[obj_var as usize].status = None;
                    if debug {
                        safe_eprintln!(
                            "[LRA] Unbounded ({} pivot_var {})",
                            if increase { "increasing" } else { "decreasing" },
                            pivot_var
                        );
                    }
                    return (OptimizationResult::Unbounded, None);
                }
            };
            // Signed move delta in delta-rational space.
            let delta = if increase { move_dist } else { -move_dist };
            let target_val = &current_val + &delta;
            // #inc-guard-memo: direct value writes below — invalidate the memo and
            // break the tracked-only chain (#inc-guard-chain).
            self.guard_clean_valid = false;
            self.guard_tracked_only = false;
            // #warm-simplex: untracked value writes.
            self.warm_invalidate();
            self.vars[pivot_var as usize].value = target_val;

            // Update all basic variables that depend on pivot_var
            for row in &self.rows {
                let coeff = row.coeff_big(pivot_var);
                if !coeff.is_zero() {
                    let basic_info = &mut self.vars[row.basic_var as usize];
                    basic_info.value += &delta.mul_rational(&coeff);
                }
            }

            // The leaving variable is the one the ratio test says blocks first —
            // never merely "some basic that happens to sit at a bound".
            //
            // Picking any at-bound basic was #R1's residual cycle: at a
            // degenerate vertex several basics sit on their bounds without
            // blocking this move, so the loop pivoted on a non-blocking row (or
            // pivoted at all during a bound flip, which changes no value), and
            // Bland's guarantee — which holds only when the leaving variable is
            // chosen among those attaining the MINIMUM ratio — did not apply.
            // The basis then revisited itself until the iteration cap and the
            // optimizer reported `Unknown` on a two-variable LP.
            if let Some(leaving_var) = leaving {
                if let Some(&row_idx) = self.basic_var_to_row.get(&leaving_var) {
                    debug_assert!(
                        !self.rows[row_idx].coeff(pivot_var).is_zero(),
                        "ratio test returned a row the entering variable is absent from"
                    );
                    self.pivot(row_idx, pivot_var);
                }
            }
        }

        // Hit iteration limit — cannot determine result
        self.pop_row_with_col_cleanup();
        self.vars[obj_var as usize].status = None;

        if debug {
            safe_eprintln!("[LRA] Hit iteration limit, returning Unknown");
        }

        (OptimizationResult::Unknown, None)
    }

    /// The ratio test: how far `var` may move before some basic variable hits a
    /// bound, and which basic variable blocks first.
    ///
    /// `None` means no basic variable bounds the move at all — the caller reads
    /// that as "unbounded in this direction" once the entering variable has no
    /// bound of its own either.
    ///
    /// Ties go to the smallest basic-variable index. That tie-break is Bland's
    /// rule, and it is load-bearing: a degenerate vertex yields several blockers
    /// at ratio zero, and choosing among them arbitrarily lets the basis cycle
    /// forever.
    fn find_pivot_limit(&self, var: u32, increase: bool) -> Option<(InfRational, u32)> {
        let mut best: Option<(InfRational, u32)> = None;
        let zero = InfRational::default();

        for row in &self.rows {
            let coeff = row.coeff_big(var);
            if coeff.is_zero() {
                continue;
            }

            let basic_info = &self.vars[row.basic_var as usize];
            let basic_val = &basic_info.value;

            // Moving `var` by Δ moves this basic by coeff·Δ; the limit is the
            // distance to the bound it moves toward (unbounded that way = no
            // limit from this row). Delta-rational: strict bounds are
            // `value ± ε` and the distance is scaled by 1/|coeff| through the
            // ε-part as well (#opt-epsilon).
            let inv_abs = BigRational::one() / coeff.abs();
            let delta = if increase == coeff.is_positive() {
                basic_info.upper.as_ref().map(|ub| {
                    (&ub.as_inf(crate::BoundType::Upper) - basic_val).mul_rational(&inv_abs)
                })
            } else {
                basic_info.lower.as_ref().map(|lb| {
                    (basic_val - &lb.as_inf(crate::BoundType::Lower)).mul_rational(&inv_abs)
                })
            };

            if let Some(d) = delta {
                if d >= zero {
                    let better = match &best {
                        None => true,
                        Some((m, blocker)) => d < *m || (d == *m && row.basic_var < *blocker),
                    };
                    if better {
                        best = Some((d, row.basic_var));
                    }
                }
            }
        }

        best
    }
}
