// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA integer-arithmetic support: cube test, rounding, and integer feasibility.
//!
//! Integer patching and direct bound injection are in `lia_patch.rs`.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermId;
use ay_core::{DebugChannel, TheoryResult, TheorySolver};
use num_traits::Zero;

use crate::rational::Rational;
use crate::types::InfRational;
use crate::{BoundType, LraSolver, VarStatus};

// Cached `--debug cube` channel (checked once per process). #8858
cached_debug_channel!(debug_cube, DebugChannel::Cube);

impl LraSolver {
    /// Move non-basic variables to their bounds.
    ///
    /// This is a prerequisite for generating valid Gomory cuts - all non-basic
    /// variables must be at a bound for the cut to be valid.
    ///
    /// For each non-basic variable:
    /// - If it has a lower bound and no upper, move to lower bound
    /// - If it has an upper bound and no lower, move to upper bound
    /// - If it has both bounds, move to whichever is closer
    /// - If it has no bounds, leave it at 0 (unbounded)
    pub fn move_nonbasic_to_bounds(&mut self) {
        for var in 0..self.vars.len() {
            let info = &self.vars[var];
            if !matches!(info.status, Some(VarStatus::NonBasic)) {
                continue;
            }

            let target: Option<InfRational> = match (&info.lower, &info.upper) {
                (Some(lb), Some(ub)) => {
                    let lb_inf = lb.as_inf(BoundType::Lower);
                    let ub_inf = ub.as_inf(BoundType::Upper);
                    // Move to the closer bound
                    let dist_to_lower = &info.value - &lb_inf;
                    let dist_to_upper = &ub_inf - &info.value;
                    if dist_to_lower <= dist_to_upper {
                        Some(lb_inf)
                    } else {
                        Some(ub_inf)
                    }
                }
                (Some(lb), None) => Some(lb.as_inf(BoundType::Lower)),
                (None, Some(ub)) => Some(ub.as_inf(BoundType::Upper)),
                (None, None) => {
                    // Unbounded - move to 0
                    if !info.value.is_zero() {
                        Some(InfRational::default())
                    } else {
                        None
                    }
                }
            };

            if let Some(new_val) = target {
                if new_val != self.vars[var].value {
                    self.update_nonbasic(var as u32, new_val);
                }
            }
        }
    }

    /// Z3's "cube test": tighten bounds on rows by a delta derived from integer
    /// variable coefficients, then re-solve the LP. If the tightened LP is still
    /// feasible, round each integer variable to the nearest integer.
    ///
    /// Reference: `reference/z3/src/math/lp/int_cube.cpp`
    ///
    /// Returns true if an integer solution was found, false otherwise.
    /// When true, caller should re-check: the integer vars have been rounded.
    pub fn try_cube_test(&mut self, integer_vars: &HashSet<TermId>) -> bool {
        let debug = debug_cube();

        if debug {
            safe_eprintln!("[CUBE] Starting cube test with {} rows", self.rows.len());
        }

        self.push();

        // Tighten bounds on each row's basic variable.
        // Delta = (1/2) * sum(|coeff_j|) for integer non-basic vars j in the row.
        // Special case: two-variable difference rows (x - y) need delta = 0.
        let mut tighten_failed = false;
        for row_idx in 0..self.rows.len() {
            let row = &self.rows[row_idx];
            let basic_var = row.basic_var;
            let coeffs = row.coeffs.clone();

            // Compute delta for this row
            let delta = Self::cube_delta_for_row(&coeffs, basic_var, integer_vars, self);

            if delta.is_zero() {
                continue;
            }

            // Tighten lower bound: lower += delta
            let info = &self.vars[basic_var as usize];
            if let Some(ref lb) = info.lower {
                let new_lower = &lb.value + &delta;
                // Check if tightening would make bounds infeasible
                if let Some(ref ub) = info.upper {
                    if new_lower > ub.value {
                        tighten_failed = true;
                        break;
                    }
                }
                self.add_direct_bound(basic_var, new_lower.to_big(), true);
            }

            // Tighten upper bound: upper -= delta
            let info = &self.vars[basic_var as usize];
            if let Some(ref ub) = info.upper {
                let new_upper = &ub.value - &delta;
                if let Some(ref lb) = info.lower {
                    if lb.value > new_upper {
                        tighten_failed = true;
                        break;
                    }
                }
                self.add_direct_bound(basic_var, new_upper.to_big(), false);
            }
        }

        if tighten_failed {
            if debug {
                safe_eprintln!("[CUBE] Tightening made bounds infeasible, aborting");
            }
            self.pop();
            return false;
        }

        // Re-solve LP with tightened bounds
        self.dirty = true;
        let result = self.dual_simplex();

        match result {
            TheoryResult::Sat => {
                // Feasible with tighter bounds — pop and round to integers
                self.pop();
                if self.round_integer_vars_if_feasible(integer_vars) {
                    if debug {
                        safe_eprintln!("[CUBE] Found integer solution via cube test");
                    }
                    true
                } else {
                    if debug {
                        safe_eprintln!(
                            "[CUBE] Rounded assignment violated bounds; rejecting cube step"
                        );
                    }
                    false
                }
            }
            _ => {
                // Infeasible with tighter bounds — pop and try moving nonbasics
                self.pop();
                self.move_nonbasic_to_bounds();
                // Z3 (int_cube.cpp:48): moving nonbasics to bounds can
                // serendipitously produce an integer solution.
                if self.all_integer_vars_integral(integer_vars)
                    && self.assignment_satisfies_bounds()
                {
                    if debug {
                        safe_eprintln!(
                            "[CUBE] Found integer solution after moving nonbasics to bounds"
                        );
                    }
                    true
                } else {
                    if debug {
                        safe_eprintln!(
                            "[CUBE] Cube test failed, LP infeasible with tighter bounds"
                        );
                    }
                    false
                }
            }
        }
    }

    /// Compute the cube delta for a row.
    ///
    /// For a 2-variable difference row (x - y where both are integer), delta = 0.
    /// For a 2-variable unit-coefficient row (+x +y or -x -y), delta = epsilon.
    /// We approximate Z3's infinitesimal epsilon with a small positive rational.
    /// For general rows, delta = (1/2) * sum(|coeff_j|) for integer variables j.
    pub(crate) fn cube_delta_for_row(
        coeffs: &[(u32, Rational)],
        _basic_var: u32,
        integer_vars: &HashSet<TermId>,
        solver: &Self,
    ) -> Rational {
        // Two-variable special cases (Z3: int_cube.cpp:84-103)
        if coeffs.len() == 2 {
            let all_int = coeffs.iter().all(|(var, _)| {
                solver
                    .var_to_term
                    .get(var)
                    .is_some_and(|t| integer_vars.contains(t))
            });
            if all_int {
                let c0 = &coeffs[0].1;
                let c1 = &coeffs[1].1;
                let one = Rational::Small(1, 1);
                let neg_one = Rational::Small(-1, 1);
                // Difference term: +1 and -1 coefficients → delta = 0
                let is_diff = (*c0 == one && *c1 == neg_one) || (*c0 == neg_one && *c1 == one);
                if is_diff {
                    return Rational::zero();
                }
                // Unit coefficients both same sign → delta = epsilon
                let is_unit_same = (*c0 == one && *c1 == one) || (*c0 == neg_one && *c1 == neg_one);
                if is_unit_same {
                    return Self::cube_epsilon();
                }
            }
        }

        // General case: delta = (1/2) * sum(|coeff_j|) for integer j
        let mut sum = Rational::zero();
        for (var, coeff) in coeffs {
            let is_int = solver
                .var_to_term
                .get(var)
                .is_some_and(|t| integer_vars.contains(t));
            if is_int {
                sum += coeff.abs();
            }
        }
        sum * Rational::new(1, 2)
    }

    /// Approximate Z3's infinitesimal epsilon with a tiny rational.
    fn cube_epsilon() -> Rational {
        Rational::new(1, 1_000_000)
    }

    /// Round all integer variables to the nearest integer value.
    ///
    /// Z3 reference: `lar_solver::round_to_integer_solution()` (lar_solver.cpp:2577-2601).
    ///
    /// 1. Round each non-basic integer variable to the nearest integer.
    /// 2. Recompute basic variable values from the tableau rows to maintain
    ///    the invariant: basic_var = Σ(coeff * nonbasic_var) + constant.
    fn round_integer_vars_to_nearest(&mut self, integer_vars: &HashSet<TermId>) {
        // Step 1: Round non-basic integer variables
        // Sort for deterministic rounding order — different orders produce different
        // basic variable values after recomputation (#3060)
        // #inc-guard-memo: this function rewrites variable values wholesale —
        // memo invalid and tracked-only chain broken (#inc-guard-chain).
        self.guard_clean_valid = false;
        self.guard_tracked_only = false;
        let mut sorted_terms: Vec<_> = self.term_to_var.iter().collect();
        sorted_terms.sort_by_key(|(&term, _)| term.0);
        for (&term, &var) in sorted_terms {
            if !integer_vars.contains(&term) {
                continue;
            }
            if !matches!(self.vars[var as usize].status, Some(VarStatus::NonBasic)) {
                continue;
            }
            let val = self.vars[var as usize].value.x_rational();
            if val.is_integer() {
                continue;
            }
            let floor = val.floor();
            let ceil = val.ceil();
            let floor_rat = Rational::from(floor);
            let ceil_rat = Rational::from(ceil);
            let dist_floor = (&val - &floor_rat).abs();
            let dist_ceil = (&ceil_rat - &val).abs();
            let rounded = if dist_floor <= dist_ceil {
                floor_rat
            } else {
                ceil_rat
            };
            self.vars[var as usize].value = InfRational::from_rat(rounded);
        }

        // Step 2: Recompute basic variable values from rows
        for row in &self.rows {
            let mut val = InfRational::from_rat(row.constant.clone());
            for (var, coeff) in &row.coeffs {
                val += &self.vars[*var as usize].value.mul_rat(coeff);
            }
            self.vars[row.basic_var as usize].value = val;
        }

        self.dirty = true;
    }

    /// Round integer variables and keep the rounded assignment only if all
    /// variable bounds remain satisfied.
    pub(crate) fn round_integer_vars_if_feasible(
        &mut self,
        integer_vars: &HashSet<TermId>,
    ) -> bool {
        let saved_values: Vec<InfRational> =
            self.vars.iter().map(|info| info.value.clone()).collect();
        self.round_integer_vars_to_nearest(integer_vars);

        if self.assignment_satisfies_bounds() {
            return true;
        }

        // #inc-guard-memo: restoring saved values is a value mutation — memo
        // invalid and tracked-only chain broken (#inc-guard-chain).
        self.guard_clean_valid = false;
        self.guard_tracked_only = false;
        for (var, saved) in self.vars.iter_mut().zip(saved_values) {
            var.value = saved;
        }
        false
    }

    /// Check whether current variable values satisfy all active bounds.
    pub(crate) fn assignment_satisfies_bounds(&self) -> bool {
        (0..self.vars.len()).all(|var| self.violates_bounds(var as u32).is_none())
    }

    /// Check whether all integer variables have integer-valued assignments.
    ///
    /// Z3 reference: `r_basis_has_inf_int()` — returns true when some basis
    /// variable is integer-sorted but fractional. We invert: return true when
    /// ALL integer variables (basis or not) are integral.
    pub(crate) fn all_integer_vars_integral(&self, integer_vars: &HashSet<TermId>) -> bool {
        for (&term, &var) in &self.term_to_var {
            if !integer_vars.contains(&term) {
                continue;
            }
            if !self.vars[var as usize].value.is_integer() {
                return false;
            }
        }
        true
    }

    // try_patch_integer_var, add_direct_bound, add_direct_bound_with_reasons
    // extracted to lia_patch.rs
}
