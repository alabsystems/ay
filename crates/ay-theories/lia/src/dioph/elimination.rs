// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable elimination loop for Diophantine equation solving.
//!
//! Implements unit-coefficient elimination, fresh-variable coefficient
//! reduction, and stall detection for the main solve loop.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;
use num_traits::{One, Signed};

use super::solver::{DiophResult, DiophSolver};

impl DiophSolver {
    /// Find the equation with minimum absolute coefficient.
    ///
    /// Returns (equation_index, variable, coefficient) or None if no
    /// non-trivial equations remain.
    pub(super) fn find_min_coeff_equation(&self) -> Option<(usize, usize, BigInt)> {
        let mut best: Option<(usize, usize, BigInt)> = None;

        for (eq_idx, eq) in self.equations.iter().enumerate() {
            if eq.is_trivial() || eq.coeffs.is_empty() {
                continue;
            }
            if let Some((var, coeff)) = eq.find_min_abs_coeff_var() {
                if let Some((_, best_var, ref best_coeff)) = best {
                    // magnitude() comparison == abs() comparison, clone-free.
                    let is_better = coeff.magnitude() < best_coeff.magnitude()
                        || (coeff.magnitude() == best_coeff.magnitude() && var < best_var);
                    if is_better {
                        best = Some((eq_idx, var, coeff));
                    }
                } else {
                    best = Some((eq_idx, var, coeff));
                }
            }
        }

        best
    }

    /// Choose a unit-coefficient elimination pivot that minimizes fill-in.
    ///
    /// Prefers substitutions that introduce the fewest new variables into
    /// other equations (similar to Z3's variable-selection policy in
    /// `find_var_to_substitute_on_espace`).
    fn find_best_unit_elimination(&self) -> Option<(usize, usize, BigInt)> {
        let mut best: Option<(usize, usize, BigInt, usize, usize)> = None;

        // Exact algebraic reformulation of the fill-in cost (#nip residual:
        // the per-candidate all-equations scan made each pivot round
        // O(equations^2 * width), dominating the boundary-chain class).
        //
        // The previous scan computed, for a candidate (eq, var):
        //
        //   fill_cost = sum over other != eq with var in other of
        //                 |{dep in eq.coeffs, dep != var, dep not in other}|
        //
        // For a fixed dep, the number of OTHER equations containing var but
        // not dep is (n[var] - 1) - (co[var,dep] - 1) = n[var] - co[var,dep]
        // (eq itself contains both var and dep, so it is subtracted from
        // both counts). Summing over the (w-1) deps:
        //
        //   fill_cost = (w-1) * n[var] - sum_dep co[var,dep]
        //
        // where n[v] is the number of equations containing v and co[a,b] is
        // the number of equations containing both a and b. Both maps are
        // rebuilt per call in O(sum of width^2) and each candidate costs
        // O(w) lookups. The value is bit-identical to the scan, and the
        // chosen pivot minimizes the total order (fill, width, eq_idx, var)
        // whose minimum is unique, so the result cannot drift.
        let mut n: HashMap<usize, usize> = HashMap::default();
        let mut co: HashMap<(usize, usize), usize> = HashMap::default();
        for eq in &self.equations {
            for &v in eq.coeffs.keys() {
                *n.entry(v).or_insert(0) += 1;
            }
            let mut vars: Vec<usize> = eq.coeffs.keys().copied().collect();
            vars.sort_unstable();
            for (i, &a) in vars.iter().enumerate() {
                for &b in &vars[i + 1..] {
                    *co.entry((a, b)).or_insert(0) += 1;
                }
            }
        }
        let co_count = |a: usize, b: usize| -> usize {
            let key = if a < b { (a, b) } else { (b, a) };
            co.get(&key).copied().unwrap_or(0)
        };

        for (eq_idx, eq) in self.equations.iter().enumerate() {
            if eq.is_trivial() || eq.is_infeasible() {
                continue;
            }

            for (&var, coeff) in &eq.coeffs {
                if !(coeff.is_one() || coeff == &-BigInt::one()) {
                    continue;
                }

                let sub_width = eq.coeffs.len().saturating_sub(1);
                let n_var = n.get(&var).copied().unwrap_or(0);
                let mut fill_cost = sub_width * n_var;
                for &dep_var in eq.coeffs.keys() {
                    if dep_var != var {
                        fill_cost -= co_count(var, dep_var);
                    }
                }

                match best {
                    None => {
                        best = Some((eq_idx, var, coeff.clone(), fill_cost, sub_width));
                    }
                    Some((best_eq_idx, best_var, _, best_fill, best_width)) => {
                        if (fill_cost, sub_width, eq_idx, var)
                            < (best_fill, best_width, best_eq_idx, best_var)
                        {
                            best = Some((eq_idx, var, coeff.clone(), fill_cost, sub_width));
                        }
                    }
                }
            }
        }

        best.map(|(eq_idx, var, coeff, _, _)| (eq_idx, var, coeff))
    }

    /// Snapshot of equation-space complexity used by the progress guard.
    fn complexity_snapshot(&self) -> (usize, Option<BigInt>) {
        let total_terms = self.equations.iter().map(|eq| eq.coeffs.len()).sum();
        let min_coeff = self
            .find_min_coeff_equation()
            .map(|(_, _, coeff)| coeff.abs());
        (total_terms, min_coeff)
    }

    /// Return true when `current` is strictly better than `best`.
    fn complexity_improved(
        current: &(usize, Option<BigInt>),
        best: &(usize, Option<BigInt>),
    ) -> bool {
        if current.0 < best.0 {
            return true;
        }
        if current.0 > best.0 {
            return false;
        }
        match (&current.1, &best.1) {
            (None, Some(_)) => true,
            (Some(_), None) | (None, None) => false,
            (Some(cur), Some(prev)) => cur < prev,
        }
    }

    /// Apply a substitution to all equations, checking for infeasibility.
    fn apply_substitution_to_equations(
        &mut self,
        var: usize,
        sub_coeffs: &HashMap<usize, BigInt>,
        sub_const: &BigInt,
        sources: &[usize],
        skip_idx: Option<usize>,
    ) -> Option<DiophResult> {
        for (i, eq) in self.equations.iter_mut().enumerate() {
            if skip_idx == Some(i) {
                continue;
            }
            let had_var = eq.coeffs.contains_key(&var);
            // Value-exact fast skip (#nip residual, the O(rows) per-pivot
            // normalize tax): an equation without `var` is untouched by
            // `substitute` (no-op by its early return), and when it is
            // already normalized the `normalize()` call is a value-no-op
            // too. Its infeasibility checks were already performed after
            // its last mutation (solve() entry scan or the apply pass that
            // mutated it), so skipping them here cannot hide a conflict.
            if !had_var && eq.normalized {
                continue;
            }
            eq.substitute(var, sub_coeffs, sub_const);
            if had_var {
                eq.merge_sources(sources);
            }
            eq.normalize();

            if eq.is_infeasible() || eq.gcd_infeasible() {
                if self.debug {
                    safe_eprintln!("[DIOPH] Infeasibility after substituting var {}", var);
                }
                return Some(Self::infeasible_from(eq));
            }
        }
        None
    }

    /// Run the main elimination loop, returning early on infeasibility.
    pub(super) fn elimination_loop(&mut self) -> Option<DiophResult> {
        let mut progress = true;
        let mut prev_min_coeff: Option<BigInt> = None;
        let mut min_coeff_stall_rounds = 0usize;
        let max_stall_rounds = self.max_stall_rounds;
        let mut best_complexity = self.complexity_snapshot();
        let mut no_complexity_progress_rounds = 0usize;

        while progress {
            progress = false;

            for eq in &self.equations {
                if eq.is_trivial() {
                    continue;
                }
                if eq.is_infeasible() {
                    if self.debug {
                        safe_eprintln!("[DIOPH] Infeasible equation found: 0 = {}", eq.constant);
                    }
                    return Some(Self::infeasible_from(eq));
                }
            }

            if let Some((eq_idx, var, coeff)) = self.find_best_unit_elimination() {
                progress = true;

                if self.debug {
                    safe_eprintln!(
                        "[DIOPH] Eliminating variable {} with coefficient {} from equation {}",
                        var,
                        coeff,
                        eq_idx
                    );
                }

                let elim_eq = self.equations.remove(eq_idx);

                let mut sub_coeffs: HashMap<usize, BigInt> = HashMap::default();
                for (&other_var, other_coeff) in &elim_eq.coeffs {
                    if other_var != var {
                        sub_coeffs.insert(other_var, -other_coeff / &coeff);
                    }
                }
                let sub_const = &elim_eq.constant / &coeff;

                if let Some(result) = self.apply_substitution_to_equations(
                    var,
                    &sub_coeffs,
                    &sub_const,
                    &elim_eq.sources,
                    None,
                ) {
                    return Some(result);
                }

                self.substitutions.insert(var, (sub_coeffs, sub_const));
                self.equations.retain(|eq| !eq.is_trivial());
                prev_min_coeff = None;
            }

            if let Some(result) = self.try_fresh_var_step(
                &mut progress,
                &mut prev_min_coeff,
                &mut min_coeff_stall_rounds,
                max_stall_rounds,
            ) {
                return Some(result);
            }

            if progress {
                let complexity = self.complexity_snapshot();
                if Self::complexity_improved(&complexity, &best_complexity) {
                    best_complexity = complexity;
                    no_complexity_progress_rounds = 0;
                } else {
                    no_complexity_progress_rounds += 1;
                    if no_complexity_progress_rounds >= max_stall_rounds {
                        if self.debug {
                            safe_eprintln!(
                                "[DIOPH] Structural progress stalled for {} rounds at terms={}, min_coeff={:?}",
                                no_complexity_progress_rounds, complexity.0, complexity.1
                            );
                        }
                        break;
                    }
                }
            }
        }
        None
    }

    /// Attempt a fresh-variable coefficient reduction step.
    fn try_fresh_var_step(
        &mut self,
        progress: &mut bool,
        prev_min_coeff: &mut Option<BigInt>,
        min_coeff_stall_rounds: &mut usize,
        max_stall_rounds: usize,
    ) -> Option<DiophResult> {
        let (eq_idx, pivot_var, pivot_coeff) = self.find_min_coeff_equation()?;
        if pivot_coeff.abs() <= BigInt::one() {
            return None;
        }

        if self.equations[eq_idx].coeffs.len() == 1 {
            if self.debug {
                safe_eprintln!("[DIOPH] Deferring 1-var non-unit equation to direct solve");
            }
            *progress = false;
            return None;
        }

        *progress = true;

        if self.debug {
            safe_eprintln!(
                "[DIOPH] Fresh var step: variable {} with coefficient {} in equation {}",
                pivot_var,
                pivot_coeff,
                eq_idx
            );
        }

        let fresh_var = self.next_fresh_var;
        self.next_fresh_var += 1;

        let fresh_def = self.equations[eq_idx].apply_fresh_var(pivot_var, fresh_var);

        let mut sub_coeffs: HashMap<usize, BigInt> = HashMap::default();
        sub_coeffs.insert(fresh_var, BigInt::one());
        for (&var, quotient) in &fresh_def.quotients {
            sub_coeffs.insert(var, -quotient.clone());
        }
        let sub_const = fresh_def.const_quotient;

        let pivot_sources = self.equations[eq_idx].sources.clone();

        if let Some(result) = self.apply_substitution_to_equations(
            pivot_var,
            &sub_coeffs,
            &sub_const,
            &pivot_sources,
            Some(eq_idx),
        ) {
            return Some(result);
        }

        self.substitutions
            .insert(pivot_var, (sub_coeffs, sub_const));
        self.equations.retain(|eq| !eq.is_trivial());

        // Check for coefficient stall
        let cur_min = self.find_min_coeff_equation().map(|(_, _, c)| c.abs());
        if let (Some(ref prev), Some(ref cur)) = (&*prev_min_coeff, &cur_min) {
            if cur > prev {
                if self.debug {
                    safe_eprintln!(
                        "[DIOPH] Coefficient regression detected: min coeff {cur} > prev {prev}"
                    );
                }
                *progress = false;
                return None;
            }
            if cur == prev {
                *min_coeff_stall_rounds += 1;
                if *min_coeff_stall_rounds >= max_stall_rounds {
                    if self.debug {
                        safe_eprintln!(
                            "[DIOPH] Stall detected: min coeff plateaued at {cur} for {} rounds",
                            *min_coeff_stall_rounds
                        );
                    }
                    *progress = false;
                    return None;
                }
            } else {
                *min_coeff_stall_rounds = 0;
            }
        }
        *prev_min_coeff = cur_min;
        None
    }
}
