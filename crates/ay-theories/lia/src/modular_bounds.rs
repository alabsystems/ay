// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound propagation and GCD tightening for modular LIA constraints.
//!
//! Propagates bounds through Diophantine substitutions, tightens bounds
//! via GCD residues, and detects modular constraint conflicts. Single
//! equality modular checking is in `modular`.

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{TermId, TheoryLit};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use tracing::{debug, info};

use crate::{gcd_of_abs, positive_mod, LiaSolver};

impl LiaSolver<'_> {
    /// Propagate bounds through cached substitutions.
    ///
    /// For each cached substitution `var = c + Σ(a_i * dep_i)`, uses current
    /// bounds on dep_i to derive tighter bounds on var. Runs both interval
    /// propagation and GCD-based tightening in a fixpoint loop.
    pub(crate) fn propagate_bounds_through_substitutions(&mut self) -> bool {
        // Run interval propagation and GCD tightening in a fixpoint loop.
        // Each pass may tighten bounds that enable further tightening.
        let max_rounds = 4;
        let mut any_changed = false;
        let mut rounds = 0usize;
        for _ in 0..max_rounds {
            rounds += 1;
            let changed_interval = self.propagate_interval_bounds();
            let changed_gcd = self.tighten_bounds_via_gcd();
            if changed_interval || changed_gcd {
                any_changed = true;
            } else {
                break;
            }
        }
        if any_changed {
            // #8147: Dioph substitution propagation modified LRA bounds.
            self.dioph_modified_bounds = true;
            debug!(
                target: "ay::lia",
                rounds,
                substitutions = self.dioph_cached_substitutions.len(),
                "Bound propagation tightened bounds"
            );
        }
        any_changed
    }

    /// Interval-based bound propagation through substitutions.
    ///
    /// For each cached substitution `var = c + Σ(a_i * dep_i)`, computes
    /// implied bounds from the interval bounds of the dependent variables.
    /// Returns true if any bound was tightened.
    fn propagate_interval_bounds(&mut self) -> bool {
        use num_rational::BigRational;
        let debug = self.debug_dioph;
        let mut changed = false;

        // Use cached equality reasons for tightened bounds (critical for
        // PDR interpolation and conflict analysis). The substitutions were
        // derived from these equalities.
        let base_reasons = self.dioph_cached_reasons.clone();

        for (term_id, coeffs, constant) in self.dioph_cached_substitutions.clone() {
            let mut implied_lower: Option<BigRational> = Some(BigRational::from(constant.clone()));
            let mut implied_upper: Option<BigRational> = Some(BigRational::from(constant.clone()));
            // #8012 soundness fix: collect bound reasons from each dependent
            // variable. The implied bound on `var` depends not only on the
            // substitution equality (base_reasons) but also on the specific
            // bounds of each dep_i. Without these, the conflict clause is
            // too strong and prunes valid SAT assignments.
            let mut lower_bound_reasons: Vec<(TermId, bool)> = Vec::new();
            let mut upper_bound_reasons: Vec<(TermId, bool)> = Vec::new();

            for (dep_term, coeff) in &coeffs {
                let (dep_lower_bound, dep_upper_bound) = match self.lra.get_bounds(*dep_term) {
                    Some((l, u)) => (l, u),
                    None => (None, None),
                };

                let coeff_rat = BigRational::from(coeff.clone());

                if coeff.is_positive() {
                    // For implied_lower: need dep_lower (positive coeff)
                    if let (Some(ref mut il), Some(ref dlb)) =
                        (&mut implied_lower, &dep_lower_bound)
                    {
                        *il += &coeff_rat * &dlb.value_big();
                        // Collect the reasons that justify this dep's lower bound
                        for (reason, &reason_val) in
                            dlb.reasons.iter().zip(dlb.reason_values.iter())
                        {
                            lower_bound_reasons.push((*reason, reason_val));
                        }
                    } else {
                        implied_lower = None;
                    }
                    // For implied_upper: need dep_upper (positive coeff)
                    if let (Some(ref mut iu), Some(ref dub)) =
                        (&mut implied_upper, &dep_upper_bound)
                    {
                        *iu += &coeff_rat * &dub.value_big();
                        for (reason, &reason_val) in
                            dub.reasons.iter().zip(dub.reason_values.iter())
                        {
                            upper_bound_reasons.push((*reason, reason_val));
                        }
                    } else {
                        implied_upper = None;
                    }
                } else {
                    // For implied_lower: need dep_upper (negative coeff)
                    if let (Some(ref mut il), Some(ref dub)) =
                        (&mut implied_lower, &dep_upper_bound)
                    {
                        *il += &coeff_rat * &dub.value_big();
                        for (reason, &reason_val) in
                            dub.reasons.iter().zip(dub.reason_values.iter())
                        {
                            lower_bound_reasons.push((*reason, reason_val));
                        }
                    } else {
                        implied_lower = None;
                    }
                    // For implied_upper: need dep_lower (negative coeff)
                    if let (Some(ref mut iu), Some(ref dlb)) =
                        (&mut implied_upper, &dep_lower_bound)
                    {
                        *iu += &coeff_rat * &dlb.value_big();
                        for (reason, &reason_val) in
                            dlb.reasons.iter().zip(dlb.reason_values.iter())
                        {
                            upper_bound_reasons.push((*reason, reason_val));
                        }
                    } else {
                        implied_upper = None;
                    }
                }
            }

            // BUG FIX: Use directional bound assertions, not add_integer_bound.
            // add_integer_bound sets BOTH lower and upper bounds (equality), but
            // propagate_interval_bounds derives one-directional bounds. Setting
            // both bounds forces the variable to a single value, causing false
            // UNSAT when the variable has a wider feasible range.
            // Example: indexof = len(x) with len(x) >= 0 correctly implies
            // indexof >= 0, but NOT indexof <= 0.
            if let Some(il) = implied_lower {
                let il_int = Self::ceil_bigint(&il);
                if let Some((Some(current_lb), _)) = self.lra.get_bounds(term_id) {
                    let current_lb_int = Self::ceil_bigint(&current_lb.value_big());
                    if il_int > current_lb_int {
                        if debug {
                            safe_eprintln!(
                                "[DIOPH] Propagating lower: {:?} {} -> {}",
                                term_id,
                                current_lb_int,
                                il_int
                            );
                        }
                        // #8012: Combine substitution reasons with dependent
                        // variable bound reasons for a complete justification.
                        let mut all_reasons = base_reasons.clone();
                        for &(reason, reason_val) in &lower_bound_reasons {
                            if !all_reasons.iter().any(|&(r, _)| r == reason) {
                                all_reasons.push((reason, reason_val));
                            }
                        }
                        let lra_var = self.lra.ensure_var_registered(term_id);
                        self.lra.add_direct_bound_with_reasons(
                            lra_var,
                            BigRational::from(il_int),
                            true, // is_lower
                            &all_reasons,
                        );
                        // Modular tightening → rescan this var (#C4).
                        self.mark_int_bound_dirty(term_id);
                        changed = true;
                    }
                }
            }

            if let Some(iu) = implied_upper {
                let iu_int = Self::floor_bigint(&iu);
                if let Some((_, Some(current_ub))) = self.lra.get_bounds(term_id) {
                    let current_ub_int = Self::floor_bigint(&current_ub.value_big());
                    if iu_int < current_ub_int {
                        if debug {
                            safe_eprintln!(
                                "[DIOPH] Propagating upper: {:?} {} -> {}",
                                term_id,
                                current_ub_int,
                                iu_int
                            );
                        }
                        // #8012: Combine substitution reasons with dependent
                        // variable bound reasons for a complete justification.
                        let mut all_reasons = base_reasons.clone();
                        for &(reason, reason_val) in &upper_bound_reasons {
                            if !all_reasons.iter().any(|&(r, _)| r == reason) {
                                all_reasons.push((reason, reason_val));
                            }
                        }
                        let lra_var = self.lra.ensure_var_registered(term_id);
                        self.lra.add_direct_bound_with_reasons(
                            lra_var,
                            BigRational::from(iu_int),
                            false, // is_upper
                            &all_reasons,
                        );
                        // Modular tightening → rescan this var (#C4).
                        self.mark_int_bound_dirty(term_id);
                        changed = true;
                    }
                }
            }
        }

        changed
    }

    /// GCD-based bound tightening (Z3: tighten_bounds_for_non_trivial_gcd).
    ///
    /// For each cached substitution `var = c + Σ(a_i * x_i)` where GCD(a_i) = g > 1:
    /// - We know `var ≡ c (mod g)`
    /// - For upper bound `ub`: tighten to `ub - ((ub - c) mod g)` if remainder != 0
    /// - For lower bound `lb`: tighten to `lb + ((c - lb) mod g)` if remainder != 0
    ///
    /// This is more powerful than interval propagation because it uses modular
    /// arithmetic to skip impossible integer values near the bounds.
    ///
    /// Returns true if any bound was tightened.
    fn tighten_bounds_via_gcd(&mut self) -> bool {
        let debug = self.debug_dioph;
        let mut changed = false;

        // Reasons for tightened bounds: the equalities that produced these substitutions.
        // Critical for PDR interpolation and conflict analysis.
        let base_reasons = self.dioph_cached_reasons.clone();

        for (term_id, coeffs, constant) in self.dioph_cached_substitutions.clone() {
            // Compute GCD of all coefficients
            let gcd = gcd_of_abs(coeffs.iter().map(|(_, c)| c.clone()));

            if gcd <= BigInt::one() {
                continue;
            }

            // var ≡ constant (mod gcd)
            let c_mod_g = positive_mod(&constant, &gcd);

            // Get current integer bounds, including the bound reasons (#8012).
            // The tightened bound depends on the existing bound value, so its
            // reason literals must be included in the justification.
            let (lb_bound, ub_bound) = match self.lra.get_bounds(term_id) {
                Some((l, u)) => (l, u),
                None => continue,
            };

            // Tighten upper bound: find largest v <= ub with v ≡ c_mod_g (mod gcd)
            // new_ub = ub - ((ub - c_mod_g) mod gcd) if remainder != 0
            if let Some(ref ub_b) = ub_bound {
                let ub = Self::floor_bigint(&ub_b.value_big());
                let diff = &ub - &c_mod_g;
                let rs_g = positive_mod(&diff, &gcd);
                if !rs_g.is_zero() {
                    let new_ub = &ub - &rs_g;
                    if debug {
                        safe_eprintln!(
                            "[DIOPH-GCD] Tighten upper: {:?} {} -> {} (mod {} residue {})",
                            term_id,
                            ub,
                            new_ub,
                            gcd,
                            c_mod_g
                        );
                    }
                    // #8012: Include both substitution reasons AND the upper
                    // bound reasons. The tightened bound depends on the current
                    // ub value which is justified by ub_b.reasons.
                    let mut all_reasons = base_reasons.clone();
                    for (reason, &reason_val) in ub_b.reasons.iter().zip(ub_b.reason_values.iter())
                    {
                        if !all_reasons.iter().any(|&(r, _)| r == *reason) {
                            all_reasons.push((*reason, reason_val));
                        }
                    }
                    let lra_var = self.lra.ensure_var_registered(term_id);
                    let rat_ub = num_rational::BigRational::from(new_ub);
                    self.lra
                        .add_direct_bound_with_reasons(lra_var, rat_ub, false, &all_reasons);
                    // GCD tightening → rescan this var (#C4).
                    self.mark_int_bound_dirty(term_id);
                    changed = true;
                }
            }

            // Tighten lower bound: find smallest v >= lb with v ≡ c_mod_g (mod gcd)
            // new_lb = lb + ((c_mod_g - lb) mod gcd) if remainder != 0
            if let Some(ref lb_b) = lb_bound {
                let lb = Self::ceil_bigint(&lb_b.value_big());
                let diff = &c_mod_g - &lb;
                let rs_g = positive_mod(&diff, &gcd);
                if !rs_g.is_zero() {
                    let new_lb = &lb + &rs_g;
                    if debug {
                        safe_eprintln!(
                            "[DIOPH-GCD] Tighten lower: {:?} {} -> {} (mod {} residue {})",
                            term_id,
                            lb,
                            new_lb,
                            gcd,
                            c_mod_g
                        );
                    }
                    // #8012: Include both substitution reasons AND the lower
                    // bound reasons.
                    let mut all_reasons = base_reasons.clone();
                    for (reason, &reason_val) in lb_b.reasons.iter().zip(lb_b.reason_values.iter())
                    {
                        if !all_reasons.iter().any(|&(r, _)| r == *reason) {
                            all_reasons.push((*reason, reason_val));
                        }
                    }
                    let lra_var = self.lra.ensure_var_registered(term_id);
                    let rat_lb = num_rational::BigRational::from(new_lb);
                    self.lra
                        .add_direct_bound_with_reasons(lra_var, rat_lb, true, &all_reasons);
                    // GCD tightening → rescan this var (#C4).
                    self.mark_int_bound_dirty(term_id);
                    changed = true;
                }
            }
        }

        changed
    }

    /// Check modular constraints derived from substitutions against bounds.
    ///
    /// For each substitution `var = c + Σ(a_i * x_i)`, if the GCD of coefficients
    /// is > 1, then `var ≡ c (mod GCD)`. Combined with bounds, this can detect
    /// infeasibility when no valid integer exists in the bounds.
    ///
    /// This is critical for CHC solving where mod constraints interact with bounds.
    pub(crate) fn check_modular_constraint_conflict(&self) -> Option<Vec<TheoryLit>> {
        let debug = self.debug_mod;

        // Check from filtered substitutions (original variables only)
        for (term_id, coeffs, constant) in &self.dioph_cached_substitutions {
            let gcd = gcd_of_abs(coeffs.iter().map(|(_, c)| c.clone()));
            if gcd > BigInt::one() {
                let residue = positive_mod(constant, &gcd);
                if let Some(conflict) =
                    self.check_modular_for_var(*term_id, &gcd, &residue, debug, "substitution")
                {
                    return Some(conflict);
                }
            }
        }

        // Check from fully-expanded modular constraints (including free params).
        // This catches cross-mod patterns like:
        //   (mod b 2)=0 ∧ (mod b 3)=0 → (mod b 6)=0
        // where the Dioph solver derives r3 = -6*f - 6*q3 (f = free param),
        // giving GCD=6 and r3 ≡ 0 (mod 6). The filtered substitutions above
        // miss this because the free param causes the expansion to be dropped.
        for (term_id, gcd, residue) in &self.dioph_cached_modular_gcds {
            if let Some(conflict) =
                self.check_modular_for_var(*term_id, gcd, residue, debug, "expanded-gcd")
            {
                return Some(conflict);
            }
        }

        None
    }

    /// Check a single modular constraint `term ≡ residue (mod gcd)` against
    /// bounds and disequalities.
    fn check_modular_for_var(
        &self,
        term_id: TermId,
        gcd: &BigInt,
        residue: &BigInt,
        debug: bool,
        source: &str,
    ) -> Option<Vec<TheoryLit>> {
        if debug {
            safe_eprintln!(
                "[MOD] Variable {:?} ≡ {} (mod {}) from {}",
                term_id,
                residue,
                gcd,
                source
            );
        }

        // Get current bounds for the variable
        let (lb_opt, ub_opt) = self.lra.get_bounds(term_id)?;
        // For integers, effective bounds are ceil(lb) to floor(ub)
        let effective_lb = lb_opt.as_ref().map(Self::effective_int_lower);
        let effective_ub = ub_opt.as_ref().map(Self::effective_int_upper);

        let (lb, ub) = match (&effective_lb, &effective_ub) {
            (Some(lb), Some(ub)) => (lb, ub),
            _ => return None,
        };

        if debug {
            safe_eprintln!("[MOD] Variable {:?} bounds: [{}, {}]", term_id, lb, ub);
        }

        // Find the first valid integer >= lb that satisfies var ≡ residue (mod gcd)
        // first_valid = lb + ((residue - lb) mod gcd)
        let diff = residue - lb;
        let adjustment = positive_mod(&diff, gcd);
        let first_valid = lb + adjustment;

        // Check if any valid integer exists in [lb, ub]
        if &first_valid > ub {
            info!(
                target: "ay::lia",
                reason = "substitution_modular",
                "Modular substitution UNSAT detected"
            );
            if debug {
                safe_eprintln!(
                    "[MOD] UNSAT: no integer in [{}, {}] satisfies ≡ {} (mod {})",
                    lb,
                    ub,
                    residue,
                    gcd
                );
            }
            // Return conflict: all asserted literals
            let conflict: Vec<TheoryLit> = self
                .asserted
                .iter()
                .map(|&(lit, val)| TheoryLit::new(lit, val))
                .collect();
            return Some(conflict);
        }

        // If bounds are tight enough, we can derive exact value
        if first_valid == *ub || &first_valid + gcd > *ub {
            // Only one valid integer in the range
            if debug {
                safe_eprintln!("[MOD] Unique solution: {:?} = {}", term_id, first_valid);
            }

            // Check if there's a disequality that excludes this unique value
            if let Some(conflict) =
                self.check_disequality_excludes_unique(term_id, &first_valid, debug)
            {
                return Some(conflict);
            }
        }

        None
    }

    /// Check if any asserted disequality excludes the given unique value for a variable.
    fn check_disequality_excludes_unique(
        &self,
        term_id: TermId,
        unique_value: &BigInt,
        debug: bool,
    ) -> Option<Vec<TheoryLit>> {
        for &diseq_lit in &self.assertion_view().negative_equalities {
            if let TermData::App(Symbol::Named(n), a) = self.terms.get(diseq_lit) {
                if n == "=" && a.len() == 2 {
                    let (lhs, rhs) = (a[0], a[1]);
                    let mut excluded_val = None;

                    if lhs == term_id {
                        if let TermData::Const(Constant::Int(c)) = self.terms.get(rhs) {
                            excluded_val = Some(c.clone());
                        }
                    }
                    if rhs == term_id {
                        if let TermData::Const(Constant::Int(c)) = self.terms.get(lhs) {
                            excluded_val = Some(c.clone());
                        }
                    }

                    if let Some(excluded) = excluded_val {
                        if &excluded == unique_value {
                            info!(
                                target: "ay::lia",
                                reason = "unique_value_excluded_by_disequality",
                                "Modular constraint conflict: unique valid value excluded"
                            );
                            if debug {
                                safe_eprintln!(
                                    "[MOD] UNSAT: unique value {} excluded by disequality {:?}",
                                    unique_value,
                                    diseq_lit
                                );
                            }
                            let mut conflict: Vec<TheoryLit> = self
                                .asserted
                                .iter()
                                .filter(|&&(_, v)| v)
                                .map(|&(lit, val)| TheoryLit::new(lit, val))
                                .collect();
                            conflict.push(TheoryLit::new(diseq_lit, false));
                            return Some(conflict);
                        }
                    }
                }
            }
        }

        None
    }
}
