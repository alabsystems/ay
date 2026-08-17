// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Modular constraint checking for LIA.
//!
//! Modular arithmetic-based infeasibility detection for integer linear
//! arithmetic. When an equality has a variable with coefficient ±1 and
//! other coefficients share a common GCD > 1, we derive modular
//! constraints that restrict the valid integer values.
//!
//! Bound propagation through substitutions, GCD tightening, and modular
//! conflict detection are in `modular_bounds`.

mod single_equality;

use ay_core::term::{Symbol, TermData};
use ay_core::{TermId, TheoryLit};
use num_bigint::BigInt;
use num_traits::One;

use crate::{gcd_of_abs, positive_mod, LiaSolver};

impl LiaSolver<'_> {
    /// Check if a disequality split conflicts with modular constraints.
    ///
    /// When a disequality split is requested for variable V with excluded value E,
    /// check if modular constraints from equalities make E the only valid integer
    /// in V's bounds. If so, the disequality V != E makes the formula UNSAT.
    pub(crate) fn check_disequality_vs_modular(
        &self,
        split: &ay_core::DisequalitySplitRequest,
    ) -> Option<Vec<TheoryLit>> {
        let debug = self.debug_mod;

        if debug {
            safe_eprintln!(
                "[MOD] check_disequality_vs_modular: var={:?}, excluded={}",
                split.variable,
                split.excluded_value
            );
            safe_eprintln!("[MOD] Asserted literals: {}", self.asserted.len());
        }

        let excluded_int = if split.excluded_value.is_integer() {
            split.excluded_value.numer().clone()
        } else {
            if debug {
                safe_eprintln!("[MOD] Excluded value is not integer, skipping");
            }
            return None; // Non-integer excluded value
        };

        // Re-enabled (#5970 fix): Diophantine substitution-based modular
        // unique-value check. The original bug was stale Dioph cache entries
        // from a different Boolean context (ITE branching with mod encoding
        // auxiliary variables). This is now safe because:
        //
        // 1. check_inner() validates the equality key at lines 86-88 before
        //    reaching NeedDisequalitySplit — stale caches are cleared when the
        //    equality set changes.
        // 2. check_during_propagate_inner() clears caches on key mismatch
        //    (check.rs:672-678).
        // 3. pop() (theory_impl.rs:138) clears all Dioph state on backtrack.
        // 4. The same dioph_cached_substitutions are already trusted by
        //    check_modular_constraint_conflict (called from Sat/Unknown paths).
        //
        // The check delegates to check_modular_for_var (modular_bounds.rs)
        // which handles both modular infeasibility and unique-value-excluded-
        // by-disequality detection. We filter to substitutions involving the
        // split variable and additionally check the split's excluded_value
        // directly (since the disequality may come from LRA as a split request
        // rather than from an asserted literal).
        for (term_id, coeffs, constant) in &self.dioph_cached_substitutions {
            if *term_id != split.variable {
                continue;
            }
            let gcd = gcd_of_abs(coeffs.iter().map(|(_, c)| c.clone()));
            if gcd <= BigInt::one() {
                continue;
            }
            let residue = positive_mod(constant, &gcd);
            if debug {
                safe_eprintln!(
                    "[MOD] Dioph substitution: {:?} ≡ {} (mod {})",
                    term_id,
                    residue,
                    gcd
                );
            }

            // Get current bounds for the split variable
            if let Some((lb_opt, ub_opt)) = self.lra.get_bounds(*term_id) {
                let effective_lb = lb_opt.as_ref().map(Self::effective_int_lower);
                let effective_ub = ub_opt.as_ref().map(Self::effective_int_upper);

                if let (Some(lb), Some(ub)) = (&effective_lb, &effective_ub) {
                    // Find first valid integer >= lb satisfying modular constraint
                    let diff = &residue - lb;
                    let adjustment = positive_mod(&diff, &gcd);
                    let first_valid = lb + &adjustment;

                    // No valid integer in bounds at all
                    if &first_valid > ub {
                        if debug {
                            safe_eprintln!(
                                "[MOD] UNSAT: no integer in [{}, {}] satisfies ≡ {} (mod {})",
                                lb,
                                ub,
                                residue,
                                gcd
                            );
                        }
                        let conflict: Vec<TheoryLit> = self
                            .asserted
                            .iter()
                            .map(|&(lit, val)| TheoryLit::new(lit, val))
                            .collect();
                        return Some(conflict);
                    }

                    // Check if there's exactly one valid integer and it matches
                    // the excluded value from the disequality split
                    let second_valid = &first_valid + &gcd;
                    if &second_valid > ub && first_valid == excluded_int {
                        if debug {
                            safe_eprintln!(
                                "[MOD] Dioph: disequality excludes unique valid value {} for {:?}",
                                excluded_int,
                                term_id
                            );
                        }
                        // Build conflict from ALL asserted literals (both
                        // polarities). The [lb, ub] window comes from LRA
                        // tableau bounds which can derive from negated atoms
                        // (e.g. !(x <= 5) => x > 5); dropping false-valued
                        // literals would make the conflict under-inclusive
                        // (seed-236 false-UNSAT bug class). Including extra
                        // genuinely-asserted literals only weakens the
                        // learned clause, which is sound.
                        let conflict: Vec<TheoryLit> = self
                            .asserted
                            .iter()
                            .map(|&(lit, val)| TheoryLit::new(lit, val))
                            .collect();
                        return Some(conflict);
                    }
                }
            }
        }

        // Also check the expanded modular GCDs (cross-mod patterns like
        // mod 2 ∧ mod 3 → mod 6)
        for (term_id, gcd, residue) in &self.dioph_cached_modular_gcds {
            if *term_id != split.variable {
                continue;
            }
            if debug {
                safe_eprintln!(
                    "[MOD] Expanded GCD: {:?} ≡ {} (mod {})",
                    term_id,
                    residue,
                    gcd
                );
            }
            if let Some((lb_opt, ub_opt)) = self.lra.get_bounds(*term_id) {
                let effective_lb = lb_opt.as_ref().map(Self::effective_int_lower);
                let effective_ub = ub_opt.as_ref().map(Self::effective_int_upper);

                if let (Some(lb), Some(ub)) = (&effective_lb, &effective_ub) {
                    let diff = residue - lb;
                    let adjustment = positive_mod(&diff, gcd);
                    let first_valid = lb + &adjustment;

                    if &first_valid > ub {
                        if debug {
                            safe_eprintln!(
                                "[MOD] UNSAT: no integer in [{}, {}] satisfies ≡ {} (mod {})",
                                lb,
                                ub,
                                residue,
                                gcd
                            );
                        }
                        let conflict: Vec<TheoryLit> = self
                            .asserted
                            .iter()
                            .map(|&(lit, val)| TheoryLit::new(lit, val))
                            .collect();
                        return Some(conflict);
                    }

                    let second_valid = &first_valid + gcd;
                    if &second_valid > ub && first_valid == excluded_int {
                        if debug {
                            safe_eprintln!(
                                "[MOD] Expanded GCD: disequality excludes unique valid value {} for {:?}",
                                excluded_int, term_id
                            );
                        }
                        let mut conflict: Vec<TheoryLit> = self
                            .asserted
                            .iter()
                            .filter(|&&(_, v)| v)
                            .map(|&(lit, val)| TheoryLit::new(lit, val))
                            .collect();
                        for &diseq_lit in &self.assertion_view().negative_equalities {
                            if let TermData::App(Symbol::Named(n), a) = self.terms.get(diseq_lit) {
                                if n == "=" && a.len() == 2 && a.contains(&split.variable) {
                                    conflict.push(TheoryLit::new(diseq_lit, false));
                                }
                            }
                        }
                        return Some(conflict);
                    }
                }
            }
        }

        // Also check single equalities for modular constraints
        for &literal in &self.assertion_view().positive_equalities {
            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }

            // #C2: the `(var, other_gcd, residue)` candidates are
            // precomputed in the linear cache. A candidate exists for
            // `split.variable` exactly when it appears with coefficient ±1
            // and the other coefficients share a GCD > 1 — the same
            // conditions the previous per-call parse checked.
            let cached = self.cached_linear(args[0], args[1]);

            if debug {
                safe_eprintln!(
                    "[MOD] Equality {:?}: {} variables, constant={}",
                    literal,
                    cached.coeffs.len(),
                    cached.constant
                );
                for (var, coeff) in &cached.coeffs {
                    safe_eprintln!("[MOD]   {:?} -> coeff {}", var, coeff);
                }
            }

            let Some((_, other_gcd, residue)) = cached
                .modular_candidates
                .iter()
                .find(|(var, _, _)| *var == split.variable)
            else {
                if debug {
                    safe_eprintln!(
                        "[MOD]   split.variable {:?} has no modular candidate in equality",
                        split.variable
                    );
                }
                continue;
            };
            let other_gcd = other_gcd.clone();
            let residue = residue.clone();

            if debug {
                safe_eprintln!("[MOD]   other_gcd={}, residue={}", other_gcd, residue);
            }

            // Get bounds on split.variable
            if let Some((lb_opt, ub_opt)) = self.lra.get_bounds(split.variable) {
                if debug {
                    safe_eprintln!("[MOD]   bounds: lb={:?}, ub={:?}", lb_opt, ub_opt);
                }
                // SOUNDNESS (seed-236 false-UNSAT bug class): the UNSAT
                // conclusion below depends on BOTH lb and ub, so the conflict
                // must include the literals that justify them. Bounds whose
                // justification cannot be named must not be used here.
                let lb_reasons = lb_opt.as_ref().and_then(Self::nameable_lra_bound_reasons);
                let ub_reasons = ub_opt.as_ref().and_then(Self::nameable_lra_bound_reasons);
                // For integers, strict bounds need adjustment:
                // lb > v means lb >= ceil(v) for strict, lb >= ceil(v) for non-strict
                // ub < v means ub <= floor(v)-1 for strict integer if v is integer
                let effective_lb = lb_opt.as_ref().map(Self::effective_int_lower);
                let effective_ub = ub_opt.as_ref().map(Self::effective_int_upper);

                if let (Some(lb), Some(ub), Some(lb_reasons), Some(ub_reasons)) =
                    (&effective_lb, &effective_ub, &lb_reasons, &ub_reasons)
                {
                    if debug {
                        safe_eprintln!("[MOD]   effective bounds: [{}, {}]", lb, ub);
                    }

                    // Find first valid integer in [lb, ub] satisfying modular constraint
                    let diff = &residue - lb;
                    let adjustment = positive_mod(&diff, &other_gcd);
                    let first_valid = lb + adjustment;

                    if debug {
                        safe_eprintln!(
                            "[MOD]   first_valid={}, excluded_int={}",
                            first_valid,
                            excluded_int
                        );
                    }

                    // Check if first_valid is the only valid integer and equals excluded_int
                    if &first_valid <= ub {
                        let second_valid = &first_valid + &other_gcd;
                        if debug {
                            safe_eprintln!("[MOD]   second_valid={}, checking if second > ub ({}) and first == excluded",
                                      second_valid, ub);
                        }
                        if &second_valid > ub && first_valid == excluded_int {
                            // The excluded value is the ONLY valid integer!
                            if debug {
                                safe_eprintln!(
                                    "[MOD] Disequality excludes unique valid value {} for {:?}",
                                    excluded_int,
                                    split.variable
                                );
                                safe_eprintln!(
                                    "[MOD] Bounds [{}, {}], residue {} (mod {})",
                                    lb,
                                    ub,
                                    residue,
                                    other_gcd
                                );
                            }
                            // Return conflict with the equality and any disequality literals
                            let mut conflict = vec![TheoryLit::new(literal, true)];
                            let mut seen: std::collections::HashSet<(TermId, bool)> =
                                conflict.iter().map(|l| (l.term, l.value)).collect();
                            // Add any asserted disequality for this variable
                            for &diseq_lit in &self.assertion_view().negative_equalities {
                                if let TermData::App(Symbol::Named(n), a) =
                                    self.terms.get(diseq_lit)
                                {
                                    if n == "=" && a.len() == 2 {
                                        // Check if this is the disequality for our variable
                                        let has_var = a.contains(&split.variable);
                                        if has_var && seen.insert((diseq_lit, false)) {
                                            conflict.push(TheoryLit::new(diseq_lit, false));
                                        }
                                    }
                                }
                            }
                            // SOUNDNESS / COMPLETENESS (#cell03): the modular
                            // UNSAT conclusion ("`first_valid` is the unique valid
                            // residue in [lb, ub] and it equals the excluded
                            // value") depends on BOTH remainder bounds `lb <= r`
                            // and `r <= ub`. Those bounds are genuinely-asserted
                            // facts (the `0 <= r` / `r < |k|` literals emitted by
                            // mod/div elimination). Without them the minimal
                            // `[eq, diseq]` conflict (e.g. `2q+r=1 ∧ r!=1`) is SAT
                            // in isolation (q=-1, r=3); the runtime conflict
                            // verifier re-checks it, finds SAT, and (correctly, to
                            // avoid learning an invalid clause) bails to Unknown.
                            // Adding already-asserted bound literals to a conflict
                            // can only shrink the model set, so this is sound.
                            for reason in self.get_bound_reasons_for_term(Some(split.variable)) {
                                if seen.insert((reason.term, reason.value)) {
                                    conflict.push(reason);
                                }
                            }
                            // SOUNDNESS: the [lb, ub] window came from the
                            // LRA tableau, whose bounds can be tighter than
                            // the direct `x OP c` atoms collected above
                            // (e.g. decision-level or derived bounds). The
                            // conclusion depends on the exact window, so the
                            // LRA bound justifications must be in the
                            // conflict too (seed-236 false-UNSAT bug class).
                            for reason in lb_reasons.iter().chain(ub_reasons.iter()) {
                                if seen.insert((reason.term, reason.value)) {
                                    conflict.push(*reason);
                                }
                            }
                            if self.debug_mod {
                                safe_eprintln!(
                                    "[MOD-CONFLICT] produced len={} for var={:?}",
                                    conflict.len(),
                                    split.variable
                                );
                            }
                            return Some(conflict);
                        }
                    }
                }
            }
        }

        None
    }
}
