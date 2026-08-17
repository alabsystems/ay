// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Modular constraint checking from individual equalities.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Symbol, TermData};
use ay_core::{TermId, TheoryLit};
use tracing::info;

use crate::{positive_mod, LiaSolver};

impl LiaSolver<'_> {
    fn extend_conflict_with_bound_reasons(conflict: &mut Vec<TheoryLit>, bound: &ay_lra::Bound) {
        for (&reason, &value) in bound.reasons.iter().zip(&bound.reason_values) {
            if !reason.is_sentinel() {
                conflict.push(TheoryLit::new(reason, value));
            }
        }
    }

    fn dedup_conflict_literals(conflict: &mut Vec<TheoryLit>) {
        let mut seen: HashSet<(TermId, bool)> = HashSet::default();
        conflict.retain(|lit| seen.insert((lit.term, lit.value)));
    }

    /// Check modular constraints from single equalities against bounds.
    ///
    /// For an equality like `r = 2*x - 2*y`, if variable `r` has coefficient ±1
    /// and all other coefficients have GCD > 1, then `r ≡ constant (mod GCD)`.
    ///
    /// Combined with bounds on `r`, this can detect infeasibility.
    pub(crate) fn check_single_equality_modular_constraints(&self) -> Option<Vec<TheoryLit>> {
        let debug = self.debug_mod;

        for &literal in &self.assertion_view().positive_equalities {
            // Check if this is an equality
            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }

            // #C2: the per-equality modular candidates `(var, other_gcd,
            // residue)` are assignment-independent and precomputed in the
            // linear cache; equalities without unit-coefficient candidates
            // (the common ITE-derived shape) are skipped without any
            // arithmetic. Only the bounds lookup below is per-assignment.
            let cached = self.cached_linear(args[0], args[1]);
            if cached.modular_candidates.is_empty() {
                continue;
            }

            for (var_term, other_gcd, residue) in &cached.modular_candidates {
                let var_term = *var_term;
                if debug {
                    safe_eprintln!(
                        "[MOD] From equality {:?}: {:?} ≡ {} (mod {})",
                        literal,
                        var_term,
                        residue,
                        other_gcd
                    );
                }

                // Check bounds on var_term
                if let Some((lb_opt, ub_opt)) = self.lra.get_bounds(var_term) {
                    let effective_lb = lb_opt.as_ref().map(Self::effective_int_lower);
                    let effective_ub = ub_opt.as_ref().map(Self::effective_int_upper);

                    if let (Some(lb), Some(ub)) = (&effective_lb, &effective_ub) {
                        if debug {
                            safe_eprintln!(
                                "[MOD] Variable {:?} bounds: [{}, {}]",
                                var_term,
                                lb,
                                ub
                            );
                        }

                        // Find first valid integer >= lb satisfying modular constraint
                        let diff = residue - lb;
                        let adjustment = positive_mod(&diff, other_gcd);
                        let first_valid = lb + adjustment;

                        if &first_valid > ub {
                            info!(
                                target: "ay::lia",
                                reason = "single_equality_modular",
                                "Modular constraint UNSAT detected"
                            );
                            if debug {
                                safe_eprintln!(
                                    "[MOD] UNSAT: no integer in [{}, {}] satisfies ≡ {} (mod {})",
                                    lb,
                                    ub,
                                    residue,
                                    other_gcd
                                );
                            }
                            let mut conflict = vec![TheoryLit::new(literal, true)];
                            if let Some(lb) = lb_opt.as_ref() {
                                Self::extend_conflict_with_bound_reasons(&mut conflict, lb);
                            }
                            if let Some(ub) = ub_opt.as_ref() {
                                Self::extend_conflict_with_bound_reasons(&mut conflict, ub);
                            }
                            Self::dedup_conflict_literals(&mut conflict);

                            // If we cannot explain the bound contribution, skip this UNSAT.
                            // Returning only the equality literal would be unsound.
                            if conflict.len() <= 1 {
                                if debug {
                                    safe_eprintln!(
                                        "[MOD] Skipping UNSAT: missing bound reason literals"
                                    );
                                }
                                continue;
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
