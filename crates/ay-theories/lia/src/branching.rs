// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Branch-and-bound variable selection and split request generation for LIA.

use super::*;

impl LiaSolver<'_> {
    /// Compute fractional part score for branching priority.
    /// Returns min(frac, 1-frac) where frac = value - floor(value).
    /// Smaller score = value is closer to an integer = lower priority for branching.
    /// Variables with score ~0.5 are furthest from any integer (best for branching).
    fn fractional_score(value: &BigRational) -> BigRational {
        let floor_val = Self::floor_rational(value);
        let frac = value - BigRational::from(floor_val);
        let half = BigRational::new(BigInt::one(), BigInt::from(2));
        debug_assert!(
            frac >= BigRational::zero() && frac < BigRational::one(),
            "BUG: fractional part out of range: value={value}, frac={frac}"
        );
        let score = if frac <= half {
            frac
        } else {
            BigRational::one() - &frac
        };
        debug_assert!(
            score >= BigRational::zero() && score <= half,
            "BUG: branching fractional score out of range: value={value}, score={score}"
        );
        score
    }

    /// Compute bound span for a variable. Returns None if unbounded.
    pub(crate) fn bound_span(&self, term: TermId) -> Option<BigRational> {
        if let Some((Some(lower), Some(upper))) = self.lra.get_bounds(term) {
            debug_assert!(
                upper.value >= lower.value,
                "BUG: inconsistent bounds for term {term:?}: lower={}, upper={}",
                lower.value,
                upper.value
            );
            Some((&upper.value - &lower.value).to_big())
        } else {
            None
        }
    }

    /// Select the best integer-infeasible variable for branching.
    /// Uses Z3-style heuristics:
    /// 1. Prefer boxed variables with smallest feasible range
    /// 2. Break ties by integrality distance for stable splits
    /// 3. Fall back to unboxed variables by integrality distance
    ///
    /// Returns the selected variable and its value, or None if all satisfied.
    pub(super) fn check_integer_constraints(&self) -> Option<(TermId, BigRational)> {
        instrument::bump(&instrument::EXTRACT_MODEL_CALLS);
        let model = self.lra.extract_model();
        let debug = self.debug_lia_branch;

        // Collect all fractional integer variables with their values
        let mut candidates: Vec<(TermId, BigRational)> = Vec::new();
        for &term in &self.integer_vars {
            if let Some(val) = model.values.get(&term) {
                if !Self::is_integer(val) {
                    candidates.push((term, val.clone()));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        // Prefer branching on variables that are not already known to be dependent
        // via unit-coefficient equalities (e.g. v2 = 4*v1 + 5*v3 + 4).
        let mut independent: Vec<(TermId, BigRational)> = Vec::new();
        let mut dependent: Vec<(TermId, BigRational)> = Vec::new();
        for (term, value) in candidates {
            if self.dioph_safe_dependent_vars.contains(&term) {
                dependent.push((term, value));
            } else {
                independent.push((term, value));
            }
        }
        let candidates = if independent.is_empty() {
            dependent
        } else {
            independent
        };

        if debug {
            safe_eprintln!(
                "[LIA] {} fractional integer variables found",
                candidates.len()
            );
        }

        let mut boxed: Vec<(TermId, BigRational, BigRational, BigRational)> = Vec::new(); // (term, value, span, score)
        let mut others: Vec<(TermId, BigRational, BigRational)> = Vec::new();

        for (term, value) in candidates {
            let score = Self::fractional_score(&value);
            if let Some(span) = self.bound_span(term) {
                boxed.push((term, value, span, score));
            } else {
                others.push((term, value, score));
            }
        }

        // Boxed variables first: smallest span tends to close quickly under splitting.
        // Then prefer stable split points (closer to an integer) and deterministic tie-breaks.
        boxed.sort_by(|a, b| {
            a.2.cmp(&b.2)
                .then_with(|| a.3.cmp(&b.3))
                .then_with(|| a.0 .0.cmp(&b.0 .0))
        });
        // Unboxed fallback: prefer stable splits and deterministic tie-breaks.
        others.sort_by(|a, b| a.2.cmp(&b.2).then_with(|| a.0 .0.cmp(&b.0 .0)));

        // Select from highest priority non-empty category
        let selected = if !boxed.is_empty() {
            if debug {
                safe_eprintln!("[LIA] Selecting from {} boxed candidates", boxed.len());
            }
            let (term, value, span, score) = boxed.remove(0);
            if debug {
                safe_eprintln!(
                    "[LIA] Selected term {} with value {}, span {}, score {}",
                    term.0,
                    value,
                    span,
                    score
                );
            }
            (term, value)
        } else {
            if debug {
                safe_eprintln!("[LIA] Selecting from {} other candidates", others.len());
            }
            // Pick first (best score) from others
            let (term, value, score) = others.remove(0);
            if debug {
                safe_eprintln!(
                    "[LIA] Selected term {} with value {}, score {}",
                    term.0,
                    value,
                    score
                );
            }
            (term, value)
        };

        instrument::bump(&instrument::INT_CONSTRAINT_SELECT);
        Some(selected)
    }

    /// Collect additional split candidates for tightly bounded integer vars.
    ///
    /// This is used by the non-incremental DPLL(T) loop to batch cheap
    /// branch-and-bound splits in one SAT round instead of requesting one
    /// split per round.
    pub fn collect_tight_domain_splits(
        &self,
        exclude_var: TermId,
        max_splits: usize,
    ) -> Vec<SplitRequest> {
        if max_splits == 0 {
            return Vec::new();
        }

        let debug = self.debug_lia;
        let mut candidates: Vec<(TermId, BigRational)> = Vec::new();
        let mut int_vars: Vec<_> = self.integer_vars.iter().copied().collect();
        int_vars.sort_by_key(|t| t.0);

        // Use current LRA bounds first. If they do not expose a tight integer interval,
        // fall back to explicit asserted bounds (x <= c, c <= x, etc.) so we can still
        // batch obvious binary/integer-domain splits in one SAT round.
        for term in int_vars {
            if term == exclude_var {
                continue;
            }

            let split_value = self
                .tight_domain_split_from_lra(term)
                .or_else(|| self.tight_domain_split_from_asserted_bounds(term));

            if let Some(value) = split_value {
                candidates.push((term, value));
                if candidates.len() >= max_splits {
                    break;
                }
            }
        }

        if debug && !candidates.is_empty() {
            safe_eprintln!(
                "[LIA] tight-domain split candidates (exclude {}): {}",
                exclude_var.0,
                candidates.len()
            );
            for (term, split_value) in &candidates {
                safe_eprintln!("[LIA]   candidate term {} split {}", term.0, split_value);
            }
        }

        candidates
            .into_iter()
            .map(|(term, value)| Self::create_split_request(term, value))
            .collect()
    }

    fn tight_domain_split_from_lra(&self, term: TermId) -> Option<BigRational> {
        let half = BigRational::new(BigInt::one(), BigInt::from(2));
        let (Some(lower), Some(upper)) = self.lra.get_bounds(term)? else {
            return None;
        };
        // During all-SAT enumeration, blocking clauses can push bounds past each
        // other (lower > upper) before the LRA solver detects infeasibility (#4947).
        // Return None to let the solver discover the conflict through normal paths.
        if upper.value < lower.value {
            return None;
        }
        let ceil_lb = Self::ceil_rational(&lower.value_big());
        let floor_ub = Self::floor_rational(&upper.value_big());
        (floor_ub == ceil_lb.clone() + BigInt::one()).then(|| BigRational::from(ceil_lb) + half)
    }

    fn tight_domain_split_from_asserted_bounds(&self, term: TermId) -> Option<BigRational> {
        let half = BigRational::new(BigInt::one(), BigInt::from(2));
        let (Some(lower), Some(upper)) = self.get_integer_bounds_for_term(Some(term)) else {
            return None;
        };
        (upper == lower.clone() + BigInt::one()).then(|| BigRational::from(lower) + half)
    }

    /// Find an integer variable whose current bounds allow multiple integer
    /// values. Returns a split request at the midpoint of the bounds.
    /// Used as fallback when the LRA simplex returns Unknown (cycling).
    pub(super) fn find_unsplit_integer_var(&self) -> Option<SplitRequest> {
        // Collect candidates: integer vars with lb < ub where ceil(lb) < floor(ub)
        let mut candidates: Vec<(TermId, BigRational, BigRational)> = Vec::new();
        for &term in &self.integer_vars {
            if let Some((Some(lb_bound), Some(ub_bound))) = self.lra.get_bounds(term) {
                let lb = lb_bound.value_big();
                let ub = ub_bound.value_big();
                // Check if there are at least 2 integer values in [lb, ub]
                let ceil_lb = Self::ceil_rational(&lb);
                let floor_ub = Self::floor_rational(&ub);
                if ceil_lb < floor_ub {
                    candidates.push((term, lb, ub));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        // Sort by TermId for determinism
        candidates.sort_by_key(|(t, _, _)| *t);

        // Pick first candidate, split at midpoint of bounds
        let (var, lb, ub) = &candidates[0];
        let midpoint = (lb + ub) / BigRational::from(BigInt::from(2));
        // Ensure midpoint is fractional (not exactly an integer) for a meaningful split
        let midpoint = if Self::is_integer(&midpoint) {
            // If midpoint is integer, nudge slightly to make it fractional
            &midpoint + BigRational::new(BigInt::from(1), BigInt::from(2))
        } else {
            midpoint
        };
        debug_assert!(
            &midpoint >= lb && &midpoint <= ub,
            "BUG: fallback split midpoint escaped bounds for term {}: midpoint={midpoint}, lb={lb}, ub={ub}",
            var.0
        );
        Some(Self::create_split_request(*var, midpoint))
    }

    pub(crate) fn create_split_request(variable: TermId, value: BigRational) -> SplitRequest {
        let floor = Self::floor_rational(&value);
        let ceil = Self::ceil_rational(&value);
        debug_assert!(
            floor <= ceil,
            "BUG: split request has inverted floor/ceil for term {}: floor={floor}, ceil={ceil}, value={value}",
            variable.0,
        );
        debug_assert!(
            BigRational::from(floor.clone()) <= value && value <= BigRational::from(ceil.clone()),
            "BUG: split request value outside [floor, ceil] for term {}: floor={floor}, value={value}, ceil={ceil}",
            variable.0,
        );

        SplitRequest {
            variable,
            value,
            floor,
            ceil,
        }
    }

    /// Try patching fractional integer variables to avoid branching.
    ///
    /// This is Z3's "patching" technique that adjusts non-basic integer variables
    /// to make fractional basic variables integral. It avoids branching entirely
    /// when successful, which can dramatically speed up solving.
    ///
    /// Returns true if any patching succeeded (caller should re-check).
    pub(super) fn try_patching(&mut self) -> bool {
        let debug = self.debug_patch;
        instrument::bump(&instrument::PATCHING_CALLS);
        instrument::bump(&instrument::EXTRACT_MODEL_CALLS);
        let model = self.lra.extract_model();

        // Find all fractional integer variables.
        // Sort by TermId for deterministic patching order (#2657).
        // HashSet iteration order is nondeterministic, and the order of patching
        // attempts affects which search branch the solver explores.
        let mut fractional_vars: Vec<TermId> = Vec::new();
        for &term in &self.integer_vars {
            if let Some(val) = model.values.get(&term) {
                if !Self::is_integer(val) {
                    fractional_vars.push(term);
                }
            }
        }
        fractional_vars.sort_by_key(|t| t.0);

        if fractional_vars.is_empty() {
            return false;
        }

        if debug {
            safe_eprintln!(
                "[PATCH] Trying to patch {} fractional vars",
                fractional_vars.len()
            );
        }

        // Try patching each fractional variable
        for term in fractional_vars {
            // Patching adjusts values and may add direct bounds on this var;
            // mark for the next integer-bounds rescan (#C4).
            self.mark_int_bound_dirty(term);
            if self.lra.try_patch_integer_var(term, &self.integer_vars) {
                // Patching one variable may fix multiple, so return immediately
                // to re-check the state
                return true;
            }
        }

        false
    }
}
