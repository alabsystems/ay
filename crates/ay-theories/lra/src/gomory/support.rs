// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    pub(super) fn is_integer_var(
        &self,
        var: u32,
        integer_vars: &HashSet<TermId>,
        int_var_ids: &HashSet<u32>,
    ) -> bool {
        if let Some(&term) = self.var_to_term.get(&var) {
            integer_vars.contains(&term)
        } else {
            int_var_ids.contains(&var)
        }
    }

    pub(super) fn collect_row_active_bound_reasons(
        &self,
        row: &TableauRow,
        basic_var: u32,
    ) -> Vec<(TermId, bool)> {
        let mut reasons = Vec::new();
        for (var, _) in &row.coeffs {
            if *var == basic_var {
                continue;
            }
            let info = &self.vars[*var as usize];
            if Self::is_at_lower_bound(info) {
                Self::append_bound_reasons(&mut reasons, info.lower.as_ref());
            }
            if Self::is_at_upper_bound(info) {
                Self::append_bound_reasons(&mut reasons, info.upper.as_ref());
            }
        }
        reasons
    }

    fn append_bound_reasons(reasons: &mut Vec<(TermId, bool)>, bound: Option<&crate::Bound>) {
        let Some(bound) = bound else {
            return;
        };

        for (reason, value) in bound.reasons.iter().zip(bound.reason_values.iter()) {
            if reason.is_sentinel() {
                continue;
            }
            let pair = (*reason, *value);
            if !reasons.contains(&pair) {
                reasons.push(pair);
            }
        }
    }

    pub(super) fn is_gomory_cut_target(
        &self,
        row: &TableauRow,
        basic_var: u32,
        integer_vars: &HashSet<TermId>,
        int_var_ids: &HashSet<u32>,
    ) -> bool {
        row.coeffs.iter().all(|(var, coeff)| {
            if *var == basic_var {
                return true;
            }
            let is_int_nb = self.is_integer_var(*var, integer_vars, int_var_ids);
            if is_int_nb && coeff.is_integer() && self.vars[*var as usize].value.is_integer() {
                return true;
            }
            let info = &self.vars[*var as usize];
            Self::is_at_lower_bound(info) || Self::is_at_upper_bound(info)
        })
    }

    pub(super) fn gomory_score(basic_value: &BigRational) -> BigRational {
        let frac = crate::fractional_part(basic_value);
        let one_minus = BigRational::one() - &frac;
        if frac <= one_minus {
            frac
        } else {
            one_minus
        }
    }

    /// Select up to `num` candidates using cubic-bias randomization.
    ///
    /// Candidates must already be sorted by score (ascending). A uniform
    /// random index is generated and cubed so that ~87.5% of selections
    /// fall in the first half of the sorted list. This prevents Gomory cut
    /// cycling while still favoring the best-scoring candidates.
    ///
    /// Reference: Z3 `gomory.cpp:408-422`.
    pub(super) fn cubic_bias_pick(
        candidates: &mut Vec<GomoryCandidate>,
        rng: &mut u32,
    ) -> GomoryCandidate {
        debug_assert!(!candidates.is_empty());
        let n = candidates.len();
        if n == 1 {
            return candidates.remove(0);
        }
        // Cubic-bias: cube the uniform ratio to compress toward index 0.
        let raw = Self::xorshift32(rng);
        let ratio = f64::from(raw) / f64::from(u32::MAX);
        let cubed = ratio * ratio * ratio;
        let k = (cubed * n as f64) as usize;
        let k = k.min(n - 1);
        candidates.remove(k)
    }

    /// Xorshift32 PRNG. Fast, minimal state, good enough for selection bias.
    fn xorshift32(state: &mut u32) -> u32 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        *state = x;
        x
    }

    pub(super) fn is_at_lower_bound(info: &VarInfo) -> bool {
        if let Some(ref lower) = info.lower {
            // Exact equality: simplex maintains non-basic variables exactly
            // at bounds in exact arithmetic (BigRational). Z3 also uses
            // exact equality (gomory.cpp via int_solver::at_lower).
            return info.value.rational() == lower.value.to_big();
        }
        false
    }

    pub(super) fn is_at_upper_bound(info: &VarInfo) -> bool {
        if let Some(ref upper) = info.upper {
            return info.value.rational() == upper.value.to_big();
        }
        false
    }

    pub(super) fn abs_ceil_coeff(coeff: &BigRational) -> BigInt {
        coeff.ceil().numer().abs()
    }

    /// Add a Gomory cut as a constraint.
    ///
    /// When `cut.reasons` is empty and `reason` is a sentinel, the cut has no
    /// transitive justification (sentinel-leak from derived bounds, #4919).
    /// Such cuts are skipped because they create sentinel-only bounds that
    /// degrade to Unknown or produce unsound partial conflicts.
    ///
    /// NRA/NIA callers pass a real `reason` term for linearization lemmas;
    /// these are unconditionally valid and are kept.
    pub fn add_gomory_cut(&mut self, cut: &GomoryCut, reason: TermId) {
        // Skip cuts with no reasons AND sentinel-only fallback — they have
        // no transitive justification (#4919).
        if cut.reasons.is_empty() && reason.is_sentinel() {
            return;
        }

        let expr = LinearExpr {
            coeffs: cut
                .coeffs
                .iter()
                .map(|(v, c)| (*v, Rational::from_big(c.clone())))
                .collect(),
            constant: Rational::zero(),
        };

        let bound_type = if cut.is_lower {
            BoundType::Lower
        } else {
            BoundType::Upper
        };

        if cut.reasons.is_empty() {
            // NRA/NIA lemma: use the provided reason term directly.
            self.assert_bound(
                expr,
                Rational::from_big(cut.bound.clone()),
                bound_type,
                false,
                reason,
                true,
            );
        } else {
            self.assert_bound_with_reasons(
                expr,
                Rational::from_big(cut.bound.clone()),
                bound_type,
                false,
                &cut.reasons,
                None,
            );
        }
        self.dirty = true;
    }
}
