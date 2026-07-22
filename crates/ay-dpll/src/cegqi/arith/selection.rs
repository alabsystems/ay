// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-based projection selection for CEGQI arithmetic.
//!
//! Implements the term selection algorithm from Reynolds et al. FMSD 2017 and
//! CVC5's `ceg_arith_instantiator.cpp`. Given collected bounds and a model
//! value, selects an instantiation term with correct divisibility properties.

use ay_core::{TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::{ArithInstantiator, Bound};

impl ArithInstantiator {
    /// Select an instantiation term using model-based projection.
    ///
    /// Based on CVC5's `getModelBasedProjectionValue` and Reynolds et al. FMSD 2017.
    /// For integer variables with bounds `c*pv >= t`, computes:
    ///   rho = (c * pv^M - t^M) mod |c|
    ///   selection = (t + rho) / c
    ///
    /// This ensures the selection term satisfies divisibility constraints and
    /// connects symbolically to the bound structure for better generalization.
    pub(crate) fn select_term(
        &self,
        terms: &mut TermStore,
        pv: TermId,
        model_value: &BigRational,
        is_integer: bool,
    ) -> Option<TermId> {
        let _ = pv; // Used for debugging
        let one = BigRational::from(BigInt::from(1));

        // Priority 1: Equalities (c*pv = t → pv = t/c)
        if let Some((coeff, term)) = self.equalities.first() {
            if *coeff == one {
                return Some(*term);
            }
            // For coeff != 1: compute t / c
            return Some(Self::divide_term(terms, *term, coeff, is_integer));
        }

        if !is_integer {
            return Some(self.select_real_term(terms, model_value));
        }

        // Priority 2: Single-sided bounds — use tightest bound with rho
        if self.upper_bounds.is_empty() && !self.lower_bounds.is_empty() {
            let bound = Self::select_tightest_lower(&self.lower_bounds, model_value);
            return Some(Self::bound_selection_term(
                terms,
                bound,
                model_value,
                is_integer,
                true,
            ));
        }

        if self.lower_bounds.is_empty() && !self.upper_bounds.is_empty() {
            let bound = Self::select_tightest_upper(&self.upper_bounds, model_value);
            return Some(Self::bound_selection_term(
                terms,
                bound,
                model_value,
                is_integer,
                false,
            ));
        }

        // Priority 3: Both bounds exist — use tightest lower bound with rho.
        // CVC5 tries lower first, then upper. We follow the same strategy.
        if !self.lower_bounds.is_empty() && !self.upper_bounds.is_empty() {
            let bound = Self::select_tightest_lower(&self.lower_bounds, model_value);
            return Some(Self::bound_selection_term(
                terms,
                bound,
                model_value,
                is_integer,
                true,
            ));
        }

        // Priority 4: No bounds at all — model value fallback
        if is_integer {
            let int_val = model_value.numer().clone() / model_value.denom();
            Some(terms.mk_int(int_val))
        } else {
            Some(terms.mk_rational(model_value.clone()))
        }
    }

    fn select_real_term(&self, terms: &mut TermStore, model_value: &BigRational) -> TermId {
        if self.upper_bounds.is_empty() && !self.lower_bounds.is_empty() {
            let bound = Self::select_tightest_lower(&self.lower_bounds, model_value);
            return Self::real_single_bound_selection_term(terms, bound, true);
        }

        if self.lower_bounds.is_empty() && !self.upper_bounds.is_empty() {
            let bound = Self::select_tightest_upper(&self.upper_bounds, model_value);
            return Self::real_single_bound_selection_term(terms, bound, false);
        }

        if !self.lower_bounds.is_empty() && !self.upper_bounds.is_empty() {
            let lower = Self::select_tightest_lower(&self.lower_bounds, model_value);
            let upper = Self::select_tightest_upper(&self.upper_bounds, model_value);
            return Self::real_midpoint_selection_term(terms, lower, upper);
        }

        terms.mk_rational(model_value.clone())
    }

    fn real_single_bound_selection_term(
        terms: &mut TermStore,
        bound: &Bound,
        is_lower: bool,
    ) -> TermId {
        let base = Self::real_bound_value_term(terms, bound);
        if !bound.strict {
            return base;
        }

        let delta = terms.mk_rational(BigRational::from(BigInt::from(1)));
        if is_lower {
            terms.mk_add(vec![base, delta])
        } else {
            terms.mk_sub(vec![base, delta])
        }
    }

    fn real_midpoint_selection_term(terms: &mut TermStore, lower: &Bound, upper: &Bound) -> TermId {
        let lower_term = Self::real_bound_value_term(terms, lower);
        let upper_term = Self::real_bound_value_term(terms, upper);
        let sum = terms.mk_add(vec![lower_term, upper_term]);
        let half = terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
        terms.mk_mul(vec![sum, half])
    }

    fn real_bound_value_term(terms: &mut TermStore, bound: &Bound) -> TermId {
        let one = BigRational::from(BigInt::from(1));
        if bound.coeff == one {
            bound.term
        } else {
            Self::divide_term(terms, bound.term, &bound.coeff, false)
        }
    }

    /// Select the tightest lower bound (the one with the largest t/c model value).
    /// If model values are not populated on bounds, falls back to the first bound.
    fn select_tightest_lower<'a>(bounds: &'a [Bound], _model_value: &BigRational) -> &'a Bound {
        let mut best = &bounds[0];
        for bound in &bounds[1..] {
            // Compare t^M / c for each bound — larger is tighter for lower bounds
            match (&best.model_value, &bound.model_value) {
                (Some(best_mv), Some(cand_mv)) => {
                    let best_val = best_mv / &best.coeff;
                    let cand_val = cand_mv / &bound.coeff;
                    if cand_val > best_val {
                        best = bound;
                    }
                }
                (None, Some(_)) => {
                    best = bound;
                }
                _ => {}
            }
        }
        best
    }

    /// Select the tightest upper bound (the one with the smallest t/c model value).
    fn select_tightest_upper<'a>(bounds: &'a [Bound], _model_value: &BigRational) -> &'a Bound {
        let mut best = &bounds[0];
        for bound in &bounds[1..] {
            match (&best.model_value, &bound.model_value) {
                (Some(best_mv), Some(cand_mv)) => {
                    let best_val = best_mv / &best.coeff;
                    let cand_val = cand_mv / &bound.coeff;
                    if cand_val < best_val {
                        best = bound;
                    }
                }
                (None, Some(_)) => {
                    best = bound;
                }
                _ => {}
            }
        }
        best
    }

    /// Construct the selection term from a bound using rho computation.
    ///
    /// For lower bound `c*pv >= t` with model value `pv^M`:
    ///   rho = (c * pv^M - t^M) mod |c|
    ///   selection = (t + rho) / c
    ///
    /// For upper bound `c*pv <= t`:
    ///   rho = (t^M - c * pv^M) mod |c|
    ///   selection = (t - rho) / c
    ///
    /// When the bound's model_value is not available or coefficient is 1,
    /// falls back to simple t/c division.
    fn bound_selection_term(
        terms: &mut TermStore,
        bound: &Bound,
        model_value: &BigRational,
        is_integer: bool,
        is_lower: bool,
    ) -> TermId {
        let one = BigRational::from(BigInt::from(1));

        // For unit coefficient, no rho computation needed (rho is always 0 mod 1 = 0)
        if bound.coeff == one {
            return bound.term;
        }

        // For non-integer (Real), no rho needed — just divide by coefficient
        if !is_integer {
            return Self::divide_term(terms, bound.term, &bound.coeff, false);
        }

        // Integer with non-unit coefficient: compute rho
        // rho = (c * pv^M - t^M) mod |c|  for lower bounds
        // rho = (t^M - c * pv^M) mod |c|  for upper bounds
        if let Some(t_model) = &bound.model_value {
            let c = &bound.coeff;
            let ce_value = c * model_value; // c * pv^M

            let diff = if is_lower {
                &ce_value - t_model // c * pv^M - t^M
            } else {
                t_model - &ce_value // t^M - c * pv^M
            };

            // Euclidean modulus: always non-negative, matching SMT-LIB semantics
            let abs_c = if c < &BigRational::from(BigInt::from(0)) {
                -c.clone()
            } else {
                c.clone()
            };
            let rho = Self::euclidean_mod_rational(&diff, &abs_c);

            if rho.is_zero() {
                // rho = 0: selection = t / c
                return Self::divide_term(terms, bound.term, c, true);
            }

            // rho > 0: selection = (t + rho) / c  or  (t - rho) / c
            debug_assert!(rho.is_integer(), "BUG: rho must be integer, got {rho}");
            let rho_int = rho.numer().clone() / rho.denom();
            let rho_term = terms.mk_int(rho_int);

            let adjusted = if is_lower {
                terms.mk_add(vec![bound.term, rho_term]) // t + rho
            } else {
                terms.mk_sub(vec![bound.term, rho_term]) // t - rho
            };

            return Self::divide_term(terms, adjusted, c, true);
        }

        // No model value available for bound term — fall back to simple division
        Self::divide_term(terms, bound.term, &bound.coeff, is_integer)
    }

    /// Euclidean modulus for BigRational: result is always in [0, |divisor|).
    /// Both operands must be integer-valued rationals.
    fn euclidean_mod_rational(a: &BigRational, b: &BigRational) -> BigRational {
        debug_assert!(
            a.is_integer() && b.is_integer(),
            "euclidean_mod_rational requires integers"
        );
        let a_int = a.numer().clone() / a.denom();
        let b_int = b.numer().clone() / b.denom();
        if b_int.is_zero() {
            return BigRational::from(BigInt::from(0));
        }
        // Euclidean remainder: r = a - b * floor(a / b), always >= 0
        let (_quot, rem) = a_int.div_rem(&b_int);
        let r = if rem < BigInt::from(0) {
            &rem + b_int.abs()
        } else {
            rem
        };
        BigRational::from(r)
    }

    /// Compute `term / coeff` as a new term.
    ///
    /// For integer sorts, creates `(div term coeff)`.
    /// For real sorts, creates `(/ term coeff)`.
    pub(super) fn divide_term(
        terms: &mut TermStore,
        term: TermId,
        coeff: &BigRational,
        is_integer: bool,
    ) -> TermId {
        if is_integer {
            // Integer division: (div term coeff_int)
            // Coefficient from integer constraints should always have denominator 1.
            // A fractional coefficient here indicates a bug in extract_bound.
            debug_assert!(
                coeff.is_integer(),
                "BUG: divide_term called with fractional coefficient {coeff} for integer sort"
            );
            let coeff_int = coeff.numer().clone() / coeff.denom();
            let coeff_term = terms.mk_int(coeff_int);
            terms.mk_intdiv(term, coeff_term)
        } else {
            // Real division: multiply by 1/coeff as a rational constant
            let inv_coeff = BigRational::new(coeff.denom().clone(), coeff.numer().clone());
            let inv_term = terms.mk_rational(inv_coeff);
            terms.mk_mul(vec![term, inv_term])
        }
    }
}
