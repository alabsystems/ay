// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deterministic resource limits shared by NIA SOS translation, search, and replay.
//!
//! Every limit is completeness-only. Hitting one declines the SOS lane; it never
//! licenses an algebraic identity or an UNSAT verdict.

use ay_core::term::TermId;
use num_rational::BigRational;
use num_traits::Zero;

use super::MultiPoly;

mod progress;
use progress::ProgressHandle;
pub(crate) use progress::SosProgress;

/// Maximum asserted theory literals inspected by one SOS attempt.
pub(crate) const MAX_SOS_ASSERTED_LITERALS: usize = 1_024;
/// Maximum source-term visits during polynomial translation.
pub(crate) const MAX_SOS_TERM_VISITS: usize = 100_000;
/// Maximum recursive source-term depth during polynomial translation.
pub(crate) const MAX_SOS_TERM_DEPTH: usize = 256;
/// Maximum retained monomials in one translated polynomial.
pub(crate) const MAX_SOS_POLY_TERMS: usize = 256;
/// Maximum monomial insert/merge operations across one translation attempt.
pub(crate) const MAX_SOS_MONOMIAL_WORK: usize = 100_000;
/// Maximum distributive term products across one translation or search attempt.
pub(crate) const MAX_SOS_TERM_PRODUCTS: usize = 100_000;
/// Maximum total retained polynomial terms admitted to search.
pub(crate) const MAX_SOS_TOTAL_POLY_TERMS: usize = 8_192;
/// Degree supported by the W3 certificate search.
pub(crate) const MAX_SOS_POLY_DEGREE: usize = 2;
/// Maximum numerator or denominator magnitude in any retained rational.
///
/// MODEL_CHECKER_CONSUMER machine arithmetic starts from Rust integers no wider than 128
/// bits, and this degree-2 lane therefore needs roughly 256 bits for a direct
/// product. A 1,024-bit envelope leaves substantial exact-elimination headroom
/// without allowing millions of LP updates over impractically large integers.
pub(crate) const MAX_SOS_COEFFICIENT_BITS: u64 = 1_024;
/// Maximum exact-rational tableau updates in one Phase-1 solve.
pub(crate) const MAX_SOS_LP_UPDATES: usize = 10_000_000;
/// Maximum pivots in one Phase-1 solve.
pub(crate) const MAX_SOS_LP_PIVOTS: usize = 4_096;
/// Maximum retained cells in one Phase-1 tableau input.
pub(crate) const MAX_SOS_LP_CELLS: usize = 65_536;

/// Charges between wall-clock progress consultations. The callback
/// behind `SosProgress` reads the deadline/memory guard (a clock
/// syscall), and the polynomial charges below run up to
/// `MAX_SOS_MONOMIAL_WORK` times per attempt: polling on every charge
/// made the clock read itself a top profile frame on Certora
/// QF_UFDTNIA 39657...48. Charges are tiny exact operations, so
/// observing a stop up to this many charges late is immaterial; the
/// refusal itself stays sticky in `SosProgress`, and explicit
/// `poll()` calls (attempt entry/final, LP pivots) remain exact.
const CHARGE_POLL_INTERVAL: u32 = 64;

/// Shared deterministic work meter for polynomial construction.
#[derive(Debug, Default)]
pub(crate) struct SosPolynomialBudget<'a> {
    term_visits: usize,
    monomial_work: usize,
    term_products: usize,
    charges_until_poll: u32,
    progress: ProgressHandle<'a>,
}

impl<'a> SosPolynomialBudget<'a> {
    pub(crate) fn with_progress(progress: &'a SosProgress<'_>) -> Self {
        Self {
            progress: ProgressHandle::new(progress),
            ..Self::default()
        }
    }

    /// Resume from a counts snapshot taken by [`Self::counts`] (the
    /// incremental SOS fragment cache continuing a previous build's
    /// cumulative budget exactly where it left off).
    pub(crate) fn with_progress_and_counts(
        progress: &'a SosProgress<'_>,
        counts: (usize, usize, usize),
    ) -> Self {
        Self {
            term_visits: counts.0,
            monomial_work: counts.1,
            term_products: counts.2,
            charges_until_poll: 0,
            progress: ProgressHandle::new(progress),
        }
    }

    /// Cumulative `(term_visits, monomial_work, term_products)` so far.
    pub(crate) fn counts(&self) -> (usize, usize, usize) {
        (self.term_visits, self.monomial_work, self.term_products)
    }

    pub(crate) fn poll(&self) -> bool {
        self.progress.poll()
    }

    /// Progress consultation for the per-charge hot paths: consults the
    /// callback on the first charge and then every
    /// `CHARGE_POLL_INTERVAL` charges. Once a refusal is observed the
    /// countdown stays at zero, so every later charge re-asks (cheap:
    /// `SosProgress` short-circuits once refused) and declines.
    pub(crate) fn poll_charged(&mut self) -> bool {
        if self.charges_until_poll == 0 {
            if !self.progress.poll() {
                return false;
            }
            self.charges_until_poll = CHARGE_POLL_INTERVAL;
        }
        self.charges_until_poll -= 1;
        true
    }

    /// Charge one source-term visit at `depth`.
    pub(crate) fn visit_term(&mut self, depth: usize) -> bool {
        if !self.poll_charged()
            || depth > MAX_SOS_TERM_DEPTH
            || self.term_visits >= MAX_SOS_TERM_VISITS
        {
            return false;
        }
        self.term_visits += 1;
        true
    }

    /// Charge one monomial insertion or coefficient merge.
    pub(crate) fn charge_monomial(&mut self) -> bool {
        if !self.poll_charged() || self.monomial_work >= MAX_SOS_MONOMIAL_WORK {
            return false;
        }
        self.monomial_work += 1;
        true
    }

    /// Charge one term-by-term distributive product.
    pub(crate) fn charge_product(&mut self) -> bool {
        if !self.poll_charged() || self.term_products >= MAX_SOS_TERM_PRODUCTS {
            return false;
        }
        self.term_products += 1;
        true
    }
}

/// Whether an exact rational fits the retained-coefficient envelope.
pub(crate) fn rational_fits(value: &BigRational) -> bool {
    value.numer().bits() <= MAX_SOS_COEFFICIENT_BITS
        && value.denom().bits() <= MAX_SOS_COEFFICIENT_BITS
}

/// Validate a polynomial before search or replay performs any expansion.
pub(crate) fn polynomial_fits(poly: &MultiPoly, vars: Option<&[TermId]>) -> bool {
    if poly.terms.len() > MAX_SOS_POLY_TERMS {
        return false;
    }
    poly.terms.iter().all(|(monomial, coefficient)| {
        !coefficient.is_zero()
            && rational_fits(coefficient)
            && monomial.len() <= MAX_SOS_POLY_DEGREE
            && monomial.windows(2).all(|pair| pair[0] <= pair[1])
            && vars.is_none_or(|allowed| monomial.iter().all(|var| allowed.contains(var)))
    })
}

fn add_term(
    poly: &mut MultiPoly,
    monomial: Vec<TermId>,
    coefficient: BigRational,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<()> {
    if !budget.charge_monomial()
        || !rational_fits(&coefficient)
        || monomial.len() > MAX_SOS_POLY_DEGREE
    {
        return None;
    }
    if coefficient.is_zero() {
        return Some(());
    }
    if let Some(index) = poly
        .terms
        .iter()
        .position(|(existing, _)| existing == &monomial)
    {
        let combined = &poly.terms[index].1 + coefficient;
        if !rational_fits(&combined) {
            return None;
        }
        if combined.is_zero() {
            poly.terms.remove(index);
        } else {
            poly.terms[index].1 = combined;
        }
        return Some(());
    }
    if poly.terms.len() >= MAX_SOS_POLY_TERMS {
        return None;
    }
    poly.terms.push((monomial, coefficient));
    Some(())
}

/// Add two polynomials within the degree, coefficient, and work envelope.
pub(crate) fn checked_poly_add(
    left: &MultiPoly,
    right: &MultiPoly,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<MultiPoly> {
    if !budget.poll() {
        return None;
    }
    let mut result = left.clone();
    for (monomial, coefficient) in &right.terms {
        add_term(&mut result, monomial.clone(), coefficient.clone(), budget)?;
    }
    Some(result)
}

/// Negate a polynomial within the coefficient and work envelope.
pub(crate) fn checked_poly_neg(
    poly: &MultiPoly,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<MultiPoly> {
    if !budget.poll() {
        return None;
    }
    let mut result = MultiPoly::zero();
    for (monomial, coefficient) in &poly.terms {
        add_term(&mut result, monomial.clone(), -coefficient, budget)?;
    }
    Some(result)
}

/// Subtract two polynomials within the degree, coefficient, and work envelope.
pub(crate) fn checked_poly_sub(
    left: &MultiPoly,
    right: &MultiPoly,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<MultiPoly> {
    let negated = checked_poly_neg(right, budget)?;
    checked_poly_add(left, &negated, budget)
}

/// Multiply two polynomials within the degree, coefficient, and work envelope.
pub(crate) fn checked_poly_mul(
    left: &MultiPoly,
    right: &MultiPoly,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<MultiPoly> {
    if !budget.poll() {
        return None;
    }
    let mut result = MultiPoly::zero();
    for (left_monomial, left_coefficient) in &left.terms {
        for (right_monomial, right_coefficient) in &right.terms {
            if !budget.charge_product() {
                return None;
            }
            let mut monomial = left_monomial.clone();
            monomial.extend_from_slice(right_monomial);
            monomial.sort_unstable();
            add_term(
                &mut result,
                monomial,
                left_coefficient * right_coefficient,
                budget,
            )?;
        }
    }
    polynomial_fits(&result, None).then_some(result)
}

/// Checked accumulator used for LP work accounting.
#[derive(Debug)]
pub(crate) struct SosLpBudget<'a> {
    updates_left: usize,
    pivots_left: usize,
    progress: ProgressHandle<'a>,
}

impl Default for SosLpBudget<'_> {
    fn default() -> Self {
        Self {
            updates_left: MAX_SOS_LP_UPDATES,
            pivots_left: MAX_SOS_LP_PIVOTS,
            progress: ProgressHandle::default(),
        }
    }
}

impl<'a> SosLpBudget<'a> {
    pub(crate) fn with_progress(progress: &'a SosProgress<'_>) -> Self {
        Self {
            progress: ProgressHandle::new(progress),
            ..Self::default()
        }
    }

    pub(crate) fn poll(&self) -> bool {
        self.progress.poll()
    }

    /// Charge exact-rational updates before performing them.
    pub(crate) fn charge_updates(&mut self, count: usize) -> bool {
        if !self.poll() {
            return false;
        }
        let Some(left) = self.updates_left.checked_sub(count) else {
            return false;
        };
        self.updates_left = left;
        true
    }

    /// Charge one simplex pivot.
    pub(crate) fn charge_pivot(&mut self) -> bool {
        if !self.poll() {
            return false;
        }
        let Some(left) = self.pivots_left.checked_sub(1) else {
            return false;
        };
        self.pivots_left = left;
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn one() -> BigRational {
        BigRational::from_integer(BigInt::from(1u8))
    }

    fn single_term(variable: u32) -> MultiPoly {
        MultiPoly {
            terms: vec![(vec![TermId(variable)], one())],
        }
    }

    #[test]
    fn term_visit_and_depth_limits_decline_at_the_boundary() {
        let mut visits = SosPolynomialBudget {
            term_visits: MAX_SOS_TERM_VISITS - 1,
            ..SosPolynomialBudget::default()
        };
        assert!(visits.visit_term(0));
        assert!(!visits.visit_term(0));

        let mut depth = SosPolynomialBudget::default();
        assert!(depth.visit_term(MAX_SOS_TERM_DEPTH));
        assert!(!depth.visit_term(MAX_SOS_TERM_DEPTH + 1));
    }

    #[test]
    fn polynomial_charges_throttle_progress_callback_but_stay_sticky() {
        use std::cell::Cell;
        // Always-allow: 200 charges must consult the (wall-clock) callback
        // far fewer times than once per charge, but at least once.
        let calls = Cell::new(0usize);
        let allow = || {
            calls.set(calls.get() + 1);
            true
        };
        let progress = SosProgress::new(&allow);
        let mut budget = SosPolynomialBudget::with_progress(&progress);
        for _ in 0..200 {
            assert!(budget.charge_monomial());
        }
        assert!(
            (1..=8).contains(&calls.get()),
            "callback invoked {} times for 200 charges",
            calls.get()
        );

        // A stop is observed within a bounded number of further charges
        // and then sticks (the lattice of refusals is unchanged, only
        // the observation lag is bounded).
        let stop_calls = Cell::new(0usize);
        let stop_after_first = || {
            stop_calls.set(stop_calls.get() + 1);
            stop_calls.get() < 2
        };
        let progress = SosProgress::new(&stop_after_first);
        let mut budget = SosPolynomialBudget::with_progress(&progress);
        let mut refused_at = None;
        for i in 0..512 {
            if !budget.charge_monomial() {
                refused_at = Some(i);
                break;
            }
        }
        let refused_at = refused_at.expect("stop must be observed within bounded charges");
        assert!(refused_at < 256, "observed after {refused_at} charges");
        assert!(!budget.charge_monomial(), "refusal must stick");
        assert!(!budget.poll(), "explicit poll must observe the refusal");
    }

    #[test]
    fn monomial_and_product_work_limits_decline_at_the_boundary() {
        let mut monomials = SosPolynomialBudget {
            monomial_work: MAX_SOS_MONOMIAL_WORK - 1,
            ..SosPolynomialBudget::default()
        };
        assert!(monomials.charge_monomial());
        assert!(!monomials.charge_monomial());

        let mut products = SosPolynomialBudget {
            term_products: MAX_SOS_TERM_PRODUCTS - 1,
            ..SosPolynomialBudget::default()
        };
        assert!(checked_poly_mul(&single_term(1), &single_term(2), &mut products).is_some());
        assert!(checked_poly_mul(&single_term(1), &single_term(2), &mut products).is_none());
    }

    #[test]
    fn polynomial_term_and_degree_limits_decline_before_expansion() {
        let too_many = MultiPoly {
            terms: (0..=MAX_SOS_POLY_TERMS)
                .map(|index| (vec![TermId(index as u32)], one()))
                .collect(),
        };
        assert!(!polynomial_fits(&too_many, None));

        let squared = MultiPoly {
            terms: vec![(vec![TermId(1), TermId(1)], one())],
        };
        assert!(checked_poly_mul(
            &squared,
            &single_term(1),
            &mut SosPolynomialBudget::default()
        )
        .is_none());
    }

    #[test]
    fn coefficient_just_over_bit_limit_declines() {
        let at_limit =
            BigRational::from_integer(BigInt::from(1u8) << (MAX_SOS_COEFFICIENT_BITS as usize - 1));
        let over_limit =
            BigRational::from_integer(BigInt::from(1u8) << MAX_SOS_COEFFICIENT_BITS as usize);
        assert!(rational_fits(&at_limit));
        assert!(!rational_fits(&over_limit));
    }

    #[test]
    fn lp_update_and_pivot_limits_decline_at_the_boundary() {
        let mut budget = SosLpBudget {
            updates_left: 1,
            pivots_left: 1,
            ..SosLpBudget::default()
        };
        assert!(budget.charge_updates(1));
        assert!(!budget.charge_updates(1));
        assert!(budget.charge_pivot());
        assert!(!budget.charge_pivot());
    }
}
