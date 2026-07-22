// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap as HashMap;

use crate::types::{PbConstraint, PbLit, PbRel, PbTerm};

/// Errors produced by cutting-planes constraint operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CpError {
    /// Cutting planes only operates on `>=` constraints.
    UnsupportedRelation(PbRel),
    /// Cutting planes requires every term to be linear.
    NonLinearTerm { term_index: usize, lit_count: usize },
    /// Scalar multiplication requires a strictly positive factor.
    NonPositiveMultiplier(i128),
    /// Division requires a strictly positive divisor.
    NonPositiveDivisor(i128),
    /// Resolution requires one constraint to contain `pivot` and the other `!pivot`.
    InvalidResolvePivot { pivot: PbLit },
    /// Coefficient arithmetic overflowed i128.
    CoefficientOverflow,
}

/// Result of a round-to-one resolution step.
///
/// Contains the resolved constraint and metadata about whether the division
/// rule was applied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoundToOneResult {
    /// The resolved constraint.
    pub constraint: CpConstraint,
    /// Whether the division rule was used to reduce the asserting literal's
    /// coefficient to 1. If false, the resolution fell back to standard
    /// addition + saturation + GCD.
    pub used_division: bool,
}

impl RoundToOneResult {
    fn new(constraint: CpConstraint, used_division: bool) -> Self {
        Self {
            constraint,
            used_division,
        }
    }
}

/// A normalized cutting-planes constraint `sum(coeff[lit] * lit) >= degree`.
///
/// The representation is intentionally linear-only and optimized for
/// coefficient arithmetic during conflict analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpConstraint {
    coeffs: HashMap<PbLit, i128>,
    degree: i128,
}

impl CpConstraint {
    /// Creates a new cutting-planes constraint and normalizes its coefficients.
    pub fn new(coeffs: HashMap<PbLit, i128>, degree: i128) -> Self {
        let mut constraint = Self { coeffs, degree };
        constraint.normalize();
        constraint
    }

    /// Returns the internal literal-to-coefficient map.
    pub fn coefficients(&self) -> &HashMap<PbLit, i128> {
        &self.coeffs
    }

    /// Returns the degree (right-hand side).
    pub fn degree(&self) -> i128 {
        self.degree
    }

    /// Returns the coefficient of a literal, or `0` when absent.
    pub fn coefficient(&self, lit: PbLit) -> i128 {
        self.coeffs.get(&lit).copied().unwrap_or(0)
    }

    /// Adds two constraints coefficient-wise and sums their degrees.
    pub fn addition(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.add_assign(other);
        result
    }

    /// Multiplies all coefficients and the degree by a positive scalar.
    pub fn multiply(&mut self, factor: i128) -> Result<(), CpError> {
        if factor <= 0 {
            return Err(CpError::NonPositiveMultiplier(factor));
        }

        for coeff in self.coeffs.values_mut() {
            *coeff = coeff
                .checked_mul(factor)
                .expect("cutting-planes coefficient multiplication must stay within i128");
        }

        self.degree = self
            .degree
            .checked_mul(factor)
            .expect("cutting-planes degree multiplication must stay within i128");
        self.simplify_trivial();
        Ok(())
    }

    /// Divides all coefficients and the degree by a positive scalar, rounding up.
    pub fn divide(&mut self, divisor: i128) -> Result<(), CpError> {
        if divisor <= 0 {
            return Err(CpError::NonPositiveDivisor(divisor));
        }

        for coeff in self.coeffs.values_mut() {
            *coeff = div_ceil_i64(*coeff, divisor);
        }
        self.degree = div_ceil_i64(self.degree, divisor);
        self.normalize();
        Ok(())
    }

    /// Caps each coefficient by the current degree.
    pub fn saturate(&mut self) {
        if self.degree == 0 {
            self.coeffs.clear();
            return;
        }

        for coeff in self.coeffs.values_mut() {
            *coeff = (*coeff).min(self.degree);
        }
        self.compact();
    }

    /// Weakens a literal away by removing its term and decreasing the degree.
    pub fn weaken(&mut self, lit: PbLit) {
        if let Some(coeff) = self.coeffs.remove(&lit) {
            self.degree = self.degree.saturating_sub(coeff).max(0);
            self.simplify_trivial();
        }
    }

    /// Divides the constraint by the GCD of all coefficients.
    pub fn gcd_divide(&mut self) -> Result<(), CpError> {
        let gcd = self.coeffs.values().copied().fold(0, gcd_i64);

        if gcd > 1 {
            self.divide(gcd)?;
        }
        Ok(())
    }

    /// Applies saturation followed by GCD strengthening.
    ///
    /// Saturation: Replace each coefficient `a_i` with `min(a_i, degree)`.
    /// Coefficients larger than the degree contribute no extra propagation power.
    ///
    /// GCD: Divide all coefficients and ceil(degree/gcd) when GCD > 1.
    ///
    /// This is the standard post-analysis strengthening from RoundingSat
    /// (Elffers & Nordstrom, SAT 2018).
    pub fn saturate_and_gcd(&mut self) -> Result<(), CpError> {
        self.saturate();
        self.gcd_divide()
    }

    /// Conservative weakening: removes literals with the smallest coefficients
    /// while preserving the asserting property.
    ///
    /// A literal can be weakened (removed) if:
    /// 1. It is not the asserting literal (the unique literal at the highest
    ///    decision level among falsified literals).
    /// 2. Removing it still leaves the constraint with degree > 0.
    /// 3. After removal, the constraint still propagates (remains asserting).
    ///
    /// The `asserting_lit` parameter identifies the literal that must be
    /// preserved. If `None`, no weakening is performed (we can't identify
    /// which literal is asserting).
    ///
    /// `falsified_fn` returns `Some(level)` for falsified literals and `None`
    /// otherwise. This is used to check that the weakened constraint remains
    /// asserting.
    pub fn weaken_conservative<F>(&mut self, asserting_lit: Option<PbLit>, mut falsified_fn: F)
    where
        F: FnMut(PbLit) -> Option<u32>,
    {
        let Some(asserting) = asserting_lit else {
            return;
        };

        // Collect candidates: non-asserting literals sorted by coefficient ascending.
        // We try to remove the smallest coefficients first.
        let mut candidates: Vec<(PbLit, i128)> = self
            .coeffs
            .iter()
            .filter(|(&lit, _)| lit != asserting)
            .map(|(&lit, &coeff)| (lit, coeff))
            .collect();
        candidates.sort_by_key(|&(_, coeff)| coeff);

        for (lit, coeff) in candidates {
            // Only weaken if the coefficient is strictly less than the degree.
            // If coeff >= degree, removing it would make the constraint trivial
            // or reduce the degree too much.
            if coeff >= self.degree {
                continue;
            }

            // Tentatively weaken: remove the literal and reduce degree.
            let new_degree = self.degree.saturating_sub(coeff).max(0);
            if new_degree <= 0 {
                // Would make constraint trivial.
                continue;
            }

            // Check that the constraint would still be asserting after weakening.
            // The asserting literal must still be the unique highest-level
            // falsified literal, and its coefficient must be enough to make
            // the constraint unit-propagating.
            let asserting_coeff = self.coefficient(asserting);
            if asserting_coeff <= 0 {
                break;
            }

            // After weakening `lit`, the slack contributed by other falsified
            // literals (excluding asserting) changes. We need to verify that
            // the constraint still forces the asserting literal.
            //
            // A simpler sufficient condition: the remaining sum of falsified
            // coefficients (excluding asserting and the weakened literal)
            // plus the asserting coefficient must be >= new_degree, AND
            // the sum without the asserting literal must be < new_degree
            // (so asserting is forced).
            let remaining_falsified_sum: i128 = self
                .coeffs
                .iter()
                .filter(|(&l, _)| l != asserting && l != lit)
                .filter(|(&l, _)| falsified_fn(l).is_some())
                .map(|(_, &c)| c)
                .sum();

            if remaining_falsified_sum >= new_degree {
                // Even without the asserting literal, the constraint is
                // satisfied by the falsified literals alone. The asserting
                // literal wouldn't be forced. Skip this weakening.
                continue;
            }

            // The asserting literal is still forced. Apply the weakening.
            self.coeffs.remove(&lit);
            self.degree = new_degree;
        }

        self.compact();
        self.simplify_trivial();
    }

    /// Full learned constraint strengthening pipeline.
    ///
    /// Applies in order:
    /// 1. Saturation (cap coefficients at degree)
    /// 2. GCD strengthening (divide by GCD of all coefficients)
    /// 3. Conservative weakening (if asserting literal is known)
    /// 4. Re-saturate and GCD after weakening (weakening may create new
    ///    opportunities)
    ///
    /// Reference: RoundingSat (Elffers & Nordstrom, SAT 2018), Section 4.
    pub fn strengthen<F>(
        &mut self,
        asserting_lit: Option<PbLit>,
        falsified_fn: F,
    ) -> Result<(), CpError>
    where
        F: FnMut(PbLit) -> Option<u32>,
    {
        // Step 1+2: Saturation + GCD.
        self.saturate_and_gcd()?;

        // Step 3: Conservative weakening.
        self.weaken_conservative(asserting_lit, falsified_fn);

        // Step 4: Re-saturate + GCD after weakening (may have new opportunities).
        self.saturate_and_gcd()?;

        Ok(())
    }

    /// Ensures all coefficients are positive by flipping literals as needed,
    /// and cancels complementary literal pairs.
    ///
    /// After normalization no two entries in `coeffs` are complementary (`x`
    /// and `~x` with positive coefficients). When both appear, the
    /// tautological identity `x + ~x = 1` is applied: the shared amount is
    /// absorbed into the degree, which is the standard PB-resolution
    /// simplification. This is required for correct conflict analysis; a
    /// learned constraint containing both `x` and `~x` with equal coefficient
    /// is trivially satisfied regardless of assignment, so the propagator can
    /// never use it to assert anything.
    pub fn normalize(&mut self) {
        let mut normalized = HashMap::new();

        for (lit, coeff) in std::mem::take(&mut self.coeffs) {
            if coeff == 0 {
                continue;
            }

            if coeff > 0 {
                add_coeff(&mut normalized, lit, coeff);
            } else {
                let positive_coeff = coeff
                    .checked_abs()
                    .expect("cutting-planes coefficients must not be i128::MIN");
                add_coeff(&mut normalized, negate_lit(lit), positive_coeff);
                self.degree = self
                    .degree
                    .checked_sub(coeff)
                    .expect("negating a negative coefficient must stay within i128");
            }
        }

        self.coeffs = normalized;
        self.cancel_complementary_literals();
        self.compact();
        self.simplify_trivial();
    }

    /// Cancels complementary literal pairs in the constraint.
    ///
    /// When both `x` and `~x` appear with positive coefficients `c1` and
    /// `c2`, the identity `x + ~x = 1` lets us rewrite
    /// `c1*x + c2*~x = m + (c1-m)*x + (c2-m)*~x` where `m = min(c1, c2)`.
    /// The constant `m` contributes unconditionally, so we subtract it from
    /// the degree and drop it from the summation. One of the two literals
    /// ends up with coefficient zero and is removed.
    ///
    /// This is a no-op when the input constraint was already normalized.
    /// Resolution in cutting-planes PB analysis can introduce complementary
    /// pairs (a literal from one side and its negation from the other),
    /// which must be cancelled to obtain an asserting learned constraint.
    fn cancel_complementary_literals(&mut self) {
        // Collect variable -> (positive_coeff, negative_coeff) where
        // positive means the literal appears as `x` and negative as `~x`.
        let mut pairs: HashMap<u32, (i128, i128)> = HashMap::new();
        for (lit, coeff) in &self.coeffs {
            let entry = pairs.entry(lit.var).or_insert((0, 0));
            if lit.negated {
                entry.1 = *coeff;
            } else {
                entry.0 = *coeff;
            }
        }

        for (var, (pos, neg)) in pairs {
            if pos == 0 || neg == 0 {
                continue;
            }
            let shared = pos.min(neg);
            self.degree = self
                .degree
                .checked_sub(shared)
                .expect("cutting-planes degree must stay within i128 after cancellation");
            let pos_lit = PbLit {
                var,
                negated: false,
            };
            let neg_lit = PbLit { var, negated: true };
            let new_pos = pos - shared;
            let new_neg = neg - shared;
            if new_pos == 0 {
                self.coeffs.remove(&pos_lit);
            } else {
                self.coeffs.insert(pos_lit, new_pos);
            }
            if new_neg == 0 {
                self.coeffs.remove(&neg_lit);
            } else {
                self.coeffs.insert(neg_lit, new_neg);
            }
        }
    }

    /// Returns whether the constraint is falsified by the current assignment.
    ///
    /// Missing variables are treated as unassigned and therefore not true.
    pub fn is_conflicting(&self, assignment: &HashMap<u32, bool>) -> bool {
        self.sum_true_terms(assignment) < self.degree
    }

    /// Returns whether exactly one literal participates at the highest level.
    ///
    /// The callback should return `Some(level)` for literals relevant to the
    /// assertion check, typically falsified literals on the trail, and `None`
    /// for satisfied literals that do not participate.
    pub fn is_asserting<F>(&self, mut trail_fn: F) -> bool
    where
        F: FnMut(PbLit) -> Option<u32>,
    {
        let mut highest_level = None;
        let mut highest_count = 0usize;

        for lit in self.coeffs.keys().copied() {
            let Some(level) = trail_fn(lit) else {
                continue;
            };

            match highest_level {
                None => {
                    highest_level = Some(level);
                    highest_count = 1;
                }
                Some(current) if level > current => {
                    highest_level = Some(level);
                    highest_count = 1;
                }
                Some(current) if level == current => {
                    highest_count += 1;
                }
                Some(_) => {}
            }
        }

        highest_level.is_some() && highest_count == 1
    }

    /// Returns `degree - sum(true coefficients)` for the current assignment.
    ///
    /// Missing variables are treated as unassigned and therefore not true.
    pub fn slack(&self, assignment: &HashMap<u32, bool>) -> i128 {
        saturating_i128_to_i64(self.degree - self.sum_true_terms(assignment))
    }

    /// Resolves this constraint with another one on a pivot literal.
    ///
    /// One side must contain `pivot` and the other `!pivot`. The two pivot
    /// coefficients are scaled to a common value, the complementary pair is
    /// removed using `pivot + !pivot = 1`, then the result is saturated and
    /// GCD-divided.
    pub fn resolve(&self, other: &Self, pivot: PbLit) -> Result<Self, CpError> {
        let negated_pivot = negate_lit(pivot);

        let (left_base, right_base) = if self.coeffs.contains_key(&pivot)
            && other.coeffs.contains_key(&negated_pivot)
        {
            (self, other)
        } else if self.coeffs.contains_key(&negated_pivot) && other.coeffs.contains_key(&pivot) {
            (other, self)
        } else {
            return Err(CpError::InvalidResolvePivot { pivot });
        };

        let left_coeff = left_base.coefficient(pivot);
        let right_coeff = right_base.coefficient(negated_pivot);
        let lcm = lcm_i64(left_coeff, right_coeff);
        let left_factor = lcm / left_coeff;
        let right_factor = lcm / right_coeff;

        let mut left = left_base.clone();
        let mut right = right_base.clone();
        left.multiply(left_factor)?;
        right.multiply(right_factor)?;

        let mut coeffs = HashMap::new();

        for (lit, coeff) in &left.coeffs {
            if *lit != pivot {
                add_coeff(&mut coeffs, *lit, *coeff);
            }
        }

        for (lit, coeff) in &right.coeffs {
            if *lit != negated_pivot {
                add_coeff(&mut coeffs, *lit, *coeff);
            }
        }

        let degree = left
            .degree
            .checked_add(right.degree)
            .and_then(|sum| sum.checked_sub(lcm))
            .expect("cutting-planes resolution arithmetic must stay within i128");

        let mut result = Self { coeffs, degree };
        result.simplify_trivial();
        result.saturate();
        result.gcd_divide()?;
        Ok(result)
    }

    /// Returns the number of terms (non-zero coefficients) in the constraint.
    pub fn len(&self) -> usize {
        self.coeffs.len()
    }

    /// Returns whether the constraint has no terms.
    pub fn is_empty(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// Round-to-one resolution: resolves two PB constraints on a pivot literal
    /// using the division rule from cutting planes.
    ///
    /// Given a conflict constraint C and a reason constraint R:
    /// 1. Scale C by the reason's pivot coefficient, scale R by C's pivot coefficient
    ///    (both divided by their GCD to minimize coefficient growth)
    /// 2. Add the scaled constraints (pivot literals cancel: p + ~p = 1)
    /// 3. Saturate the result
    /// 4. If the asserting literal's coefficient > 1, apply the division rule:
    ///    divide all coefficients by that coefficient, rounding up
    ///
    /// The `asserting_lit` is the literal we want to propagate. If `None`,
    /// the division step is skipped and the result is just addition + saturation.
    ///
    /// Returns `None` if the pivot is not present in the expected polarity,
    /// or if arithmetic overflow would occur.
    ///
    /// Reference: "Divide and Conquer: Towards Faster Pseudo-Boolean Solving"
    /// (Elffers & Nordstrom, SAT 2018), Section 3.
    pub fn resolve_round_to_one(
        &self,
        reason: &Self,
        pivot: PbLit,
        asserting_lit: Option<PbLit>,
    ) -> Result<RoundToOneResult, CpError> {
        let negated_pivot = negate_lit(pivot);

        // Determine which side has the positive pivot and which has the negated.
        let (pivot_side, negated_side) =
            if self.coefficient(pivot) > 0 && reason.coefficient(negated_pivot) > 0 {
                (self, reason)
            } else if self.coefficient(negated_pivot) > 0 && reason.coefficient(pivot) > 0 {
                (reason, self)
            } else {
                return Err(CpError::InvalidResolvePivot { pivot });
            };

        let a = pivot_side.coefficient(pivot);
        let b = negated_side.coefficient(negated_pivot);

        // Scale to cancel the pivot: multiply each side by the other's pivot
        // coefficient divided by GCD, so the pivot coefficients become equal.
        let g = gcd_i64(a, b);
        let left_factor = b / g;
        let right_factor = a / g;

        let mut scaled_left = pivot_side.clone();
        let mut scaled_right = negated_side.clone();

        // Use checked multiplication with overflow fallback.
        if left_factor > 1 {
            if scaled_left.multiply_checked(left_factor).is_err() {
                // Overflow: fall back to standard resolve.
                return self
                    .resolve(reason, pivot)
                    .map(|c| RoundToOneResult::new(c, false));
            }
        }
        if right_factor > 1 {
            if scaled_right.multiply_checked(right_factor).is_err() {
                return self
                    .resolve(reason, pivot)
                    .map(|c| RoundToOneResult::new(c, false));
            }
        }

        // Build the resolvent by adding all terms except the pivot pair.
        let mut coeffs = HashMap::new();
        for (&lit, &coeff) in &scaled_left.coeffs {
            if lit != pivot {
                add_coeff(&mut coeffs, lit, coeff);
            }
        }
        for (&lit, &coeff) in &scaled_right.coeffs {
            if lit != negated_pivot {
                add_coeff(&mut coeffs, lit, coeff);
            }
        }

        // Cancel: the pivot pair contributes (lcm * p + lcm * ~p) = lcm,
        // which is subtracted from the sum of degrees.
        let lcm = a / g * b; // = left_factor * b = right_factor * a
        let degree = scaled_left
            .degree
            .checked_add(scaled_right.degree)
            .and_then(|sum| sum.checked_sub(lcm));

        let Some(degree) = degree else {
            // Overflow fallback.
            return self
                .resolve(reason, pivot)
                .map(|c| RoundToOneResult::new(c, false));
        };

        let mut resolved = Self { coeffs, degree };
        resolved.normalize();
        resolved.saturate();

        // Apply the division rule if we have an asserting literal and its
        // coefficient is > 1. Dividing by this coefficient (with ceiling on
        // all other coefficients and the degree) makes the asserting literal
        // have coefficient 1, which maximizes its propagation power.
        let mut used_division = false;
        if let Some(alit) = asserting_lit {
            let a_coeff = resolved.coefficient(alit);
            if a_coeff > 1 {
                // Division: divide all coefficients by a_coeff, rounding up.
                // This is the key "round-to-one" step.
                if resolved.divide(a_coeff).is_ok() {
                    used_division = true;
                }
            }
        }

        if !used_division {
            // Still apply GCD reduction.
            let _ = resolved.gcd_divide();
        }

        Ok(RoundToOneResult::new(resolved, used_division))
    }

    /// Checked multiplication that returns Err on overflow instead of panicking.
    pub(crate) fn multiply_checked(&mut self, factor: i128) -> Result<(), CpError> {
        if factor <= 0 {
            return Err(CpError::NonPositiveMultiplier(factor));
        }

        for coeff in self.coeffs.values_mut() {
            match coeff.checked_mul(factor) {
                Some(v) => *coeff = v,
                None => return Err(CpError::CoefficientOverflow),
            }
        }

        match self.degree.checked_mul(factor) {
            Some(v) => self.degree = v,
            None => return Err(CpError::CoefficientOverflow),
        }
        self.simplify_trivial();
        Ok(())
    }

    pub(crate) fn add_assign(&mut self, other: &Self) {
        for (lit, coeff) in &other.coeffs {
            add_coeff(&mut self.coeffs, *lit, *coeff);
        }

        self.degree = self
            .degree
            .checked_add(other.degree)
            .expect("cutting-planes degree addition must stay within i128");
        self.compact();
        self.simplify_trivial();
    }

    fn compact(&mut self) {
        self.coeffs.retain(|_, coeff| *coeff != 0);
    }

    fn simplify_trivial(&mut self) {
        if self.degree <= 0 {
            self.degree = 0;
            self.coeffs.clear();
        } else {
            self.compact();
        }
    }

    fn sum_true_terms(&self, assignment: &HashMap<u32, bool>) -> i128 {
        self.coeffs
            .iter()
            .filter(|(lit, _)| literal_is_true(**lit, assignment))
            .map(|(_, coeff)| *coeff)
            .sum()
    }
}

impl TryFrom<&PbConstraint> for CpConstraint {
    type Error = CpError;

    fn try_from(constraint: &PbConstraint) -> Result<Self, Self::Error> {
        if constraint.rel != PbRel::Ge {
            return Err(CpError::UnsupportedRelation(constraint.rel));
        }

        let mut coeffs = HashMap::new();

        for (index, term) in constraint.terms.iter().enumerate() {
            if term.lits.len() != 1 {
                return Err(CpError::NonLinearTerm {
                    term_index: index,
                    lit_count: term.lits.len(),
                });
            }

            add_coeff(&mut coeffs, term.lits[0], term.coeff);
        }

        Ok(Self::new(coeffs, constraint.rhs))
    }
}

impl TryFrom<PbConstraint> for CpConstraint {
    type Error = CpError;

    fn try_from(constraint: PbConstraint) -> Result<Self, Self::Error> {
        Self::try_from(&constraint)
    }
}

impl From<&CpConstraint> for PbConstraint {
    fn from(constraint: &CpConstraint) -> Self {
        let mut terms: Vec<PbTerm> = constraint
            .coeffs
            .iter()
            .map(|(lit, coeff)| PbTerm {
                coeff: *coeff,
                lits: vec![*lit],
            })
            .collect();

        terms.sort_by_key(|term| (term.lits[0].var, term.lits[0].negated));

        Self {
            terms,
            rel: PbRel::Ge,
            rhs: constraint.degree,
        }
    }
}

impl From<CpConstraint> for PbConstraint {
    fn from(constraint: CpConstraint) -> Self {
        Self::from(&constraint)
    }
}

pub(crate) fn negate_lit(lit: PbLit) -> PbLit {
    PbLit {
        var: lit.var,
        negated: !lit.negated,
    }
}

pub(crate) fn add_coeff(coeffs: &mut HashMap<PbLit, i128>, lit: PbLit, delta: i128) {
    let next = coeffs
        .get(&lit)
        .copied()
        .unwrap_or(0)
        .checked_add(delta)
        .expect("cutting-planes coefficient addition must stay within i128");
    if next == 0 {
        coeffs.remove(&lit);
    } else {
        coeffs.insert(lit, next);
    }
}

pub(crate) fn literal_is_true(lit: PbLit, assignment: &HashMap<u32, bool>) -> bool {
    let value = assignment.get(&lit.var).copied().unwrap_or(false);
    if lit.negated {
        !value
    } else {
        value
    }
}

pub(crate) fn gcd_i64(lhs: i128, rhs: i128) -> i128 {
    let mut a = lhs
        .checked_abs()
        .expect("cutting-planes GCD input must not be i128::MIN");
    let mut b = rhs
        .checked_abs()
        .expect("cutting-planes GCD input must not be i128::MIN");

    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }

    a
}

pub(crate) fn lcm_i64(lhs: i128, rhs: i128) -> i128 {
    let gcd = gcd_i64(lhs, rhs);
    lhs.checked_div(gcd)
        .and_then(|q| q.checked_mul(rhs))
        .expect("cutting-planes LCM arithmetic must stay within i128")
}

pub(crate) fn div_ceil_i64(value: i128, divisor: i128) -> i128 {
    let quotient = value / divisor;
    let remainder = value % divisor;

    if value > 0 && remainder != 0 {
        quotient + 1
    } else {
        quotient
    }
}

// Inert i64-era passthrough: slack values are already `i128`. Explicit no-op.
pub(crate) fn saturating_i128_to_i64(value: i128) -> i128 {
    value
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn not(var: u32) -> PbLit {
        PbLit { var, negated: true }
    }

    fn cp(entries: &[(PbLit, i128)], degree: i128) -> CpConstraint {
        let coeffs = entries.iter().copied().collect();
        CpConstraint::new(coeffs, degree)
    }

    fn ge_constraint(entries: &[(PbLit, i128)], rhs: i128) -> PbConstraint {
        PbConstraint {
            terms: entries
                .iter()
                .map(|(lit, coeff)| PbTerm {
                    coeff: *coeff,
                    lits: vec![*lit],
                })
                .collect(),
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn sorted_terms(constraint: &PbConstraint) -> Vec<(PbLit, i128)> {
        let mut terms: Vec<(PbLit, i128)> = constraint
            .terms
            .iter()
            .map(|term| (term.lits[0], term.coeff))
            .collect();
        terms.sort_by_key(|(lit, _)| (lit.var, lit.negated));
        terms
    }

    #[test]
    fn test_addition_of_two_constraints() {
        let lhs = cp(&[(lit(1), 2), (not(2), 1)], 2);
        let rhs = cp(&[(lit(1), 3), (lit(3), 4)], 5);

        let sum = lhs.addition(&rhs);

        assert_eq!(sum.degree(), 7);
        assert_eq!(sum.coefficient(lit(1)), 5);
        assert_eq!(sum.coefficient(not(2)), 1);
        assert_eq!(sum.coefficient(lit(3)), 4);
    }

    #[test]
    fn test_multiplication_by_scalar() {
        let mut constraint = cp(&[(lit(1), 2), (lit(2), 1)], 3);

        constraint
            .multiply(4)
            .expect("positive scalar must multiply");

        assert_eq!(constraint.degree(), 12);
        assert_eq!(constraint.coefficient(lit(1)), 8);
        assert_eq!(constraint.coefficient(lit(2)), 4);
    }

    #[test]
    fn test_division_with_ceiling() {
        let mut constraint = cp(&[(lit(1), 5), (lit(2), 6)], 7);

        constraint.divide(4).expect("positive divisor must divide");

        assert_eq!(constraint.degree(), 2);
        assert_eq!(constraint.coefficient(lit(1)), 2);
        assert_eq!(constraint.coefficient(lit(2)), 2);
    }

    #[test]
    fn test_saturation_caps_coefficients_at_degree() {
        let mut constraint = cp(&[(lit(1), 5), (lit(2), 2)], 3);

        constraint.saturate();

        assert_eq!(constraint.degree(), 3);
        assert_eq!(constraint.coefficient(lit(1)), 3);
        assert_eq!(constraint.coefficient(lit(2)), 2);
    }

    #[test]
    fn test_weakening_removes_literal_and_reduces_degree() {
        let mut constraint = cp(&[(lit(1), 4), (lit(2), 2)], 5);

        constraint.weaken(lit(1));

        assert_eq!(constraint.degree(), 1);
        assert_eq!(constraint.coefficient(lit(1)), 0);
        assert_eq!(constraint.coefficient(lit(2)), 2);
    }

    #[test]
    fn test_gcd_divide_uses_ceiling_on_degree() {
        let mut constraint = cp(&[(lit(1), 6), (not(2), 12)], 9);

        constraint
            .gcd_divide()
            .expect("gcd division on positive coefficients must succeed");

        assert_eq!(constraint.degree(), 2);
        assert_eq!(constraint.coefficient(lit(1)), 1);
        assert_eq!(constraint.coefficient(not(2)), 2);
    }

    #[test]
    fn test_resolve_cancels_pivot_and_simplifies() {
        let conflict = cp(&[(lit(1), 3), (lit(2), 6)], 6);
        let reason = cp(&[(not(1), 2), (lit(3), 4)], 4);

        let resolved = conflict
            .resolve(&reason, lit(1))
            .expect("constraints contain complementary pivot literals");

        assert_eq!(resolved.degree(), 2);
        assert_eq!(resolved.coefficient(lit(1)), 0);
        assert_eq!(resolved.coefficient(not(1)), 0);
        assert_eq!(resolved.coefficient(lit(2)), 1);
        assert_eq!(resolved.coefficient(lit(3)), 1);
    }

    #[test]
    fn test_conflicting_and_asserting_detection() {
        let constraint = cp(&[(lit(1), 1), (lit(2), 1)], 2);
        let assignment = HashMap::from([(1, true), (2, false)]);

        assert!(constraint.is_conflicting(&assignment));
        assert_eq!(constraint.slack(&assignment), 1);

        let asserting = constraint.is_asserting(|lit| match lit.var {
            1 => Some(1),
            2 => Some(3),
            _ => None,
        });
        assert!(asserting);

        let not_asserting = constraint.is_asserting(|_| Some(3));
        assert!(!not_asserting);
    }

    #[test]
    fn test_normalization_flips_negative_coefficients() {
        let mut constraint = CpConstraint {
            coeffs: HashMap::from([(lit(1), -3), (not(2), 2)]),
            degree: 4,
        };

        constraint.normalize();

        assert_eq!(constraint.degree(), 7);
        assert_eq!(constraint.coefficient(lit(1)), 0);
        assert_eq!(constraint.coefficient(not(1)), 3);
        assert_eq!(constraint.coefficient(not(2)), 2);
    }

    #[test]
    fn test_round_trip_pb_constraint_to_cp_constraint() {
        let original = ge_constraint(&[(lit(1), 2), (not(2), 3)], 4);

        let cp = CpConstraint::try_from(&original).expect("linear >= constraints must convert");
        let round_tripped = PbConstraint::from(&cp);

        assert_eq!(round_tripped.rel, PbRel::Ge);
        assert_eq!(round_tripped.rhs, 4);
        assert_eq!(sorted_terms(&round_tripped), sorted_terms(&original));
    }

    // --- Strengthening pipeline tests ---

    #[test]
    fn test_saturate_and_gcd_combined() {
        // 10*x1 + 6*x2 >= 6
        // After saturation: 6*x1 + 6*x2 >= 6
        // GCD = 6, so divide: 1*x1 + 1*x2 >= 1
        let mut constraint = cp(&[(lit(1), 10), (lit(2), 6)], 6);

        constraint
            .saturate_and_gcd()
            .expect("saturate_and_gcd must succeed");

        assert_eq!(constraint.degree(), 1);
        assert_eq!(constraint.coefficient(lit(1)), 1);
        assert_eq!(constraint.coefficient(lit(2)), 1);
    }

    #[test]
    fn test_saturate_and_gcd_no_change_needed() {
        // 2*x1 + 3*x2 >= 4
        // After saturation: no change (both < 4)
        // GCD = 1, no division.
        let mut constraint = cp(&[(lit(1), 2), (lit(2), 3)], 4);

        constraint
            .saturate_and_gcd()
            .expect("saturate_and_gcd must succeed");

        assert_eq!(constraint.degree(), 4);
        assert_eq!(constraint.coefficient(lit(1)), 2);
        assert_eq!(constraint.coefficient(lit(2)), 3);
    }

    #[test]
    fn test_saturate_and_gcd_all_saturated_then_gcd() {
        // 12*x1 + 8*x2 + 20*x3 >= 4
        // After saturation: 4*x1 + 4*x2 + 4*x3 >= 4
        // GCD = 4, divide: 1*x1 + 1*x2 + 1*x3 >= 1
        let mut constraint = cp(&[(lit(1), 12), (lit(2), 8), (lit(3), 20)], 4);

        constraint
            .saturate_and_gcd()
            .expect("saturate_and_gcd must succeed");

        assert_eq!(constraint.degree(), 1);
        assert_eq!(constraint.coefficient(lit(1)), 1);
        assert_eq!(constraint.coefficient(lit(2)), 1);
        assert_eq!(constraint.coefficient(lit(3)), 1);
    }

    #[test]
    fn test_weaken_conservative_removes_small_coefficient() {
        // 3*x1 + 1*x2 + 3*x3 >= 4
        // Asserting literal: x1 (at level 5, highest level).
        // x2 is falsified at level 2, x3 is falsified at level 3.
        // x2 has coefficient 1 < degree 4.
        // After weakening x2: 3*x1 + 3*x3 >= 3
        // Check: remaining falsified sum without asserting (just x3=3) >= 3? Yes.
        // So asserting literal is NOT forced if we weaken x2. Skip x2.
        //
        // Actually let's use a case where weakening works:
        // 5*x1 + 1*x2 + 1*x3 >= 3
        // x1 asserting at level 5. x2 falsified at level 2, x3 falsified at level 3.
        // x2 has coeff 1 < degree 3. After weakening x2: 5*x1 + 1*x3 >= 2.
        // Remaining falsified without asserting = x3 coeff 1 < 2. So asserting is forced.
        let mut constraint = cp(&[(lit(1), 5), (lit(2), 1), (lit(3), 1)], 3);

        constraint.weaken_conservative(Some(lit(1)), |l| match l.var {
            1 => Some(5), // asserting, highest level
            2 => Some(2), // falsified at level 2
            3 => Some(3), // falsified at level 3
            _ => None,
        });

        // x2 should be weakened away (coeff 1 < degree, and asserting is preserved).
        assert_eq!(constraint.coefficient(lit(2)), 0, "x2 should be weakened");
        assert!(
            constraint.coefficient(lit(1)) > 0,
            "asserting literal must remain"
        );
        assert!(constraint.degree() > 0, "degree must remain positive");
    }

    #[test]
    fn test_weaken_conservative_preserves_asserting_literal() {
        // 3*x1 + 2*x2 >= 4
        // x1 is asserting (level 5), x2 is falsified (level 3).
        // We should NOT weaken x1 (the asserting literal).
        let mut constraint = cp(&[(lit(1), 3), (lit(2), 2)], 4);

        constraint.weaken_conservative(Some(lit(1)), |l| match l.var {
            1 => Some(5),
            2 => Some(3),
            _ => None,
        });

        // x1 must not be removed (it's the asserting literal).
        assert!(
            constraint.coefficient(lit(1)) > 0,
            "asserting literal must be preserved"
        );
    }

    #[test]
    fn test_weaken_conservative_no_asserting_does_nothing() {
        // Without an asserting literal, no weakening should occur.
        let mut constraint = cp(&[(lit(1), 3), (lit(2), 1)], 3);
        let original_degree = constraint.degree();

        constraint.weaken_conservative(None, |_| Some(1));

        assert_eq!(constraint.degree(), original_degree);
        assert_eq!(constraint.coefficient(lit(1)), 3);
        assert_eq!(constraint.coefficient(lit(2)), 1);
    }

    #[test]
    fn test_weaken_conservative_does_not_make_trivial() {
        // 2*x1 + 2*x2 >= 2
        // x1 asserting at level 5. x2 falsified at level 3.
        // x2 has coeff 2 >= degree 2, so it should not be weakened
        // (removing it would reduce degree to 0).
        let mut constraint = cp(&[(lit(1), 2), (lit(2), 2)], 2);

        constraint.weaken_conservative(Some(lit(1)), |l| match l.var {
            1 => Some(5),
            2 => Some(3),
            _ => None,
        });

        // x2 should remain because its coefficient >= degree.
        assert_eq!(constraint.coefficient(lit(2)), 2);
    }

    #[test]
    fn test_strengthen_full_pipeline() {
        // 12*x1 + 4*x2 + 1*x3 >= 6
        // Step 1 (saturate): 6*x1 + 4*x2 + 1*x3 >= 6
        // Step 2 (GCD=1): no change
        // Step 3 (weaken): x3 has coeff 1 < 6. If x1 is asserting (level 5),
        //   x2 falsified at level 3, x3 falsified at level 2:
        //   After weakening x3: 6*x1 + 4*x2 >= 5
        //   Remaining falsified without asserting = x2 coeff 4 < 5. Asserting forced.
        // Step 4 (re-saturate+GCD): 5*x1 + 4*x2 >= 5, GCD=1, no change.
        let mut constraint = cp(&[(lit(1), 12), (lit(2), 4), (lit(3), 1)], 6);

        constraint
            .strengthen(Some(lit(1)), |l| match l.var {
                1 => Some(5),
                2 => Some(3),
                3 => Some(2),
                _ => None,
            })
            .expect("strengthen must succeed");

        // x3 should be removed by weakening.
        assert_eq!(
            constraint.coefficient(lit(3)),
            0,
            "x3 should be weakened away"
        );
        // Asserting literal must remain.
        assert!(constraint.coefficient(lit(1)) > 0);
        // Degree should be reduced.
        assert!(
            constraint.degree() < 6,
            "degree should be reduced after weakening"
        );
        assert!(constraint.degree() > 0, "degree must remain positive");
    }

    #[test]
    fn test_strengthen_gcd_after_saturation() {
        // 10*x1 + 10*x2 + 10*x3 >= 5
        // Saturate: 5*x1 + 5*x2 + 5*x3 >= 5
        // GCD = 5: 1*x1 + 1*x2 + 1*x3 >= 1
        // Weakening: all coefficients equal to degree, none can be weakened.
        let mut constraint = cp(&[(lit(1), 10), (lit(2), 10), (lit(3), 10)], 5);

        constraint
            .strengthen(Some(lit(1)), |l| match l.var {
                1 => Some(5),
                2 => Some(3),
                3 => Some(2),
                _ => None,
            })
            .expect("strengthen must succeed");

        assert_eq!(constraint.degree(), 1);
        assert_eq!(constraint.coefficient(lit(1)), 1);
        assert_eq!(constraint.coefficient(lit(2)), 1);
        assert_eq!(constraint.coefficient(lit(3)), 1);
    }

    // --- Round-to-one resolution tests ---

    #[test]
    fn test_resolve_round_to_one_basic_division() {
        // Conflict: 3*x1 + 2*x2 + 4*x3 >= 5
        // Reason:   2*~x1 + 1*x4 >= 1
        // Pivot: x1 (conflict has x1, reason has ~x1)
        //
        // Standard resolve would scale conflict by 2, reason by 3:
        //   6*x1 + 4*x2 + 8*x3 >= 10
        //   6*~x1 + 3*x4 >= 3
        // Add and cancel: 4*x2 + 8*x3 + 3*x4 >= 10+3-6 = 7
        // Saturate: 4*x2 + 7*x3 + 3*x4 >= 7
        //
        // With round-to-one, if x2 is the asserting literal (coeff 4 > 1):
        // Divide by 4: ceil(4/4)*x2 + ceil(7/4)*x3 + ceil(3/4)*x4 >= ceil(7/4)
        //            = 1*x2 + 2*x3 + 1*x4 >= 2
        let conflict = cp(&[(lit(1), 3), (lit(2), 2), (lit(3), 4)], 5);
        let reason = cp(&[(not(1), 2), (lit(4), 1)], 1);

        let result = conflict
            .resolve_round_to_one(&reason, lit(1), Some(lit(2)))
            .expect("round-to-one resolution must succeed");

        assert!(result.used_division, "division rule should be applied");
        assert_eq!(
            result.constraint.coefficient(lit(2)),
            1,
            "asserting literal coefficient must be 1 after round-to-one"
        );
        assert!(
            result.constraint.degree() > 0,
            "degree must remain positive"
        );
        // The constraint should be smaller than the non-divided version.
        assert!(
            result.constraint.degree() <= 7,
            "degree should be reduced by division"
        );
    }

    #[test]
    fn test_resolve_round_to_one_no_division_needed() {
        // When the asserting literal already has coefficient 1 after standard
        // addition + saturation, no division is needed.
        // Conflict: 1*x1 + 1*x2 >= 1 (clause)
        // Reason:   1*~x1 + 1*x3 >= 1 (clause)
        // Pivot: x1
        // Result: 1*x2 + 1*x3 >= 1 (still a clause, no division needed)
        let conflict = cp(&[(lit(1), 1), (lit(2), 1)], 1);
        let reason = cp(&[(not(1), 1), (lit(3), 1)], 1);

        let result = conflict
            .resolve_round_to_one(&reason, lit(1), Some(lit(2)))
            .expect("round-to-one resolution must succeed");

        assert!(
            !result.used_division,
            "division should not be used when asserting coeff is already 1"
        );
        assert_eq!(result.constraint.coefficient(lit(2)), 1);
        assert_eq!(result.constraint.coefficient(lit(3)), 1);
        assert_eq!(result.constraint.degree(), 1);
    }

    #[test]
    fn test_resolve_round_to_one_without_asserting_lit() {
        // When no asserting literal is specified, fall back to standard resolve.
        let conflict = cp(&[(lit(1), 3), (lit(2), 2)], 4);
        let reason = cp(&[(not(1), 2), (lit(3), 1)], 2);

        let result = conflict
            .resolve_round_to_one(&reason, lit(1), None)
            .expect("round-to-one resolution must succeed");

        assert!(
            !result.used_division,
            "no division without asserting literal"
        );
        // Should still produce a valid constraint.
        assert!(result.constraint.degree() > 0);
    }

    #[test]
    fn test_resolve_round_to_one_cancellation() {
        // Test that cancellation (same variable, opposite signs) is handled.
        // Conflict: 2*x1 + 3*x2 + 2*x3 >= 4
        // Reason:   1*~x1 + 2*~x2 + 1*x4 >= 2
        // Pivot: x1
        // After scaling and addition, x2 and ~x2 might both appear.
        // The normalize step in CpConstraint::new handles this.
        let conflict = cp(&[(lit(1), 2), (lit(2), 3), (lit(3), 2)], 4);
        let reason = cp(&[(not(1), 1), (not(2), 2), (lit(4), 1)], 2);

        let result = conflict
            .resolve_round_to_one(&reason, lit(1), Some(lit(3)))
            .expect("round-to-one resolution must succeed");

        // After resolving on x1, both x2 and ~x2 may appear. After normalize,
        // net coefficient determines the outcome.
        assert!(result.constraint.degree() > 0);
    }

    #[test]
    fn test_resolve_round_to_one_invalid_pivot() {
        // Neither constraint contains the expected pivot polarity.
        let conflict = cp(&[(lit(2), 1)], 1);
        let reason = cp(&[(lit(3), 1)], 1);

        let err = conflict
            .resolve_round_to_one(&reason, lit(1), None)
            .unwrap_err();
        assert!(matches!(err, CpError::InvalidResolvePivot { .. }));
    }

    #[test]
    fn test_resolve_round_to_one_large_coefficients() {
        // Test with large coefficients to exercise overflow-safe paths.
        let conflict = cp(&[(lit(1), 1_000_000), (lit(2), 500_000)], 800_000);
        let reason = cp(&[(not(1), 2_000_000), (lit(3), 300_000)], 1_500_000);

        let result = conflict
            .resolve_round_to_one(&reason, lit(1), Some(lit(2)))
            .expect("round-to-one resolution must succeed with large coefficients");

        assert!(result.constraint.degree() > 0);
        assert!(
            result.constraint.coefficient(lit(2)) >= 1,
            "asserting literal must have positive coefficient"
        );
    }

    #[test]
    fn test_resolve_round_to_one_pigeonhole_like() {
        // Simulate a pigeonhole-like scenario where round-to-one produces
        // a shorter proof than standard resolution.
        //
        // At-most-one: 1*~p1 + 1*~p2 + 1*~p3 >= 2
        // Pigeon 1 in some hole: 1*p1 >= 1
        //
        // Resolve on p1:
        //   Conflict (scaled): 1*~p1 + 1*~p2 + 1*~p3 >= 2
        //   Reason (scaled):   1*p1 >= 1
        //   Result: 1*~p2 + 1*~p3 >= 2+1-1 = 2
        //
        // This is cardinality so no division needed, but it demonstrates the
        // basic resolve path correctly handles the standard pigeonhole case.
        let at_most_one = cp(&[(not(1), 1), (not(2), 1), (not(3), 1)], 2);
        let pigeon_assigned = cp(&[(lit(1), 1)], 1);

        let result = at_most_one
            .resolve_round_to_one(&pigeon_assigned, lit(1), Some(not(2)))
            .expect("pigeonhole resolve must succeed");

        // ~p2 + ~p3 >= 2 means both p2 and p3 must be false.
        assert_eq!(result.constraint.coefficient(not(2)), 1);
        assert_eq!(result.constraint.coefficient(not(3)), 1);
        assert_eq!(result.constraint.degree(), 2);
        // Both p2 and p3 are forced false — this is a unit constraint
        // equivalent to the clause (~p2 AND ~p3).
    }

    #[test]
    fn test_resolve_round_to_one_weighted_pigeonhole() {
        // Weighted pigeonhole where round-to-one shines.
        // Conflict: 3*x1 + 3*x2 + 3*x3 >= 7
        //   (need at least 3 of these to sum to 7: need all 3)
        // Reason: 2*~x1 + 1*x4 >= 2
        //   (x4 must be true or ~x1 must contribute 2)
        //
        // Resolve on x1:
        // Scale conflict by 2, reason by 3 (LCM = 6):
        //   6*x1 + 6*x2 + 6*x3 >= 14
        //   6*~x1 + 3*x4 >= 6
        // Add: 6*x2 + 6*x3 + 3*x4 >= 14+6-6 = 14
        // Saturate: cap coefficients at 14 → no change
        //
        // If x2 is asserting (coeff 6 > 1):
        // Divide by 6: ceil(6/6)*x2 + ceil(6/6)*x3 + ceil(3/6)*x4 >= ceil(14/6)
        //            = 1*x2 + 1*x3 + 1*x4 >= 3
        let conflict = cp(&[(lit(1), 3), (lit(2), 3), (lit(3), 3)], 7);
        let reason = cp(&[(not(1), 2), (lit(4), 1)], 2);

        let result = conflict
            .resolve_round_to_one(&reason, lit(1), Some(lit(2)))
            .expect("weighted pigeonhole resolve must succeed");

        assert!(result.used_division, "division should be applied");
        assert_eq!(
            result.constraint.coefficient(lit(2)),
            1,
            "asserting literal must have coefficient 1"
        );
        // After division by 6 and saturate:
        // x2=1, x3=1, x4=1, degree=3
        assert_eq!(result.constraint.coefficient(lit(3)), 1);
        assert_eq!(result.constraint.coefficient(lit(4)), 1);
        assert_eq!(result.constraint.degree(), 3);
    }

    #[test]
    fn test_multiply_checked_overflow() {
        let mut constraint = cp(&[(lit(1), i128::MAX / 2 + 1)], i128::MAX / 2 + 1);
        let result = constraint.multiply_checked(3);
        assert!(
            result.is_err(),
            "multiply_checked must return error on overflow"
        );
        assert!(matches!(result.unwrap_err(), CpError::CoefficientOverflow));
    }

    #[test]
    fn test_multiply_checked_non_positive() {
        let mut constraint = cp(&[(lit(1), 2)], 2);
        let result = constraint.multiply_checked(0);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            CpError::NonPositiveMultiplier(0)
        ));
    }

    #[test]
    fn test_resolve_round_to_one_produces_shorter_constraint() {
        // Demonstrate that round-to-one produces a constraint with fewer
        // terms or smaller coefficients than standard resolve.
        //
        // Conflict: 5*x1 + 4*x2 + 3*x3 + 2*x4 >= 8
        // Reason: 3*~x1 + 2*x5 >= 3
        // Pivot: x1
        //
        // Standard resolve (LCM = 15):
        //   15*x1 + 12*x2 + 9*x3 + 6*x4 >= 24
        //   15*~x1 + 10*x5 >= 15
        //   Add: 12*x2 + 9*x3 + 6*x4 + 10*x5 >= 24+15-15 = 24
        //   Saturate(24): no change
        //
        // With round-to-one on x2 (coeff 12):
        //   Divide by 12: 1*x2 + 1*x3 + 1*x4 + 1*x5 >= 2
        //
        // This is dramatically shorter!
        let conflict = cp(&[(lit(1), 5), (lit(2), 4), (lit(3), 3), (lit(4), 2)], 8);
        let reason = cp(&[(not(1), 3), (lit(5), 2)], 3);

        let r2o_result = conflict
            .resolve_round_to_one(&reason, lit(1), Some(lit(2)))
            .expect("round-to-one must succeed");

        let std_result = conflict
            .resolve(&reason, lit(1))
            .expect("standard resolve must succeed");

        // Round-to-one should produce smaller coefficients.
        assert!(
            r2o_result.constraint.degree() <= std_result.degree(),
            "round-to-one degree {} should be <= standard degree {}",
            r2o_result.constraint.degree(),
            std_result.degree()
        );
        assert!(
            r2o_result.used_division,
            "division must be applied in this case"
        );
        assert_eq!(
            r2o_result.constraint.coefficient(lit(2)),
            1,
            "asserting literal must have coefficient 1"
        );
    }
}
