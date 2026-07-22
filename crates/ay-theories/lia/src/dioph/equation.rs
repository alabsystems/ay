// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::extended_gcd_bigint;
use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

/// A linear integer equation: Σ(coeff * var) = constant
///
/// Tracks provenance via `sources`: indices of original input equations that
/// were combined (by substitution or fresh-variable steps) to produce this
/// equation.  When an infeasibility is derived, only the source equations
/// listed here are needed in the conflict explanation.
#[derive(Debug, Clone)]
pub(crate) struct IntEquation {
    /// Variable coefficients: variable index -> coefficient
    ///
    /// INVARIANT (soundness-critical): any code path that mutates `coeffs`
    /// or `constant` MUST set `normalized = false` (as `substitute()` /
    /// `apply_fresh_var()` do; `normalize()` sets it back to `true`). The
    /// elimination apply pass skips re-normalization + infeasibility recheck
    /// of `normalized` rows it did not touch; leaving `normalized == true`
    /// after a value change could hide a conflict.
    pub coeffs: HashMap<usize, BigInt>,
    /// Right-hand side constant. See the `coeffs` invariant: mutating this
    /// must also clear `normalized`.
    pub constant: BigInt,
    /// Indices of the original input equations that contributed to this equation.
    /// Empty means "not tracked" (backwards-compatible with old callers).
    pub sources: Vec<usize>,
    /// True when `normalize()` has run since the last mutation. Used by the
    /// elimination loop to skip value-no-op re-normalization passes over
    /// untouched equations (#nip residual: the per-pivot all-equations
    /// normalize was a dominant O(rows^2) bignum-gcd cost). `normalize()` is
    /// idempotent, so skipping it on an equation with `normalized == true`
    /// is value-exact.
    pub normalized: bool,
}

impl IntEquation {
    /// Create a new equation with given coefficients and constant
    pub(crate) fn new(coeffs: HashMap<usize, BigInt>, constant: BigInt) -> Self {
        Self {
            coeffs,
            constant,
            sources: Vec::new(),
            normalized: false,
        }
    }

    /// Create a new equation with provenance tracking.
    pub(crate) fn with_source(
        coeffs: HashMap<usize, BigInt>,
        constant: BigInt,
        source_idx: usize,
    ) -> Self {
        Self {
            coeffs,
            constant,
            sources: vec![source_idx],
            normalized: false,
        }
    }

    /// Check if this equation is trivially satisfied (0 = 0)
    pub(crate) fn is_trivial(&self) -> bool {
        self.coeffs.is_empty() && self.constant.is_zero()
    }

    /// Check if this equation is infeasible (0 = c where c ≠ 0)
    pub(crate) fn is_infeasible(&self) -> bool {
        self.coeffs.is_empty() && !self.constant.is_zero()
    }

    /// Apply GCD test: if GCD of coefficients doesn't divide constant, infeasible
    pub(crate) fn gcd_infeasible(&self) -> bool {
        if self.coeffs.is_empty() {
            return !self.constant.is_zero();
        }

        let mut gcd = BigInt::zero();
        for coeff in self.coeffs.values() {
            if gcd.is_zero() {
                gcd = coeff.abs();
            } else {
                gcd = gcd.gcd(&coeff.abs());
            }
            if gcd.is_one() {
                return false; // GCD=1 divides everything
            }
        }

        if gcd.is_zero() {
            return !self.constant.is_zero();
        }

        !(&self.constant % &gcd).is_zero()
    }

    /// Find a variable with coefficient ±1 (unit coefficient)
    /// Returns the variable index and coefficient (1 or -1)
    #[cfg(test)]
    pub(crate) fn find_unit_var(&self) -> Option<(usize, BigInt)> {
        self.coeffs
            .iter()
            .filter(|(_, coeff)| coeff.is_one() || *coeff == &-BigInt::one())
            .min_by_key(|(&var, _)| var)
            .map(|(&var, coeff)| (var, coeff.clone()))
    }

    /// Find the variable with minimum absolute coefficient
    /// Returns (variable index, coefficient) or None if empty
    pub(crate) fn find_min_abs_coeff_var(&self) -> Option<(usize, BigInt)> {
        // |a|.cmp(|b|) == a.magnitude().cmp(b.magnitude()) without the
        // BigInt clone that `.abs()` performs (#nip residual hot path).
        self.coeffs
            .iter()
            .min_by(|(&var_a, coeff_a), (&var_b, coeff_b)| {
                coeff_a
                    .magnitude()
                    .cmp(coeff_b.magnitude())
                    .then_with(|| var_a.cmp(&var_b))
            })
            .map(|(&var, coeff)| (var, coeff.clone()))
    }

    /// Substitute variable `var` with expression `sub_expr - sub_const`
    /// where sub_expr is coefficients and sub_const is the constant
    ///
    /// If this equation has term `a * var`, replace it with:
    /// `a * (sub_expr - sub_const) / coeff_in_sub`
    pub(crate) fn substitute(
        &mut self,
        var: usize,
        sub_coeffs: &HashMap<usize, BigInt>,
        sub_const: &BigInt,
    ) {
        let Some(a) = self.coeffs.remove(&var) else {
            return; // Variable not in this equation
        };
        self.normalized = false;

        // For each term in the substitution, add scaled coefficient
        for (&sub_var, sub_coeff) in sub_coeffs {
            let scaled = &a * sub_coeff;
            *self.coeffs.entry(sub_var).or_insert_with(BigInt::zero) += &scaled;
        }

        // Adjust constant: if var = (constant - sub_expr) then
        // a*var = a*constant - a*sub_expr
        // So we add a*sub_const to our constant
        self.constant -= &a * sub_const;

        // Clean up zero coefficients
        self.coeffs.retain(|_, v| !v.is_zero());
    }

    /// Merge source provenance from another equation's sources into this one.
    /// Used when this equation is modified using information from `other_sources`
    /// (e.g., during variable elimination via substitution).
    ///
    /// Both `self.sources` and `other_sources` are maintained sorted and
    /// deduplicated (constructors produce <= 1 element; this merge preserves
    /// the invariant), so a linear merge-union produces the identical result
    /// to the previous contains+push+sort — without the O(n^2 log n) re-sort
    /// cascade on long substitution chains (#nip residual hot path).
    pub(crate) fn merge_sources(&mut self, other_sources: &[usize]) {
        debug_assert!(self.sources.windows(2).all(|w| w[0] < w[1]));
        debug_assert!(other_sources.windows(2).all(|w| w[0] < w[1]));
        if other_sources.is_empty() {
            return;
        }
        // Fast path: other_sources ⊆ self.sources (common on chain shapes).
        if other_sources.len() <= self.sources.len() {
            let mut i = 0;
            let mut subset = true;
            for &src in other_sources {
                while i < self.sources.len() && self.sources[i] < src {
                    i += 1;
                }
                if i >= self.sources.len() || self.sources[i] != src {
                    subset = false;
                    break;
                }
            }
            if subset {
                return;
            }
        }
        let mut merged = Vec::with_capacity(self.sources.len() + other_sources.len());
        let (mut i, mut j) = (0usize, 0usize);
        while i < self.sources.len() && j < other_sources.len() {
            match self.sources[i].cmp(&other_sources[j]) {
                std::cmp::Ordering::Less => {
                    merged.push(self.sources[i]);
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    merged.push(other_sources[j]);
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    merged.push(self.sources[i]);
                    i += 1;
                    j += 1;
                }
            }
        }
        merged.extend_from_slice(&self.sources[i..]);
        merged.extend_from_slice(&other_sources[j..]);
        self.sources = merged;
    }

    /// Normalize equation by dividing by GCD of all coefficients and constant
    pub(crate) fn normalize(&mut self) {
        self.normalized = true;
        if self.coeffs.is_empty() {
            return;
        }

        let mut gcd = self.constant.abs();
        for coeff in self.coeffs.values() {
            if gcd.is_zero() {
                gcd = coeff.abs();
            } else {
                gcd = gcd.gcd(&coeff.abs());
            }
        }

        if gcd > BigInt::one() {
            for coeff in self.coeffs.values_mut() {
                *coeff = &*coeff / &gcd;
            }
            self.constant = &self.constant / &gcd;
        }
    }

    /// Apply fresh variable transformation to reduce coefficient magnitude.
    ///
    /// Given equation: a*x + b*y + ... = c where x has minimum |a| > 1,
    /// introduce fresh variable t = x + floor(b/a)*y + ... + floor(c/a)
    /// so that: a*t + (b mod a)*y + ... + (c mod a) = 0
    ///
    /// Key insight: After transformation, coefficient magnitudes decrease like
    /// the Euclidean algorithm, eventually reaching 1.
    ///
    /// Returns the fresh variable definition and updates self with remainder coefficients.
    pub(crate) fn apply_fresh_var(&mut self, pivot_var: usize, fresh_var: usize) -> FreshVarDef {
        let pivot_coeff = self.coeffs.get(&pivot_var).cloned().unwrap_or_default();
        if pivot_coeff.is_zero() {
            return FreshVarDef {
                quotients: HashMap::default(),
                const_quotient: BigInt::zero(),
            };
        }
        self.normalized = false;

        // Build the fresh variable definition: t = x + sum(floor(b_i/a)*x_i) + floor(c/a)
        let mut quotients: HashMap<usize, BigInt> = HashMap::default();

        // For each other variable, compute quotient and remainder
        // a_i = q_i * a + r_i where 0 <= r_i < |a|
        let mut new_coeffs: HashMap<usize, BigInt> = HashMap::default();
        for (&var, coeff) in &self.coeffs {
            if var == pivot_var {
                // The fresh variable gets the SAME coefficient as pivot_var
                // Because: a*x = a*(t - quotients) = a*t - ...
                new_coeffs.insert(fresh_var, pivot_coeff.clone());
            } else {
                // q = floor(coeff / pivot_coeff), r = coeff mod pivot_coeff
                let (q, r) = div_rem_euclidean(coeff, &pivot_coeff);
                if !q.is_zero() {
                    quotients.insert(var, q);
                }
                if !r.is_zero() {
                    new_coeffs.insert(var, r);
                }
            }
        }

        // Handle constant: c = q * a + r where 0 <= r < |a|
        let (const_q, const_r) = div_rem_euclidean(&self.constant, &pivot_coeff);
        let const_quotient = const_q;

        // Update equation: a*t + r_1*x_1 + ... = r_c
        // Wait - the equation should be: a*t + Σ(r_i*x_i) = c - a*const_quotient
        // But c - a*const_quotient = const_r by construction
        self.coeffs = new_coeffs;
        self.constant = const_r;

        // Remove zero coefficients
        self.coeffs.retain(|_, v| !v.is_zero());

        FreshVarDef {
            quotients,
            const_quotient,
        }
    }
}

/// Euclidean division: a = q*b + r where 0 <= r < |b|
fn div_rem_euclidean(a: &BigInt, b: &BigInt) -> (BigInt, BigInt) {
    if b.is_zero() {
        return (BigInt::zero(), a.clone());
    }
    let (mut q, mut r) = a.div_rem(b);
    // Rust's div_rem gives remainder with same sign as dividend
    // We want remainder in [0, |b|)
    if r.is_negative() {
        if b.is_positive() {
            r += b;
            q -= BigInt::one();
        } else {
            r -= b;
            q += BigInt::one();
        }
    }
    (q, r)
}

/// Definition of a fresh variable for tracking substitutions.
///
/// Tracks how a pivot variable is expressed in terms of other variables:
/// `fresh_var = pivot_var + sum(quotient[i] * x_i) + const_quotient`
#[derive(Debug, Clone)]
pub(crate) struct FreshVarDef {
    /// Quotients: coefficients for each variable in the substitution
    pub quotients: HashMap<usize, BigInt>,
    /// Constant part of the quotient
    pub const_quotient: BigInt,
}

impl IntEquation {
    /// Try to solve a 2-variable equation using extended GCD.
    ///
    /// For equation `a*x + b*y = c`:
    /// 1. Compute gcd(a, b) with Bezout coefficients: g = a*s + b*t
    /// 2. If c % g != 0, infeasible
    /// 3. Particular solution: x0 = (c/g)*s, y0 = (c/g)*t
    /// 4. General solution: x = x0 + (b/g)*k, y = y0 - (a/g)*k for integer k
    ///
    /// Returns Some((var_x, var_y, x0, y0, b/g, a/g)) if this is a 2-variable equation,
    /// where the general solution is:
    ///   x = x0 + step_x * k
    ///   y = y0 - step_y * k
    /// Returns None if not a 2-variable equation or if infeasible.
    pub(crate) fn solve_two_variable(&self) -> Option<TwoVarSolution> {
        if self.coeffs.len() != 2 {
            return None;
        }

        // Sort variables by index for deterministic iteration order
        let mut vars: Vec<_> = self.coeffs.iter().map(|(&v, c)| (v, c.clone())).collect();
        vars.sort_by_key(|(v, _)| *v);

        let (var_x, coeff_a) = vars.remove(0);
        let (var_y, coeff_b) = vars.remove(0);

        let (g, s, t) = extended_gcd_bigint(&coeff_a, &coeff_b);

        // Check if c is divisible by g
        if !(&self.constant % &g).is_zero() {
            return None; // Infeasible - will be caught by gcd_infeasible
        }

        let c_div_g = &self.constant / &g;

        // Particular solution
        let x0 = &c_div_g * &s;
        let y0 = &c_div_g * &t;

        // Step sizes for the parameter k
        let step_x = coeff_b / &g; // b/g
        let step_y = coeff_a / &g; // a/g (note: y = y0 - (a/g)*k)

        Some(TwoVarSolution {
            var_x,
            var_y,
            x0,
            y0,
            step_x,
            step_y,
        })
    }
}

/// Solution representation for a 2-variable Diophantine equation.
///
/// General solution: x = x0 + step_x * k, y = y0 - step_y * k
#[derive(Debug, Clone)]
pub(crate) struct TwoVarSolution {
    /// First variable index
    pub var_x: usize,
    /// Second variable index
    pub var_y: usize,
    /// Particular solution for x
    pub x0: BigInt,
    /// Particular solution for y
    pub y0: BigInt,
    /// Step size for x (b/gcd)
    pub step_x: BigInt,
    /// Step size for y (a/gcd)
    pub step_y: BigInt,
}

impl TwoVarSolution {
    /// Given bounds on x, compute the range of valid k values.
    /// Returns (k_min, k_max) where k_min <= k <= k_max.
    pub(crate) fn k_bounds_from_x(
        &self,
        x_lo: Option<&BigInt>,
        x_hi: Option<&BigInt>,
    ) -> (Option<BigInt>, Option<BigInt>) {
        if self.step_x.is_zero() {
            // x is fixed at x0
            return (None, None);
        }

        let mut k_min: Option<BigInt> = None;
        let mut k_max: Option<BigInt> = None;

        // x = x0 + step_x * k
        // For x >= x_lo: k >= (x_lo - x0) / step_x (if step_x > 0)
        //                k <= (x_lo - x0) / step_x (if step_x < 0)
        // For x <= x_hi: k <= (x_hi - x0) / step_x (if step_x > 0)
        //                k >= (x_hi - x0) / step_x (if step_x < 0)

        if self.step_x.is_positive() {
            if let Some(lo) = x_lo {
                // k >= ceil((lo - x0) / step_x)
                let diff = lo - &self.x0;
                let k = ceil_div(&diff, &self.step_x);
                k_min = Some(k);
            }
            if let Some(hi) = x_hi {
                // k <= floor((hi - x0) / step_x)
                let diff = hi - &self.x0;
                let k = floor_div(&diff, &self.step_x);
                k_max = Some(k);
            }
        } else {
            // step_x < 0
            if let Some(lo) = x_lo {
                // k <= floor((lo - x0) / step_x) (dividing by negative flips direction)
                let diff = lo - &self.x0;
                let k = floor_div(&diff, &self.step_x);
                k_max = Some(k);
            }
            if let Some(hi) = x_hi {
                // k >= ceil((hi - x0) / step_x)
                let diff = hi - &self.x0;
                let k = ceil_div(&diff, &self.step_x);
                k_min = Some(k);
            }
        }

        (k_min, k_max)
    }

    /// Given bounds on y, compute the range of valid k values.
    pub(crate) fn k_bounds_from_y(
        &self,
        y_lo: Option<&BigInt>,
        y_hi: Option<&BigInt>,
    ) -> (Option<BigInt>, Option<BigInt>) {
        if self.step_y.is_zero() {
            // y is fixed at y0
            return (None, None);
        }

        let mut k_min: Option<BigInt> = None;
        let mut k_max: Option<BigInt> = None;

        // y = y0 - step_y * k
        // For y >= y_lo: -step_y * k >= y_lo - y0
        //                k <= (y0 - y_lo) / step_y (if step_y > 0)
        //                k >= (y0 - y_lo) / step_y (if step_y < 0)

        if self.step_y.is_positive() {
            if let Some(lo) = y_lo {
                // y >= y_lo => k <= floor((y0 - y_lo) / step_y)
                let diff = &self.y0 - lo;
                let k = floor_div(&diff, &self.step_y);
                k_max = Some(k);
            }
            if let Some(hi) = y_hi {
                // y <= y_hi => k >= ceil((y0 - y_hi) / step_y)
                let diff = &self.y0 - hi;
                let k = ceil_div(&diff, &self.step_y);
                k_min = Some(k);
            }
        } else {
            // step_y < 0
            if let Some(lo) = y_lo {
                // y >= y_lo => k >= ceil((y0 - y_lo) / step_y)
                let diff = &self.y0 - lo;
                let k = ceil_div(&diff, &self.step_y);
                k_min = Some(k);
            }
            if let Some(hi) = y_hi {
                // y <= y_hi => k <= floor((y0 - y_hi) / step_y)
                let diff = &self.y0 - hi;
                let k = floor_div(&diff, &self.step_y);
                k_max = Some(k);
            }
        }

        (k_min, k_max)
    }

    /// Compute (x, y) for a given k value
    pub(crate) fn evaluate(&self, k: &BigInt) -> (BigInt, BigInt) {
        let x = &self.x0 + &self.step_x * k;
        let y = &self.y0 - &self.step_y * k;
        (x, y)
    }
}

/// Ceiling division: ceil(a / b) for integers
fn ceil_div(a: &BigInt, b: &BigInt) -> BigInt {
    assert!(!b.is_zero(), "Division by zero in ceil_div");
    let (q, r) = a.div_rem(b);
    if r.is_zero() {
        q
    } else if (a.is_positive() && b.is_positive()) || (a.is_negative() && b.is_negative()) {
        // Same sign: round up
        q + BigInt::one()
    } else {
        // Different signs: already rounded towards zero which is ceil for negative result
        q
    }
}

/// Floor division: floor(a / b) for integers
fn floor_div(a: &BigInt, b: &BigInt) -> BigInt {
    assert!(!b.is_zero(), "Division by zero in floor_div");
    let (q, r) = a.div_rem(b);
    if r.is_zero() {
        q
    } else if (a.is_positive() && b.is_positive()) || (a.is_negative() && b.is_negative()) {
        // Same sign: already rounded towards zero which is floor for positive result
        q
    } else {
        // Different signs: round down
        q - BigInt::one()
    }
}
