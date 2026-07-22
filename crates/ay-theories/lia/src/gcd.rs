// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GCD-based infeasibility checks and rational-bound helpers for LIA.

use super::*;
use tracing::{debug, info};

impl LiaSolver<'_> {
    /// GCD divisibility test over asserted positive equalities.
    ///
    /// #C2: the divisibility verdict is assignment-independent per equality
    /// (a structural property of the equation), so it is precomputed once in
    /// the atom-indexed linear cache; this is now a pure scan over cached
    /// bools instead of a per-check term-DAG re-parse with fresh BigInt maps.
    pub(super) fn gcd_test(&self) -> Option<TheoryConflict> {
        use num_rational::Rational64;

        let debug = self.debug_gcd;
        let mut tested_equalities = 0usize;

        if debug {
            safe_eprintln!(
                "[GCD] Running GCD test on {} asserted literals",
                self.asserted.len()
            );
        }

        for &literal in &self.assertion_view().positive_equalities {
            // Check if this is an equality
            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }

            let cached = self.cached_linear(args[0], args[1]);

            if cached.coeffs.is_empty() {
                continue;
            }
            tested_equalities += 1;

            if debug {
                safe_eprintln!(
                    "[GCD] Equality: coeffs={:?}, constant={}",
                    cached.coeffs.iter().map(|(_, c)| c).collect::<Vec<_>>(),
                    cached.constant
                );
            }

            // `gcd == 0` (all-zero coefficients) is skipped, matching the
            // historical behavior; otherwise the cached verdict decides.
            if cached.gcd.is_zero() {
                continue;
            }
            debug_assert!(
                cached.gcd.is_positive(),
                "BUG: cached gcd is non-positive: {}",
                cached.gcd
            );

            if !cached.gcd_divides {
                // Cold path: recompute the remainder only for diagnostics.
                if debug {
                    let remainder = &cached.constant % &cached.gcd;
                    safe_eprintln!(
                        "[GCD] UNSAT: GCD={} does not divide constant={} (remainder={})",
                        cached.gcd,
                        cached.constant,
                        remainder
                    );
                }
                // Return conflict with the equality as the reason.
                // Farkas coefficient 1 - the equality is the sole contributor.
                let literals = vec![TheoryLit::new(literal, true)];
                let farkas = FarkasAnnotation::new(vec![Rational64::from(1)]);
                info!(
                    target: "ay::lia",
                    tested_equalities,
                    conflicting_literal = literal.0,
                    gcd = %cached.gcd,
                    constant = %cached.constant,
                    "LIA GCD test found divisibility conflict"
                );
                return Some(TheoryConflict::with_farkas(literals, farkas));
            }
        }

        debug!(
            target: "ay::lia",
            tested_equalities,
            "LIA GCD test completed without conflict"
        );

        None
    }

    // gcd_test_tableau, ext_gcd_test, collect_tableau_gcd_conflict_literals,
    // append_bound_reason_literals extracted to gcd_tableau.rs

    pub(crate) fn update_gcd_and_least_coeff(
        abs_scaled: &BigInt,
        is_bounded: bool,
        gcds: &mut BigInt,
        least_coeff: &mut BigInt,
        least_coeff_is_bounded: &mut bool,
    ) {
        if gcds.is_zero() {
            gcds.clone_from(abs_scaled);
            least_coeff.clone_from(abs_scaled);
            *least_coeff_is_bounded = is_bounded;
            return;
        }

        *gcds = gcds.gcd(abs_scaled);

        if abs_scaled < &*least_coeff {
            least_coeff.clone_from(abs_scaled);
            *least_coeff_is_bounded = is_bounded;
        } else if abs_scaled == &*least_coeff {
            // Keep "bounded" true if any tied least-coefficient variable is bounded.
            *least_coeff_is_bounded |= is_bounded;
        }
    }

    /// Ceiling of a rational number: ceil(r)
    pub(crate) fn ceil_rational(r: &BigRational) -> BigInt {
        if r.is_integer() {
            r.to_integer()
        } else if r.is_positive() {
            r.to_integer() + BigInt::one()
        } else {
            r.to_integer()
        }
    }

    /// Floor of a rational number: floor(r)
    pub(crate) fn floor_rational(r: &BigRational) -> BigInt {
        if r.is_integer() {
            r.to_integer()
        } else if r.is_negative() {
            r.to_integer() - BigInt::one()
        } else {
            r.to_integer()
        }
    }

    /// i64 fast path for [`Self::effective_int_lower`] (#C4).
    ///
    /// Exact whenever it returns `Some`: `Rational::ceil_int` is the exact
    /// mathematical ceiling for inline values, and the strict-integer `+1`
    /// adjustment is checked. Returns `None` (caller falls back to the
    /// BigInt path) for `Rational::Big` bounds or on i64 overflow.
    pub(crate) fn effective_int_lower_i64(b: &Bound) -> Option<i64> {
        let c = b.value.ceil_int()?;
        if b.strict && b.value.is_integer() {
            c.checked_add(1)
        } else {
            Some(c)
        }
    }

    /// i64 fast path for [`Self::effective_int_upper`] (#C4).
    ///
    /// Exact whenever it returns `Some`; see [`Self::effective_int_lower_i64`].
    pub(crate) fn effective_int_upper_i64(b: &Bound) -> Option<i64> {
        let f = b.value.floor_int()?;
        if b.strict && b.value.is_integer() {
            f.checked_sub(1)
        } else {
            Some(f)
        }
    }

    /// Effective integer lower bound from a rational bound.
    ///
    /// For integer variables, a strict bound `x > n` (where n is integer) becomes
    /// `x >= n+1`. A non-strict bound `x >= r` becomes `x >= ceil(r)`.
    pub(crate) fn effective_int_lower(b: &Bound) -> BigInt {
        let bv = b.value.to_big();
        let result = if b.strict && Self::is_integer(&bv) {
            Self::floor_rational(&bv) + BigInt::one()
        } else {
            Self::ceil_rational(&bv)
        };
        // INVARIANT: effective lower bound must be >= the rational bound value
        debug_assert!(
            BigRational::from(result.clone()) >= bv,
            "BUG: effective_int_lower({}{}) = {} is below bound",
            if b.strict { ">" } else { ">=" },
            bv,
            result
        );
        result
    }

    /// Effective integer upper bound from a rational bound.
    ///
    /// For integer variables, a strict bound `x < n` (where n is integer) becomes
    /// `x <= n-1`. A non-strict bound `x <= r` becomes `x <= floor(r)`.
    pub(crate) fn effective_int_upper(b: &Bound) -> BigInt {
        let bv = b.value.to_big();
        let result = if b.strict && Self::is_integer(&bv) {
            Self::floor_rational(&bv) - BigInt::one()
        } else {
            Self::floor_rational(&bv)
        };
        // INVARIANT: effective upper bound must be <= the rational bound value
        debug_assert!(
            BigRational::from(result.clone()) <= bv,
            "BUG: effective_int_upper({}{}) = {} is above bound",
            if b.strict { "<" } else { "<=" },
            b.value,
            result
        );
        result
    }
}

#[cfg(test)]
#[path = "gcd_tests.rs"]
mod tests;
