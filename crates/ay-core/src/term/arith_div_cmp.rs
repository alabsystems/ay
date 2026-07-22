// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Division, modulo, absolute value, min/max, type conversions, and comparison
//! term constructors for TermStore.
//!
//! Extracted from `arithmetic.rs` as part of code-health module split.
//! The primary arithmetic operations (add, sub, mul, neg) remain in `arithmetic.rs`.

use super::*;
use num_traits::One;

impl TermStore {
    /// Create real division with constant folding
    pub fn mk_div(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(self.sort(lhs) == &Sort::Real && self.sort(rhs) == &Sort::Real);
        // Constant folding for rationals
        if let (Some(r1), Some(r2)) = (self.get_rational(lhs), self.get_rational(rhs)) {
            if !r2.is_zero() {
                return self.mk_rational(r1.clone() / r2.clone());
            }
        }

        // x / 1 = x  (divisor is the non-zero constant 1, always sound).
        if let Some(r) = self.get_rational(rhs) {
            if *r == BigRational::one() {
                return lhs;
            }
        }

        // 0 / x = 0  ONLY when the divisor is a known non-zero constant.
        //
        // SMT-LIB Reals makes `/` total, but leaves `(/ a 0)` UNCONSTRAINED
        // (a single consistent but unspecified value, like `div`/`mod` for
        // Ints). So `(/ 0 x)` is NOT necessarily 0 when `x` may be 0 — folding
        // it unconditionally wrongly refutes models with `x = 0`
        // (#div0-soundness). Require a non-zero constant divisor before folding
        // the numerator-is-zero case.
        if let Some(r1) = self.get_rational(lhs) {
            if r1.is_zero() {
                if let Some(r2) = self.get_rational(rhs) {
                    if !r2.is_zero() {
                        return self.mk_rational(BigRational::zero());
                    }
                }
            }
        }

        // NOTE: `x / x = 1` is intentionally NOT folded: when `x = 0`,
        // `(/ 0 0)` is unconstrained, so the identity does not hold. The
        // non-zero-constant case is already handled by full constant folding
        // above.

        self.intern(
            TermData::App(Symbol::named("/"), vec![lhs, rhs]),
            Sort::Real,
        )
    }

    /// Create integer division with constant folding
    pub fn mk_intdiv(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(self.sort(lhs) == &Sort::Int && self.sort(rhs) == &Sort::Int);
        // Constant folding for integers
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            if !n2.is_zero() {
                // SMT-LIB div: Euclidean division where remainder is always non-negative.
                // a = b * q + r, 0 <= r < |b|.
                // Compute non-negative remainder first, then derive quotient.
                let rem = smt_euclid_rem(n1, n2);
                return self.mk_int((n1 - &rem) / n2);
            }
        }

        // x div 1 = x  (divisor is the non-zero constant 1, always sound).
        if let Some(n) = self.get_int(rhs) {
            if n.is_one() {
                return lhs;
            }
        }

        // 0 div x = 0  ONLY when the divisor is a known non-zero constant.
        //
        // SMT-LIB Ints makes `div` total, but leaves `(div a 0)` UNCONSTRAINED
        // (a single consistent but unspecified value). So `(div 0 x)` is NOT
        // necessarily 0 when `x` may be 0 — folding it unconditionally wrongly
        // refutes models with `x = 0` (#div0-soundness). Require a non-zero
        // constant divisor before folding the numerator-is-zero case.
        if let Some(n1) = self.get_int(lhs) {
            if n1.is_zero() {
                if let Some(n2) = self.get_int(rhs) {
                    if !n2.is_zero() {
                        return self.mk_int(BigInt::zero());
                    }
                }
            }
        }

        // NOTE: `x div x = 1` is intentionally NOT folded: when `x = 0`,
        // `(div 0 0)` is unconstrained, so the identity does not hold. The
        // non-zero-constant case is already handled by full constant folding
        // above.

        self.intern(
            TermData::App(Symbol::named("div"), vec![lhs, rhs]),
            Sort::Int,
        )
    }

    /// Create integer remainder (SMT-LIB / Z3 `rem`) with constant folding.
    ///
    /// Z3 semantics (matching `reference/z3/src/ast/arith_decl_plugin.cpp`
    /// `OP_REM` and the `reference/z3/src/tactic/arith/purify_arith_tactic.cpp`
    /// rule): the remainder takes the sign of the divisor, not the dividend:
    ///
    /// ```text
    /// (rem t1 t2) = ite (>= t2 0) (mod t1 t2) (- (mod t1 t2))     when t2 != 0
    /// ```
    ///
    /// For positive `t2`, `(rem t1 t2) == (mod t1 t2)`. They differ only when
    /// the divisor is negative.
    ///
    /// **Zero-divisor handling (Z3 #9140):** SMT-LIB leaves both `(mod x 0)`
    /// and `(rem x 0)` under-specified (returning distinct uninterpreted
    /// values). We therefore intern `(rem x y)` as its own `"rem"`
    /// application — distinct from `"mod"` — whenever the divisor is not a
    /// non-zero constant. That preserves `(distinct (rem x 0) (mod x 0))`
    /// as satisfiable, matching the cvc5 / Z3 ≥4.15 behaviour.
    ///
    /// For a non-zero integer constant divisor, we either fold (when the
    /// dividend is also constant) or rewrite to `mod`/`-mod` as above so the
    /// LIA theory can reason about the result.
    pub fn mk_rem(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(self.sort(lhs) == &Sort::Int && self.sort(rhs) == &Sort::Int);

        // Constant folding when both inputs are integer literals and divisor != 0.
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            if !n2.is_zero() {
                // SMT-LIB Euclidean remainder is always non-negative.
                let euclid_r = smt_euclid_rem(n1, n2);
                // Z3 `rem`: sign follows divisor. If divisor is negative,
                // negate the Euclidean remainder.
                let rem_val = if n2.is_negative() {
                    -euclid_r
                } else {
                    euclid_r
                };
                return self.mk_int(rem_val);
            }
        }

        // Divisor-side simplifications that hold for non-zero constant divisors.
        // Copy the sign/magnitude bits out so we can call `&mut self` below.
        let rhs_const = self.get_int(rhs).cloned();
        if let Some(n) = rhs_const {
            if !n.is_zero() {
                // x rem 1 = 0, x rem -1 = 0.
                if n.is_one() || n == -BigInt::one() {
                    return self.mk_int(BigInt::zero());
                }
                // Safe to rewrite to the ite(y>=0, mod, -mod) form since y is
                // a known non-zero constant: the result is either `mod x y`
                // (when y > 0) or `-(mod x y)` (when y < 0).
                let modv = self.mk_mod(lhs, rhs);
                if n.is_negative() {
                    return self.mk_neg(modv);
                }
                return modv;
            }
        }

        // 0 rem y = 0  ONLY when the divisor is a known non-zero constant.
        //
        // SMT-LIB / Z3 leave `(rem a 0)` UNCONSTRAINED (the same #9140
        // under-specification as `mod`/`div`), so `(rem 0 y)` is not
        // necessarily 0 when `y` may be 0. Folding it unconditionally wrongly
        // refutes models with `y = 0` (#div0-soundness).
        if let Some(n1) = self.get_int(lhs) {
            if n1.is_zero() {
                if let Some(n2) = self.get_int(rhs) {
                    if !n2.is_zero() {
                        return self.mk_int(BigInt::zero());
                    }
                }
            }
        }

        // NOTE: `x rem x = 0` is intentionally NOT folded: when `x = 0`,
        // `(rem 0 0)` is unconstrained, so the identity does not hold.

        // Symbolic or zero-constant divisor: keep `rem` as its own symbol.
        // This preserves the Z3 #9140 property that `(distinct (rem x 0)
        // (mod x 0))` is satisfiable.
        self.intern(
            TermData::App(Symbol::named("rem"), vec![lhs, rhs]),
            Sort::Int,
        )
    }

    /// Create modulo with constant folding
    pub fn mk_mod(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(self.sort(lhs) == &Sort::Int && self.sort(rhs) == &Sort::Int);
        // Constant folding for integers
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            if !n2.is_zero() {
                // SMT-LIB mod: Euclidean remainder, always non-negative.
                // a = b * (div a b) + (mod a b), 0 <= (mod a b) < |b|.
                return self.mk_int(smt_euclid_rem(n1, n2));
            }
        }

        // x mod 1 = 0  (divisor is the non-zero constant 1, always sound).
        if let Some(n) = self.get_int(rhs) {
            if n.is_one() {
                return self.mk_int(BigInt::zero());
            }
        }

        // 0 mod x = 0  ONLY when the divisor is a known non-zero constant.
        //
        // As with `div`, SMT-LIB leaves `(mod a 0)` UNCONSTRAINED, so
        // `(mod 0 x)` is not necessarily 0 when `x` may be 0. Folding it
        // unconditionally wrongly refutes models with `x = 0`
        // (#div0-soundness).
        if let Some(n1) = self.get_int(lhs) {
            if n1.is_zero() {
                if let Some(n2) = self.get_int(rhs) {
                    if !n2.is_zero() {
                        return self.mk_int(BigInt::zero());
                    }
                }
            }
        }

        // NOTE: `x mod x = 0` is intentionally NOT folded: when `x = 0`,
        // `(mod 0 0)` is unconstrained, so the identity does not hold.

        self.intern(
            TermData::App(Symbol::named("mod"), vec![lhs, rhs]),
            Sort::Int,
        )
    }

    /// Create absolute value with constant folding and ITE expansion
    ///
    /// For non-constant arguments, expands `(abs x)` to `(ite (>= x 0) x (- x))`.
    /// This ensures the LIA theory can properly reason about absolute value.
    pub fn mk_abs(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::Int | Sort::Real),
            "BUG: mk_abs expects Int or Real, got {:?}",
            self.sort(arg)
        );
        // Constant folding for integers
        if let Some(n) = self.get_int(arg) {
            if n.is_negative() {
                return self.mk_int(-n.clone());
            }
            return arg;
        }

        // Constant folding for rationals
        if let Some(r) = self.get_rational(arg) {
            if *r < BigRational::zero() {
                return self.mk_rational(-r.clone());
            }
            return arg;
        }

        // Expand to ITE: (abs x) -> (ite (>= x 0) x (- x))
        // This allows the LIA/LRA theories to properly handle abs
        let zero = match self.sort(arg) {
            Sort::Real => self.mk_rational(BigRational::zero()),
            _ => self.mk_int(BigInt::zero()),
        };
        let cond = self.mk_ge(arg, zero);
        let neg_arg = self.mk_neg(arg);
        self.mk_ite(cond, arg, neg_arg)
    }

    /// Create minimum of two values with constant folding and ITE expansion
    ///
    /// For non-constant arguments, expands `(min x y)` to `(ite (<= x y) x y)`.
    pub fn mk_min(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(lhs), Sort::Int | Sort::Real),
            "BUG: mk_min expects Int or Real, got {:?}",
            self.sort(lhs)
        );
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_min expects same sort, got {:?} vs {:?}",
            self.sort(lhs),
            self.sort(rhs)
        );
        // Same value: min(x, x) = x
        if lhs == rhs {
            return lhs;
        }

        // Integer constant folding
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            return if n1 < n2 {
                self.mk_int(n1.clone())
            } else {
                self.mk_int(n2.clone())
            };
        }

        // Rational constant folding
        if let (Some(r1), Some(r2)) = (self.get_rational(lhs), self.get_rational(rhs)) {
            return if r1 < r2 {
                self.mk_rational(r1.clone())
            } else {
                self.mk_rational(r2.clone())
            };
        }

        // Expand to ITE: (min x y) -> (ite (<= x y) x y)
        let cond = self.mk_le(lhs, rhs);
        self.mk_ite(cond, lhs, rhs)
    }

    /// Create maximum of two values with constant folding and ITE expansion
    ///
    /// For non-constant arguments, expands `(max x y)` to `(ite (>= x y) x y)`.
    pub fn mk_max(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(lhs), Sort::Int | Sort::Real),
            "BUG: mk_max expects Int or Real, got {:?}",
            self.sort(lhs)
        );
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_max expects same sort, got {:?} vs {:?}",
            self.sort(lhs),
            self.sort(rhs)
        );
        // Same value: max(x, x) = x
        if lhs == rhs {
            return lhs;
        }

        // Integer constant folding
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            return if n1 > n2 {
                self.mk_int(n1.clone())
            } else {
                self.mk_int(n2.clone())
            };
        }

        // Rational constant folding
        if let (Some(r1), Some(r2)) = (self.get_rational(lhs), self.get_rational(rhs)) {
            return if r1 > r2 {
                self.mk_rational(r1.clone())
            } else {
                self.mk_rational(r2.clone())
            };
        }

        // Expand to ITE: (max x y) -> (ite (>= x y) x y)
        let cond = self.mk_ge(lhs, rhs);
        self.mk_ite(cond, lhs, rhs)
    }

    // =======================================================================
    // Type conversion operations
    // =======================================================================

    /// Convert an integer to a real (SMT-LIB: `to_real`).
    ///
    /// For constants, this creates a rational with denominator 1.
    /// For symbolic integers, creates a `to_real` application.
    pub fn mk_to_real(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            self.sort(arg) == &Sort::Int,
            "BUG: mk_to_real expects Int arg, got {:?}",
            self.sort(arg)
        );

        // Constant folding: convert integer constant to rational
        if let Some(n) = self.get_int(arg) {
            return self.mk_rational(BigRational::from(n.clone()));
        }

        self.intern(
            TermData::App(Symbol::named("to_real"), vec![arg]),
            Sort::Real,
        )
    }

    /// Convert a real to an integer via floor (SMT-LIB: `to_int`).
    ///
    /// For constants, computes floor(r). For symbolic reals, creates a `to_int` application.
    pub fn mk_to_int(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            self.sort(arg) == &Sort::Real,
            "BUG: mk_to_int expects Real arg, got {:?}",
            self.sort(arg)
        );

        // Constant folding: floor of rational
        if let Some(r) = self.get_rational(arg) {
            return self.mk_int(r.floor().to_integer());
        }

        // to_int(to_real(n)) = n — the round-trip is the identity on Int.
        // (#to-real-bridge; builtin-only via get_to_real_arg.)
        if let Some(n) = self.get_to_real_arg(arg) {
            return n;
        }

        self.intern(TermData::App(Symbol::named("to_int"), vec![arg]), Sort::Int)
    }

    /// Test if a real value is an integer (SMT-LIB: `is_int`).
    ///
    /// For constants, returns true/false. For symbolic reals, creates an `is_int` application.
    pub fn mk_is_int(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            self.sort(arg) == &Sort::Real,
            "BUG: mk_is_int expects Real arg, got {:?}",
            self.sort(arg)
        );

        // Constant folding: check if rational is an integer
        if let Some(r) = self.get_rational(arg) {
            return self.mk_bool(r.is_integer());
        }

        // is_int(to_real(n)) = true — the image of Int under to_real is
        // integer-valued. (#to-real-bridge; builtin-only via get_to_real_arg.)
        if self.get_to_real_arg(arg).is_some() {
            return self.true_term();
        }

        self.intern(
            TermData::App(Symbol::named("is_int"), vec![arg]),
            Sort::Bool,
        )
    }

    // =======================================================================
    // Comparison operations with constant folding
    // =======================================================================

    /// Create less-than comparison with constant folding
    pub fn mk_lt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(lhs), Sort::Int | Sort::Real),
            "BUG: mk_lt expects Int or Real, got {:?}",
            self.sort(lhs)
        );
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_lt expects same sort, got {:?} < {:?}",
            self.sort(lhs),
            self.sort(rhs)
        );
        // x < x = false
        if lhs == rhs {
            return self.false_term();
        }

        // Integer constant folding
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            return self.mk_bool(n1 < n2);
        }

        // Rational constant folding
        if let (Some(r1), Some(r2)) = (self.get_rational(lhs), self.get_rational(rhs)) {
            return self.mk_bool(r1 < r2);
        }

        // to_real-integrality rewrites (#to-real-bridge). All EQUIVALENCES, so
        // they are safe under any polarity/quantifier:
        //   to_real(a) < to_real(b)  <=>  a < b        (to_real is monotone)
        //   to_real(n) < c           <=>  n <= ceil(c)-1
        //   c < to_real(n)           <=>  floor(c)+1 <= n
        // (c=5.5 -> n<=5; integral c=5 -> n<=4; c=-5.5 -> n<=-6 — verified
        // including negatives and integral constants.) Guarded by
        // get_to_real_arg: builtin-only (stands down when a user declaration
        // shadows `to_real`) and Int-sorted argument only.
        if let (Some(a), Some(b)) = (self.get_to_real_arg(lhs), self.get_to_real_arg(rhs)) {
            return self.mk_lt(a, b);
        }
        if let Some(n) = self.get_to_real_arg(lhs) {
            if let Some(c) = self.get_rational(rhs).cloned() {
                let bound = self.mk_int(c.ceil().to_integer() - 1);
                return self.mk_le(n, bound);
            }
        }
        if let Some(n) = self.get_to_real_arg(rhs) {
            if let Some(c) = self.get_rational(lhs).cloned() {
                let bound = self.mk_int(c.floor().to_integer() + 1);
                return self.mk_le(bound, n);
            }
        }

        self.intern(
            TermData::App(Symbol::named("<"), vec![lhs, rhs]),
            Sort::Bool,
        )
    }

    /// Create less-than-or-equal comparison with constant folding
    pub fn mk_le(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(lhs), Sort::Int | Sort::Real),
            "BUG: mk_le expects Int or Real, got {:?}",
            self.sort(lhs)
        );
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_le expects same sort, got {:?} <= {:?}",
            self.sort(lhs),
            self.sort(rhs)
        );
        // x <= x = true
        if lhs == rhs {
            return self.true_term();
        }

        // Integer constant folding
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            return self.mk_bool(n1 <= n2);
        }

        // Rational constant folding
        if let (Some(r1), Some(r2)) = (self.get_rational(lhs), self.get_rational(rhs)) {
            return self.mk_bool(r1 <= r2);
        }

        // to_real-integrality rewrites (#to-real-bridge), mirroring mk_lt:
        //   to_real(a) <= to_real(b)  <=>  a <= b
        //   to_real(n) <= c           <=>  n <= floor(c)
        //   c <= to_real(n)           <=>  ceil(c) <= n
        if let (Some(a), Some(b)) = (self.get_to_real_arg(lhs), self.get_to_real_arg(rhs)) {
            return self.mk_le(a, b);
        }
        if let Some(n) = self.get_to_real_arg(lhs) {
            if let Some(c) = self.get_rational(rhs).cloned() {
                let bound = self.mk_int(c.floor().to_integer());
                return self.mk_le(n, bound);
            }
        }
        if let Some(n) = self.get_to_real_arg(rhs) {
            if let Some(c) = self.get_rational(lhs).cloned() {
                let bound = self.mk_int(c.ceil().to_integer());
                return self.mk_le(bound, n);
            }
        }

        self.intern(
            TermData::App(Symbol::named("<="), vec![lhs, rhs]),
            Sort::Bool,
        )
    }

    /// Create greater-than comparison with constant folding
    ///
    /// Normalized to less-than: (> a b) -> (< b a)
    pub fn mk_gt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Normalize: (> a b) -> (< b a) for canonical form
        self.mk_lt(rhs, lhs)
    }

    /// Create greater-than-or-equal comparison with constant folding
    ///
    /// Normalized to less-than-or-equal: (>= a b) -> (<= b a)
    pub fn mk_ge(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Normalize: (>= a b) -> (<= b a) for canonical form
        self.mk_le(rhs, lhs)
    }
}
