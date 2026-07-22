// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl TermStore {
    /// Create bitvector unsigned division with constant folding
    ///
    /// Simplifications:
    /// - Constant folding: bvudiv(x, c) when both are constants
    /// - Identity: bvudiv(x, 1) → x
    ///
    /// SMT-LIB: bvudiv(x, 0) = all_ones for any x
    pub fn mk_bvudiv(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvudiv", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let zero = BigInt::zero();
        let one = BigInt::one();
        // Constant folding (includes div-by-zero: bvudiv(x, 0) = all_ones)
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            if *v2 == zero {
                return self.mk_bitvec(Self::bv_ones(w1), w1);
            }
            let result = v1.clone() / v2.clone();
            return self.mk_bitvec(Self::bv_mask(&result, w1), w1);
        }

        // Identity: x / 1 = x
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v == one {
                return a;
            }
        }

        // Power-of-two constant divisor: bvudiv(x, 2^k) = bvlshr(x, k) — exact
        // SMT-LIB equivalence for every x (wishlist rank 3, 2026-07-08). Shifts
        // are decided precisely everywhere (bit-blast fragment, word-level
        // reasoning); the division app must not survive where a lane would
        // abstract it. Divisor 0/1 already handled above, so k >= 1 here.
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v > zero && (v & (v - BigInt::one())) == zero {
                if let Some(k) = v.trailing_zeros() {
                    let shift = self.mk_bitvec(BigInt::from(k), width);
                    return self.mk_bvlshr(vec![a, shift]);
                }
            }
        }

        // NOTE: "zero dividend" (0/x → 0) and "self-division" (x/x → 1) rules
        // are unsound because x could be 0, and bvudiv(0,0) = all_ones per SMT-LIB.

        self.mk_bv_binary_app("bvudiv", args, width)
    }

    /// Create bitvector unsigned remainder with constant folding
    ///
    /// Simplifications:
    /// - Constant folding: bvurem(x, c) when both are constants (and c != 0)
    /// - SMT-LIB div-by-zero: bvurem(x, 0) → x
    /// - Identity: bvurem(x, 1) → 0
    /// - Self-remainder: bvurem(x, x) → 0
    /// - Zero dividend: bvurem(0, x) → 0
    pub fn mk_bvurem(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvurem", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let zero = BigInt::zero();
        let one = BigInt::one();

        // Constant folding (includes div-by-zero: bvurem(x, 0) = x)
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            if *v2 != zero {
                return self.mk_bitvec(v1 % v2, w1);
            } else {
                return self.mk_bitvec(v1.clone(), w1);
            }
        }

        // SMT-LIB: x % 0 = x
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v == zero {
                return a;
            }
        }

        // Identity: x % 1 = 0
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v == one {
                return self.mk_bitvec(zero, width);
            }
        }

        // Zero dividend: 0 % x = 0 (correct even when x=0: bvurem(0,0) = 0)
        if let Some((v, _)) = self.get_bitvec(a) {
            if *v == zero {
                return self.mk_bitvec(zero, width);
            }
        }

        // Self-remainder: x % x = 0 (correct even when x=0: bvurem(0,0) = 0)
        if a == b {
            return self.mk_bitvec(zero, width);
        }

        // Power-of-two constant divisor: bvurem(x, 2^k) = bvand(x, 2^k - 1) —
        // exact SMT-LIB equivalence for every x (wishlist rank 3, 2026-07-08).
        // Divisor 0/1 already handled above, so k >= 1 here.
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v > zero && (v & (v - BigInt::one())) == zero {
                let mask = self.mk_bitvec(v - BigInt::one(), width);
                return self.mk_bvand(vec![a, mask]);
            }
        }

        self.mk_bv_binary_app("bvurem", args, width)
    }

    /// Create signed bitvector division with constant folding
    ///
    /// SMT-LIB semantics (bvsdiv s t):
    /// - Signed division, truncated towards zero
    /// - sign(result) = sign(s) XOR sign(t)
    /// - |result| = |s| / |t|
    ///
    /// Simplifications:
    /// - Constant folding: bvsdiv(#x06, #x02) → #x03
    /// - SMT-LIB div-by-zero: bvsdiv(x, 0) = all_ones when msb(x)=0, else 1
    /// - Identity: bvsdiv(x, 1) → x
    ///
    /// SMT-LIB: bvsdiv(x, 0) = if msb(x)=0 then ~0 else 1
    pub fn mk_bvsdiv(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvsdiv", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let zero = BigInt::zero();
        let one = BigInt::one();
        let sign_threshold = BigInt::one() << (width - 1);

        // Constant folding (includes div-by-zero)
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            if *v2 != zero {
                let s1 = Self::to_signed(v1, w1);
                let s2 = Self::to_signed(v2, w1);
                // Signed division truncated towards zero
                let quotient = if (s1 >= zero) == (s2 >= zero) {
                    s1.abs() / s2.abs()
                } else {
                    -(s1.abs() / s2.abs())
                };
                return self.mk_bitvec(Self::from_signed(&quotient, w1), w1);
            } else {
                // SMT-LIB: bvsdiv(x, 0) = if msb(x)=0 then ~0 else 1
                if *v1 < sign_threshold {
                    return self.mk_bitvec(Self::bv_ones(w1), w1);
                } else {
                    return self.mk_bitvec(one, w1);
                }
            }
        }

        // Identity: x / 1 = x
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v == one {
                return a;
            }
        }

        // NOTE: "zero dividend" (0/x → 0) and "self-division" (x/x → 1) rules
        // are unsound because x could be 0, and bvsdiv(0,0) = all_ones per SMT-LIB.

        self.mk_bv_binary_app("bvsdiv", args, width)
    }

    /// Create signed bitvector remainder with constant folding
    ///
    /// SMT-LIB semantics (bvsrem s t):
    /// - sign(result) = sign(s) (sign follows dividend)
    /// - s = (bvsdiv s t) * t + (bvsrem s t)
    ///
    /// Simplifications:
    /// - Constant folding: bvsrem(#x07, #x03) → #x01
    /// - Identity: bvsrem(x, 1) → 0
    /// - Self-remainder: bvsrem(x, x) → 0
    /// - Zero dividend: bvsrem(0, x) → 0
    pub fn mk_bvsrem(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvsrem", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let zero = BigInt::zero();
        let one = BigInt::one();

        // Constant folding (includes div-by-zero: bvsrem(x, 0) = x)
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            if *v2 != zero {
                let s1 = Self::to_signed(v1, w1);
                let s2 = Self::to_signed(v2, w1);
                // Result sign follows dividend (s1)
                let remainder = if s1 >= zero {
                    s1.abs() % s2.abs()
                } else {
                    -(s1.abs() % s2.abs())
                };
                return self.mk_bitvec(Self::from_signed(&remainder, w1), w1);
            } else {
                return self.mk_bitvec(v1.clone(), w1);
            }
        }

        // Identity: x % 1 = 0
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v == one {
                return self.mk_bitvec(zero, width);
            }
        }

        // Zero dividend: 0 % x = 0 (correct even when x=0: bvsrem(0,0) = 0)
        if let Some((v, _)) = self.get_bitvec(a) {
            if *v == zero {
                return self.mk_bitvec(zero, width);
            }
        }

        // Self-remainder: x % x = 0 (correct even when x=0: bvsrem(0,0) = 0)
        if a == b {
            return self.mk_bitvec(zero, width);
        }

        self.mk_bv_binary_app("bvsrem", args, width)
    }

    /// Create signed bitvector modulo with constant folding
    ///
    /// SMT-LIB semantics (bvsmod s t):
    /// - sign(result) = sign(t) (sign follows divisor)
    /// - Result is the unique value r such that:
    ///   - 0 <= r < |t| or |t| < r <= 0
    ///   - s = q*t + r for some integer q
    ///
    /// Simplifications:
    /// - Constant folding: bvsmod(#xFB, #x03) → #x02 (i.e., -5 mod 3 = 2)
    /// - Identity: bvsmod(x, 1) → 0
    /// - Self-modulo: bvsmod(x, x) → 0
    /// - Zero dividend: bvsmod(0, x) → 0
    pub fn mk_bvsmod(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvsmod", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let zero = BigInt::zero();
        let one = BigInt::one();

        // Constant folding (includes div-by-zero: bvsmod(x, 0) = x)
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            if *v2 != zero {
                let s1 = Self::to_signed(v1, w1);
                let s2 = Self::to_signed(v2, w1);
                let abs_t = s2.abs();
                let u = s1.abs() % &abs_t;

                let result = if u == zero {
                    zero
                } else if s1 >= zero && s2 >= zero {
                    // Both positive: result is u
                    u
                } else if s1 < zero && s2 >= zero {
                    // s < 0, t > 0: result is t - u
                    &abs_t - u
                } else if s1 >= zero && s2 < zero {
                    // s >= 0, t < 0: result is u + t (which is u - |t|)
                    u - &abs_t
                } else {
                    // Both negative: result is -u
                    -u
                };
                return self.mk_bitvec(Self::from_signed(&result, w1), w1);
            } else {
                return self.mk_bitvec(v1.clone(), w1);
            }
        }

        // Identity: x mod 1 = 0
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v == one {
                return self.mk_bitvec(zero, width);
            }
        }

        // Zero dividend: 0 mod x = 0 (correct even when x=0: bvsmod(0,0) = 0)
        if let Some((v, _)) = self.get_bitvec(a) {
            if *v == zero {
                return self.mk_bitvec(zero, width);
            }
        }

        // Self-modulo: x mod x = 0 (correct even when x=0: bvsmod(0,0) = 0)
        if a == b {
            return self.mk_bitvec(zero, width);
        }

        self.mk_bv_binary_app("bvsmod", args, width)
    }

    /// Create bitvector comparison returning 1-bit bitvector
    ///
    /// SMT-LIB semantics (bvcomp s t):
    /// - Returns #b1 if s = t, #b0 if s ≠ t
    ///
    /// Simplifications:
    /// - Constant folding: bvcomp(#x05, #x05) → #b1
    /// - Reflexivity: bvcomp(x, x) → #b1
    pub fn mk_bvcomp(&mut self, a: TermId, b: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(a), Sort::BitVec(_)) && matches!(self.sort(b), Sort::BitVec(_)),
            "BUG: mk_bvcomp expects BitVec args, got {:?} and {:?}",
            self.sort(a),
            self.sort(b)
        );
        debug_assert!(
            self.sort(a) == self.sort(b),
            "BUG: mk_bvcomp expects same-width BitVec args"
        );
        // Reflexivity: bvcomp(x, x) = #b1
        if a == b {
            return self.mk_bitvec(BigInt::one(), 1);
        }

        // Constant folding
        if let (Some((v1, _)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            return if v1 == v2 {
                self.mk_bitvec(BigInt::one(), 1)
            } else {
                self.mk_bitvec(BigInt::zero(), 1)
            };
        }

        self.intern(
            TermData::App(Symbol::named("bvcomp"), vec![a, b]),
            Sort::bitvec(1),
        )
    }
}
