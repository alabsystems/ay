// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector evaluation helpers for model evaluation.
//!
//! Extracted from `mod.rs` to reduce file size (Wave C1 of #2998 module splits).
//! All methods are `impl Executor` — they share the same method namespace.

use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::{EvalValue, Executor, Model};

impl Executor {
    pub(super) fn normalize_bv_value(value: BigInt, width: u32) -> BigInt {
        // Euclidean residue mod 2^width, i.e. the unsigned `width`-bit value.
        // `value & (2^width - 1)` equals `((value % 2^width) + 2^width) % 2^width`
        // for EVERY BigInt: num-bigint's bitwise ops use two's-complement
        // (infinite sign-extension) semantics, so masking the low `width` bits
        // yields the non-negative residue even for negative `value`
        // (e.g. -1 & 0xFF = 255) and for width == 0 (mask = 0 -> 0). ANDing with
        // the non-negative finite mask always clears the sign bit, so the result
        // is non-negative. This avoids the two BigInt divisions the modulo form
        // performs on a very hot model-evaluation path (#eval-bv-normalize).
        let mask = (BigInt::one() << width) - 1;
        &value & &mask
    }

    /// Extract a BV shift amount, returning `None` if the shift >= width.
    ///
    /// `to_u32_digits().1.first()` only reads the low base-2^32 digit, so a
    /// shift amount of 2^32 on a 64-bit BV would incorrectly yield 0.
    /// Instead, compare the full BigInt against width first.
    fn bv_shift_amount(b: &BigInt, width: u32) -> Option<usize> {
        if b.sign() == num_bigint::Sign::Minus || *b >= BigInt::from(width) {
            None // shift >= width -> result is 0 (or all-1s for ashr of negative)
        } else {
            // Safe: b < width <= u32::MAX, so fits in usize
            Some(b.to_u32_digits().1.first().copied().unwrap_or(0) as usize)
        }
    }

    pub(super) fn to_signed_bv(unsigned: &BigInt, width: u32) -> BigInt {
        if width == 0 {
            return BigInt::zero();
        }
        let sign_bit = BigInt::from(1) << (width - 1);
        if unsigned >= &sign_bit {
            unsigned - (BigInt::from(1) << width)
        } else {
            unsigned.clone()
        }
    }

    /// BV model cache fallback for BV application terms (#5627).
    ///
    /// When semantic evaluation of a BV operation returns Unknown (e.g., because
    /// a child variable was eliminated by BVE and not recovered), fall back to
    /// the bit-blasted value in the BV model cache. The bit-blaster assigns SAT
    /// variables to ALL BV terms (including applications like sign_extend), and
    /// after SAT solving + reconstruction, those variables have correct values.
    /// This mirrors the existing select fallback at line ~1705.
    pub(super) fn bv_model_cache_fallback(
        &self,
        model: &Model,
        term_id: TermId,
        sort: &Sort,
    ) -> EvalValue {
        // The cache is keyed only by the application's ambient TermId. A
        // lambda body can reuse that TermId at several beta values, so the
        // cached result is valid here only when the application is independent
        // of every active binding.
        if super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, term_id) {
            return EvalValue::Unknown;
        }
        if let Sort::BitVec(bv) = sort {
            if let Some(ref bv_model) = model.bv_model {
                if let Some(val) = bv_model.values.get(&term_id) {
                    return EvalValue::BitVec {
                        value: val.clone(),
                        width: bv.width,
                    };
                }
            }
        }
        EvalValue::Unknown
    }

    /// Check if a child term is a BV variable missing from the BV model (#5627).
    ///
    /// Returns true when the child is a BV-sorted variable and the BV model
    /// exists but does NOT contain an entry for it. This indicates the variable
    /// was eliminated by preprocessing and not recovered during model extraction.
    /// Its evaluate_term result will be a default 0, which is unreliable.
    ///
    /// Also returns true if the child is a BV application term whose recursive
    /// sub-terms include a missing variable (transitive check via bv_model cache:
    /// if the application term itself IS in the cache, the cache value is reliable
    /// regardless of whether sub-variables are missing).
    pub(super) fn is_bv_child_missing_from_model(&self, model: &Model, child_id: TermId) -> bool {
        let sort = self.ctx.terms.sort(child_id);
        if !matches!(sort, Sort::BitVec(_)) {
            return false;
        }
        let bv_model = match &model.bv_model {
            Some(m) => m,
            None => return false,
        };
        // If the child itself is in the BV model, its value is reliable.
        if bv_model.values.contains_key(&child_id) {
            return false;
        }
        // Child is not in the BV model. If it's a variable, it's missing.
        matches!(self.ctx.terms.get(child_id), TermData::Var(_, _))
    }

    fn evaluate_bv_comparison_predicate(
        &self,
        model: &Model,
        name: &str,
        args: &[TermId],
    ) -> EvalValue {
        if args.len() != 2 {
            return EvalValue::Unknown;
        }
        let (lhs, lhs_width) = match self.evaluate_term(model, args[0]) {
            EvalValue::BitVec { value, width } => (value, width),
            _ => return EvalValue::Unknown,
        };
        let (rhs, rhs_width) = match self.evaluate_term(model, args[1]) {
            EvalValue::BitVec { value, width } => (value, width),
            _ => return EvalValue::Unknown,
        };
        if lhs_width != rhs_width {
            return EvalValue::Unknown;
        }
        let lhs_unsigned = Self::normalize_bv_value(lhs, lhs_width);
        let rhs_unsigned = Self::normalize_bv_value(rhs, rhs_width);
        let result = match name {
            "bvult" => lhs_unsigned < rhs_unsigned,
            "bvule" => lhs_unsigned <= rhs_unsigned,
            "bvugt" => lhs_unsigned > rhs_unsigned,
            "bvuge" => lhs_unsigned >= rhs_unsigned,
            "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
                let lhs_signed = Self::to_signed_bv(&lhs_unsigned, lhs_width);
                let rhs_signed = Self::to_signed_bv(&rhs_unsigned, rhs_width);
                match name {
                    "bvslt" => lhs_signed < rhs_signed,
                    "bvsle" => lhs_signed <= rhs_signed,
                    "bvsgt" => lhs_signed > rhs_signed,
                    "bvsge" => lhs_signed >= rhs_signed,
                    _ => unreachable!(),
                }
            }
            _ => return EvalValue::Unknown,
        };
        EvalValue::Bool(result)
    }

    /// Evaluate a bitvector application term.
    ///
    /// Handles all `bv*`, `concat`, `extract`, `zero_extend`, `sign_extend`,
    /// `rotate_left`, `rotate_right`, `repeat`, `int2bv`, and `bv2nat` operations.
    pub(super) fn evaluate_bv_app(
        &self,
        model: &Model,
        sym: &Symbol,
        name: &str,
        args: &[TermId],
        sort: &Sort,
        term_id: TermId,
    ) -> EvalValue {
        match name {
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
                self.evaluate_bv_comparison_predicate(model, name, args)
            }
            // BitVec addition
            "bvadd" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                let modulus = BigInt::from(1) << width;
                let mut sum = BigInt::zero();
                for &arg in args {
                    match self.evaluate_term(model, arg) {
                        EvalValue::BitVec { value, .. } => {
                            sum = (sum + value) % &modulus;
                        }
                        _ => return self.bv_model_cache_fallback(model, term_id, sort),
                    }
                }
                EvalValue::BitVec { value: sum, width }
            }
            // BitVec subtraction
            "bvsub" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::BitVec { value: a, .. }, EvalValue::BitVec { value: b, .. }) => {
                        let modulus = BigInt::from(1) << width;
                        // Compute (a - b) mod 2^width using modular arithmetic
                        let result = ((a - b) % &modulus + &modulus) % &modulus;
                        EvalValue::BitVec {
                            value: result,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec multiplication
            "bvmul" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                let modulus = BigInt::from(1) << width;
                let mut product = BigInt::one();
                for &arg in args {
                    match self.evaluate_term(model, arg) {
                        EvalValue::BitVec { value, .. } => {
                            product = (product * value) % &modulus;
                        }
                        _ => return self.bv_model_cache_fallback(model, term_id, sort),
                    }
                }
                EvalValue::BitVec {
                    value: product,
                    width,
                }
            }
            // BitVec negation (two's complement)
            "bvneg" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 1 {
                    return EvalValue::Unknown;
                }
                match self.evaluate_term(model, args[0]) {
                    EvalValue::BitVec { value, .. } => {
                        let value = Self::normalize_bv_value(value, width);
                        let modulus = BigInt::from(1) << width;
                        // Two's complement negation: -x = 2^width - x
                        let result = (&modulus - value) % &modulus;
                        EvalValue::BitVec {
                            value: result,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec bitwise AND
            "bvand" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.is_empty() {
                    // All 1s as identity for AND
                    let all_ones = (BigInt::from(1) << width) - 1;
                    return EvalValue::BitVec {
                        value: all_ones,
                        width,
                    };
                }
                let mut result = match self.evaluate_term(model, args[0]) {
                    EvalValue::BitVec { value, .. } => Self::normalize_bv_value(value, width),
                    _ => return self.bv_model_cache_fallback(model, term_id, sort),
                };
                for &arg in &args[1..] {
                    match self.evaluate_term(model, arg) {
                        EvalValue::BitVec { value, .. } => {
                            result &= Self::normalize_bv_value(value, width);
                        }
                        _ => return self.bv_model_cache_fallback(model, term_id, sort),
                    }
                }
                EvalValue::BitVec {
                    value: result,
                    width,
                }
            }
            // BitVec bitwise OR
            "bvor" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                let mut result = BigInt::zero();
                for &arg in args {
                    match self.evaluate_term(model, arg) {
                        EvalValue::BitVec { value, .. } => {
                            result |= Self::normalize_bv_value(value, width);
                        }
                        _ => return self.bv_model_cache_fallback(model, term_id, sort),
                    }
                }
                EvalValue::BitVec {
                    value: result,
                    width,
                }
            }
            // BitVec bitwise XOR
            "bvxor" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                let mut result = BigInt::zero();
                for &arg in args {
                    match self.evaluate_term(model, arg) {
                        EvalValue::BitVec { value, .. } => {
                            result ^= Self::normalize_bv_value(value, width);
                        }
                        _ => return self.bv_model_cache_fallback(model, term_id, sort),
                    }
                }
                EvalValue::BitVec {
                    value: result,
                    width,
                }
            }
            // BitVec bitwise NOT
            "bvnot" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 1 {
                    return EvalValue::Unknown;
                }
                match self.evaluate_term(model, args[0]) {
                    EvalValue::BitVec { value, .. } => {
                        let value = Self::normalize_bv_value(value, width);
                        let mask = (BigInt::from(1) << width) - 1;
                        let result = value ^ mask;
                        EvalValue::BitVec {
                            value: result,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec NAND: ~(a & b)
            "bvnand" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::BitVec { value: a, .. }, EvalValue::BitVec { value: b, .. }) => {
                        let a = Self::normalize_bv_value(a, width);
                        let b = Self::normalize_bv_value(b, width);
                        let mask = (BigInt::from(1) << width) - 1;
                        EvalValue::BitVec {
                            value: (a & b) ^ mask,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec NOR: ~(a | b)
            "bvnor" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::BitVec { value: a, .. }, EvalValue::BitVec { value: b, .. }) => {
                        let a = Self::normalize_bv_value(a, width);
                        let b = Self::normalize_bv_value(b, width);
                        let mask = (BigInt::from(1) << width) - 1;
                        EvalValue::BitVec {
                            value: (a | b) ^ mask,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec XNOR: ~(a ^ b)
            "bvxnor" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::BitVec { value: a, .. }, EvalValue::BitVec { value: b, .. }) => {
                        let a = Self::normalize_bv_value(a, width);
                        let b = Self::normalize_bv_value(b, width);
                        let mask = (BigInt::from(1) << width) - 1;
                        EvalValue::BitVec {
                            value: (a ^ b) ^ mask,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec shift left
            "bvshl" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::BitVec { value: a, .. }, EvalValue::BitVec { value: b, .. }) => {
                        let a = Self::normalize_bv_value(a, width);
                        let result = match Self::bv_shift_amount(&b, width) {
                            None => BigInt::zero(),
                            Some(shift) => {
                                let modulus = BigInt::from(1) << width;
                                (a << shift) % modulus
                            }
                        };
                        EvalValue::BitVec {
                            value: result,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec logical shift right
            "bvlshr" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::BitVec { value: a, .. }, EvalValue::BitVec { value: b, .. }) => {
                        let a = Self::normalize_bv_value(a, width);
                        let result = match Self::bv_shift_amount(&b, width) {
                            None => BigInt::zero(),
                            Some(shift) => &a >> shift,
                        };
                        EvalValue::BitVec {
                            value: result,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec arithmetic shift right
            "bvashr" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::BitVec { value: a, .. }, EvalValue::BitVec { value: b, .. }) => {
                        let a_norm = Self::normalize_bv_value(a, width);
                        let signed = Self::to_signed_bv(&a_norm, width);
                        let result = match Self::bv_shift_amount(&b, width) {
                            None => {
                                if signed.is_negative() {
                                    (BigInt::from(1) << width) - 1
                                } else {
                                    BigInt::zero()
                                }
                            }
                            Some(shift) => {
                                let shifted = &signed >> shift;
                                Self::normalize_bv_value(shifted, width)
                            }
                        };
                        EvalValue::BitVec {
                            value: result,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec unsigned division
            "bvudiv" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::BitVec { value: a, .. }, EvalValue::BitVec { value: b, .. }) => {
                        let a = Self::normalize_bv_value(a, width);
                        let b = Self::normalize_bv_value(b, width);
                        let result = if b.is_zero() {
                            // SMT-LIB: bvudiv by zero = all 1s
                            (BigInt::from(1) << width) - 1
                        } else {
                            &a / &b
                        };
                        EvalValue::BitVec {
                            value: result,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec unsigned remainder
            "bvurem" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::BitVec { value: a, .. }, EvalValue::BitVec { value: b, .. }) => {
                        let a = Self::normalize_bv_value(a, width);
                        let b = Self::normalize_bv_value(b, width);
                        let result = if b.is_zero() {
                            // SMT-LIB: bvurem by zero = dividend
                            a
                        } else {
                            &a % &b
                        };
                        EvalValue::BitVec {
                            value: result,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec signed division (SMT-LIB semantics)
            "bvsdiv" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::BitVec { value: a, .. }, EvalValue::BitVec { value: b, .. }) => {
                        let a = Self::normalize_bv_value(a, width);
                        let b = Self::normalize_bv_value(b, width);
                        let result = if b.is_zero() {
                            // SMT-LIB: bvsdiv by zero is unspecified;
                            // follow Z3 convention: all 1s if dividend >= 0, 1 if < 0
                            let sa = Self::to_signed_bv(&a, width);
                            if sa >= BigInt::zero() {
                                (BigInt::from(1) << width) - 1 // -1 unsigned
                            } else {
                                BigInt::one() // 1
                            }
                        } else {
                            let sa = Self::to_signed_bv(&a, width);
                            let sb = Self::to_signed_bv(&b, width);
                            // Truncation toward zero (Rust semantics match SMT-LIB)
                            let q = &sa / &sb;
                            Self::normalize_bv_value(q, width)
                        };
                        EvalValue::BitVec {
                            value: result,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec signed remainder (sign follows dividend)
            "bvsrem" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::BitVec { value: a, .. }, EvalValue::BitVec { value: b, .. }) => {
                        let a = Self::normalize_bv_value(a, width);
                        let b = Self::normalize_bv_value(b, width);
                        let result = if b.is_zero() {
                            // SMT-LIB: bvsrem by zero = dividend
                            a
                        } else {
                            let sa = Self::to_signed_bv(&a, width);
                            let sb = Self::to_signed_bv(&b, width);
                            // Rust % has sign follow dividend (matches SMT-LIB bvsrem)
                            let r = &sa % &sb;
                            Self::normalize_bv_value(r, width)
                        };
                        EvalValue::BitVec {
                            value: result,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // BitVec signed modulo (sign follows divisor)
            "bvsmod" => {
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                let width = bv.width;
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::BitVec { value: a, .. }, EvalValue::BitVec { value: b, .. }) => {
                        let a = Self::normalize_bv_value(a, width);
                        let b = Self::normalize_bv_value(b, width);
                        let result = if b.is_zero() {
                            // SMT-LIB: bvsmod by zero = dividend
                            a
                        } else {
                            let sa = Self::to_signed_bv(&a, width);
                            let sb = Self::to_signed_bv(&b, width);
                            // bvsmod: result has sign of divisor
                            let r = &sa % &sb;
                            let r = if r.is_zero() || (r.sign() == sb.sign()) {
                                r
                            } else {
                                r + &sb
                            };
                            Self::normalize_bv_value(r, width)
                        };
                        EvalValue::BitVec {
                            value: result,
                            width,
                        }
                    }
                    _ => self.bv_model_cache_fallback(model, term_id, sort),
                }
            }
            // Structural BV operations delegated to eval_bv_structural.rs:
            // concat, extract, zero_extend, sign_extend, rotate_left,
            // rotate_right, repeat, int2bv, bv2nat, bvcomp.
            _ => {
                if let Some(result) =
                    self.evaluate_bv_structural(model, sym, name, args, sort, term_id)
                {
                    return result;
                }
                EvalValue::Unknown
            }
        }
    }
}
