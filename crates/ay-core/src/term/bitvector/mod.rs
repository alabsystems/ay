// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector term constructors for TermStore.
//!
//! Includes bitvector arithmetic, bitwise, shift, comparison, and
//! extract/concat/extend operations with constant folding and simplifications.

mod arithmetic;
mod bitwise;
mod comparison;
mod conversion;
mod division;
mod extract_concat;
mod shift;

use super::*;

impl TermStore {
    /// Helper: extract bitvector constant value and width
    pub(super) fn get_bitvec(&self, id: TermId) -> Option<(&BigInt, u32)> {
        match self.get(id) {
            TermData::Const(Constant::BitVec { value, width }) => Some((value, *width)),
            _ => None,
        }
    }

    /// Helper: get the width of a bitvector term.
    ///
    /// Returns `None` for non-BitVec sorts and for zero-width bitvectors
    /// (which are invalid in SMT-LIB and used as a sentinel for unknown
    /// width in fallback paths). This prevents `width - 1` underflows
    /// in downstream constant-folding and signed-interpretation code (#7933).
    fn get_bv_width(&self, id: TermId) -> Option<u32> {
        match self.sort(id) {
            Sort::BitVec(w) if w.width > 0 => Some(w.width),
            _ => None,
        }
    }

    fn validate_bv_binary_op_args(&self, op_name: &str, args: &[TermId]) {
        debug_assert!(
            args.len() == 2,
            "BUG: {op_name} expects 2 args, got {}",
            args.len()
        );
        debug_assert!(
            args.iter()
                .all(|&arg| matches!(self.sort(arg), Sort::BitVec(_))),
            "BUG: {op_name} expects BitVec args"
        );
        debug_assert!(
            args.windows(2).all(|w| self.sort(w[0]) == self.sort(w[1])),
            "BUG: {op_name} expects same-width BitVec args"
        );
    }

    fn mk_bv_binary_fallback(&mut self, op_name: &'static str, args: Vec<TermId>) -> TermId {
        if let Some(width) = args.first().and_then(|&arg| self.get_bv_width(arg)) {
            return self.mk_bv_binary_app(op_name, args, width);
        }
        // Preserve the first arg's sort when width is unknown (#7933).
        let sort = args
            .first()
            .map(|&a| self.sort(a).clone())
            .unwrap_or(Sort::Bool);
        self.intern(TermData::App(Symbol::named(op_name), args), sort)
    }

    fn prepare_bv_binary_op(
        &mut self,
        op_name: &'static str,
        args: Vec<TermId>,
    ) -> Result<(TermId, TermId, u32, Vec<TermId>), TermId> {
        self.validate_bv_binary_op_args(op_name, &args);
        if args.len() != 2 {
            return Err(self.mk_bv_binary_fallback(op_name, args));
        }
        let (a, b) = (args[0], args[1]);
        let Some(width) = self.get_bv_width(a) else {
            return Err(self.mk_bv_binary_fallback(op_name, args));
        };
        Ok((a, b, width, args))
    }

    fn mk_bv_binary_app(&mut self, op_name: &'static str, args: Vec<TermId>, width: u32) -> TermId {
        self.intern(
            TermData::App(Symbol::named(op_name), args),
            Sort::bitvec(width),
        )
    }

    /// All-ones mask for the given bit width: `2^width - 1`.
    fn bv_ones(width: u32) -> BigInt {
        (BigInt::one() << width) - 1
    }

    /// Helper: mask value to width bits (ensure value is in range [0, 2^width))
    fn bv_mask(value: &BigInt, width: u32) -> BigInt {
        value & Self::bv_ones(width)
    }

    /// If `value` is a power of 2, return its log2. Otherwise return None.
    /// Only valid for positive values. Returns None for zero or negative.
    fn bv_log2_exact(value: &BigInt) -> Option<u32> {
        if value.sign() != num_bigint::Sign::Plus {
            return None;
        }
        // A positive integer is a power of 2 iff (v & (v - 1)) == 0
        let v_minus_one = value - BigInt::one();
        if (value & &v_minus_one) != BigInt::zero() {
            return None;
        }
        // Count trailing zeros to get the exponent
        // For a power of 2, the bit length minus 1 gives the exponent
        Some((value.bits() - 1) as u32)
    }
}
