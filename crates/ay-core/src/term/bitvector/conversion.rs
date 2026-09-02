// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl TermStore {
    /// Convert a bitvector to a non-negative integer (SMT-LIB: bv2nat).
    ///
    /// `bv2nat` interprets the bitvector as an unsigned number in `[0, 2^w)`.
    pub fn mk_bv2nat(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::BitVec(_)),
            "BUG: mk_bv2nat expects BitVec arg, got {:?}",
            self.sort(arg)
        );
        if let Some((v, _w)) = self.get_bitvec(arg) {
            return self.mk_int(v.clone());
        }

        self.intern(TermData::App(Symbol::named("bv2nat"), vec![arg]), Sort::Int)
    }

    /// Convert a bitvector to an integer with optional signed interpretation (Z3: bv2int).
    ///
    /// - `is_signed = false`: Same as `bv2nat`, interprets as unsigned in `[0, 2^w)`.
    /// - `is_signed = true`: Two's complement signed, in `[-2^(w-1), 2^(w-1))`.
    ///
    /// For signed conversion of width `w`:
    /// - If MSB is 0: result = bv2nat(x)
    /// - If MSB is 1: result = bv2nat(x) - 2^w
    ///
    /// This is equivalent to: `ite(bvslt x 0, bv2nat(x) - 2^w, bv2nat(x))`
    pub fn mk_bv2int(&mut self, arg: TermId, is_signed: bool) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::BitVec(_)),
            "BUG: mk_bv2int expects BitVec arg, got {:?}",
            self.sort(arg)
        );
        if !is_signed {
            return self.mk_bv2nat(arg);
        }

        // Signed conversion - reuse to_signed helper for consistency
        if let Some((v, w)) = self.get_bitvec(arg) {
            let result = Self::to_signed(v, w);
            return self.mk_int(result);
        }

        // Symbolic case: ite(bvslt x 0, bv2nat(x) - 2^w, bv2nat(x))
        let Some(width) = self.get_bv_width(arg) else {
            // Graceful fallback when sort is not BitVec (#7933).
            return self.mk_bv2nat(arg);
        };
        let zero = self.mk_bitvec(BigInt::zero(), width);
        let is_neg = self.mk_bvslt(arg, zero);
        let unsigned = self.mk_bv2nat(arg);
        let modulus = BigInt::one() << width;
        let modulus_term = self.mk_int(modulus);
        let signed_neg = self.mk_sub(vec![unsigned, modulus_term]);
        self.mk_ite(is_neg, signed_neg, unsigned)
    }

    /// Convert an integer to a bitvector of fixed width (SMT-LIB: `(_ int2bv w)`).
    ///
    /// Semantics: `int2bv(w, n)` is `n mod 2^w`, represented as a bitvector of width `w`.
    pub fn mk_int2bv(&mut self, width: u32, arg: TermId) -> TermId {
        debug_assert!(
            self.sort(arg) == &Sort::Int,
            "BUG: mk_int2bv expects Int arg, got {:?}",
            self.sort(arg)
        );
        // int2bv(w, bv2nat(x)) = x, when x has width w
        if let TermData::App(Symbol::Named(name), args) = self.get(arg) {
            if name == "bv2nat" {
                if let &[inner] = args.as_slice() {
                    if self.get_bv_width(inner) == Some(width) {
                        return inner;
                    }
                }
            }
        }

        // Constant folding
        if let Some(n) = self.get_int(arg) {
            let modulus = BigInt::one() << width;
            let mut reduced = n.clone() % &modulus;
            if reduced.is_negative() {
                reduced += &modulus;
            }
            let reduced = Self::bv_mask(&reduced, width);
            return self.mk_bitvec(reduced, width);
        }

        self.intern(
            TermData::App(Symbol::indexed("int2bv", vec![width]), vec![arg]),
            Sort::bitvec(width),
        )
    }
}
