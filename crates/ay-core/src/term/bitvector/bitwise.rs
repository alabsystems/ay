// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl TermStore {
    fn masked_sign_extend_to_zero_extend(
        &mut self,
        candidate: TermId,
        mask: &BigInt,
        width: u32,
    ) -> Option<TermId> {
        let TermData::App(Symbol::Indexed(name, indices), args) = self.get(candidate).clone()
        else {
            return None;
        };
        if name != "sign_extend" || indices.len() != 1 || args.len() != 1 {
            return None;
        }

        let inner = args[0];
        let inner_width = self.get_bv_width(inner)?;
        if inner_width.checked_add(indices[0])? != width {
            return None;
        }
        if mask != &Self::bv_ones(inner_width) {
            return None;
        }

        Some(self.mk_bvzero_extend(indices[0], inner))
    }

    /// Create bitvector bitwise AND with constant folding and simplifications
    ///
    /// Simplifications:
    /// - Constant folding: bvand(#xFF, #x0F) → #x0F
    /// - Zero: bvand(x, 0) → 0
    /// - All-ones: bvand(x, -1) → x (where -1 is all bits set)
    /// - Idempotent: bvand(x, x) → x
    pub fn mk_bvand(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvand", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let zero = BigInt::zero();
        let all_ones = Self::bv_ones(width);

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            return self.mk_bitvec(v1 & v2, w1);
        }

        // Zero annihilator: x & 0 = 0
        if let Some((v, _)) = self.get_bitvec(b) {
            let v = v.clone();
            if v == zero {
                return self.mk_bitvec(zero, width);
            }
            // Identity: x & all_ones = x
            if v == all_ones {
                return a;
            }
            if let Some(result) = self.masked_sign_extend_to_zero_extend(a, &v, width) {
                return result;
            }
        }
        if let Some((v, _)) = self.get_bitvec(a) {
            let v = v.clone();
            if v == zero {
                return self.mk_bitvec(zero, width);
            }
            if v == all_ones {
                return b;
            }
            if let Some(result) = self.masked_sign_extend_to_zero_extend(b, &v, width) {
                return result;
            }
        }

        // Idempotent: x & x = x
        if a == b {
            return a;
        }

        self.mk_bv_binary_app("bvand", args, width)
    }

    /// Create bitvector bitwise OR with constant folding and simplifications
    ///
    /// Simplifications:
    /// - Constant folding: bvor(#xF0, #x0F) → #xFF
    /// - Identity: bvor(x, 0) → x
    /// - All-ones: bvor(x, -1) → -1
    /// - Idempotent: bvor(x, x) → x
    pub fn mk_bvor(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvor", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let zero = BigInt::zero();
        let all_ones = Self::bv_ones(width);

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            return self.mk_bitvec(v1 | v2, w1);
        }

        // Identity: x | 0 = x
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v == zero {
                return a;
            }
            // Annihilator: x | all_ones = all_ones
            if *v == all_ones {
                return self.mk_bitvec(all_ones, width);
            }
        }
        if let Some((v, _)) = self.get_bitvec(a) {
            if *v == zero {
                return b;
            }
            if *v == all_ones {
                return self.mk_bitvec(all_ones, width);
            }
        }

        // Idempotent: x | x = x
        if a == b {
            return a;
        }

        self.mk_bv_binary_app("bvor", args, width)
    }

    /// Create bitvector bitwise XOR with constant folding and simplifications
    ///
    /// Simplifications:
    /// - Constant folding: bvxor(#xF0, #x0F) → #xFF
    /// - Identity: bvxor(x, 0) → x
    /// - Self-XOR: bvxor(x, x) → 0
    pub fn mk_bvxor(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvxor", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let zero = BigInt::zero();

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            return self.mk_bitvec(v1 ^ v2, w1);
        }

        // Identity: x ^ 0 = x
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v == zero {
                return a;
            }
        }
        if let Some((v, _)) = self.get_bitvec(a) {
            if *v == zero {
                return b;
            }
        }

        // Self-XOR: x ^ x = 0
        if a == b {
            return self.mk_bitvec(zero, width);
        }

        self.mk_bv_binary_app("bvxor", args, width)
    }

    /// Create bitvector bitwise NAND with simplifications.
    ///
    /// Defined as: bvnand(a, b) = bvnot(bvand(a, b))
    pub fn mk_bvnand(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, _, _) = match self.prepare_bv_binary_op("bvnand", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let and_term = self.mk_bvand(vec![a, b]);
        self.mk_bvnot(and_term)
    }

    /// Create bitvector bitwise NOR with simplifications.
    ///
    /// Defined as: bvnor(a, b) = bvnot(bvor(a, b))
    pub fn mk_bvnor(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, _, _) = match self.prepare_bv_binary_op("bvnor", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let or_term = self.mk_bvor(vec![a, b]);
        self.mk_bvnot(or_term)
    }

    /// Create bitvector bitwise XNOR with simplifications.
    ///
    /// Defined as: bvxnor(a, b) = bvnot(bvxor(a, b))
    pub fn mk_bvxnor(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, _, _) = match self.prepare_bv_binary_op("bvxnor", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let xor_term = self.mk_bvxor(vec![a, b]);
        self.mk_bvnot(xor_term)
    }

    /// Create bitvector bitwise NOT with constant folding and simplifications
    ///
    /// Simplifications:
    /// - Constant folding: bvnot(#xFF) → #x00 (for 8-bit)
    /// - Double negation: bvnot(bvnot(x)) → x
    pub fn mk_bvnot(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::BitVec(_)),
            "BUG: mk_bvnot expects BitVec, got {:?}",
            self.sort(arg)
        );
        let Some(width) = self.get_bv_width(arg) else {
            // Graceful fallback: preserve the input sort (#7933).
            let sort = self.sort(arg).clone();
            return self.intern(TermData::App(Symbol::named("bvnot"), vec![arg]), sort);
        };
        let all_ones = Self::bv_ones(width);

        // Constant folding
        if let Some((v, w)) = self.get_bitvec(arg) {
            return self.mk_bitvec(&all_ones ^ v, w);
        }

        // Double negation: bvnot(bvnot(x)) → x
        if let TermData::App(sym, args) = self.get(arg) {
            if sym.name() == "bvnot" && args.len() == 1 {
                return args[0];
            }
        }

        self.intern(
            TermData::App(Symbol::named("bvnot"), vec![arg]),
            Sort::bitvec(width),
        )
    }

    /// Create bitvector negation with constant folding and simplifications
    ///
    /// bvneg(x) = -x (two's complement)
    ///
    /// Simplifications:
    /// - Constant folding: bvneg(#x01) → #xFF (for 8-bit)
    /// - Double negation: bvneg(bvneg(x)) → x
    /// - Zero: bvneg(0) → 0
    pub fn mk_bvneg(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::BitVec(_)),
            "BUG: mk_bvneg expects BitVec, got {:?}",
            self.sort(arg)
        );
        let Some(width) = self.get_bv_width(arg) else {
            // Graceful fallback: preserve the input sort (#7933).
            let sort = self.sort(arg).clone();
            return self.intern(TermData::App(Symbol::named("bvneg"), vec![arg]), sort);
        };
        let modulus = BigInt::one() << width;

        // Constant folding (two's complement: -x = ~x + 1 = (2^n - x) mod 2^n)
        if let Some((v, w)) = self.get_bitvec(arg) {
            if v.is_zero() {
                return arg;
            }
            let result = Self::bv_mask(&(&modulus - v), w);
            return self.mk_bitvec(result, w);
        }

        // Double negation: bvneg(bvneg(x)) → x
        if let TermData::App(sym, args) = self.get(arg) {
            if sym.name() == "bvneg" && args.len() == 1 {
                return args[0];
            }
        }

        self.intern(
            TermData::App(Symbol::named("bvneg"), vec![arg]),
            Sort::bitvec(width),
        )
    }
}
