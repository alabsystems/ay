// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl TermStore {
    fn bv_extract_range(&self, term: TermId) -> Option<(TermId, u32, u32)> {
        let TermData::App(Symbol::Indexed(name, indices), args) = self.get(term) else {
            return None;
        };
        if name != "extract" || indices.len() != 2 || args.len() != 1 || indices[0] < indices[1] {
            return None;
        }
        Some((args[0], indices[0], indices[1]))
    }

    /// Extract bits `[high:low]` from a bitvector (SMT-LIB: `(_ extract i j)`)
    ///
    /// Simplifications:
    /// - Constant folding: extract(7,4,#xFF) → #x0F
    /// - Full extract: extract(n-1,0,x) → x (extracting all bits)
    ///
    /// The result width is high - low + 1.
    pub fn mk_bvextract(&mut self, high: u32, low: u32, arg: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::BitVec(_)),
            "BUG: mk_bvextract expects BitVec arg, got {:?}",
            self.sort(arg)
        );
        // Validate indices: high >= low
        if high < low {
            // Invalid extract, return the term as-is with generic sort
            return self.intern(
                TermData::App(Symbol::indexed("extract", vec![high, low]), vec![arg]),
                Sort::bitvec(1),
            );
        }

        let result_width = high - low + 1;
        let Some(src_width) = self.get_bv_width(arg) else {
            return self.intern(
                TermData::App(Symbol::indexed("extract", vec![high, low]), vec![arg]),
                Sort::bitvec(result_width),
            );
        };

        // Full extract simplification: extract(n-1,0,x) → x
        if high == src_width - 1 && low == 0 {
            return arg;
        }

        // Constant folding
        if let Some((val, _)) = self.get_bitvec(arg) {
            let shifted = val >> low;
            let result = Self::bv_mask(&shifted, result_width);
            return self.mk_bitvec(result, result_width);
        }

        match self.get(arg).clone() {
            // Extract over concat simplification
            // For extract[hi:lo](concat(a, b)) where |b| = w_b:
            // - If hi < w_b: extract from b only
            // - If lo >= w_b: extract from a with adjusted indices
            // - If crossing boundary: split into concat of two extracts
            TermData::App(Symbol::Named(name), concat_args)
                if name == "concat" && concat_args.len() == 2 =>
            {
                let a = concat_args[0]; // high part
                let b = concat_args[1]; // low part

                if let Some(w_b) = self.get_bv_width(b) {
                    if w_b > 0 {
                        if high < w_b {
                            // Case 1: entirely within b (low part)
                            return self.mk_bvextract(high, low, b);
                        } else if low >= w_b {
                            // Case 2: entirely within a (high part)
                            return self.mk_bvextract(high - w_b, low - w_b, a);
                        } else {
                            // Case 3: crosses boundary
                            // low < w_b AND high >= w_b
                            let high_part = self.mk_bvextract(high - w_b, 0, a);
                            let low_part = self.mk_bvextract(w_b - 1, low, b);
                            return self.mk_bvconcat(vec![high_part, low_part]);
                        }
                    }
                }
            }
            // extract(h,l, zero_extend(k, x)) is either an extract from x, an
            // all-zero slice from the extension, or a concat of those pieces.
            TermData::App(Symbol::Indexed(name, indices), ext_args)
                if name == "zero_extend" && indices.len() == 1 && ext_args.len() == 1 =>
            {
                let inner = ext_args[0];
                if let Some(inner_width) = self.get_bv_width(inner) {
                    if high < inner_width {
                        return self.mk_bvextract(high, low, inner);
                    }
                    if low >= inner_width {
                        return self.mk_bitvec(BigInt::zero(), result_width);
                    }

                    let zero_width = high - inner_width + 1;
                    let zero_bits = self.mk_bitvec(BigInt::zero(), zero_width);
                    let low_part = self.mk_bvextract(inner_width - 1, low, inner);
                    return self.mk_bvconcat(vec![zero_bits, low_part]);
                }
            }
            // extract(h,l, extract(h2,l2,x)) -> extract(l2+h,l2+l,x)
            TermData::App(Symbol::Indexed(name, indices), extract_args)
                if name == "extract" && indices.len() == 2 && extract_args.len() == 1 =>
            {
                let inner = extract_args[0];
                return self.mk_bvextract(indices[1] + high, indices[1] + low, inner);
            }
            // extract(w-1, 0, bvmul(X, Y)) -> bvmul(extract(w-1,0,X), extract(w-1,0,Y))
            //
            // The low w bits of a product depend only on the low w bits of the
            // operands: (X*Y) mod 2^w == ((X mod 2^w) * (Y mod 2^w)) mod 2^w.
            // The narrower multiply is strictly cheaper to bit-blast, and
            // combined with extract-over-{zero,sign}_extend this collapses the
            // truncated-multiply identity `(zext a * zext b)[w-1:0] == a*b`
            // (the x86 Umul_I32/I64 low-half lowering proof) to `a*b == a*b`.
            // We reach this arm only for a proper sub-extract (the full extract
            // extract(n-1,0,x)->x is handled above), so result_width < src_width.
            TermData::App(Symbol::Named(name), mul_args)
                if name == "bvmul" && mul_args.len() == 2 && low == 0 =>
            {
                let lo_x = self.mk_bvextract(result_width - 1, 0, mul_args[0]);
                let lo_y = self.mk_bvextract(result_width - 1, 0, mul_args[1]);
                return self.mk_bvmul(vec![lo_x, lo_y]);
            }
            _ => {}
        }

        self.intern(
            TermData::App(Symbol::indexed("extract", vec![high, low]), vec![arg]),
            Sort::bitvec(result_width),
        )
    }

    /// Concatenate two bitvectors (SMT-LIB: concat)
    ///
    /// Result width is the sum of input widths. The first argument becomes
    /// the high bits, the second becomes the low bits.
    ///
    /// Simplifications:
    /// - Constant folding: concat(#x0F, #xF0) → #x0FF0
    pub fn mk_bvconcat(&mut self, args: Vec<TermId>) -> TermId {
        debug_assert!(
            args.iter()
                .all(|&a| matches!(self.sort(a), Sort::BitVec(_))),
            "BUG: mk_bvconcat expects all BitVec args"
        );
        if args.len() != 2 {
            // concat is binary
            let width = args.iter().filter_map(|&a| self.get_bv_width(a)).sum();
            return self.intern(
                TermData::App(Symbol::named("concat"), args),
                Sort::bitvec(width),
            );
        }

        let (high, low) = (args[0], args[1]);
        let (Some(high_width), Some(low_width)) = (self.get_bv_width(high), self.get_bv_width(low))
        else {
            let width = self.get_bv_width(high).unwrap_or(0) + self.get_bv_width(low).unwrap_or(0);
            return self.intern(
                TermData::App(Symbol::named("concat"), args),
                Sort::bitvec(width),
            );
        };
        let result_width = high_width + low_width;

        // Constant folding
        if let (Some((v_high, _)), Some((v_low, _))) = (self.get_bitvec(high), self.get_bitvec(low))
        {
            let result = (v_high << low_width) | v_low;
            return self.mk_bitvec(result, result_width);
        }

        // concat(0_k, x) -> zero_extend(k, x). This canonicalizes common
        // high-half carry expressions before BV bit-blasting.
        if let Some((v_high, _)) = self.get_bitvec(high) {
            if v_high.is_zero() {
                return self.mk_bvzero_extend(high_width, low);
            }
        }

        // Adjacent extracts from the same source combine into one extract:
        // concat(extract(h,m,x), extract(m-1,l,x)) -> extract(h,l,x).
        if let (Some((high_source, high_hi, high_lo)), Some((low_source, low_hi, low_lo))) =
            (self.bv_extract_range(high), self.bv_extract_range(low))
        {
            if high_source == low_source && low_hi.checked_add(1) == Some(high_lo) {
                return self.mk_bvextract(high_hi, low_lo, high_source);
            }
        }

        self.intern(
            TermData::App(Symbol::named("concat"), args),
            Sort::bitvec(result_width),
        )
    }

    /// Zero-extend a bitvector by i bits (SMT-LIB: (_ zero_extend i))
    ///
    /// Adds i zero bits to the most significant end.
    ///
    /// Simplifications:
    /// - Zero extension by 0: zero_extend(0,x) → x
    /// - Constant folding: zero_extend(4,#x0F) → #x00F
    pub fn mk_bvzero_extend(&mut self, i: u32, arg: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::BitVec(_)),
            "BUG: mk_bvzero_extend expects BitVec arg, got {:?}",
            self.sort(arg)
        );
        let Some(src_width) = self.get_bv_width(arg) else {
            // Graceful fallback: construct the term without simplification (#7933).
            // When extending by 0 bits, preserve the input sort; otherwise
            // use the extension amount as best-effort width.
            let sort = if i == 0 {
                self.sort(arg).clone()
            } else {
                Sort::bitvec(i)
            };
            return self.intern(
                TermData::App(Symbol::indexed("zero_extend", vec![i]), vec![arg]),
                sort,
            );
        };
        let result_width = src_width + i;

        // Zero extension by 0 bits is identity
        if i == 0 {
            return arg;
        }

        // Constant folding (value stays the same, just wider representation)
        if let Some((val, _)) = self.get_bitvec(arg) {
            return self.mk_bitvec(val.clone(), result_width);
        }

        // zero_extend(i, zero_extend(j, x)) -> zero_extend(i + j, x)
        if let TermData::App(Symbol::Indexed(name, indices), ext_args) = self.get(arg).clone() {
            if name == "zero_extend" && indices.len() == 1 && ext_args.len() == 1 {
                let inner = ext_args[0];
                if self.get_bv_width(inner).is_some() {
                    if let Some(total_i) = i.checked_add(indices[0]) {
                        return self.mk_bvzero_extend(total_i, inner);
                    }
                }
            }
        }

        self.intern(
            TermData::App(Symbol::indexed("zero_extend", vec![i]), vec![arg]),
            Sort::bitvec(result_width),
        )
    }

    /// Sign-extend a bitvector by i bits (SMT-LIB: (_ sign_extend i))
    ///
    /// Adds i copies of the sign bit (MSB) to the most significant end.
    ///
    /// Simplifications:
    /// - Sign extension by 0: sign_extend(0,x) → x
    /// - Constant folding: sign_extend(4,#x8F) → #xFF8F (for 8-bit input)
    pub fn mk_bvsign_extend(&mut self, i: u32, arg: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::BitVec(_)),
            "BUG: mk_bvsign_extend expects BitVec arg, got {:?}",
            self.sort(arg)
        );
        let Some(src_width) = self.get_bv_width(arg) else {
            // Graceful fallback (#7933): preserve input sort when extending
            // by 0 bits; otherwise use extension amount as best-effort width.
            let sort = if i == 0 {
                self.sort(arg).clone()
            } else {
                Sort::bitvec(i)
            };
            return self.intern(
                TermData::App(Symbol::indexed("sign_extend", vec![i]), vec![arg]),
                sort,
            );
        };
        let result_width = src_width + i;

        // Sign extension by 0 bits is identity
        if i == 0 {
            return arg;
        }

        // Constant folding
        if let Some((val, w)) = self.get_bitvec(arg) {
            let sign_bit = (val >> (w - 1)) & BigInt::one();
            let result = if sign_bit.is_zero() {
                // Positive: same as zero extension
                val.clone()
            } else {
                // Negative: set all the new high bits to 1
                let extension_mask = Self::bv_ones(i) << w;
                val | &extension_mask
            };
            return self.mk_bitvec(result, result_width);
        }

        self.intern(
            TermData::App(Symbol::indexed("sign_extend", vec![i]), vec![arg]),
            Sort::bitvec(result_width),
        )
    }

    /// Rotate left by i bits (SMT-LIB: (_ rotate_left i))
    ///
    /// Rotates the bitvector left by i bit positions.
    /// Bits shifted out the left are shifted in on the right.
    ///
    /// Simplifications:
    /// - Rotation by 0: rotate_left(0,x) → x
    /// - Rotation by width: rotate_left(n,x) → x (where n = width)
    /// - Constant folding
    pub fn mk_bvrotate_left(&mut self, i: u32, arg: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::BitVec(_)),
            "BUG: mk_bvrotate_left expects BitVec arg, got {:?}",
            self.sort(arg)
        );
        let Some(width) = self.get_bv_width(arg) else {
            // Width unknown: preserve the input sort so downstream ops
            // never see a zero-width bitvector (#7933).
            let sort = self.sort(arg).clone();
            return self.intern(
                TermData::App(Symbol::indexed("rotate_left", vec![i]), vec![arg]),
                sort,
            );
        };

        // Normalize rotation amount to [0, width)
        let rotation = if width > 0 { i % width } else { 0 };

        // Rotation by 0 is identity
        if rotation == 0 {
            return arg;
        }

        // Constant folding
        if let Some((val, w)) = self.get_bitvec(arg) {
            let mask = Self::bv_ones(w);
            let left_part = (val << rotation) & &mask;
            let right_part = val >> (w - rotation);
            let result = left_part | right_part;
            return self.mk_bitvec(result, w);
        }

        self.intern(
            TermData::App(Symbol::indexed("rotate_left", vec![i]), vec![arg]),
            Sort::bitvec(width),
        )
    }

    /// Rotate right by i bits (SMT-LIB: (_ rotate_right i))
    ///
    /// Rotates the bitvector right by i bit positions.
    /// Bits shifted out the right are shifted in on the left.
    ///
    /// Simplifications:
    /// - Rotation by 0: rotate_right(0,x) → x
    /// - Rotation by width: rotate_right(n,x) → x (where n = width)
    /// - Constant folding
    pub fn mk_bvrotate_right(&mut self, i: u32, arg: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::BitVec(_)),
            "BUG: mk_bvrotate_right expects BitVec arg, got {:?}",
            self.sort(arg)
        );
        let Some(width) = self.get_bv_width(arg) else {
            // Width unknown: preserve the input sort (#7933).
            let sort = self.sort(arg).clone();
            return self.intern(
                TermData::App(Symbol::indexed("rotate_right", vec![i]), vec![arg]),
                sort,
            );
        };

        // Normalize rotation amount to [0, width)
        let rotation = if width > 0 { i % width } else { 0 };

        // Rotation by 0 is identity
        if rotation == 0 {
            return arg;
        }

        // Constant folding
        if let Some((val, w)) = self.get_bitvec(arg) {
            let mask = Self::bv_ones(w);
            let right_part = val >> rotation;
            let left_part = (val << (w - rotation)) & &mask;
            let result = left_part | right_part;
            return self.mk_bitvec(result, w);
        }

        self.intern(
            TermData::App(Symbol::indexed("rotate_right", vec![i]), vec![arg]),
            Sort::bitvec(width),
        )
    }

    /// Repeat a bitvector i times (SMT-LIB: (_ repeat i))
    ///
    /// Concatenates i copies of the bitvector.
    /// Result width is original width * i.
    ///
    /// Simplifications:
    /// - Repeat 1: repeat(1,x) → x
    /// - Constant folding
    pub fn mk_bvrepeat(&mut self, i: u32, arg: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::BitVec(_)),
            "BUG: mk_bvrepeat expects BitVec arg, got {:?}",
            self.sort(arg)
        );
        let Some(src_width) = self.get_bv_width(arg) else {
            // Width unknown: preserve the input sort (#7933).
            let sort = self.sort(arg).clone();
            return self.intern(
                TermData::App(Symbol::indexed("repeat", vec![i]), vec![arg]),
                sort,
            );
        };
        let result_width = src_width * i;

        // Repeat 1 is identity
        if i == 1 {
            return arg;
        }

        // Repeat 0 is not valid in SMT-LIB, but handle gracefully
        if i == 0 {
            return self.mk_bitvec(BigInt::zero(), 1);
        }

        // Constant folding
        if let Some((val, w)) = self.get_bitvec(arg) {
            let mut result = BigInt::zero();
            for _ in 0..i {
                result = (result << w) | val;
            }
            return self.mk_bitvec(result, result_width);
        }

        self.intern(
            TermData::App(Symbol::indexed("repeat", vec![i]), vec![arg]),
            Sort::bitvec(result_width),
        )
    }
}
