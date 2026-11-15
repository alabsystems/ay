// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector extraction and reduction to the low slice.

use super::*;

impl TermStore {
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

        if let Some(result) =
            self.try_bvextract_application_fold(high, low, arg, src_width, result_width)
        {
            return result;
        }

        self.intern(
            TermData::App(Symbol::indexed("extract", vec![high, low]), vec![arg]),
            Sort::bitvec(result_width),
        )
    }

    fn try_bvextract_application_fold(
        &mut self,
        high: u32,
        low: u32,
        arg: TermId,
        src_width: u32,
        result_width: u32,
    ) -> Option<TermId> {
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
                            return Some(self.mk_bvextract(high, low, b));
                        } else if low >= w_b {
                            // Case 2: entirely within a (high part)
                            return Some(self.mk_bvextract(high - w_b, low - w_b, a));
                        } else {
                            // Case 3: crosses boundary
                            // low < w_b AND high >= w_b
                            let high_part = self.mk_bvextract(high - w_b, 0, a);
                            let low_part = self.mk_bvextract(w_b - 1, low, b);
                            return Some(self.mk_bvconcat(vec![high_part, low_part]));
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
                        return Some(self.mk_bvextract(high, low, inner));
                    }
                    if low >= inner_width {
                        return Some(self.mk_bitvec(BigInt::zero(), result_width));
                    }

                    let zero_width = high - inner_width + 1;
                    let zero_bits = self.mk_bitvec(BigInt::zero(), zero_width);
                    let low_part = self.mk_bvextract(inner_width - 1, low, inner);
                    return Some(self.mk_bvconcat(vec![zero_bits, low_part]));
                }
            }
            // extract(h,l, extract(h2,l2,x)) -> extract(l2+h,l2+l,x)
            TermData::App(Symbol::Indexed(name, indices), extract_args)
                if name == "extract" && indices.len() == 2 && extract_args.len() == 1 =>
            {
                let inner = extract_args[0];
                return Some(self.mk_bvextract(indices[1] + high, indices[1] + low, inner));
            }
            other => {
                return self.try_bvextract_low_arithmetic(high, low, src_width, result_width, other)
            }
        }
        None
    }

    fn try_bvextract_low_arithmetic(
        &mut self,
        high: u32,
        low: u32,
        src_width: u32,
        result_width: u32,
        data: TermData,
    ) -> Option<TermId> {
        match data {
            // Reduction modulo 2^w commutes with addition. Narrow a proper
            // low slice before bit-blasting, including extended Wasm addresses.
            // A slice with low > 0 cannot use this rule: carry from the bits
            // below the slice still contributes to its value.
            TermData::App(Symbol::Named(name), add_args)
                if name == "bvadd"
                    && add_args.len() == 2
                    && low == 0
                    && high < src_width
                    && add_args
                        .iter()
                        .all(|&term| self.get_bv_width(term) == Some(src_width)) =>
            {
                let left = self.mk_bvextract(high, 0, add_args[0]);
                let right = self.mk_bvextract(high, 0, add_args[1]);
                return Some(self.mk_bvadd(vec![left, right]));
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
                return Some(self.mk_bvmul(vec![lo_x, lo_y]));
            }
            _ => {}
        }
        None
    }
}
