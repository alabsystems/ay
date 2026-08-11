// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use super::{Context, ElaborateError, Result};

impl Context {
    /// Reject width-incompatible operands for width-sensitive BV operations.
    ///
    /// Width-sensitive ops (bvadd, bvshl, bvult, ...) require all operands to
    /// be BitVecs of the *same* width. SMT-LIB literals like `#x1` are only
    /// 4 bits wide, so `(bvadd x #x1)` with an 8-bit `x` is ill-typed. z3
    /// rejects this with a clean sort-mismatch error; without this guard the
    /// ill-typed term reaches the core builders and trips a debug_assert
    /// ("BUG: bvadd expects same-width BitVec args"), crashing with exit 101.
    ///
    /// Returning a `SortMismatch` here surfaces a graceful `(error ...)`
    /// instead of a panic. Width-coercing equality (`=`/`distinct`) is handled
    /// separately via `maybe_coerce_bv_widths` and intentionally NOT routed
    /// through this check, so well-typed input keeps its existing verdict.
    fn expect_bv_same_width(&self, name: &str, args: &[TermId]) -> Result<()> {
        let mut expected: Option<u32> = None;
        for &arg in args {
            let width = self.expect_bv_operand_width(name, arg)?;
            match expected {
                None => expected = Some(width),
                Some(w) if w == width => {}
                Some(w) => {
                    return Err(ElaborateError::SortMismatch {
                        expected: format!("(_ BitVec {w})"),
                        actual: format!(
                            "(_ BitVec {width}): {name} requires same-width BitVec operands"
                        ),
                    });
                }
            }
        }
        Ok(())
    }

    fn check_concat_result_width(&self, args: &[TermId]) -> Result<()> {
        let mut total = 0u32;
        for &arg in args {
            let width = self.expect_bv_operand_width("concat", arg)?;
            total = total.checked_add(width).ok_or_else(|| {
                ElaborateError::InvalidConstant("concat result width overflows".to_string())
            })?;
        }
        Self::checked_bitvector_sort(total).map(|_| ())
    }

    pub(super) fn try_elaborate_bitvector_app(
        &mut self,
        name: &str,
        arg_ids: &[TermId],
    ) -> Result<Option<TermId>> {
        match name {
            "bvadd" | "bvmul" | "bvand" | "bvor" | "bvxor" | "concat" => {
                if arg_ids.len() < 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires at least 2 arguments"
                    )));
                }
                // `concat` joins BitVecs of differing widths by design and is
                // NOT width-sensitive; all the others require equal widths.
                if name != "concat" {
                    self.expect_bv_same_width(name, arg_ids)?;
                } else {
                    self.check_concat_result_width(arg_ids)?;
                }
                let mut result = match name {
                    "bvadd" => self.terms.mk_bvadd(vec![arg_ids[0], arg_ids[1]]),
                    "bvmul" => self.terms.mk_bvmul(vec![arg_ids[0], arg_ids[1]]),
                    "bvand" => self.terms.mk_bvand(vec![arg_ids[0], arg_ids[1]]),
                    "bvor" => self.terms.mk_bvor(vec![arg_ids[0], arg_ids[1]]),
                    "bvxor" => self.terms.mk_bvxor(vec![arg_ids[0], arg_ids[1]]),
                    _ => self.terms.mk_bvconcat(vec![arg_ids[0], arg_ids[1]]),
                };
                for &arg in &arg_ids[2..] {
                    result = match name {
                        "bvadd" => self.terms.mk_bvadd(vec![result, arg]),
                        "bvmul" => self.terms.mk_bvmul(vec![result, arg]),
                        "bvand" => self.terms.mk_bvand(vec![result, arg]),
                        "bvor" => self.terms.mk_bvor(vec![result, arg]),
                        "bvxor" => self.terms.mk_bvxor(vec![result, arg]),
                        _ => self.terms.mk_bvconcat(vec![result, arg]),
                    };
                }
                Ok(Some(result))
            }
            "bvsub" | "bvnand" | "bvnor" | "bvxnor" | "bvshl" | "bvlshr" | "bvashr" | "bvudiv"
            | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                self.expect_bv_same_width(name, arg_ids)?;
                Ok(Some(match name {
                    "bvsub" => self.terms.mk_bvsub(arg_ids.to_vec()),
                    "bvnand" => self.terms.mk_bvnand(arg_ids.to_vec()),
                    "bvnor" => self.terms.mk_bvnor(arg_ids.to_vec()),
                    "bvxnor" => self.terms.mk_bvxnor(arg_ids.to_vec()),
                    "bvshl" => self.terms.mk_bvshl(arg_ids.to_vec()),
                    "bvlshr" => self.terms.mk_bvlshr(arg_ids.to_vec()),
                    "bvashr" => self.terms.mk_bvashr(arg_ids.to_vec()),
                    "bvudiv" => self.terms.mk_bvudiv(arg_ids.to_vec()),
                    "bvurem" => self.terms.mk_bvurem(arg_ids.to_vec()),
                    "bvsdiv" => self.terms.mk_bvsdiv(arg_ids.to_vec()),
                    "bvsrem" => self.terms.mk_bvsrem(arg_ids.to_vec()),
                    _ => self.terms.mk_bvsmod(arg_ids.to_vec()),
                }))
            }
            // `bv2int` (z3 spelling) and `ubv_to_int` (SMT-LIB 2.7 spelling) are
            // the UNSIGNED bit-vector-to-integer conversion — identical to the
            // standard `bv2nat`. Alias them to the same internal term so z3 /
            // SMT-LIB-2.7 inputs parse instead of erroring with "unknown
            // constant". `sbv_to_int` (SMT-LIB 2.7) is the SIGNED counterpart and
            // is elaborated CORRECTLY as a signed conversion (NOT aliased to the
            // unsigned `bv2nat`, which would be a wrong answer) — see below.
            "bvnot" | "bvneg" | "bv2nat" | "bv2int" | "ubv_to_int" | "sbv_to_int" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.expect_bv_operand_width(name, arg_ids[0])?;
                Ok(Some(match name {
                    "bvnot" => self.terms.mk_bvnot(arg_ids[0]),
                    "bvneg" => self.terms.mk_bvneg(arg_ids[0]),
                    // Signed BV→Int: sbv_to_int(x) = bv2nat(x) - 2^w when the
                    // sign bit is set, else bv2nat(x). `mk_bv2int(_, true)`
                    // constant-folds ground BVs (0xff -> -1, 0x80 -> -128) and
                    // emits the `ite(bvslt x 0, bv2nat(x) - 2^w, bv2nat(x))`
                    // expansion for symbolic operands — self-contained over
                    // standard ops, verified EXACT against z3.
                    "sbv_to_int" => self.terms.mk_bv2int(arg_ids[0], true),
                    _ => self.terms.mk_bv2nat(arg_ids[0]),
                }))
            }
            "bvcomp" | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt"
            | "bvsge" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                self.expect_bv_same_width(name, arg_ids)?;
                Ok(Some(match name {
                    "bvcomp" => self.terms.mk_bvcomp(arg_ids[0], arg_ids[1]),
                    "bvult" => self.terms.mk_bvult(arg_ids[0], arg_ids[1]),
                    "bvule" => self.terms.mk_bvule(arg_ids[0], arg_ids[1]),
                    "bvugt" => self.terms.mk_bvugt(arg_ids[0], arg_ids[1]),
                    "bvuge" => self.terms.mk_bvuge(arg_ids[0], arg_ids[1]),
                    "bvslt" => self.terms.mk_bvslt(arg_ids[0], arg_ids[1]),
                    "bvsle" => self.terms.mk_bvsle(arg_ids[0], arg_ids[1]),
                    "bvsgt" => self.terms.mk_bvsgt(arg_ids[0], arg_ids[1]),
                    _ => self.terms.mk_bvsge(arg_ids[0], arg_ids[1]),
                }))
            }
            // SMT-LIB BitVec overflow predicates (Bool-sorted). Elaborated to
            // existing BV ops via their standard definitions (each equivalence
            // verified EXACT against z3 over widths 1..=8). Without this AY would
            // hit the `unknown constant` path, drop the assertion, and return a
            // spurious SAT (a wrong answer) instead of a sound verdict.
            "bvnego" | "bvuaddo" | "bvusubo" | "bvsaddo" | "bvssubo" | "bvumulo" | "bvsmulo"
            | "bvsdivo" => {
                let arity = if name == "bvnego" { 1 } else { 2 };
                self.expect_exact_arity(name, arg_ids, arity)?;
                if arity == 2 {
                    self.expect_bv_same_width(name, arg_ids)?;
                }
                let Sort::BitVec(bv) = self.terms.sort(arg_ids[0]).clone() else {
                    return Err(ElaborateError::SortMismatch {
                        expected: "(_ BitVec n)".to_string(),
                        actual: format!("{name} requires BitVec operands"),
                    });
                };
                if matches!(name, "bvumulo" | "bvsmulo") {
                    let expanded_width = bv.width.checked_mul(2).ok_or_else(|| {
                        ElaborateError::InvalidConstant(
                            "multiplication-overflow expansion width overflows".to_string(),
                        )
                    })?;
                    Self::checked_bitvector_sort(expanded_width)?;
                }
                Ok(Some(self.elaborate_bv_overflow(name, arg_ids, bv.width)?))
            }
            // BV reduction ops (z3 / SMT-LIB). Each returns a 1-bit BitVec and
            // desugars to existing ops via its standard definition (bvcomp
            // yields #b1 iff its operands are equal):
            //   bvredand(x) = #b1 iff EVERY bit is set = (bvcomp x 11..1)
            //   bvredor(x)  = #b1 iff ANY  bit is set  = bvnot(bvcomp x 00..0)
            // Without this AY hits the `unknown constant` path and falls closed
            // to `unknown` where z3 decides. Verified EXACT against z3.
            "bvredand" | "bvredor" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                let Sort::BitVec(bv) = self.terms.sort(arg_ids[0]).clone() else {
                    return Err(ElaborateError::SortMismatch {
                        expected: "(_ BitVec n)".to_string(),
                        actual: format!("{name} requires a BitVec operand"),
                    });
                };
                let w = bv.width;
                Ok(Some(if name == "bvredand" {
                    let all_ones = (BigInt::from(1) << w as usize) - BigInt::from(1);
                    let ones = self.terms.mk_bitvec(all_ones, w);
                    self.terms.mk_bvcomp(arg_ids[0], ones)
                } else {
                    let zero = self.terms.mk_bitvec(BigInt::from(0), w);
                    let is_zero = self.terms.mk_bvcomp(arg_ids[0], zero);
                    self.terms.mk_bvnot(is_zero)
                }))
            }
            _ => Ok(None),
        }
    }

    /// Elaborate a BitVec overflow predicate to its standard definition over
    /// existing BV operations (#bv-overflow-predicates). Each formula was
    /// validated to be EXACTLY equivalent to z3's builtin across widths 1..=8.
    fn elaborate_bv_overflow(&mut self, name: &str, args: &[TermId], n: u32) -> Result<TermId> {
        let x = args[0];
        let result = match name {
            // bvnego(x): negation overflows iff x is the signed minimum 1000..0.
            "bvnego" => {
                let smin = self.terms.mk_bitvec(BigInt::from(1) << (n as usize - 1), n);
                self.terms.mk_eq(x, smin)
            }
            // bvuaddo(x,y): unsigned add overflows iff (x +_n y) < x (unsigned).
            "bvuaddo" => {
                let s = self.terms.mk_bvadd(vec![x, args[1]]);
                self.terms.mk_bvult(s, x)
            }
            // bvusubo(x,y): unsigned subtract borrows iff x < y (unsigned).
            "bvusubo" => self.terms.mk_bvult(x, args[1]),
            // bvsaddo(x,y): signed add overflows iff operands share a sign bit and
            // the result's sign bit differs.
            "bvsaddo" => {
                let y = args[1];
                let s = self.terms.mk_bvadd(vec![x, y]);
                let mx = self.terms.mk_bvextract(n - 1, n - 1, x);
                let my = self.terms.mk_bvextract(n - 1, n - 1, y);
                let ms = self.terms.mk_bvextract(n - 1, n - 1, s);
                let same_sign = self.terms.mk_eq(mx, my);
                let res_eq = self.terms.mk_eq(mx, ms);
                let res_diff = self.terms.mk_not(res_eq);
                self.terms.mk_and(vec![same_sign, res_diff])
            }
            // bvssubo(x,y): signed subtract overflows iff operands differ in sign
            // and the result's sign bit differs from the minuend's.
            "bvssubo" => {
                let y = args[1];
                let d = self.terms.mk_bvsub(vec![x, y]);
                let mx = self.terms.mk_bvextract(n - 1, n - 1, x);
                let my = self.terms.mk_bvextract(n - 1, n - 1, y);
                let md = self.terms.mk_bvextract(n - 1, n - 1, d);
                let same_op = self.terms.mk_eq(mx, my);
                let diff_op = self.terms.mk_not(same_op);
                let same_res = self.terms.mk_eq(mx, md);
                let diff_res = self.terms.mk_not(same_res);
                self.terms.mk_and(vec![diff_op, diff_res])
            }
            // bvumulo(x,y): unsigned mul overflows iff the high n bits of the
            // 2n-bit unsigned product are nonzero.
            "bvumulo" => {
                let y = args[1];
                let zx = self.terms.mk_bvzero_extend(n, x);
                let zy = self.terms.mk_bvzero_extend(n, y);
                let prod = self.terms.mk_bvmul(vec![zx, zy]);
                let hi = self.terms.mk_bvextract(2 * n - 1, n, prod);
                let zero = self.terms.mk_bitvec(BigInt::from(0), n);
                let eq = self.terms.mk_eq(hi, zero);
                self.terms.mk_not(eq)
            }
            // bvsmulo(x,y): signed mul overflows iff the full 2n-bit signed product
            // is not the sign-extension of its low n bits (does not fit in n bits).
            "bvsmulo" => {
                let y = args[1];
                let sx = self.terms.mk_bvsign_extend(n, x);
                let sy = self.terms.mk_bvsign_extend(n, y);
                let prod = self.terms.mk_bvmul(vec![sx, sy]);
                let low = self.terms.mk_bvextract(n - 1, 0, prod);
                let relow = self.terms.mk_bvsign_extend(n, low);
                let eq = self.terms.mk_eq(relow, prod);
                self.terms.mk_not(eq)
            }
            // bvsdivo(x,y): signed divide overflows iff x is the signed minimum and
            // y is all-ones (-1): signed_min / -1 is not representable.
            "bvsdivo" => {
                let y = args[1];
                let smin = self.terms.mk_bitvec(BigInt::from(1) << (n as usize - 1), n);
                let all_ones = self.terms.mk_bitvec((BigInt::from(1) << n as usize) - 1, n);
                let x_smin = self.terms.mk_eq(x, smin);
                let y_neg1 = self.terms.mk_eq(y, all_ones);
                self.terms.mk_and(vec![x_smin, y_neg1])
            }
            _ => {
                return Err(ElaborateError::Unsupported(format!(
                    "unknown bit-vector overflow predicate {name}"
                )))
            }
        };
        Ok(result)
    }
}
