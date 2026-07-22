// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural bitvector evaluation: concat, extract, extend, rotate, repeat,
//! int2bv, bv2nat, bvcomp.
//!
//! Extracted from `eval_bv.rs` to keep file sizes under 1000 lines
//! (#5970 code-health splits).

use ay_core::term::Symbol;
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::{EvalValue, Executor, Model};

impl Executor {
    /// Evaluate a structural BV operation (concat, extract, extend, rotate,
    /// repeat, int2bv, bv2nat, bvcomp).
    ///
    /// Returns `Some(value)` if recognized, `None` otherwise.
    pub(super) fn evaluate_bv_structural(
        &self,
        model: &Model,
        sym: &Symbol,
        name: &str,
        args: &[TermId],
        sort: &Sort,
        term_id: TermId,
    ) -> Option<EvalValue> {
        match name {
            // BitVec concatenation
            "concat" => {
                if args.len() != 2 {
                    return Some(EvalValue::Unknown);
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (
                        EvalValue::BitVec {
                            value: hi,
                            width: hi_w,
                        },
                        EvalValue::BitVec {
                            value: lo,
                            width: lo_w,
                        },
                    ) => {
                        let hi = Self::normalize_bv_value(hi, hi_w);
                        let lo = Self::normalize_bv_value(lo, lo_w);
                        let result = (hi << lo_w as usize) | lo;
                        Some(EvalValue::BitVec {
                            value: result,
                            width: hi_w + lo_w,
                        })
                    }
                    // Fallback to BV model cache (#5627).
                    _ => Some(self.bv_model_cache_fallback(model, term_id, sort)),
                }
            }
            // BitVec extraction (indexed: (_ extract hi lo))
            "extract" => {
                let Sort::BitVec(bv) = sort else {
                    return Some(EvalValue::Unknown);
                };
                if let Symbol::Indexed(_, indices) = sym {
                    if indices.len() == 2 && args.len() == 1 && indices[0] >= indices[1] {
                        let hi = indices[0];
                        let lo = indices[1];
                        if let EvalValue::BitVec { value, width } =
                            self.evaluate_term(model, args[0])
                        {
                            let val = Self::normalize_bv_value(value, width);
                            let extract_width = hi - lo + 1;
                            let mask = (BigInt::one() << extract_width as usize) - BigInt::one();
                            let extracted = (val >> lo as usize) & mask;
                            return Some(EvalValue::BitVec {
                                value: extracted,
                                width: bv.width,
                            });
                        }
                    }
                }
                Some(self.bv_model_cache_fallback(model, term_id, sort))
            }
            // BitVec zero extension
            "zero_extend" => {
                let Sort::BitVec(bv) = sort else {
                    return Some(EvalValue::Unknown);
                };
                let result_width = bv.width;
                if args.len() != 1 {
                    return Some(EvalValue::Unknown);
                }
                if self.is_bv_child_missing_from_model(model, args[0]) {
                    let cached = self.bv_model_cache_fallback(model, term_id, sort);
                    if !matches!(cached, EvalValue::Unknown) {
                        return Some(cached);
                    }
                }
                match self.evaluate_term(model, args[0]) {
                    EvalValue::BitVec { value, width } => {
                        let val = Self::normalize_bv_value(value, width);
                        Some(EvalValue::BitVec {
                            value: val,
                            width: result_width,
                        })
                    }
                    _ => Some(self.bv_model_cache_fallback(model, term_id, sort)),
                }
            }
            // BitVec sign extension
            "sign_extend" => {
                let Sort::BitVec(bv) = sort else {
                    return Some(EvalValue::Unknown);
                };
                let result_width = bv.width;
                if args.len() != 1 {
                    return Some(EvalValue::Unknown);
                }
                if self.is_bv_child_missing_from_model(model, args[0]) {
                    let cached = self.bv_model_cache_fallback(model, term_id, sort);
                    if !matches!(cached, EvalValue::Unknown) {
                        return Some(cached);
                    }
                }
                match self.evaluate_term(model, args[0]) {
                    EvalValue::BitVec { value, width } => {
                        let val = Self::normalize_bv_value(value, width);
                        let signed = Self::to_signed_bv(&val, width);
                        let result = Self::normalize_bv_value(signed, result_width);
                        Some(EvalValue::BitVec {
                            value: result,
                            width: result_width,
                        })
                    }
                    _ => Some(self.bv_model_cache_fallback(model, term_id, sort)),
                }
            }
            // BitVec rotate left: (_ rotate_left n)
            "rotate_left" => Some(self.eval_bv_rotate(model, sym, args, sort, term_id, true)),
            // BitVec rotate right: (_ rotate_right n)
            "rotate_right" => Some(self.eval_bv_rotate(model, sym, args, sort, term_id, false)),
            // BitVec repeat: (_ repeat n)
            "repeat" => {
                let Sort::BitVec(bv) = sort else {
                    return Some(EvalValue::Unknown);
                };
                if args.len() != 1 {
                    return Some(EvalValue::Unknown);
                }
                if self.is_bv_child_missing_from_model(model, args[0]) {
                    let cached = self.bv_model_cache_fallback(model, term_id, sort);
                    if !matches!(cached, EvalValue::Unknown) {
                        return Some(cached);
                    }
                }
                if let Symbol::Indexed(_, indices) = sym {
                    if let Some(&n) = indices.first() {
                        if n == 0 {
                            return Some(EvalValue::Unknown);
                        }
                        if let EvalValue::BitVec { value, width } =
                            self.evaluate_term(model, args[0])
                        {
                            let val = Self::normalize_bv_value(value, width);
                            let mut result = val.clone();
                            for _ in 1..n {
                                result = (result << width as usize) | &val;
                            }
                            return Some(EvalValue::BitVec {
                                value: result,
                                width: bv.width,
                            });
                        }
                    }
                }
                Some(self.bv_model_cache_fallback(model, term_id, sort))
            }
            // int2bv: (_ int2bv n) converts Int to (_ BitVec n)
            "int2bv" => {
                let Sort::BitVec(bv) = sort else {
                    return Some(EvalValue::Unknown);
                };
                if args.len() != 1 {
                    return Some(EvalValue::Unknown);
                }
                if let EvalValue::Rational(r) = self.evaluate_term(model, args[0]) {
                    if r.is_integer() {
                        let int_val = r.to_integer();
                        let width = bv.width;
                        let modulus = BigInt::one() << width as usize;
                        let val = ((int_val % &modulus) + &modulus) % &modulus;
                        return Some(EvalValue::BitVec { value: val, width });
                    }
                }
                Some(self.bv_model_cache_fallback(model, term_id, sort))
            }
            // BV to natural number conversion (#5115)
            "bv2nat" => {
                if args.len() != 1 {
                    return Some(EvalValue::Unknown);
                }
                if let EvalValue::BitVec { value, width } = self.evaluate_term(model, args[0]) {
                    let val = Self::normalize_bv_value(value, width);
                    return Some(EvalValue::Rational(BigRational::from(val)));
                }
                // (#B2) Companion-bridge fallback. When `k`'s BitVec value is
                // NOT recoverable from the model — there is no BV model because
                // `k` occurs only inside `bv2nat(k)`, so the BV theory never
                // produced a value for it — the arithmetic solver treats the
                // Int-sorted `(bv2nat k)` term as an opaque variable and assigns
                // it directly. Use that assignment so a Route-A array-length
                // companion `(= L (bv2nat k))` evaluates to a DEFINITE Int
                // instead of `Unknown`, which closes the over-rejection that
                // dropped genuine SAT models (and still rejects decoupled ones,
                // since `L != v` then evaluates definitively false).
                //
                // SOUNDNESS: `bv2nat(k)` is the unsigned value of a width-`w`
                // bitvector, so it must lie in `[0, 2^w)`. The solver emits this
                // range axiom for every `bv2nat` term (a decoupled `L = 300`
                // with `L = bv2nat(k:8)` is correctly UNSAT), so the opaque
                // assignment is already in range; we re-check `0 <= v < 2^w`
                // here as a hard guard. Any in-range `v` is realized by the
                // witness `k = int2bv_w(v)`, so accepting it never validates an
                // impossible model, and an out-of-range value (which the range
                // axiom forbids) is rejected back to `Unknown`. Gated on the
                // absence of a BV model so it can never override a real BV
                // assignment, and it is validation-side only — it can only turn
                // a spuriously-`Unknown` companion into a definite value, never
                // an UNSAT into SAT.
                //
                // The companion assignment is keyed only by this application's
                // ambient TermId. It is not reusable when the application
                // contains an active lambda binder.
                if model.bv_model.is_none()
                    && !super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, term_id)
                {
                    if let Sort::BitVec(bv) = self.ctx.terms.sort(args[0]) {
                        let modulus = BigInt::one() << bv.width as usize;
                        if let Some(ref lia_model) = model.lia_model {
                            if let Some(v) = lia_model.values.get(&term_id) {
                                if v >= &BigInt::zero() && v < &modulus {
                                    return Some(EvalValue::Rational(BigRational::from(v.clone())));
                                }
                            }
                        }
                        if let Some(ref lra_model) = model.lra_model {
                            if let Some(v) = lra_model.values.get(&term_id) {
                                if v.is_integer() {
                                    let iv = v.to_integer();
                                    if iv >= BigInt::zero() && iv < modulus {
                                        return Some(EvalValue::Rational(BigRational::from(iv)));
                                    }
                                }
                            }
                        }
                    }
                }
                Some(EvalValue::Unknown)
            }
            // BitVec comparison returning (_ BitVec 1)
            "bvcomp" => {
                if args.len() != 2 {
                    return Some(EvalValue::Unknown);
                }
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (
                        EvalValue::BitVec {
                            value: a,
                            width: aw,
                        },
                        EvalValue::BitVec {
                            value: b,
                            width: bw,
                        },
                    ) => {
                        if aw != bw {
                            return Some(EvalValue::Unknown);
                        }
                        let a = Self::normalize_bv_value(a, aw);
                        let b = Self::normalize_bv_value(b, bw);
                        Some(EvalValue::BitVec {
                            value: if a == b {
                                BigInt::one()
                            } else {
                                BigInt::zero()
                            },
                            width: 1,
                        })
                    }
                    _ => Some(self.bv_model_cache_fallback(model, term_id, sort)),
                }
            }
            _ => None,
        }
    }

    /// Shared implementation for rotate_left and rotate_right.
    fn eval_bv_rotate(
        &self,
        model: &Model,
        sym: &Symbol,
        args: &[TermId],
        sort: &Sort,
        term_id: TermId,
        is_left: bool,
    ) -> EvalValue {
        let Sort::BitVec(bv) = sort else {
            return EvalValue::Unknown;
        };
        if args.len() != 1 {
            return EvalValue::Unknown;
        }
        if let Symbol::Indexed(_, indices) = sym {
            if let Some(&n) = indices.first() {
                let width = bv.width;
                let k = if width > 0 { n % width } else { 0 };
                if let EvalValue::BitVec { value, width: w } = self.evaluate_term(model, args[0]) {
                    if w != width {
                        return EvalValue::Unknown;
                    }
                    let val = Self::normalize_bv_value(value, width);
                    if k == 0 {
                        return EvalValue::BitVec { value: val, width };
                    }
                    let modulus = BigInt::one() << width as usize;
                    let (shift_big, shift_small) = if is_left {
                        (k, width - k)
                    } else {
                        (width - k, k)
                    };
                    let left = (&val << shift_big as usize) % &modulus;
                    let right = &val >> shift_small as usize;
                    return EvalValue::BitVec {
                        value: left | right,
                        width,
                    };
                }
            }
        }
        self.bv_model_cache_fallback(model, term_id, sort)
    }
}
