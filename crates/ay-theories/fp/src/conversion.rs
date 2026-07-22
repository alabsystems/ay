// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP conversion helpers: rounding-mode decoding and `to_fp` encodings.

use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::{CnfLit, Sort};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::model_value::FpModelValue;
use super::{FpDecomposed, FpPrecision, FpSolver, RoundingMode};

impl FpSolver<'_> {
    /// Get rounding mode from a term.
    /// Handles both `TermData::App("RNE", _)` (from parser/API) and
    /// `TermData::Var("RNE", _)` (from some frontends). See #6203.
    /// INVARIANT (#P0.2 symbolic RoundingMode): the silent-RNE default
    /// branches below must be UNREACHABLE for a symbolic (non-literal) mode.
    /// Upstream, `check_fp_support` fails ANY non-literal RoundingMode-sorted
    /// term closed to `unknown` before bit-blasting, the rm_expand
    /// enumeration substitutes literal modes before solving, and the model
    /// evaluator's concretization bails (fails closed) on an unpinned RM
    /// term. Defaulting a live symbolic mode to RNE here would drop
    /// constraints like `(= rm RTP)` — a wrong verdict in both directions —
    /// so the debug assertions make any regression of that guard loud.
    pub(crate) fn get_rounding_mode(&self, term: TermId) -> RoundingMode {
        let data = self.terms.get(term);
        match data {
            TermData::App(sym, _) => match RoundingMode::from_name(sym.name()) {
                Some(rm) => rm,
                None => {
                    debug_assert!(
                        false,
                        "get_rounding_mode reached with non-literal mode app '{}' — \
                         upstream fail-close guard regressed (#P0.2)",
                        sym.name()
                    );
                    tracing::warn!(
                        name = sym.name(),
                        "unrecognized rounding mode, defaulting to RNE"
                    );
                    RoundingMode::default()
                }
            },
            TermData::Var(name, _) => match RoundingMode::from_name(name) {
                Some(rm) => rm,
                None => {
                    debug_assert!(
                        false,
                        "get_rounding_mode reached with symbolic mode variable '{name}' — \
                         upstream fail-close guard regressed (#P0.2)"
                    );
                    tracing::warn!(
                        name,
                        "unrecognized rounding mode variable, defaulting to RNE"
                    );
                    RoundingMode::default()
                }
            },
            _ => {
                debug_assert!(
                    false,
                    "get_rounding_mode reached with non-symbolic mode term {term:?} — \
                     upstream fail-close guard regressed (#P0.2)"
                );
                tracing::warn!(?term, "non-symbolic rounding mode term, defaulting to RNE");
                RoundingMode::default()
            }
        }
    }

    /// Decompose an FP constructor `(fp sign_bv exp_bv sig_bv)` into CNF
    /// variables. Each of the three fields is handled independently:
    ///
    /// * A BV-constant field is pinned to its literal bit pattern.
    /// * A symbolic (non-constant) field is bit-blasted via `bitblast_bv_term`
    ///   and the resulting CNF bits become the corresponding FP field bits.
    ///
    /// This is critical for soundness (#bug8): when only some fields are
    /// symbolic, the concrete fields must still constrain the value. Previously
    /// any non-constant field caused the entire decomposition to return
    /// unconstrained variables, which let predicates such as `fp.isZero` over a
    /// `(fp s #b0...0 #b...1)` (concrete subnormal mantissa) be wrong-SAT by
    /// freely choosing exponent/significand bits.
    pub(crate) fn decompose_fp_constructor(
        &mut self,
        args: &[TermId],
        precision: FpPrecision,
    ) -> FpDecomposed {
        let sign = self.fp_constructor_sign_bit(args[0]);
        let exponent = self.fp_constructor_field_bits(args[1], precision.exponent_bits() as usize);
        let significand =
            self.fp_constructor_field_bits(args[2], precision.significand_bits() as usize - 1);

        FpDecomposed {
            sign,
            exponent,
            significand,
            precision,
        }
    }

    /// Resolve the sign bit of an `(fp s e m)` constructor: a literal for a
    /// 1-bit BV constant, else the bit-blasted symbolic BV bit.
    fn fp_constructor_sign_bit(&mut self, arg: TermId) -> CnfLit {
        if let Some(v) = self.extract_bv_const(arg) {
            return if v.bit(0) {
                self.const_true()
            } else {
                self.const_false()
            };
        }
        let bits = self.bitblast_bv_term(arg, 1);
        bits[0]
    }

    /// Resolve an exponent/significand field of an `(fp s e m)` constructor:
    /// constant bits when the BV arg is a constant, else the symbolic BV bits.
    fn fp_constructor_field_bits(&mut self, arg: TermId, width: usize) -> Vec<CnfLit> {
        if let Some(v) = self.extract_bv_const(arg) {
            return (0..width)
                .map(|i| {
                    if v.bit(i as u64) {
                        self.const_true()
                    } else {
                        self.const_false()
                    }
                })
                .collect();
        }
        self.bitblast_bv_term(arg, width)
    }

    /// Decompose `(_ to_fp eb sb)` based on argument count and sorts.
    pub(crate) fn decompose_to_fp(
        &mut self,
        args: &[TermId],
        precision: FpPrecision,
    ) -> FpDecomposed {
        match args.len() {
            1 => self.make_to_fp_from_bv_reinterpret(args[0], precision),
            2 => {
                let rm = self.get_rounding_mode(args[0]);
                let arg_sort = self.terms.sort(args[1]).clone();
                match arg_sort {
                    Sort::FloatingPoint(..) => {
                        let x = self.get_fp(args[1]);
                        self.make_to_fp_float(&x, rm, precision)
                    }
                    Sort::BitVec(_) => self.make_to_fp_signed(args[1], rm, precision),
                    Sort::Real | Sort::Int => self.make_to_fp_real(args[1], rm, precision),
                    _ => {
                        tracing::warn!(
                            ?arg_sort,
                            "to_fp: unsupported argument sort for 2-arg variant"
                        );
                        self.has_encoding_gap = true;
                        self.fresh_decomposed(precision)
                    }
                }
            }
            3 => self.decompose_fp_constructor(args, precision),
            _ => {
                tracing::warn!(nargs = args.len(), "to_fp: unexpected argument count");
                self.fresh_decomposed(precision)
            }
        }
    }

    /// Decompose `(_ to_fp_unsigned eb sb) rm bv` — unsigned BV-to-FP.
    pub(crate) fn decompose_to_fp_unsigned(
        &mut self,
        args: &[TermId],
        precision: FpPrecision,
    ) -> FpDecomposed {
        if args.len() != 2 {
            tracing::warn!(
                nargs = args.len(),
                "to_fp_unsigned: expected 2 arguments (rm, bv)"
            );
            return self.fresh_decomposed(precision);
        }
        let rm = self.get_rounding_mode(args[0]);
        self.make_to_fp_unsigned(args[1], rm, precision)
    }

    /// Reinterpret a bitvector as an IEEE 754 floating-point bit pattern.
    fn make_to_fp_from_bv_reinterpret(
        &mut self,
        bv_term: TermId,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;
        let total = 1 + eb + (sb - 1);

        if let Some(bv_val) = self.extract_bv_const(bv_term) {
            let fp = self.fresh_decomposed(precision);
            let sign_val = bv_val.bit((total - 1) as u64);
            self.constrain_constant(
                &fp,
                sign_val,
                |i| bv_val.bit(u64::from(i) + (sb as u64 - 1)),
                |i| bv_val.bit(u64::from(i)),
            );
            return fp;
        }

        let Some(bv_bits) = self.bitblast_conv_bv_arg(bv_term, total) else {
            return self.fresh_decomposed(precision);
        };
        FpDecomposed {
            sign: bv_bits[total - 1],
            exponent: bv_bits[sb - 1..sb - 1 + eb].to_vec(),
            significand: bv_bits[0..sb - 1].to_vec(),
            precision,
        }
    }

    /// Bit-blast a (possibly composite) BV argument to an int→fp conversion.
    ///
    /// Conversion arguments are frequently composite — e.g. unsigned int→fp is
    /// encoded as signed `to_fp` applied to `((_ zero_extend k) a)`. The leaf-
    /// only [`Self::bitblast_bv_term`] returns fresh *unconstrained* bits for
    /// such terms (and flags an encoding gap), which made the whole conversion
    /// collapse to Unknown. This uses the recursive composite-aware encoder
    /// ([`Self::bitblast_bv_value`]) which handles `zero_extend`/`sign_extend`/
    /// `extract`/`concat`/`bv*` precisely, and fails closed (flagging the gap so
    /// the result is a sound Unknown) only on a genuinely unsupported composite.
    pub(crate) fn bitblast_conv_bv_arg(
        &mut self,
        bv_term: TermId,
        bv_sz: usize,
    ) -> Option<Vec<CnfLit>> {
        match self.bitblast_bv_value(bv_term, bv_sz) {
            Some(bits) => Some(bits),
            None => {
                self.has_encoding_gap = true;
                None
            }
        }
    }

    /// Convert a signed bitvector to floating-point with rounding.
    fn make_to_fp_signed(
        &mut self,
        bv_term: TermId,
        rm: RoundingMode,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;
        let exp_sz = eb + 2;
        let sig_sz = sb + 4;

        let bv_sz = match self.terms.sort(bv_term).clone() {
            Sort::BitVec(bvs) => bvs.width as usize,
            _ => {
                tracing::warn!("to_fp signed: argument is not BitVec");
                return self.fresh_decomposed(precision);
            }
        };

        let Some(bv_bits) = self.bitblast_conv_bv_arg(bv_term, bv_sz) else {
            return self.fresh_decomposed(precision);
        };
        let is_zero = self.make_all_zero(&bv_bits);
        let zero_fp = self.make_zero(precision, false);

        let sign_bit = bv_bits[bv_sz - 1];
        let neg_bv = self.bv_neg(&bv_bits);
        let abs_bv = self.make_ite_bits(sign_bit, &neg_bv, &bv_bits);

        let lz = self.bv_leading_zeros(&abs_bv, exp_sz);
        let lz_extended = if bv_sz > exp_sz {
            self.zero_extend(&lz, bv_sz - exp_sz)
        } else if bv_sz < exp_sz {
            lz[..bv_sz].to_vec()
        } else {
            lz.clone()
        };
        let shifted = self.bv_shl(&abs_bv, &lz_extended);

        let mut sig_bits = Vec::with_capacity(sig_sz);
        if bv_sz >= sig_sz {
            let top_start = bv_sz - (sig_sz - 1);
            let sticky_bits: Vec<CnfLit> = shifted[..top_start].to_vec();
            let sticky = self.bv_or_reduce(&sticky_bits);
            sig_bits.push(sticky);
            sig_bits.extend_from_slice(&shifted[top_start..]);
        } else {
            let pad = sig_sz - bv_sz;
            let zero = self.const_false();
            for _ in 0..pad {
                sig_bits.push(zero);
            }
            sig_bits.extend_from_slice(&shifted);
        }
        debug_assert_eq!(sig_bits.len(), sig_sz);

        let base_exp = self.const_bv((bv_sz as u64).wrapping_sub(2), exp_sz);
        let exp_bits = self.bv_sub(&base_exp, &lz);

        let rounded = self.fp_round(precision, rm, sign_bit, &sig_bits, &exp_bits);
        self.make_ite_fp(is_zero, &zero_fp, &rounded, precision)
    }

    /// Convert an unsigned bitvector to floating-point with rounding.
    fn make_to_fp_unsigned(
        &mut self,
        bv_term: TermId,
        rm: RoundingMode,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;
        let exp_sz = eb + 2;
        let sig_sz = sb + 4;

        let bv_sz = match self.terms.sort(bv_term).clone() {
            Sort::BitVec(bvs) => bvs.width as usize,
            _ => {
                tracing::warn!("to_fp_unsigned: argument is not BitVec");
                return self.fresh_decomposed(precision);
            }
        };

        let Some(bv_bits) = self.bitblast_conv_bv_arg(bv_term, bv_sz) else {
            return self.fresh_decomposed(precision);
        };
        let result_sign = self.const_false();
        let is_zero = self.make_all_zero(&bv_bits);
        let zero_fp = self.make_zero(precision, false);

        let lz = self.bv_leading_zeros(&bv_bits, exp_sz);
        let lz_extended = if bv_sz > exp_sz {
            self.zero_extend(&lz, bv_sz - exp_sz)
        } else if bv_sz < exp_sz {
            lz[..bv_sz].to_vec()
        } else {
            lz.clone()
        };
        let shifted = self.bv_shl(&bv_bits, &lz_extended);

        let mut sig_bits = Vec::with_capacity(sig_sz);
        if bv_sz >= sig_sz {
            let top_start = bv_sz - (sig_sz - 1);
            let sticky_bits: Vec<CnfLit> = shifted[..top_start].to_vec();
            let sticky = self.bv_or_reduce(&sticky_bits);
            sig_bits.push(sticky);
            sig_bits.extend_from_slice(&shifted[top_start..]);
        } else {
            let pad = sig_sz - bv_sz;
            let zero = self.const_false();
            for _ in 0..pad {
                sig_bits.push(zero);
            }
            sig_bits.extend_from_slice(&shifted);
        }
        debug_assert_eq!(sig_bits.len(), sig_sz);

        let base_exp = self.const_bv((bv_sz as u64).wrapping_sub(2), exp_sz);
        let exp_bits = self.bv_sub(&base_exp, &lz);

        let rounded = self.fp_round(precision, rm, result_sign, &sig_bits, &exp_bits);
        self.make_ite_fp(is_zero, &zero_fp, &rounded, precision)
    }

    /// Convert a ground Real (or Int) literal to floating-point with rounding.
    ///
    /// `(_ to_fp eb sb) rm <real-literal>` rounds the exact rational value of
    /// the (constant) argument into the target FP format under `rm` and pins the
    /// result to that constant bit pattern.
    ///
    /// The argument must be a *ground* rational expression (literals composed
    /// with `+ - * /`); the SMT-LIB grammar only permits constant Reals here in
    /// quantifier-free FP. If the value cannot be reduced to a ground rational,
    /// or the target format is outside the exact-rounding helper's supported
    /// range, we fail closed (flag an encoding gap so the solver returns a sound
    /// `unknown` rather than guessing an unconstrained value).
    fn make_to_fp_real(
        &mut self,
        real_term: TermId,
        rm: RoundingMode,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let Some(value) = self.eval_ground_rational(real_term) else {
            tracing::warn!(
                ?real_term,
                "to_fp from Real: argument is not a ground rational literal — encoding gap"
            );
            self.has_encoding_gap = true;
            return self.fresh_decomposed(precision);
        };

        let eb = precision.exponent_bits();
        let sb = precision.significand_bits();
        let Some(mv) = FpModelValue::from_rational_with_format(&value, eb, sb, rm) else {
            tracing::warn!(
                eb,
                sb,
                "to_fp from Real: format unsupported by exact rounding — encoding gap"
            );
            self.has_encoding_gap = true;
            return self.fresh_decomposed(precision);
        };

        self.constrain_to_model_value(&mv, precision)
    }

    /// Pin a fresh decomposed FP value to a concrete [`FpModelValue`] bit
    /// pattern (sign / biased exponent / stored significand).
    fn constrain_to_model_value(
        &mut self,
        mv: &FpModelValue,
        precision: FpPrecision,
    ) -> FpDecomposed {
        match *mv {
            FpModelValue::PosZero { .. } => self.make_zero(precision, false),
            FpModelValue::NegZero { .. } => self.make_zero(precision, true),
            FpModelValue::PosInf { .. } => self.make_infinity(precision, false),
            FpModelValue::NegInf { .. } => self.make_infinity(precision, true),
            FpModelValue::NaN { .. } => self.make_nan_value(precision),
            FpModelValue::Fp {
                sign,
                exponent,
                significand,
                ..
            } => {
                let fp = self.fresh_decomposed(precision);
                self.constrain_constant(
                    &fp,
                    sign,
                    |i| (exponent >> i) & 1 == 1,
                    |i| (significand >> i) & 1 == 1,
                );
                fp
            }
        }
    }

    /// Evaluate a *ground* Real/Int term to an exact [`BigRational`].
    ///
    /// Returns `None` if the term contains any non-constant leaf or an
    /// operator/shape this evaluator does not cover (caller fails closed).
    fn eval_ground_rational(&self, term: TermId) -> Option<BigRational> {
        match self.terms.get(term) {
            TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
            TermData::Const(Constant::Int(n)) => Some(BigRational::from(n.clone())),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" if !args.is_empty() => {
                    let mut sum = BigRational::from(BigInt::from(0));
                    for &a in args {
                        sum += self.eval_ground_rational(a)?;
                    }
                    Some(sum)
                }
                "-" if args.len() == 1 => Some(-self.eval_ground_rational(args[0])?),
                "-" if args.len() >= 2 => {
                    let mut acc = self.eval_ground_rational(args[0])?;
                    for &a in &args[1..] {
                        acc -= self.eval_ground_rational(a)?;
                    }
                    Some(acc)
                }
                "*" if !args.is_empty() => {
                    let mut prod = BigRational::from(BigInt::from(1));
                    for &a in args {
                        prod *= self.eval_ground_rational(a)?;
                    }
                    Some(prod)
                }
                "/" if args.len() >= 2 => {
                    let mut acc = self.eval_ground_rational(args[0])?;
                    for &a in &args[1..] {
                        let d = self.eval_ground_rational(a)?;
                        if d.numer() == &BigInt::from(0) {
                            return None;
                        }
                        acc /= d;
                    }
                    Some(acc)
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Convert FP to FP with different precision.
    fn make_to_fp_float(
        &mut self,
        x: &FpDecomposed,
        rm: RoundingMode,
        to_precision: FpPrecision,
    ) -> FpDecomposed {
        let from_precision = x.precision;
        let from_eb = from_precision.exponent_bits() as usize;
        let from_sb = from_precision.significand_bits() as usize;
        let to_eb = to_precision.exponent_bits() as usize;
        let to_sb = to_precision.significand_bits() as usize;

        if from_eb == to_eb && from_sb == to_sb {
            return x.clone();
        }

        let x_nan = self.is_nan(x);
        let x_inf = self.is_infinite(x);
        let x_zero = self.is_zero(x);
        let result = self.fresh_decomposed(to_precision);

        let nan = self.make_nan_value(to_precision);
        self.constrain_fp_when(x_nan, &result, &nan);

        let pos_inf = self.make_infinity(to_precision, false);
        let neg_inf = self.make_infinity(to_precision, true);
        let pos_inf_cond = {
            let not_sign = -x.sign;
            self.make_and(x_inf, not_sign)
        };
        let neg_inf_cond = self.make_and(x_inf, x.sign);
        self.constrain_fp_when(pos_inf_cond, &result, &pos_inf);
        self.constrain_fp_when(neg_inf_cond, &result, &neg_inf);

        let pos_zero = self.make_zero(to_precision, false);
        let neg_zero = self.make_zero(to_precision, true);
        let pos_zero_cond = {
            let not_sign = -x.sign;
            self.make_and(x_zero, not_sign)
        };
        let neg_zero_cond = self.make_and(x_zero, x.sign);
        self.constrain_fp_when(pos_zero_cond, &result, &pos_zero);
        self.constrain_fp_when(neg_zero_cond, &result, &neg_zero);

        let (sgn, sig, exp, lz) = self.unpack(x, true);

        let sig_sz = to_sb + 4;
        let res_sig = if from_sb < (to_sb + 3) {
            let pad = to_sb + 3 - from_sb;
            let zero = self.const_false();
            let mut res = vec![zero; pad];
            res.extend_from_slice(&sig);
            res.push(zero);
            debug_assert_eq!(res.len(), sig_sz);
            res
        } else if from_sb > (to_sb + 3) {
            let keep = to_sb + 2;
            let high: Vec<CnfLit> = sig[from_sb - keep..from_sb].to_vec();
            let low: Vec<CnfLit> = sig[..from_sb - keep].to_vec();
            let sticky = self.bv_or_reduce(&low);
            let zero = self.const_false();
            let mut res = vec![sticky];
            res.extend_from_slice(&high);
            res.push(zero);
            debug_assert_eq!(res.len(), sig_sz);
            res
        } else {
            let zero = self.const_false();
            let mut res = sig;
            res.push(zero);
            debug_assert_eq!(res.len(), sig_sz);
            res
        };

        let exp_sz = to_eb + 2;
        // Compute the normalized unbiased exponent `exp - lz` in a working width
        // wide enough to hold the source's most-negative normalized exponent, then
        // saturate (sign-aware clamp) into the target's `to_eb + 2` field.
        //
        // `exp` (from unpack) is the SIGNED unbiased source exponent at width
        // `from_eb`. For a subnormal source it is `1 - from_bias`, and the
        // leading-zero normalization subtracts `lz` (0..=from_sb). The result
        // `(1 - from_bias) - lz` can be far more negative than a `to_eb + 2`-bit
        // signed field can hold (e.g. source (5,8) gives -17, below the 5-bit
        // signed minimum -16, which would WRAP to +15 and make fp_round emit
        // infinity instead of the correct smallest subnormal). Materializing the
        // subtraction at a narrow width before clamping is the unsoundness.
        //
        // Work in W = max(from_eb, to_eb) + 2 bits, keeping the exponent signed
        // and un-truncated, mirroring z3's fpa2bv_converter::mk_to_fp_float which
        // keeps the exponent at max(from_ebits, to_ebits) + 2 through normalization
        // so fp_round's TINY (underflow-to-subnormal) path receives the true,
        // very-negative exponent.
        let work_sz = from_eb.max(to_eb) + 2;
        debug_assert!(work_sz >= exp_sz, "work width must cover target exp field");
        debug_assert!(work_sz >= from_eb, "work width must cover source exp width");

        // Sign-extend the signed source exponent into the working width.
        let exp_w = if exp.len() < work_sz {
            self.sign_extend(&exp, work_sz - exp.len())
        } else {
            // `exp` is at most `from_eb` wide <= work_sz, so this is the
            // exact-width case; keep it defensive.
            exp[..work_sz].to_vec()
        };
        // `lz` is a non-negative count, so zero-extend into the working width.
        let lz_w = if lz.len() < work_sz {
            self.zero_extend(&lz, work_sz - lz.len())
        } else {
            lz[..work_sz].to_vec()
        };
        // Exact signed subtraction in the wide working width (no overflow).
        let res_exp_w = self.bv_sub(&exp_w, &lz_w);

        // Saturate into the target `exp_sz`-bit signed field. Representable range
        // is [-2^(exp_sz-1), 2^(exp_sz-1) - 1]. Build the bounds at exp_sz width
        // and sign-extend into the working width for comparison.
        let min_pat = 1u64 << (exp_sz - 1); // 100...0 = most-negative signed value
        let max_pat = min_pat - 1; // 011...1 = most-positive signed value
        let exp_min_sz = self.const_bv(min_pat, exp_sz);
        let exp_max_sz = self.const_bv(max_pat, exp_sz);
        let exp_min_w = self.sign_extend(&exp_min_sz, work_sz - exp_sz);
        let exp_max_w = self.sign_extend(&exp_max_sz, work_sz - exp_sz);

        let too_low = self.bv_slt(&res_exp_w, &exp_min_w);
        let too_high = self.bv_slt(&exp_max_w, &res_exp_w);
        // clamped = too_low ? min : (too_high ? max : res_exp_w)
        let hi_clamped = self.make_ite_bits(too_high, &exp_max_w, &res_exp_w);
        let clamped_w = self.make_ite_bits(too_low, &exp_min_w, &hi_clamped);
        // Value is now guaranteed in [min, max], so the low exp_sz bits are an
        // exact (lossless) representation of the signed clamped exponent.
        let res_exp = clamped_w[..exp_sz].to_vec();

        let normal_result = self.fp_round(to_precision, rm, sgn, &res_sig, &res_exp);
        let special = {
            let nan_or_inf = self.make_or(x_nan, x_inf);
            self.make_or(nan_or_inf, x_zero)
        };
        let not_special = -special;
        self.constrain_fp_when(not_special, &result, &normal_result);

        result
    }
}
