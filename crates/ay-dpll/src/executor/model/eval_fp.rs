// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point evaluation helpers for model evaluation.
//!
//! Extracted from `mod.rs` to reduce file size (Wave C1 of #2998 module splits).
//! All methods are `impl Executor` — they share the same method namespace.

use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId};
use ay_fp::{FpModelValue, RoundingMode};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::{EvalValue, Executor, Model};

mod controlled;
mod fields;
#[cfg(test)]
mod tests;
#[cfg(test)]
pub(in crate::executor) use controlled::FpEvalPhase;

/// Round an exact rational to an integer per the SMT-LIB rounding-mode
/// semantics used by `fp.to_sbv` / `fp.to_ubv`:
/// RTZ = truncate, RTP = ceiling, RTN = floor, RNE = nearest (ties to even),
/// RNA = nearest (ties away from zero).
fn round_rational_to_integer(r: &BigRational, rm: RoundingMode) -> BigInt {
    let floor = r.floor().to_integer();
    let frac = r - BigRational::from(floor.clone());
    let half = BigRational::new(BigInt::one(), BigInt::from(2));
    let up = match rm {
        RoundingMode::RTN => false,
        RoundingMode::RTP => frac.is_positive(),
        RoundingMode::RTZ => frac.is_positive() && r.is_negative(),
        RoundingMode::RNE => {
            frac > half || (frac == half && (&floor % BigInt::from(2)).magnitude().is_one())
        }
        RoundingMode::RNA => {
            // Ties away from zero: at exactly .5, positive values round up
            // (away), negative values round down (away, i.e. keep floor).
            frac > half || (frac == half && !r.is_negative())
        }
    };
    if up {
        floor + BigInt::one()
    } else {
        floor
    }
}

impl Executor {
    /// Resolve a rounding-mode operand to a concrete mode: a literal
    /// (`RNE`…`roundTowardZero`) directly, otherwise THROUGH THE MODEL
    /// (#P0.2 symbolic RoundingMode — the FP enumeration / EUF coverage
    /// passes pin every symbolic RM term to a literal, surfaced by
    /// `evaluate_term` as an `Element` carrying the mode's long name).
    /// `None` — never a silent RNE default — when the model does not pin it.
    fn rounding_mode(&self, model: &Model, rm_term: TermId) -> Option<RoundingMode> {
        if !crate::executor::rm_domain::is_rm_sort(self.ctx.terms.sort(rm_term)) {
            return None;
        }
        if let Some(literal) = crate::executor::rm_domain::rm_literal_mode(&self.ctx.terms, rm_term)
        {
            return Some(literal);
        }
        match self.evaluate_term(model, rm_term) {
            EvalValue::Element(name) => RoundingMode::from_name(&name),
            _ => None,
        }
    }

    /// The value the solve chose for an application of `fp.to_ubv`/`fp.to_sbv`
    /// at an argument where SMT-LIB leaves the result unspecified (NaN, an
    /// infinity, or out of range for the width).
    ///
    /// The conversion is still a FUNCTION of `(rm, x)`: every application of
    /// the same operator, width and mode at an equal `x` denotes one value. The
    /// FP bit-blaster records each application's chosen bits; this reads the
    /// application's own record or — when preprocessing rewrote the
    /// application the solver saw (a folded constant argument) — the record of
    /// any application of the same function at an equal argument. Disagreeing
    /// records, or none, abstain (`Unknown`).
    fn unspec_to_bv(
        &self,
        model: &Model,
        term_id: TermId,
        sort: &Sort,
        rm: RoundingMode,
        x: &FpModelValue,
    ) -> EvalValue {
        let own = self.bv_model_cache_fallback(model, term_id, sort);
        if !matches!(own, EvalValue::Unknown) {
            return own;
        }
        let TermData::App(own_symbol, _) = self.ctx.terms.get(term_id) else {
            return EvalValue::Unknown;
        };
        let name = own_symbol.name();
        let (Some(bv_model), Sort::BitVec(bv)) = (model.bv_model.as_ref(), sort) else {
            return EvalValue::Unknown;
        };
        let key = x.to_smtlib();
        let mut chosen: Option<&BigInt> = None;
        for (&other, value) in &bv_model.values {
            let TermData::App(sym, args) = self.ctx.terms.get(other) else {
                continue;
            };
            if other == term_id
                || sym.name() != name
                || args.len() != 2
                || self.ctx.terms.sort(other) != sort
                || super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, other)
                || self.rounding_mode(model, args[0]) != Some(rm)
            {
                continue;
            }
            match self.evaluate_term(model, args[1]) {
                EvalValue::Fp(y) if y.to_smtlib() == key => {}
                _ => continue,
            }
            match chosen {
                None => chosen = Some(value),
                Some(previous) if previous == value => {}
                Some(_) => return EvalValue::Unknown,
            }
        }
        chosen.map_or(EvalValue::Unknown, |value| EvalValue::BitVec {
            value: value.clone(),
            width: bv.width,
        })
    }

    /// Exact IEEE 754 remainder `fp.rem(x, y)` for the model evaluator.
    ///
    /// SMT-LIB `fp.rem` is the IEEE 754 *remainder* (`x - y*n`, where
    /// `n = roundTiesToEven(x/y)`), NOT C `fmod`/`%`. The subtraction is exact
    /// (`|result| <= |y|/2`), so the true result is always representable in the
    /// operand format. We compute it with exact rational/bigint arithmetic —
    /// mirroring the blaster's exact bounded modular reduction
    /// (`ay_fp::special_ops::rem_modular_reduce`) — rather than via `f64`. The
    /// old `f64` path (`(fa/fb).round_ties_even()`, then `fa - fb*q`) overflowed
    /// or lost precision for large exponent gaps (e.g. `1e300 rem 3`,
    /// `1e-300 rem 1e-320`), which could yield a wrong remainder and hence a
    /// wrong model. (#fp-rem-exact)
    ///
    /// Special cases, identical to the blaster/z3:
    ///   * either operand NaN            → NaN
    ///   * `rem(±inf, y)`                → NaN
    ///   * `rem(x, ±inf)`               → x
    ///   * `rem(x, ±0)`                 → NaN
    ///   * `rem(±0, y)` (y finite ≠ 0)  → ±0 (sign of x)
    ///   * result exactly zero           → zero with the sign of x
    ///   * otherwise sign follows the exact subtraction (`from_rational`)
    fn fp_rem_exact(&self, x: &FpModelValue, y: &FpModelValue) -> EvalValue {
        let eb = x.eb();
        let sb = x.sb();
        let make_zero_like_x = |neg: bool| {
            if neg {
                EvalValue::Fp(FpModelValue::NegZero { eb, sb })
            } else {
                EvalValue::Fp(FpModelValue::PosZero { eb, sb })
            }
        };

        // NaN propagation and the infinite/zero special cases.
        if x.is_nan() || y.is_nan() || x.is_infinite() || y.is_zero() {
            return EvalValue::Fp(FpModelValue::NaN { eb, sb });
        }
        if y.is_infinite() {
            return EvalValue::Fp(x.clone());
        }
        if x.is_zero() {
            return make_zero_like_x(x.is_negative());
        }

        // Both operands finite and nonzero: exact rational remainder.
        let (Some(xr), Some(yr)) = (x.to_rational(), y.to_rational()) else {
            return EvalValue::Unknown;
        };
        let q = &xr / &yr;
        let n = round_rational_to_integer(&q, RoundingMode::RNE);
        let r = &xr - &yr * BigRational::from_integer(n);

        if r.numer().is_zero() {
            // Sign of a zero remainder follows the dividend x.
            return make_zero_like_x(x.is_negative());
        }
        // The remainder is exact and representable, so RNE performs no rounding.
        FpModelValue::from_rational_with_format(&r, eb, sb, RoundingMode::RNE)
            .map_or(EvalValue::Unknown, EvalValue::Fp)
    }

    fn signed_bv_to_bigint(&self, value: &BigInt, width: u32) -> BigInt {
        if width == 0 {
            return value.clone();
        }
        let sign_bit = (value >> (width - 1) as usize) & BigInt::one();
        if sign_bit.is_zero() {
            value.clone()
        } else {
            value - (BigInt::one() << width as usize)
        }
    }

    fn cast_fp_value(
        &self,
        value: &FpModelValue,
        eb: u32,
        sb: u32,
        rm: RoundingMode,
    ) -> Option<FpModelValue> {
        if value.is_nan() {
            Some(FpModelValue::NaN { eb, sb })
        } else if value.is_infinite() {
            Some(if value.is_negative() {
                FpModelValue::NegInf { eb, sb }
            } else {
                FpModelValue::PosInf { eb, sb }
            })
        } else if value.is_zero() {
            Some(if value.is_negative() {
                FpModelValue::NegZero { eb, sb }
            } else {
                FpModelValue::PosZero { eb, sb }
            })
        } else {
            let rational = value.to_rational()?;
            FpModelValue::from_rational_with_format(&rational, eb, sb, rm)
        }
    }

    fn convert_value_to_fp_eval(
        &self,
        value: EvalValue,
        eb: u32,
        sb: u32,
        rm: RoundingMode,
        signed_bv: bool,
    ) -> EvalValue {
        match value {
            EvalValue::Rational(r) => FpModelValue::from_rational_with_format(&r, eb, sb, rm)
                .map_or(EvalValue::Unknown, EvalValue::Fp),
            EvalValue::BitVec { value, width } => {
                let int_value = if signed_bv {
                    self.signed_bv_to_bigint(&value, width)
                } else {
                    value
                };
                let rational = BigRational::from_integer(int_value);
                FpModelValue::from_rational_with_format(&rational, eb, sb, rm)
                    .map_or(EvalValue::Unknown, EvalValue::Fp)
            }
            EvalValue::Fp(v) => self
                .cast_fp_value(&v, eb, sb, rm)
                .map_or(EvalValue::Unknown, EvalValue::Fp),
            _ => EvalValue::Unknown,
        }
    }

    /// `name(args)` computed exactly by `ay_fp::exact`, or Unknown when an
    /// operand or the mode is not pinned or the result is not computed there.
    fn exact_fp_op(&self, model: &Model, name: &str, args: &[TermId]) -> EvalValue {
        use ay_fp::exact;
        let fp = |i: usize| match self.evaluate_term(model, *args.get(i)?) {
            EvalValue::Fp(v) => Some(v),
            _ => None,
        };
        let rounded =
            |op: fn(RoundingMode, &FpModelValue, &FpModelValue) -> Option<FpModelValue>| {
                op(self.rounding_mode(model, args[0])?, &fp(1)?, &fp(2)?)
            };
        let value = match name {
            "fp.add" => rounded(exact::add),
            "fp.sub" => rounded(exact::sub),
            "fp.mul" => rounded(exact::mul),
            "fp.div" => rounded(exact::div),
            "fp.fma" => (|| {
                exact::fma(
                    self.rounding_mode(model, args[0])?,
                    &fp(1)?,
                    &fp(2)?,
                    &fp(3)?,
                )
            })(),
            "fp.sqrt" => (|| exact::sqrt(self.rounding_mode(model, args[0])?, &fp(1)?))(),
            "fp.roundToIntegral" => {
                (|| exact::round_to_integral(self.rounding_mode(model, args[0])?, &fp(1)?))()
            }
            "fp.min" => (|| exact::min(&fp(0)?, &fp(1)?))(),
            "fp.max" => (|| exact::max(&fp(0)?, &fp(1)?))(),
            _ => None,
        };
        value.map_or(EvalValue::Unknown, EvalValue::Fp)
    }

    /// Evaluate a floating-point application term.
    ///
    /// Handles all `fp.*` operations, `fp` constructor, `to_fp`, `to_fp_unsigned`,
    /// and FP conversion operations (`fp.to_ubv`, `fp.to_sbv`, `fp.to_real`, `fp.to_ieee_bv`).
    pub(super) fn evaluate_fp_app(
        &self,
        model: &Model,
        _sym: &Symbol,
        name: &str,
        args: &[TermId],
        sort: &Sort,
        term_id: TermId,
    ) -> EvalValue {
        if self.evaluation_stop_origin().is_some() {
            return EvalValue::Unknown;
        }
        let work_before = super::eval_guard::work_budget_poison();
        if matches!(sort, Sort::FloatingPoint(..))
            && !super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, term_id)
        {
            if let Some(ref fp_model) = model.fp_model {
                if let Some(val) = fp_model.values.get(&term_id) {
                    return EvalValue::Fp(val.clone());
                }
            }
        }

        let eval = match name {
            "+zero" | "fp.zero" if args.is_empty() => match sort {
                Sort::FloatingPoint(eb, sb) => {
                    EvalValue::Fp(FpModelValue::PosZero { eb: *eb, sb: *sb })
                }
                _ => EvalValue::Unknown,
            },
            "-zero" if args.is_empty() => match sort {
                Sort::FloatingPoint(eb, sb) => {
                    EvalValue::Fp(FpModelValue::NegZero { eb: *eb, sb: *sb })
                }
                _ => EvalValue::Unknown,
            },
            "+oo" | "fp.inf" if args.is_empty() => match sort {
                Sort::FloatingPoint(eb, sb) => {
                    EvalValue::Fp(FpModelValue::PosInf { eb: *eb, sb: *sb })
                }
                _ => EvalValue::Unknown,
            },
            "-oo" if args.is_empty() => match sort {
                Sort::FloatingPoint(eb, sb) => {
                    EvalValue::Fp(FpModelValue::NegInf { eb: *eb, sb: *sb })
                }
                _ => EvalValue::Unknown,
            },
            "NaN" | "fp.nan" if args.is_empty() => match sort {
                Sort::FloatingPoint(eb, sb) => {
                    EvalValue::Fp(FpModelValue::NaN { eb: *eb, sb: *sb })
                }
                _ => EvalValue::Unknown,
            },
            // ===== Floating-point operations (Part of #5995) =====

            // FP classification predicates
            "fp.isNaN" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_nan()),
                _ => EvalValue::Unknown,
            },
            "fp.isInfinite" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_infinite()),
                _ => EvalValue::Unknown,
            },
            "fp.isZero" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_zero()),
                _ => EvalValue::Unknown,
            },
            "fp.isNormal" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_normal()),
                _ => EvalValue::Unknown,
            },
            "fp.isSubnormal" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_subnormal()),
                _ => EvalValue::Unknown,
            },
            "fp.isPositive" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_positive()),
                _ => EvalValue::Unknown,
            },
            "fp.isNegative" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_negative()),
                _ => EvalValue::Unknown,
            },

            // FP unary operations
            "fp.neg" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Fp(v.negate()),
                _ => EvalValue::Unknown,
            },
            "fp.abs" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Fp(v.abs()),
                _ => EvalValue::Unknown,
            },

            // FP comparison predicates (exact same-format field order)
            "fp.eq" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => EvalValue::Bool(a.fp_eq(&b)),
                    _ => EvalValue::Unknown,
                }
            }
            "fp.lt" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => {
                        a.fp_lt(&b).map_or(EvalValue::Unknown, EvalValue::Bool)
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "fp.leq" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => {
                        a.fp_leq(&b).map_or(EvalValue::Unknown, EvalValue::Bool)
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "fp.gt" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => {
                        a.fp_gt(&b).map_or(EvalValue::Unknown, EvalValue::Bool)
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "fp.geq" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => {
                        a.fp_geq(&b).map_or(EvalValue::Unknown, EvalValue::Bool)
                    }
                    _ => EvalValue::Unknown,
                }
            }

            // Rounding arithmetic, exactly under every mode and format
            // (`ay_fp::exact`: exact rationals, one rounding). A result it does
            // not compute (a format outside its envelope, `fp.min` of +0 and
            // -0, an unpinned mode) is Unknown here and is evaluated by the
            // bit-blasted fallback below.
            "fp.add" | "fp.sub" | "fp.mul" | "fp.div" if args.len() == 3 => {
                self.exact_fp_op(model, name, args)
            }
            "fp.sqrt" | "fp.roundToIntegral" if args.len() == 2 => {
                self.exact_fp_op(model, name, args)
            }
            "fp.fma" if args.len() == 4 => self.exact_fp_op(model, name, args),
            "fp.min" | "fp.max" if args.len() == 2 => self.exact_fp_op(model, name, args),
            "fp.rem" if args.len() == 2 => {
                // fp.rem has no rounding mode argument. Computed with exact
                // rational arithmetic (see `fp_rem_exact`) — the f64 path lost
                // precision / overflowed for large exponent gaps. (#fp-rem-exact)
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => self.fp_rem_exact(&a, &b),
                    _ => EvalValue::Unknown,
                }
            }
            // FP constructor: (fp #bS #bE #bM) → FpModelValue
            "fp" if args.len() == 3 => self
                .fp_from_model_fields(model, args, sort)
                .map_or(EvalValue::Unknown, EvalValue::Fp),

            // (_ to_fp eb sb) from BV: reinterpret bitvector as IEEE 754
            "to_fp" if args.len() == 1 => self
                .fp_from_model_ieee_bits(model, args[0], sort)
                .map_or(EvalValue::Unknown, EvalValue::Fp),

            // (_ to_fp eb sb) from FP / signed BV / Real / Int
            // args[0] = rounding mode, args[1] = source value
            "to_fp" if args.len() == 2 => {
                let Some(rm) = self.rounding_mode(model, args[0]) else {
                    return EvalValue::Unknown;
                };
                let Sort::FloatingPoint(eb, sb) = sort else {
                    return EvalValue::Unknown;
                };
                self.convert_value_to_fp_eval(
                    self.evaluate_term(model, args[1]),
                    *eb,
                    *sb,
                    rm,
                    true,
                )
            }

            // (_ to_fp_unsigned eb sb) : unsigned BV → FP
            // args[0] = rounding mode, args[1] = unsigned bitvector
            "to_fp_unsigned" if args.len() == 2 => {
                let Some(rm) = self.rounding_mode(model, args[0]) else {
                    return EvalValue::Unknown;
                };
                let Sort::FloatingPoint(eb, sb) = sort else {
                    return EvalValue::Unknown;
                };
                self.convert_value_to_fp_eval(
                    self.evaluate_term(model, args[1]),
                    *eb,
                    *sb,
                    rm,
                    false,
                )
            }

            // (_ fp.to_ubv m) : FP → (_ BitVec m)
            // args[0] = rounding mode, args[1] = FP value
            "fp.to_ubv" if args.len() == 2 => {
                let Some(rm) = self.rounding_mode(model, args[0]) else {
                    return EvalValue::Unknown;
                };
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                match self.evaluate_term(model, args[1]) {
                    EvalValue::Fp(v) => {
                        // NaN, the infinities and out-of-range values leave the
                        // result unspecified — but the solve CHOSE one, as a
                        // function of (rm, x). Read that choice back (recorded
                        // by the FP bit-blaster), as `fp.to_ieee_bv` of NaN
                        // does; abstain when it is not recorded.
                        if v.is_nan() || v.is_infinite() {
                            return self.unspec_to_bv(model, term_id, sort, rm, &v);
                        }
                        match v.to_rational() {
                            Some(r) => {
                                // Exact rational rounding under the requested mode
                                // (RTZ/RTP/RTN/RNE/RNA), then unsigned range check.
                                let int_val = round_rational_to_integer(&r, rm);
                                let width = bv.width;
                                let max_val = (BigInt::one() << width as usize) - BigInt::one();
                                if int_val.is_negative() || int_val > max_val {
                                    return self.unspec_to_bv(model, term_id, sort, rm, &v);
                                }
                                EvalValue::BitVec {
                                    value: int_val,
                                    width,
                                }
                            }
                            None => EvalValue::Unknown,
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }

            // (_ fp.to_sbv m) : FP → (_ BitVec m) (signed)
            // args[0] = rounding mode, args[1] = FP value
            "fp.to_sbv" if args.len() == 2 => {
                let Some(rm) = self.rounding_mode(model, args[0]) else {
                    return EvalValue::Unknown;
                };
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                match self.evaluate_term(model, args[1]) {
                    EvalValue::Fp(v) => {
                        // Unspecified off its domain, but chosen: see fp.to_ubv.
                        if v.is_nan() || v.is_infinite() {
                            return self.unspec_to_bv(model, term_id, sort, rm, &v);
                        }
                        match v.to_rational() {
                            Some(r) => {
                                // Exact rational rounding under the requested mode
                                // (RTZ/RTP/RTN/RNE/RNA), then signed range check.
                                let int_val = round_rational_to_integer(&r, rm);
                                let width = bv.width;
                                // Signed range: [-(2^(w-1)), 2^(w-1) - 1]
                                let min_val = -(BigInt::one() << (width as usize - 1));
                                let max_val =
                                    (BigInt::one() << (width as usize - 1)) - BigInt::one();
                                if int_val < min_val || int_val > max_val {
                                    return self.unspec_to_bv(model, term_id, sort, rm, &v);
                                }
                                // Two's complement encoding
                                let modulus = BigInt::one() << width as usize;
                                let val = ((int_val % &modulus) + &modulus) % &modulus;
                                EvalValue::BitVec { value: val, width }
                            }
                            None => EvalValue::Unknown,
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }

            // fp.to_real : FP → Real
            "fp.to_real" if args.len() == 1 => {
                match self.evaluate_term(model, args[0]) {
                    EvalValue::Fp(v) => {
                        // Use to_rational() for exact conversion (not to_f64()
                        // which loses precision for values not representable
                        // as f64, e.g. Float128 subnormals).
                        match v.to_rational() {
                            Some(r) => EvalValue::Rational(r),
                            // NaN and the infinities: SMT-LIB leaves the result
                            // unspecified but TOTAL, so there is nothing to
                            // recompute — the solve CHOSE a value, and
                            // `pin_undefined_fp_to_real` recorded it against
                            // this application. Reading it back is what makes
                            // the choice observable to the validator and the
                            // independent gate; without it the model silently
                            // omits an interpretation it actually committed to.
                            None => model
                                .lra_model
                                .as_ref()
                                .and_then(|lra| lra.values.get(&term_id))
                                .map_or(EvalValue::Unknown, |r| EvalValue::Rational(r.clone())),
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }

            // fp.to_ieee_bv : FP → BV (bit-pattern reinterpretation)
            "fp.to_ieee_bv" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => {
                    // NaN has ONE value per FP sort but many IEEE encodings, so
                    // which encoding `fp.to_ieee_bv` returns is unspecified
                    // (the solver picks one free-but-shared pattern per format;
                    // see `FpSolver::bitblast_to_ieee_bv`). Recomputing a
                    // canonical guess here would contradict the solver's own
                    // choice and falsify a perfectly good model, so read the
                    // chosen encoding out of the bit-blasted assignment and
                    // abstain when it is not recorded.
                    if v.is_nan() {
                        let chosen = self.bv_model_cache_fallback(model, term_id, sort);
                        // With no bit-blasted BV assignment anywhere in this
                        // solve there is no choice to contradict, so any NaN
                        // encoding is a faithful value: report the canonical
                        // quiet NaN rather than declining.
                        if matches!(chosen, EvalValue::Unknown) && model.bv_model.is_some() {
                            return EvalValue::Unknown;
                        }
                        if !matches!(chosen, EvalValue::Unknown) {
                            return chosen;
                        }
                    }
                    let (value, width) = v.to_ieee_bv();
                    EvalValue::BitVec { value, width }
                }
                _ => EvalValue::Unknown,
            },
            _ => EvalValue::Unknown,
        };

        if matches!(eval, EvalValue::Unknown) {
            // A stopped child is not an unavailable operand to reconstruct.
            // This local comparison does not turn every opportunistic W4
            // budget refusal elsewhere into a terminal evaluation failure.
            if self.evaluation_stop_origin().is_some() {
                return EvalValue::Unknown;
            }
            if super::eval_guard::work_budget_poison() != work_before {
                self.record_evaluation_stop(
                    crate::executor_types::UnknownOrigin::DeterministicResourceBudget,
                );
                return EvalValue::Unknown;
            }
            // These fields were checked exactly above. An invalid shape or
            // unavailable field is not permission to reconstruct another value.
            // Keep this refusal after the stopped-child checks so a work-budget
            // refusal remains sticky for the entire external read.
            if (name == "fp" && args.len() == 3) || (name == "to_fp" && args.len() == 1) {
                return EvalValue::Unknown;
            }
            match self.evaluate_fp_term_via_bitblast_controlled(model, term_id, &|_| {}) {
                Ok(Some(value)) => EvalValue::Fp(value),
                Ok(None) => EvalValue::Unknown,
                Err(origin) => {
                    self.record_evaluation_stop(origin);
                    EvalValue::Unknown
                }
            }
        } else {
            eval
        }
    }
}
