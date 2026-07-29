// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point evaluation helpers for model evaluation.
//!
//! Extracted from `mod.rs` to reduce file size (Wave C1 of #2998 module splits).
//! All methods are `impl Executor` — they share the same method namespace.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData, TermStore};
use ay_core::{Sort, TermId};
use ay_fp::{FpModelValue, FpSolver, RoundingMode};
use ay_sat::{SatResult, Solver as SatSolver};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::{EvalValue, Executor, Model};

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
        let literal = match self.ctx.terms.get(rm_term) {
            TermData::App(sym, _) => RoundingMode::from_name(sym.name()),
            TermData::Var(name, _) => RoundingMode::from_name(name),
            _ => None,
        };
        if literal.is_some() {
            return literal;
        }
        match self.evaluate_term(model, rm_term) {
            EvalValue::Element(name) => RoundingMode::from_name(&name),
            _ => None,
        }
    }

    fn is_rne_rounding_mode(&self, model: &Model, rm_term: TermId) -> bool {
        matches!(self.rounding_mode(model, rm_term), Some(RoundingMode::RNE))
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

    /// Convert an `f64` result back to an `EvalValue::Fp`, inheriting the
    /// format (eb, sb) from a reference operand. Returns `Unknown` for
    /// formats wider than Float64 (eb=11, sb=53).
    fn f64_to_fp_eval(&self, val: f64, reference: &FpModelValue) -> EvalValue {
        let eb = reference.eb();
        let sb = reference.sb();
        if eb > 11 || sb > 53 {
            return EvalValue::Unknown;
        }
        if val.is_nan() {
            return EvalValue::Fp(FpModelValue::NaN { eb, sb });
        }
        if val.is_infinite() {
            return if val.is_sign_positive() {
                EvalValue::Fp(FpModelValue::PosInf { eb, sb })
            } else {
                EvalValue::Fp(FpModelValue::NegInf { eb, sb })
            };
        }
        if val == 0.0 {
            return if val.is_sign_negative() {
                EvalValue::Fp(FpModelValue::NegZero { eb, sb })
            } else {
                EvalValue::Fp(FpModelValue::PosZero { eb, sb })
            };
        }
        // Decompose into IEEE 754 components
        let bits = val.to_bits();
        let sign = (bits >> 63) != 0;
        let f64_exp = ((bits >> 52) & 0x7FF) as i64;
        let f64_frac = bits & 0x000F_FFFF_FFFF_FFFF;

        let bias = (1i64 << (eb - 1)) - 1;
        let stored_bits = sb - 1;

        if f64_exp == 0 {
            // Subnormal in f64 — try to represent in target format
            // The actual exponent is 1 - 1023 = -1022 for f64 subnormals
            let f64_bias: i64 = 1023;
            let actual_exp = 1 - f64_bias;
            let target_exp_biased = actual_exp + bias;
            if target_exp_biased <= 0 {
                // Subnormal in target format too
                let shift = i64::from(stored_bits) - 52 + (1 - target_exp_biased);
                let sig = if shift >= 0 {
                    f64_frac << shift as u64
                } else {
                    f64_frac >> (-shift) as u64
                };
                EvalValue::Fp(FpModelValue::Fp {
                    sign,
                    exponent: 0,
                    significand: sig,
                    eb,
                    sb,
                })
            } else {
                // Normalizes in target format — punt to Unknown for now
                EvalValue::Unknown
            }
        } else {
            // Normal in f64
            let f64_bias: i64 = 1023;
            let actual_exp = f64_exp - f64_bias;
            let target_exp_biased = actual_exp + bias;
            let max_exp = (1i64 << eb) - 1;
            if target_exp_biased >= max_exp {
                // Overflow to infinity in target format
                return if sign {
                    EvalValue::Fp(FpModelValue::NegInf { eb, sb })
                } else {
                    EvalValue::Fp(FpModelValue::PosInf { eb, sb })
                };
            }
            if target_exp_biased <= 0 {
                // Underflow to subnormal or zero in target format
                // Shift significand right by (1 - target_exp_biased) places
                let hidden = 1u64 << 52;
                let full_sig = f64_frac | hidden;
                let right_shift = (1 - target_exp_biased) as u64;
                let shift_to_target = if stored_bits >= 52 {
                    i64::from(stored_bits - 52)
                } else {
                    -i64::from(52 - stored_bits)
                };
                let sig = if shift_to_target >= 0 {
                    (full_sig >> right_shift) << shift_to_target as u64
                } else {
                    full_sig >> (right_shift + (-shift_to_target) as u64)
                };
                if sig == 0 {
                    return if sign {
                        EvalValue::Fp(FpModelValue::NegZero { eb, sb })
                    } else {
                        EvalValue::Fp(FpModelValue::PosZero { eb, sb })
                    };
                }
                return EvalValue::Fp(FpModelValue::Fp {
                    sign,
                    exponent: 0,
                    significand: sig,
                    eb,
                    sb,
                });
            }
            // Normal in target format: shift significand with RNE rounding (#6203)
            let sig = if stored_bits >= 52 {
                f64_frac << (stored_bits - 52)
            } else {
                let shift = 52 - stored_bits;
                let truncated = f64_frac >> shift;
                // RNE: check guard, round, sticky bits
                let guard = (f64_frac >> (shift - 1)) & 1;
                let sticky = if shift >= 2 {
                    (f64_frac & ((1u64 << (shift - 1)) - 1)) != 0
                } else {
                    false
                };
                // Round up if: guard=1 AND (sticky=1 OR truncated is odd)
                if guard == 1 && (sticky || (truncated & 1) == 1) {
                    truncated + 1
                } else {
                    truncated
                }
            };
            // Handle significand overflow from rounding (e.g., 0b1111...1 + 1)
            let max_sig = (1u64 << stored_bits) - 1;
            if sig > max_sig {
                let new_exp = target_exp_biased + 1;
                if new_exp >= max_exp {
                    return if sign {
                        EvalValue::Fp(FpModelValue::NegInf { eb, sb })
                    } else {
                        EvalValue::Fp(FpModelValue::PosInf { eb, sb })
                    };
                }
                EvalValue::Fp(FpModelValue::Fp {
                    sign,
                    exponent: new_exp as u64,
                    significand: 0, // carry into exponent
                    eb,
                    sb,
                })
            } else {
                EvalValue::Fp(FpModelValue::Fp {
                    sign,
                    exponent: target_exp_biased as u64,
                    significand: sig,
                    eb,
                    sb,
                })
            }
        }
    }

    fn clone_eval_value_term(
        &self,
        terms: &mut TermStore,
        sort: &Sort,
        value: &EvalValue,
    ) -> Option<TermId> {
        match value {
            EvalValue::Bool(v) => Some(terms.mk_bool(*v)),
            EvalValue::Rational(r) => {
                if matches!(sort, Sort::Int) && r.is_integer() {
                    Some(terms.mk_int(r.numer().clone()))
                } else {
                    Some(terms.mk_rational(r.clone()))
                }
            }
            EvalValue::BitVec { value, width } => Some(terms.mk_bitvec(value.clone(), *width)),
            EvalValue::Fp(fp) => self.clone_fp_value_term(terms, fp),
            EvalValue::String(s) => Some(terms.mk_string(s.clone())),
            // RoundingMode model value (#P0.2 symbolic RoundingMode): clone as
            // the literal nullary app, which the standalone FP solver resolves
            // by name (`RoundingMode::from_name` accepts the long spelling).
            EvalValue::Element(name)
                if matches!(sort, Sort::Uninterpreted(s) if s == "RoundingMode")
                    && RoundingMode::from_name(name).is_some() =>
            {
                Some(terms.mk_app(Symbol::named(name), vec![], sort.clone()))
            }
            _ => None,
        }
    }

    fn clone_fp_value_term(&self, terms: &mut TermStore, value: &FpModelValue) -> Option<TermId> {
        let eb = value.eb();
        let sb = value.sb();
        let sort = Sort::FloatingPoint(eb, sb);
        match value {
            FpModelValue::PosZero { .. } => {
                Some(terms.mk_app(Symbol::indexed("+zero", vec![eb, sb]), vec![], sort))
            }
            FpModelValue::NegZero { .. } => {
                Some(terms.mk_app(Symbol::indexed("-zero", vec![eb, sb]), vec![], sort))
            }
            FpModelValue::PosInf { .. } => {
                Some(terms.mk_app(Symbol::indexed("+oo", vec![eb, sb]), vec![], sort))
            }
            FpModelValue::NegInf { .. } => {
                Some(terms.mk_app(Symbol::indexed("-oo", vec![eb, sb]), vec![], sort))
            }
            FpModelValue::NaN { .. } => {
                Some(terms.mk_app(Symbol::indexed("NaN", vec![eb, sb]), vec![], sort))
            }
            FpModelValue::Fp { .. } => {
                let (bits, _) = value.to_ieee_bv();
                let sig_width = sb - 1;
                let sign = (&bits >> (eb + sig_width)) & BigInt::one();
                let exp_mask = (BigInt::one() << eb) - BigInt::one();
                let sig_mask = (BigInt::one() << sig_width) - BigInt::one();
                let exponent = (&bits >> sig_width) & exp_mask;
                let significand = bits & sig_mask;
                let sign_term = terms.mk_bitvec(sign, 1);
                let exp_term = terms.mk_bitvec(exponent, eb);
                let sig_term = terms.mk_bitvec(significand, sig_width);
                Some(terms.mk_app(
                    Symbol::named("fp"),
                    vec![sign_term, exp_term, sig_term],
                    sort,
                ))
            }
        }
    }

    fn clone_constant_term(&self, terms: &mut TermStore, constant: &Constant) -> Option<TermId> {
        match constant {
            Constant::Bool(v) => Some(terms.mk_bool(*v)),
            Constant::Int(v) => Some(terms.mk_int(v.clone())),
            Constant::Rational(v) => Some(terms.mk_rational(v.0.clone())),
            Constant::BitVec { value, width } => Some(terms.mk_bitvec(value.clone(), *width)),
            Constant::String(s) => Some(terms.mk_string(s.clone())),
            _ => None,
        }
    }

    fn concretize_term_for_fp_eval(
        &self,
        model: &Model,
        term_id: TermId,
        concrete_terms: &mut TermStore,
        cache: &mut HashMap<TermId, TermId>,
    ) -> Option<TermId> {
        if let Some(&cached) = cache.get(&term_id) {
            return Some(cached);
        }

        let sort = self.ctx.terms.sort(term_id).clone();

        // FP bit-blast completion rebuilds a fresh concrete term. A scoped
        // lambda value must be cloned into that term before any ambient FP
        // model lookup; otherwise the rebuilt expression captures the bound
        // variable's context-free model value instead of its beta value.
        if let Some(value) = super::dt_model::active_term_override_lookup(&self.ctx.terms, term_id)
        {
            let concrete = self.clone_eval_value_term(concrete_terms, &sort, &value)?;
            cache.insert(term_id, concrete);
            return Some(concrete);
        }

        if !matches!(sort, Sort::FloatingPoint(..)) {
            let eval = self.evaluate_term(model, term_id);
            if !matches!(eval, EvalValue::Unknown) {
                let concrete = self.clone_eval_value_term(concrete_terms, &sort, &eval)?;
                cache.insert(term_id, concrete);
                return Some(concrete);
            }
        } else if !super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, term_id) {
            if let Some(fp_model) = &model.fp_model {
                if let Some(value) = fp_model.values.get(&term_id) {
                    let concrete = self.clone_fp_value_term(concrete_terms, value)?;
                    cache.insert(term_id, concrete);
                    return Some(concrete);
                }
            }
        }

        // FAIL CLOSED on an unpinned symbolic RoundingMode (#P0.2): cloning an
        // RM-sorted Var symbolically would let the standalone FP solver's
        // `get_rounding_mode` fall into its silent `default() == RNE` branch —
        // a wrong evaluation, not just an unknown one. (A model-pinned RM term
        // was already cloned as its literal by the Element arm above; a
        // LITERAL app or literal-named Var — embedder terms — resolves by name
        // downstream and passes through.)
        if matches!(&sort, Sort::Uninterpreted(s) if s == "RoundingMode")
            && !crate::executor::rm_domain::is_rm_literal(&self.ctx.terms, term_id)
        {
            return None;
        }

        let concrete = match self.ctx.terms.get(term_id) {
            TermData::Const(constant) => self.clone_constant_term(concrete_terms, constant)?,
            TermData::Var(name, _) => concrete_terms.mk_var(name.clone(), sort.clone()),
            TermData::App(sym, args) => {
                let concrete_args = args
                    .iter()
                    .map(|&arg| self.concretize_term_for_fp_eval(model, arg, concrete_terms, cache))
                    .collect::<Option<Vec<_>>>()?;
                concrete_terms.mk_app(sym.clone(), concrete_args, sort.clone())
            }
            TermData::Not(arg) => {
                let concrete_arg =
                    self.concretize_term_for_fp_eval(model, *arg, concrete_terms, cache)?;
                concrete_terms.mk_not(concrete_arg)
            }
            TermData::Ite(cond, then_term, else_term) => {
                let concrete_cond =
                    self.concretize_term_for_fp_eval(model, *cond, concrete_terms, cache)?;
                let concrete_then =
                    self.concretize_term_for_fp_eval(model, *then_term, concrete_terms, cache)?;
                let concrete_else =
                    self.concretize_term_for_fp_eval(model, *else_term, concrete_terms, cache)?;
                concrete_terms.mk_ite(concrete_cond, concrete_then, concrete_else)
            }
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return None,
            _ => return None,
        };

        cache.insert(term_id, concrete);
        Some(concrete)
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

    fn evaluate_fp_term_via_bitblast(&self, model: &Model, term_id: TermId) -> EvalValue {
        let Sort::FloatingPoint(..) = self.ctx.terms.sort(term_id) else {
            return EvalValue::Unknown;
        };

        let mut concrete_terms = TermStore::new();
        let mut cache = HashMap::default();
        let Some(concrete_term) =
            self.concretize_term_for_fp_eval(model, term_id, &mut concrete_terms, &mut cache)
        else {
            return EvalValue::Unknown;
        };

        let mut fp_solver = FpSolver::new(&concrete_terms);
        fp_solver.get_fp(concrete_term);
        if fp_solver.has_encoding_gap() {
            return EvalValue::Unknown;
        }

        let term_to_fp = fp_solver.term_to_fp().clone();
        let clauses = fp_solver.take_clauses();
        let mut sat_solver = SatSolver::new(fp_solver.num_vars() as usize);
        sat_solver.set_congruence_enabled(false);
        for clause in &clauses {
            let lits: Vec<ay_sat::Literal> = clause
                .literals()
                .iter()
                .map(|&lit| crate::cnf_lit_to_sat(lit))
                .collect();
            sat_solver.add_clause(lits);
        }

        match sat_solver.solve().into_inner() {
            SatResult::Sat(sat_model) => {
                let fp_model =
                    Self::extract_fp_model_from_bits(&sat_model, &term_to_fp, 0, &concrete_terms);
                fp_model
                    .values
                    .get(&concrete_term)
                    .cloned()
                    .map(EvalValue::Fp)
                    .unwrap_or(EvalValue::Unknown)
            }
            _ => EvalValue::Unknown,
        }
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

            // FP comparison predicates (via f64 conversion)
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

            // FP arithmetic (via f64 conversion, rounding mode arg[0])
            // f64 natively uses RNE. For non-RNE rounding modes, we
            // cannot compute the correct result via f64, so return
            // Unknown to skip model validation (#6203).
            "fp.add" if args.len() == 3 => {
                if !self.is_rne_rounding_mode(model, args[0]) {
                    EvalValue::Unknown
                } else {
                    match (
                        self.evaluate_term(model, args[1]),
                        self.evaluate_term(model, args[2]),
                    ) {
                        (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                            (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa + fb, &a),
                            _ => EvalValue::Unknown,
                        },
                        _ => EvalValue::Unknown,
                    }
                }
            }
            "fp.sub" if args.len() == 3 => {
                if !self.is_rne_rounding_mode(model, args[0]) {
                    EvalValue::Unknown
                } else {
                    match (
                        self.evaluate_term(model, args[1]),
                        self.evaluate_term(model, args[2]),
                    ) {
                        (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                            (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa - fb, &a),
                            _ => EvalValue::Unknown,
                        },
                        _ => EvalValue::Unknown,
                    }
                }
            }
            "fp.mul" if args.len() == 3 => {
                if !self.is_rne_rounding_mode(model, args[0]) {
                    EvalValue::Unknown
                } else {
                    match (
                        self.evaluate_term(model, args[1]),
                        self.evaluate_term(model, args[2]),
                    ) {
                        (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                            (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa * fb, &a),
                            _ => EvalValue::Unknown,
                        },
                        _ => EvalValue::Unknown,
                    }
                }
            }
            "fp.div" if args.len() == 3 => {
                if !self.is_rne_rounding_mode(model, args[0]) {
                    EvalValue::Unknown
                } else {
                    match (
                        self.evaluate_term(model, args[1]),
                        self.evaluate_term(model, args[2]),
                    ) {
                        (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                            (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa / fb, &a),
                            _ => EvalValue::Unknown,
                        },
                        _ => EvalValue::Unknown,
                    }
                }
            }
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
            "fp.sqrt" if args.len() == 2 => {
                // args[0] = rounding mode, args[1] = x
                if !self.is_rne_rounding_mode(model, args[0]) {
                    EvalValue::Unknown
                } else {
                    match self.evaluate_term(model, args[1]) {
                        EvalValue::Fp(a) => match a.to_f64() {
                            Some(fa) => self.f64_to_fp_eval(fa.sqrt(), &a),
                            None => EvalValue::Unknown,
                        },
                        _ => EvalValue::Unknown,
                    }
                }
            }
            "fp.min" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                        (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa.min(fb), &a),
                        _ => EvalValue::Unknown,
                    },
                    _ => EvalValue::Unknown,
                }
            }
            "fp.max" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                        (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa.max(fb), &a),
                        _ => EvalValue::Unknown,
                    },
                    _ => EvalValue::Unknown,
                }
            }
            "fp.roundToIntegral" if args.len() == 2 => {
                // args[0] = rounding mode, args[1] = x
                if !self.is_rne_rounding_mode(model, args[0]) {
                    EvalValue::Unknown
                } else {
                    match self.evaluate_term(model, args[1]) {
                        EvalValue::Fp(a) => match a.to_f64() {
                            Some(fa) => self.f64_to_fp_eval(fa.round(), &a),
                            None => EvalValue::Unknown,
                        },
                        _ => EvalValue::Unknown,
                    }
                }
            }
            "fp.fma" if args.len() == 4 => {
                // args[0] = rounding mode, args[1..3] = x, y, z
                // fma(x, y, z) = x * y + z
                if !self.is_rne_rounding_mode(model, args[0]) {
                    EvalValue::Unknown
                } else {
                    match (
                        self.evaluate_term(model, args[1]),
                        self.evaluate_term(model, args[2]),
                        self.evaluate_term(model, args[3]),
                    ) {
                        (EvalValue::Fp(a), EvalValue::Fp(b), EvalValue::Fp(c)) => {
                            match (a.to_f64(), b.to_f64(), c.to_f64()) {
                                (Some(fa), Some(fb), Some(fc)) => {
                                    self.f64_to_fp_eval(fa.mul_add(fb, fc), &a)
                                }
                                _ => EvalValue::Unknown,
                            }
                        }
                        _ => EvalValue::Unknown,
                    }
                }
            }

            // FP constructor: (fp #bS #bE #bM) → FpModelValue
            "fp" if args.len() == 3 => {
                let sign_val = match self.evaluate_term(model, args[0]) {
                    EvalValue::BitVec { value, width: 1 } => value != BigInt::zero(),
                    _ => return EvalValue::Unknown,
                };
                let exp_val = match self.evaluate_term(model, args[1]) {
                    EvalValue::BitVec { value, width } => (value.to_u64().unwrap_or(0), width),
                    _ => return EvalValue::Unknown,
                };
                let sig_val = match self.evaluate_term(model, args[2]) {
                    EvalValue::BitVec { value, width } => (value.to_u64().unwrap_or(0), width),
                    _ => return EvalValue::Unknown,
                };
                let eb = exp_val.1;
                let sb = sig_val.1 + 1; // SMT-LIB sb includes hidden bit
                let exponent = exp_val.0;
                let significand = sig_val.0;
                let max_exponent = (1u64 << eb) - 1;
                let fp_value = if exponent == max_exponent && significand != 0 {
                    FpModelValue::NaN { eb, sb }
                } else if exponent == max_exponent && significand == 0 {
                    if sign_val {
                        FpModelValue::NegInf { eb, sb }
                    } else {
                        FpModelValue::PosInf { eb, sb }
                    }
                } else if exponent == 0 && significand == 0 {
                    if sign_val {
                        FpModelValue::NegZero { eb, sb }
                    } else {
                        FpModelValue::PosZero { eb, sb }
                    }
                } else {
                    FpModelValue::Fp {
                        sign: sign_val,
                        exponent,
                        significand,
                        eb,
                        sb,
                    }
                };
                EvalValue::Fp(fp_value)
            }

            // (_ to_fp eb sb) from BV: reinterpret bitvector as IEEE 754
            "to_fp" if args.len() == 1 => {
                let Sort::FloatingPoint(eb, sb) = sort else {
                    return EvalValue::Unknown;
                };
                match self.evaluate_term(model, args[0]) {
                    EvalValue::BitVec { value, .. } => {
                        let total_bits = eb + sb;
                        let sign_val =
                            (value.clone() >> (total_bits - 1)) & BigInt::one() != BigInt::zero();
                        let exp_mask = (BigInt::one() << eb) - 1;
                        let exponent = ((value.clone() >> (sb - 1)) & &exp_mask)
                            .to_u64()
                            .unwrap_or(0);
                        let sig_mask = (BigInt::one() << (sb - 1)) - 1;
                        let significand = (&value & &sig_mask).to_u64().unwrap_or(0);
                        let max_exponent = (1u64 << eb) - 1;
                        let fp_value = if exponent == max_exponent && significand != 0 {
                            FpModelValue::NaN { eb: *eb, sb: *sb }
                        } else if exponent == max_exponent && significand == 0 {
                            if sign_val {
                                FpModelValue::NegInf { eb: *eb, sb: *sb }
                            } else {
                                FpModelValue::PosInf { eb: *eb, sb: *sb }
                            }
                        } else if exponent == 0 && significand == 0 {
                            if sign_val {
                                FpModelValue::NegZero { eb: *eb, sb: *sb }
                            } else {
                                FpModelValue::PosZero { eb: *eb, sb: *sb }
                            }
                        } else {
                            FpModelValue::Fp {
                                sign: sign_val,
                                exponent,
                                significand,
                                eb: *eb,
                                sb: *sb,
                            }
                        };
                        EvalValue::Fp(fp_value)
                    }
                    _ => EvalValue::Unknown,
                }
            }

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
                        if v.is_nan() || v.is_infinite() {
                            return EvalValue::Unknown;
                        }
                        match v.to_rational() {
                            Some(r) => {
                                // Exact rational rounding under the requested mode
                                // (RTZ/RTP/RTN/RNE/RNA), then unsigned range check.
                                let int_val = round_rational_to_integer(&r, rm);
                                let width = bv.width;
                                let max_val = (BigInt::one() << width as usize) - BigInt::one();
                                if int_val.is_negative() || int_val > max_val {
                                    return EvalValue::Unknown; // out of range → unspecified
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
                        if v.is_nan() || v.is_infinite() {
                            return EvalValue::Unknown;
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
                                    return EvalValue::Unknown; // overflow
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
                            None => EvalValue::Unknown,
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
            self.evaluate_fp_term_via_bitblast(model, term_id)
        } else {
            eval
        }
    }
}
