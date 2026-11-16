// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original value-to-term spelling; controlled callers bracket every clone.

use ay_core::term::{Constant, Symbol};
use ay_fp::RoundingMode;
use num_bigint::BigInt;

use super::super::EvalValue;
use super::*;

impl Executor {
    /// Field copies plus the bounded local payloads of three scalars and one
    /// application. The owner separately polls actual arena capacity growth.
    pub(in crate::executor) fn fp_model_clone_scratch_bytes(value: &FpModelValue) -> Option<usize> {
        let (eb, sb) = (value.eb(), value.sb());
        if !(2..=ay_fp::MAX_ENCODING_EXPONENT_BITS).contains(&eb)
            || !(2..=ay_fp::MAX_ENCODING_SIGNIFICAND_BITS).contains(&sb)
        {
            return None;
        }
        let occupied = match value {
            FpModelValue::Exact(fields) => fields
                .exponent()
                .bits()
                .checked_add(fields.significand().bits())?,
            FpModelValue::Fp {
                sign,
                exponent,
                significand,
                ..
            } => {
                FpModelValue::from_fields(*sign, *exponent, *significand, eb, sb)?;
                u64::from(u64::BITS - exponent.leading_zeros())
                    + u64::from(u128::BITS - significand.leading_zeros())
            }
            _ => 0,
        };
        usize::try_from(occupied.div_ceil(64))
            .ok()?
            .checked_mul(4 * size_of::<u64>())?
            .checked_add(4096)
    }

    pub(super) fn clone_eval_value_term(
        &self,
        terms: &mut TermStore,
        sort: &Sort,
        value: &EvalValue,
        control: &Control<'_>,
    ) -> Result<Option<TermId>, UnknownOrigin> {
        let result = match value {
            EvalValue::Bool(v) => Some(terms.mk_bool(*v)),
            EvalValue::Rational(r) => {
                if matches!(sort, Sort::Int) && r.is_integer() {
                    Some(terms.mk_int(r.numer().clone()))
                } else {
                    Some(terms.mk_rational(r.clone()))
                }
            }
            EvalValue::BitVec { value, width } => Some(terms.mk_bitvec(value.clone(), *width)),
            EvalValue::Fp(fp) => return self.clone_fp_value_term(terms, sort, fp, control),
            EvalValue::String(s) => Some(terms.mk_string(s.clone())),
            // RoundingMode model value (#P0.2 symbolic RoundingMode): clone as
            // the literal nullary app, which the standalone FP solver resolves
            // by name (`RoundingMode::from_name` accepts the long spelling).
            EvalValue::Element(name)
                if matches!(sort, Sort::Uninterpreted(s) if s == "RoundingMode")
                    && RoundingMode::from_name(name).is_some()
                    && !terms.is_declared_function(name) =>
            {
                Some(terms.mk_app(Symbol::named(name), vec![], sort.clone()))
            }
            _ => None,
        };
        Ok(result)
    }

    pub(super) fn clone_fp_value_term(
        &self,
        terms: &mut TermStore,
        expected: &Sort,
        value: &FpModelValue,
        control: &Control<'_>,
    ) -> Result<Option<TermId>, UnknownOrigin> {
        if !control.admit_fp_clone(terms, expected, value)? {
            return Ok(None);
        }
        let eb = value.eb();
        let sb = value.sb();
        let sort = Sort::FloatingPoint(eb, sb);
        let result = match value {
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
            FpModelValue::Exact(_) | FpModelValue::Fp { .. } => {
                let (sign, exponent, significand) = match value {
                    FpModelValue::Exact(fields) => (
                        fields.sign(),
                        BigInt::from(fields.exponent().clone()),
                        BigInt::from(fields.significand().clone()),
                    ),
                    FpModelValue::Fp {
                        sign,
                        exponent,
                        significand,
                        ..
                    } => (*sign, BigInt::from(*exponent), BigInt::from(*significand)),
                    _ => return Ok(None),
                };
                let sign_term = terms.mk_bitvec(BigInt::from(u8::from(sign)), 1);
                let exp_term = terms.mk_bitvec(exponent, eb);
                let sig_term = terms.mk_bitvec(significand, sb - 1);
                Some(terms.mk_app(
                    Symbol::named("fp"),
                    vec![sign_term, exp_term, sig_term],
                    sort,
                ))
            }
        };
        control.poll(Some(terms))?;
        Ok(result)
    }

    pub(super) fn clone_constant_term(
        &self,
        terms: &mut TermStore,
        constant: &Constant,
    ) -> Option<TermId> {
        match constant {
            Constant::Bool(v) => Some(terms.mk_bool(*v)),
            Constant::Int(v) => Some(terms.mk_int(v.clone())),
            Constant::Rational(v) => Some(terms.mk_rational(v.0.clone())),
            Constant::BitVec { value, width } => Some(terms.mk_bitvec(value.clone(), *width)),
            Constant::String(s) => Some(terms.mk_string(s.clone())),
            _ => None,
        }
    }
}
