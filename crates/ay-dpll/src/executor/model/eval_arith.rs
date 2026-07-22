// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic evaluation helpers for model evaluation.
//!
//! Handles SMT-LIB arithmetic operations: `+`, `-`, `*`, `/`, `div`, `mod`,
//! `abs`, `to_real`, `to_int`, `is_int`, `<`, `<=`, `>`, `>=`.
//!
//! Values are exact real scalars: rationals, or exact real ALGEBRAIC values
//! (`EvalValue::Algebraic`, e.g. `√2` for an NRA `x*x = 2` witness). All
//! algebraic arithmetic is exact — residue reduction modulo the defining
//! polynomial and Sturm-sequence sign determination (see `ay_nra::algebraic`)
//! — so `(* x x)` at `x = √2` evaluates to the exact rational `2` and
//! `(> x 0)` to a definitive `true`. Anything that cannot be computed exactly
//! evaluates to `Unknown` (fail closed), never to an approximation.
//!
//! Extracted from `mod.rs` to reduce file size (#5970 code-health splits).
//! All methods are `impl Executor` — they share the same method namespace.

use ay_core::TermId;
use ay_nra::RealScalar;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::{EvalValue, Executor, Model};

/// Lift an evaluated value into an exact real scalar, or `None` for
/// non-numeric / unknown values.
fn to_scalar(v: EvalValue) -> Option<RealScalar> {
    match v {
        EvalValue::Rational(r) => Some(RealScalar::Rational(r)),
        EvalValue::Algebraic(a) => Some(RealScalar::Algebraic(a)),
        _ => None,
    }
}

/// Lower an exact real scalar back to an evaluated value.
fn from_scalar(s: RealScalar) -> EvalValue {
    match s {
        RealScalar::Rational(r) => EvalValue::Rational(r),
        RealScalar::Algebraic(a) => EvalValue::Algebraic(a),
    }
}

impl Executor {
    /// Evaluate an arithmetic operator application.
    ///
    /// Caller must only pass recognized arithmetic operator names.
    pub(super) fn evaluate_arith_app(
        &self,
        model: &Model,
        name: &str,
        args: &[TermId],
    ) -> EvalValue {
        match name {
            // Arithmetic addition
            "+" => {
                let mut sum = RealScalar::Rational(BigRational::zero());
                for &arg in args {
                    let Some(v) = to_scalar(self.evaluate_term(model, arg)) else {
                        return EvalValue::Unknown;
                    };
                    match sum.add(&v) {
                        Some(s) => sum = s,
                        None => return EvalValue::Unknown,
                    }
                }
                from_scalar(sum)
            }
            // Arithmetic subtraction (unary or binary)
            "-" => {
                if args.is_empty() {
                    return EvalValue::Unknown;
                }
                let Some(mut result) = to_scalar(self.evaluate_term(model, args[0])) else {
                    return EvalValue::Unknown;
                };
                if args.len() == 1 {
                    // Unary negation
                    return from_scalar(result.neg());
                }
                for &arg in &args[1..] {
                    let Some(v) = to_scalar(self.evaluate_term(model, arg)) else {
                        return EvalValue::Unknown;
                    };
                    match result.add(&v.neg()) {
                        Some(s) => result = s,
                        None => return EvalValue::Unknown,
                    }
                }
                from_scalar(result)
            }
            // Arithmetic multiplication
            "*" => {
                // Zero short-circuit (#anra-nested-product wrong-sat): `0 * x = 0`
                // for ANY x over Int/Real, even when x is Unknown. Without this, a
                // nonlinear product whose value is forced to zero by a definitively
                // zero factor — e.g. `(* (* (select A 1) (select A 1)) (select A 5))`
                // with `(select A 1) = 0` but `(select A 5)` unresolved — evaluated to
                // Unknown, so an assertion `(= <product> 2.0)` could not be observed as
                // Bool(false) and the internally-inconsistent model escaped as a wrong
                // SAT. Computing the definitive 0 lets the strict gate degrade SAT →
                // Unknown. SOUND: 0 times anything is 0 in any model, so this can only
                // make a product MORE concrete (Unknown → 0), never flip a verdict.
                // (An ALGEBRAIC factor is never zero: residue reduction collapses an
                // exactly-zero value to the rational 0 at construction.)
                let mut product = RealScalar::Rational(BigRational::from_integer(BigInt::from(1)));
                let mut saw_unknown = false;
                for &arg in args {
                    match to_scalar(self.evaluate_term(model, arg)) {
                        Some(RealScalar::Rational(r)) if r.is_zero() => {
                            return EvalValue::Rational(BigRational::zero());
                        }
                        Some(v) => match product.mul(&v) {
                            Some(pr) => product = pr,
                            None => saw_unknown = true,
                        },
                        None => saw_unknown = true,
                    }
                }
                if saw_unknown {
                    EvalValue::Unknown
                } else {
                    from_scalar(product)
                }
            }
            // Arithmetic division
            "/" => {
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                let num = to_scalar(self.evaluate_term(model, args[0]));
                let denom = to_scalar(self.evaluate_term(model, args[1]));
                match (num, denom) {
                    // Exact reciprocal: rational, or algebraic via the
                    // reversed defining polynomial (`RealScalar::recip`). A
                    // zero denominator or a refinement cap fails closed to
                    // Unknown — never an approximation.
                    (Some(n), Some(d)) => match d.recip() {
                        Some(inv) => match n.mul(&inv) {
                            Some(q) => from_scalar(q),
                            None => EvalValue::Unknown,
                        },
                        None => EvalValue::Unknown,
                    },
                    _ => EvalValue::Unknown,
                }
            }
            // SMT-LIB integer division (Euclidean, rounds toward -∞)
            // div t1 t2 = floor(t1/t2) when t2 > 0
            //           = ceil(t1/t2) when t2 < 0
            // Defined such that (mod t1 t2) is always non-negative.
            "div" => {
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                let lhs = self.evaluate_term(model, args[0]);
                let rhs = self.evaluate_term(model, args[1]);
                match (lhs, rhs) {
                    (EvalValue::Rational(n), EvalValue::Rational(d)) => {
                        if d.is_zero() || !n.is_integer() || !d.is_integer() {
                            EvalValue::Unknown
                        } else {
                            let ni = n.numer().clone();
                            let di = d.numer().clone();
                            let q = Self::euclidean_div(&ni, &di);
                            EvalValue::Rational(BigRational::from_integer(q))
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            // SMT-LIB integer modulo (Euclidean, always non-negative)
            // mod t1 t2 = t1 - (div t1 t2) * t2
            // Result satisfies: 0 <= (mod t1 t2) < |t2|
            "mod" => {
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                let lhs = self.evaluate_term(model, args[0]);
                let rhs = self.evaluate_term(model, args[1]);
                match (lhs, rhs) {
                    (EvalValue::Rational(n), EvalValue::Rational(d)) => {
                        if d.is_zero() || !n.is_integer() || !d.is_integer() {
                            EvalValue::Unknown
                        } else {
                            let ni = n.numer().clone();
                            let di = d.numer().clone();
                            let q = Self::euclidean_div(&ni, &di);
                            let r = ni - q * &di;
                            EvalValue::Rational(BigRational::from_integer(r))
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            // SMT-LIB / Z3 integer remainder `rem`, whose result takes the sign
            // of the DIVISOR (unlike `mod`, which is always non-negative):
            //   rem t1 t2 =  (mod t1 t2)  when t2 > 0
            //            = -(mod t1 t2)  when t2 < 0
            // Under-specified when t2 = 0 (Z3 #9140: kept distinct from `mod`),
            // so a zero divisor evaluates to Unknown rather than a pinned value.
            "rem" => {
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                let lhs = self.evaluate_term(model, args[0]);
                let rhs = self.evaluate_term(model, args[1]);
                match (lhs, rhs) {
                    (EvalValue::Rational(n), EvalValue::Rational(d)) => {
                        if d.is_zero() || !n.is_integer() || !d.is_integer() {
                            EvalValue::Unknown
                        } else {
                            let ni = n.numer().clone();
                            let di = d.numer().clone();
                            let q = Self::euclidean_div(&ni, &di);
                            let euclid_r = ni - q * &di; // 0 <= euclid_r < |di|
                            let rem = if di.is_negative() {
                                -euclid_r
                            } else {
                                euclid_r
                            };
                            EvalValue::Rational(BigRational::from_integer(rem))
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            // Absolute value
            "abs" => {
                if args.len() != 1 {
                    return EvalValue::Unknown;
                }
                match self.evaluate_term(model, args[0]) {
                    EvalValue::Rational(v) => EvalValue::Rational(v.abs()),
                    EvalValue::Algebraic(a) => match a.sign() {
                        Some(s) if s < 0 => EvalValue::Algebraic(a.neg()),
                        Some(_) => EvalValue::Algebraic(a),
                        None => EvalValue::Unknown,
                    },
                    _ => EvalValue::Unknown,
                }
            }
            // Int-to-Real conversion (#5947): to_real(x) evaluates
            // x and returns its value. LRA treats to_real as identity,
            // but the model evaluator needs this to look up Int-sorted
            // variables in the LIA model for model validation.
            "to_real" => {
                if args.len() != 1 {
                    return EvalValue::Unknown;
                }
                self.evaluate_term(model, args[0])
            }
            // Real-to-Int conversion: to_int(x) = floor(x)
            "to_int" => {
                if args.len() != 1 {
                    return EvalValue::Unknown;
                }
                match self.evaluate_term(model, args[0]) {
                    EvalValue::Rational(r) => {
                        let floored = r.floor().to_integer();
                        EvalValue::Rational(BigRational::from(floored))
                    }
                    // Exact floor of an algebraic real (interval refinement +
                    // integrality certificate).
                    EvalValue::Algebraic(a) => match a.floor() {
                        Some(n) => EvalValue::Rational(BigRational::from(n)),
                        None => EvalValue::Unknown,
                    },
                    other => other,
                }
            }
            // is_int(x) = true iff x is an integer
            "is_int" => {
                if args.len() != 1 {
                    return EvalValue::Unknown;
                }
                match self.evaluate_term(model, args[0]) {
                    EvalValue::Rational(r) => EvalValue::Bool(r.is_integer()),
                    EvalValue::Algebraic(a) => match a.is_integer() {
                        Some(b) => EvalValue::Bool(b),
                        None => EvalValue::Unknown,
                    },
                    _ => EvalValue::Unknown,
                }
            }
            // Less than
            "<" => self.eval_arith_cmp(model, args, |o| o == std::cmp::Ordering::Less),
            // Less than or equal
            "<=" => self.eval_arith_cmp(model, args, |o| o != std::cmp::Ordering::Greater),
            // Greater than
            ">" => self.eval_arith_cmp(model, args, |o| o == std::cmp::Ordering::Greater),
            // Greater than or equal
            ">=" => self.eval_arith_cmp(model, args, |o| o != std::cmp::Ordering::Less),
            _ => unreachable!("evaluate_arith_app called with non-arithmetic operator: {name}"),
        }
    }

    /// Helper for binary arithmetic comparison operators. Comparison of
    /// algebraic values is exact (Sturm-sequence sign determination); an
    /// undecidable comparison evaluates to Unknown (fail closed).
    fn eval_arith_cmp(
        &self,
        model: &Model,
        args: &[TermId],
        accept: impl FnOnce(std::cmp::Ordering) -> bool,
    ) -> EvalValue {
        if args.len() != 2 {
            return EvalValue::Unknown;
        }
        let lhs = to_scalar(self.evaluate_term(model, args[0]));
        let rhs = to_scalar(self.evaluate_term(model, args[1]));
        match (lhs, rhs) {
            (Some(l), Some(r)) => match l.cmp_exact(&r) {
                Some(ord) => EvalValue::Bool(accept(ord)),
                None => EvalValue::Unknown,
            },
            _ => EvalValue::Unknown,
        }
    }

    /// SMT-LIB Euclidean integer division: floor(n/d).
    ///
    /// Returns the unique integer q such that n = q*d + r and 0 <= r < |d|.
    /// Rust's truncating division differs from SMT-LIB when n and d have
    /// opposite signs.
    pub(super) fn euclidean_div(n: &BigInt, d: &BigInt) -> BigInt {
        use num_integer::Integer;
        let (q, r) = n.div_rem(d);
        // Rust truncates toward zero; adjust when remainder is negative.
        if r < BigInt::zero() {
            if *d > BigInt::zero() {
                q - 1
            } else {
                q + 1
            }
        } else {
            q
        }
    }
}
