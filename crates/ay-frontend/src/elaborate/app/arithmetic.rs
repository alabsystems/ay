// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, Symbol, TermId};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::{Context, ElaborateError, Result};

impl Context {
    pub(super) fn try_elaborate_arithmetic_app(
        &mut self,
        name: &str,
        arg_ids: &mut [TermId],
    ) -> Result<Option<TermId>> {
        match name {
            "+" => {
                if arg_ids.is_empty() {
                    return Err(ElaborateError::InvalidConstant(
                        "+ requires at least 1 argument, got 0".to_string(),
                    ));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                Ok(Some(self.terms.mk_add(arg_ids.to_vec())))
            }
            "-" => {
                if arg_ids.is_empty() {
                    return Err(ElaborateError::InvalidConstant(
                        "- requires at least 1 argument, got 0".to_string(),
                    ));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                Ok(Some(self.terms.mk_sub(arg_ids.to_vec())))
            }
            // Z3 5.0.0 registers `~` as the unary-minus spelling. Unlike
            // left-associative `-`, it accepts exactly one operand.
            "~" => {
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "~ requires 1 argument, got {}",
                        arg_ids.len()
                    )));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                if !matches!(self.terms.sort(arg_ids[0]), Sort::Int | Sort::Real) {
                    return Err(ElaborateError::SortMismatch {
                        expected: "Int or Real".to_string(),
                        actual: self.terms.sort(arg_ids[0]).to_string(),
                    });
                }
                Ok(Some(self.terms.mk_neg(arg_ids[0])))
            }
            "*" => {
                if arg_ids.is_empty() {
                    return Err(ElaborateError::InvalidConstant(
                        "* requires at least 1 argument, got 0".to_string(),
                    ));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                Ok(Some(self.terms.mk_mul(arg_ids.to_vec())))
            }
            "^" => Ok(Some(self.elaborate_power(arg_ids)?)),
            "**" => Ok(Some(self.elaborate_integer_power(arg_ids)?)),
            // Z3 5.0.0's null-logic registry exposes `/` through its binary
            // left-associative declaration, whose AST application treats one
            // Real operand as the identity. The extension logics HORN and ALL
            // retain that registry behavior. Standard SMT-LIB logics instead
            // keep their theory arity: `(/ Real Real Real :left-assoc)` means
            // two-or-more operands.
            "/" => {
                if arg_ids.len() == 1 && matches!(self.logic(), None | Some("HORN") | Some("ALL")) {
                    let argument = arg_ids[0];
                    let actual = self.terms.sort(argument);
                    if actual != &Sort::Real {
                        return Err(ElaborateError::SortMismatch {
                            expected: Sort::Real.to_string(),
                            actual: actual.to_string(),
                        });
                    }
                    return Ok(Some(argument));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                if self.int_real_coercions() {
                    self.promote_int_consts_to_real(arg_ids)?;
                }
                if arg_ids.len() < 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "/ requires at least 2 arguments, got {}",
                        arg_ids.len()
                    )));
                }
                self.expect_all_args_sort(arg_ids, &Sort::Real)?;
                let mut acc = arg_ids[0];
                for &rhs in &arg_ids[1..] {
                    acc = self.terms.mk_div(acc, rhs);
                }
                Ok(Some(acc))
            }
            // The same Z3 5.0.0 null-logic/HORN/ALL left-associative behavior
            // makes unary `div` an Int identity. Standard SMT-LIB logics still
            // use the two-or-more `Ints` theory signature. Note that `mod`,
            // `rem` and `abs` are fixed-arity and must stay so.
            "div" => {
                if arg_ids.len() == 1 && matches!(self.logic(), None | Some("HORN") | Some("ALL")) {
                    let argument = arg_ids[0];
                    let actual = self.terms.sort(argument);
                    if actual != &Sort::Int {
                        return Err(ElaborateError::SortMismatch {
                            expected: Sort::Int.to_string(),
                            actual: actual.to_string(),
                        });
                    }
                    return Ok(Some(argument));
                }
                if arg_ids.len() < 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "div requires at least 2 arguments, got {}",
                        arg_ids.len()
                    )));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                self.expect_all_args_sort(arg_ids, &Sort::Int)?;
                let mut acc = arg_ids[0];
                for &rhs in &arg_ids[1..] {
                    acc = self.terms.mk_intdiv(acc, rhs);
                }
                Ok(Some(acc))
            }
            "mod" => {
                if arg_ids.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "mod requires 2 arguments, got {}",
                        arg_ids.len()
                    )));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                self.expect_all_args_sort(arg_ids, &Sort::Int)?;
                Ok(Some(self.terms.mk_mod(arg_ids[0], arg_ids[1])))
            }
            "rem" => {
                if arg_ids.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "rem requires 2 arguments, got {}",
                        arg_ids.len()
                    )));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                self.expect_all_args_sort(arg_ids, &Sort::Int)?;
                Ok(Some(self.terms.mk_rem(arg_ids[0], arg_ids[1])))
            }
            "abs" => {
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "abs requires 1 argument".to_string(),
                    ));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                if !matches!(self.terms.sort(arg_ids[0]), Sort::Int | Sort::Real) {
                    return Err(ElaborateError::SortMismatch {
                        expected: "Int or Real".to_string(),
                        actual: self.terms.sort(arg_ids[0]).to_string(),
                    });
                }
                Ok(Some(self.terms.mk_abs(arg_ids[0])))
            }
            "min" | "max" => {
                if arg_ids.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires 2 arguments"
                    )));
                }
                self.maybe_promote_numeric_args(arg_ids)?;
                Ok(Some(match name {
                    "min" => self.terms.mk_min(arg_ids[0], arg_ids[1]),
                    _ => self.terms.mk_max(arg_ids[0], arg_ids[1]),
                }))
            }
            "<" | "<=" | ">" | ">=" => {
                if arg_ids.len() < 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires at least 2 arguments"
                    )));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                if arg_ids.len() == 2 {
                    return Ok(Some(match name {
                        "<" => self.terms.mk_lt(arg_ids[0], arg_ids[1]),
                        "<=" => self.terms.mk_le(arg_ids[0], arg_ids[1]),
                        ">" => self.terms.mk_gt(arg_ids[0], arg_ids[1]),
                        _ => self.terms.mk_ge(arg_ids[0], arg_ids[1]),
                    }));
                }
                let mut cmps = Vec::new();
                for i in 0..arg_ids.len() - 1 {
                    cmps.push(match name {
                        "<" => self.terms.mk_lt(arg_ids[i], arg_ids[i + 1]),
                        "<=" => self.terms.mk_le(arg_ids[i], arg_ids[i + 1]),
                        ">" => self.terms.mk_gt(arg_ids[i], arg_ids[i + 1]),
                        _ => self.terms.mk_ge(arg_ids[i], arg_ids[i + 1]),
                    });
                }
                Ok(Some(self.terms.mk_and(cmps)))
            }
            _ => Ok(None),
        }
    }

    /// Elaborate `(^ base exp)` over Int/Real arithmetic.
    ///
    /// SMT-LIB (Reals_Ints §3.8) defines `^` as partial. This elaborator
    /// unfolds `(^ base n)` when `n` is a concrete integer literal:
    ///
    /// * `n == 0` → `1` (SMT-LIB: `x^0 = 1` for all `x`, including `0^0`
    ///   per Z3's convention of treating `0^0 = 1` via `^0`).
    /// * `n == 1` → `base`.
    /// * `n > 1` → `base * base * ... * base` (n factors).
    /// * `n < 0` → `(ite (= base 0) <fresh> (/ 1 base^|n|))`. The fresh
    ///   uninterpreted constant captures the SMT-LIB under-specification
    ///   for `0^n` when `n < 0`.
    ///
    /// Symbolic and non-integral exponents are rejected until AY has a theory
    /// implementation for them. Treating a surviving `^` application as an
    /// uninterpreted function is unsound: constraints on the exponent can make
    /// Z3 prove facts that EUF alone cannot see.
    #[allow(clippy::too_many_lines)]
    fn elaborate_power(&mut self, arg_ids: &[TermId]) -> Result<TermId> {
        if arg_ids.len() != 2 {
            return Err(ElaborateError::InvalidConstant(format!(
                "^ requires 2 arguments, got {}",
                arg_ids.len()
            )));
        }
        let base = arg_ids[0];
        let exp = arg_ids[1];

        let base_sort = self.terms.sort(base).clone();
        if !matches!(base_sort, Sort::Int | Sort::Real) {
            return Err(ElaborateError::InvalidConstant(format!(
                "^ requires arithmetic base, got {base_sort:?}"
            )));
        }

        // Try to extract a concrete integer exponent.
        let exp_int = self.terms.extract_integer_constant(exp);

        if let Some(n) = exp_int {
            return Ok(self.unfold_integer_power(base, &base_sort, &n));
        }

        Err(ElaborateError::Unsupported(
            "symbolic or non-integral exponentiation with `^` is not supported".to_string(),
        ))
    }

    /// Elaborate SMT-LIB 2.7 integer exponentiation `(** base exponent)`.
    ///
    /// The `Ints` theory gives `**` the rank `Int Int -> Int`. AY can lower a
    /// concrete integer exponent exactly into its existing integer arithmetic:
    /// non-negative powers become products, while a negative power is
    /// `(div 1 (base^(-exponent)))`. This is the defining equation in the
    /// pinned `Ints` theory, including its deliberately under-specified
    /// `(div 1 0)` value when the base is zero.
    ///
    /// A symbolic exponent remains a valid QF_EIA term. Preserve it as a typed
    /// built-in application; the executor detects that surviving application
    /// before theory dispatch and returns `unknown`, so AY accepts the standard
    /// syntax without treating exponentiation as an unconstrained function.
    fn elaborate_integer_power(&mut self, arg_ids: &[TermId]) -> Result<TermId> {
        if arg_ids.len() != 2 {
            return Err(ElaborateError::InvalidConstant(format!(
                "** requires 2 arguments, got {}",
                arg_ids.len()
            )));
        }

        for &arg in arg_ids {
            let actual = self.terms.sort(arg);
            if actual != &Sort::Int {
                return Err(ElaborateError::SortMismatch {
                    expected: Sort::Int.to_string(),
                    actual: actual.to_string(),
                });
            }
        }

        if let Some(exponent) = self.terms.extract_integer_constant(arg_ids[1]) {
            Ok(self.unfold_smtlib_integer_power(arg_ids[0], &exponent))
        } else {
            Ok(self
                .terms
                .mk_app(Symbol::named("**"), vec![arg_ids[0], arg_ids[1]], Sort::Int))
        }
    }

    /// Lower `(** base exponent)` for a concrete integer exponent.
    fn unfold_smtlib_integer_power(&mut self, base: TermId, exponent: &BigInt) -> TermId {
        if exponent.is_zero() {
            // Required by SMT-LIB Ints, including (** 0 0) = 1.
            return self.terms.mk_int(BigInt::one());
        }

        let positive_power = self.repeated_product(base, &exponent.abs());
        if !exponent.is_negative() {
            return positive_power;
        }

        let one = self.terms.mk_int(BigInt::one());
        self.terms.mk_intdiv(one, positive_power)
    }

    /// Unfold `(^ base n)` where `n` is a concrete integer.
    fn unfold_integer_power(&mut self, base: TermId, base_sort: &Sort, n: &BigInt) -> TermId {
        // n == 0: return 1 in the base's sort.
        if n.is_zero() {
            return match base_sort {
                Sort::Real => self.terms.mk_rational(BigRational::one()),
                _ => self.terms.mk_int(BigInt::one()),
            };
        }

        let abs_n = n.abs();
        let positive_power = self.repeated_product(base, &abs_n);

        if !n.is_negative() {
            return positive_power;
        }

        // n < 0: (ite (= base 0) <fresh_uf> (/ 1 base^|n|))
        //
        // SMT-LIB leaves `0^n` for `n < 0` under-specified. A fresh
        // uninterpreted constant in the base's sort captures any
        // permissible interpretation the solver might assign.
        let zero = match base_sort {
            Sort::Real => self.terms.mk_rational(BigRational::zero()),
            _ => self.terms.mk_int(BigInt::zero()),
        };
        let is_base_zero = self.terms.mk_eq(base, zero);

        let undefined = self
            .terms
            .mk_fresh_var("pow_neg_at_zero", base_sort.clone());

        // Division requires Real operands.
        let one_real = self.terms.mk_rational(BigRational::one());
        let positive_real = if matches!(base_sort, Sort::Int) {
            self.terms.mk_to_real(positive_power)
        } else {
            positive_power
        };
        let reciprocal = self.terms.mk_div(one_real, positive_real);

        // The else-branch is Real; coerce the fresh-var branch to match
        // when the base is Int to keep sorts consistent.
        let (then_br, else_br) = match base_sort {
            Sort::Int => {
                let undef_real = self.terms.mk_to_real(undefined);
                (undef_real, reciprocal)
            }
            _ => (undefined, reciprocal),
        };

        self.terms.mk_ite(is_base_zero, then_br, else_br)
    }

    /// Compute `base^n` as a product of `n` copies of `base` using
    /// exponentiation-by-squaring to keep the term size O(log n).
    fn repeated_product(&mut self, base: TermId, n: &BigInt) -> TermId {
        debug_assert!(
            !n.is_zero() && !n.is_negative(),
            "repeated_product: expected positive exponent"
        );

        // For small exponents, build a flat product so the arithmetic
        // simplifiers see `x * x * ... * x` and can apply coefficient
        // collection. For large exponents, fall back to squaring.
        let small_limit: u32 = 32;
        if let Some(n_u32) = n.to_u32() {
            if n_u32 <= small_limit {
                let factors = vec![base; n_u32 as usize];
                return self.terms.mk_mul(factors);
            }
        }

        // Exponentiation by squaring for large exponents.
        let mut result: Option<TermId> = None;
        let mut current_square = base;
        let bits = n.bits();
        for i in 0..bits {
            if n.bit(i) {
                result = Some(match result {
                    Some(r) => self.terms.mk_mul(vec![r, current_square]),
                    None => current_square,
                });
            }
            if i + 1 < bits {
                current_square = self.terms.mk_mul(vec![current_square, current_square]);
            }
        }
        result.expect("repeated_product: positive exponent must set result")
    }
}
