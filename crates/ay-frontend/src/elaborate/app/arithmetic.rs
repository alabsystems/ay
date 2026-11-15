// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Constant, Sort, Symbol, TermData, TermId};
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
                if self.preserve_sequence_power {
                    return self.preserve_ring_application("+", arg_ids).map(Some);
                }
                Ok(Some(self.terms.mk_add(arg_ids.to_vec())))
            }
            "-" => {
                if arg_ids.is_empty() {
                    return Err(ElaborateError::InvalidConstant(
                        "- requires at least 1 argument, got 0".to_string(),
                    ));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                if self.preserve_sequence_power {
                    return self.preserve_ring_application("-", arg_ids).map(Some);
                }
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
                if self.preserve_sequence_power {
                    return self.preserve_ring_application("*", arg_ids).map(Some);
                }
                Ok(Some(self.terms.mk_mul(arg_ids.to_vec())))
            }
            "^" if self.preserve_sequence_power => {
                if arg_ids.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(
                        "^ requires two arguments".into(),
                    ));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                let sort = self.terms.sort(arg_ids[0]).clone();
                if !matches!(sort, Sort::Int | Sort::Real) {
                    return Err(ElaborateError::InvalidConstant(
                        "^ requires arithmetic arguments".into(),
                    ));
                }
                self.expect_all_args_sort(arg_ids, &sort)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::Named("^".into()),
                    arg_ids.to_vec(),
                    Sort::Real,
                )))
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
    /// * `n == 0` → `1` for a nonzero numeral base. Otherwise
    ///   `(ite (= base 0) <0^0> 1)`, where `<0^0>` is one private constant per
    ///   base sort: z3 keeps `0^0` as its uninterpreted `^0` (libz3 5.1.0
    ///   answers `(assert (= r (^ 0.0 0.0))) (assert (not (= r 1.0)))` `sat`
    ///   with `^0 = [else -> 2]`, and `(^ 0 0)` over Int and `(^ 0.0 0.0)` take
    ///   independent values), so `0^0` is one unconstrained value per sort and
    ///   `x^0` is `1` wherever `x` is nonzero.
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
    // Explicit simplification must see the authored ring structure: eager
    // arithmetic normalization here would erase flat/max_degree semantics.
    fn preserve_ring_application(&mut self, head: &str, args: &[TermId]) -> Result<TermId> {
        let sort = self.terms.sort(args[0]).clone();
        if !matches!(sort, Sort::Int | Sort::Real) {
            return Err(ElaborateError::InvalidConstant(
                "arithmetic arguments required".into(),
            ));
        }
        self.expect_all_args_sort(args, &sort)?;
        Ok(self
            .terms
            .mk_app_structural(Symbol::Named(head.into()), args, sort))
    }

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
            if n.is_zero() {
                return Ok(self.power_zero_exponent(base, &base_sort));
            }
            return self.unfold_integer_power(base, &base_sort, &n);
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
            self.unfold_smtlib_integer_power(arg_ids[0], &exponent)
        } else {
            Ok(self
                .terms
                .mk_app(Symbol::named("**"), vec![arg_ids[0], arg_ids[1]], Sort::Int))
        }
    }

    /// Lower `(** base exponent)` for a concrete integer exponent.
    fn unfold_smtlib_integer_power(&mut self, base: TermId, exponent: &BigInt) -> Result<TermId> {
        if exponent.is_zero() {
            // Required by SMT-LIB Ints, including (** 0 0) = 1.
            return Ok(self.terms.mk_int(BigInt::one()));
        }

        let positive_power = self.repeated_product(base, &exponent.abs())?;
        if !exponent.is_negative() {
            return Ok(positive_power);
        }

        let one = self.terms.mk_int(BigInt::one());
        Ok(self.terms.mk_intdiv(one, positive_power))
    }

    /// `(^ base exp)` for an exponent equal to zero: `1` for a nonzero
    /// numeral base, else `(ite (= base 0) <0^0> 1)` (see `elaborate_power`).
    ///
    /// `<0^0>` is the elaborator-private constant [`zero_power_of_zero`] of
    /// the base sort, shared by every `0^0` of that sort, so `0^0` is
    /// functionally consistent (`(^ a 0)` and `(^ 0.0 0.0)` agree when
    /// `a = 0`, as z3's `^0` makes them) while a forced-nonzero base still
    /// folds to `1` in the solver (`(not (= a 0.0))` with `(^ a 0.0) != 1` is
    /// unsat).
    fn power_zero_exponent(&mut self, base: TermId, base_sort: &Sort) -> TermId {
        let (one, zero) = match base_sort {
            Sort::Real => (
                self.terms.mk_rational(BigRational::one()),
                self.terms.mk_rational(BigRational::zero()),
            ),
            _ => (
                self.terms.mk_int(BigInt::one()),
                self.terms.mk_int(BigInt::zero()),
            ),
        };
        if self.is_nonzero_numeral(base) {
            return one;
        }
        let is_base_zero = self.terms.mk_eq(base, zero);
        let zero_power = self
            .terms
            .mk_var(zero_power_of_zero(base_sort), base_sort.clone());
        self.terms.mk_ite(is_base_zero, zero_power, one)
    }

    /// Whether `term` is a numeral other than zero (`2`, `0.5`, `(- 3)`).
    fn is_nonzero_numeral(&self, term: TermId) -> bool {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => !n.is_zero(),
            TermData::Const(Constant::Rational(r)) => !r.0.is_zero(),
            TermData::App(symbol, args) if symbol.name() == "-" && args.len() == 1 => {
                self.is_nonzero_numeral(args[0])
            }
            _ => false,
        }
    }

    /// Unfold `(^ base n)` where `n` is a concrete integer.
    fn unfold_integer_power(
        &mut self,
        base: TermId,
        base_sort: &Sort,
        n: &BigInt,
    ) -> Result<TermId> {
        // n == 0 is `power_zero_exponent`'s; `repeated_product` refuses it.
        let abs_n = n.abs();
        let positive_power = self.repeated_product(base, &abs_n)?;

        if !n.is_negative() {
            return Ok(positive_power);
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

        Ok(self.terms.mk_ite(is_base_zero, then_br, else_br))
    }

    /// Compute `base^n` as a product of `n` copies of `base` using
    /// exponentiation-by-squaring to keep the term size O(log n).
    fn repeated_product(&mut self, base: TermId, n: &BigInt) -> Result<TermId> {
        if n.is_zero() || n.is_negative() {
            return Err(ElaborateError::InvalidConstant(
                "repeated product requires a positive exponent".to_string(),
            ));
        }

        // For small exponents, build a flat product so the arithmetic
        // simplifiers see `x * x * ... * x` and can apply coefficient
        // collection. For large exponents, fall back to squaring.
        let small_limit: u32 = 32;
        if let Some(n_u32) = n.to_u32() {
            if n_u32 <= small_limit {
                let factors = vec![base; n_u32 as usize];
                return Ok(self.terms.mk_mul(factors));
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
        result.ok_or_else(|| {
            ElaborateError::InvalidConstant(
                "positive exponent had no set bit during expansion".to_string(),
            )
        })
    }
}

/// The name of the private constant standing for `0^0` over `sort` (`Int`
/// or `Real`). It is in the internal `!ay.` namespace, which source text
/// cannot declare (`is_source_reserved_symbol`), so it never collides with a
/// user symbol. It is not in the `__ay_` namespace: the engine reads those
/// names as solver-minted witnesses, and its model validation skips the
/// assertions holding one (measured: `(assert (= (^ 0.0 0.0) 1.0))` answered
/// unknown, "all 2 assertions were skipped").
fn zero_power_of_zero(sort: &Sort) -> String {
    format!("!ay.zero-power-of-zero.{sort}")
}

#[cfg(test)]
#[path = "arithmetic_power_zero_tests.rs"]
mod power_zero_tests;
