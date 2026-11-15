// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create an addition (a + b). Panics if sorts don't match.
    pub fn add(&mut self, a: Term, b: Term) -> Term {
        self.try_add(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an addition (a + b). Both args must be same arithmetic sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_add(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("add", a)?;
        let b_id = self.resolve_term("add", b)?;
        if let Some(result) =
            self.try_complex_fold("add", &[a_id, b_id], TermStore::mk_complex_add)?
        {
            return Ok(result);
        }
        self.expect_same_arith_sort("add", a, b)?;
        let result = self.terms_mut().mk_add(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
    }

    /// Create an addition of multiple terms. Panics if sorts don't match.
    pub fn add_many(&mut self, terms: &[Term]) -> Term {
        self.try_add_many(terms).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an addition of multiple terms. All must be same arithmetic sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_add_many(&mut self, terms: &[Term]) -> Result<Term, SolverError> {
        let ids = terms
            .iter()
            .copied()
            .map(|term| self.resolve_term("add_many", term))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(result) = self.try_complex_fold("add_many", &ids, TermStore::mk_complex_add)? {
            return Ok(result);
        }
        if let Some(&first) = terms.first() {
            self.expect_arith("add_many", first)?;
            for &t in &terms[1..] {
                self.expect_same_arith_sort("add_many", first, t)?;
            }
        }
        let result = self.terms_mut().mk_add(ids);
        Ok(self.wrap_term(result))
    }

    /// Create a subtraction (a - b). Panics if sorts don't match.
    pub fn sub(&mut self, a: Term, b: Term) -> Term {
        self.try_sub(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a subtraction (a - b). Both args must be same arithmetic sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_sub(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("sub", a)?;
        let b_id = self.resolve_term("sub", b)?;
        if let Some(result) =
            self.try_complex_fold("sub", &[a_id, b_id], TermStore::mk_complex_subtract)?
        {
            return Ok(result);
        }
        self.expect_same_arith_sort("sub", a, b)?;
        let result = self.terms_mut().mk_sub(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
    }

    /// Create a multiplication (a * b). Panics if sorts don't match.
    pub fn mul(&mut self, a: Term, b: Term) -> Term {
        self.try_mul(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a multiplication (a * b). Both args must be same arithmetic sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_mul(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("mul", a)?;
        let b_id = self.resolve_term("mul", b)?;
        if let Some(result) =
            self.try_complex_fold("mul", &[a_id, b_id], TermStore::mk_complex_multiply)?
        {
            return Ok(result);
        }
        self.expect_same_arith_sort("mul", a, b)?;
        let result = self.terms_mut().mk_mul(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
    }

    /// Create a multiplication of multiple terms. Panics if sorts don't match.
    pub fn mul_many(&mut self, terms: &[Term]) -> Term {
        self.try_mul_many(terms).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a multiplication of multiple terms. All must be same arithmetic sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_mul_many(&mut self, terms: &[Term]) -> Result<Term, SolverError> {
        let ids = terms
            .iter()
            .copied()
            .map(|term| self.resolve_term("mul_many", term))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(result) =
            self.try_complex_fold("mul_many", &ids, TermStore::mk_complex_multiply)?
        {
            return Ok(result);
        }
        if let Some(&first) = terms.first() {
            self.expect_arith("mul_many", first)?;
            for &t in &terms[1..] {
                self.expect_same_arith_sort("mul_many", first, t)?;
            }
        }
        let result = self.terms_mut().mk_mul(ids);
        Ok(self.wrap_term(result))
    }

    /// Create a negation (-a). Panics if arg is not arithmetic.
    pub fn neg(&mut self, a: Term) -> Term {
        self.try_neg(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a negation (-a). Arg must be Int or Real.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_neg(&mut self, a: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("neg", a)?;
        if self.terms().sort(a_id) == &Sort::Complex {
            let result = self.terms_mut().mk_complex_negate(a_id);
            return self.finish_complex_construction("neg", &[a_id], result);
        }
        self.expect_arith("neg", a)?;
        let result = self.terms_mut().mk_neg(a_id);
        Ok(self.wrap_term(result))
    }

    /// Create a real division (a / b). Panics if args are not both Real.
    pub fn div(&mut self, a: Term, b: Term) -> Term {
        self.try_div(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a real division (a / b). Both args must be Real.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_div(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("div", a)?;
        let b_id = self.resolve_term("div", b)?;
        if let Some(result) =
            self.try_complex_fold("div", &[a_id, b_id], TermStore::mk_complex_divide)?
        {
            return Ok(result);
        }
        self.expect_both_real("div", a, b)?;
        let result = self.terms_mut().mk_div(a_id, b_id);
        Ok(self.wrap_term(result))
    }

    /// Create an integer division (a div b). Panics if args are not both Int.
    pub fn int_div(&mut self, a: Term, b: Term) -> Term {
        self.try_int_div(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an integer division (a div b). Both args must be Int.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_int_div(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("int_div", a)?;
        let b_id = self.resolve_term("int_div", b)?;
        self.expect_both_int("int_div", a, b)?;
        let result = self.terms_mut().mk_intdiv(a_id, b_id);
        Ok(self.wrap_term(result))
    }

    /// Create a modulo operation (a mod b). Panics if args are not both Int.
    pub fn modulo(&mut self, a: Term, b: Term) -> Term {
        self.try_modulo(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a modulo operation (a mod b). Both args must be Int.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_modulo(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("modulo", a)?;
        let b_id = self.resolve_term("modulo", b)?;
        self.expect_both_int("modulo", a, b)?;
        let result = self.terms_mut().mk_mod(a_id, b_id);
        Ok(self.wrap_term(result))
    }

    /// Create a floor division (a fdiv b). Panics if args are not both Int.
    ///
    /// Floor division rounds toward negative infinity, unlike SMT-LIB `div` which
    /// is Euclidean (remainder always non-negative). They differ only when the
    /// divisor is negative:
    /// - `floor_div(7, -2) = -4` (floor), vs `div(7, -2) = -3` (Euclidean)
    /// - `floor_div(-7, 2) = -4` (same as Euclidean for positive divisor)
    ///
    /// Encoding: `ite(b > 0, div(a,b), ite(mod(a,b) = 0, div(a,b), div(a,b) - 1))`
    pub fn floor_div(&mut self, a: Term, b: Term) -> Term {
        self.try_floor_div(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a floor division (a fdiv b). Both args must be Int.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_floor_div(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_both_int("floor_div", a, b)?;
        let zero = self.int_const(0);
        let one = self.int_const(1);
        let div_ab = self.try_int_div(a, b)?;
        let mod_ab = self.try_modulo(a, b)?;
        let b_gt_zero = self.try_gt(b, zero)?;
        let mod_eq_zero = self.try_eq(mod_ab, zero)?;
        let div_minus_one = self.try_sub(div_ab, one)?;
        let neg_divisor_case = self.try_ite(mod_eq_zero, div_ab, div_minus_one)?;
        let result = self.try_ite(b_gt_zero, div_ab, neg_divisor_case)?;
        Ok(result)
    }

    /// Create a floor modulo (a fmod b). Panics if args are not both Int.
    ///
    /// Floor modulo is defined as `a - floor_div(a, b) * b`. The result has the
    /// same sign as the divisor `b`, unlike SMT-LIB `mod` where the result is
    /// always non-negative.
    ///
    /// Encoding: `a - floor_div(a, b) * b`
    pub fn floor_mod(&mut self, a: Term, b: Term) -> Term {
        self.try_floor_mod(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a floor modulo (a fmod b). Both args must be Int.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_floor_mod(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_both_int("floor_mod", a, b)?;
        let fdiv = self.try_floor_div(a, b)?;
        let fdiv_times_b = self.try_mul(fdiv, b)?;
        let result = self.try_sub(a, fdiv_times_b)?;
        Ok(result)
    }

    /// Create an absolute value (abs a). Panics if arg is not arithmetic.
    pub fn abs(&mut self, a: Term) -> Term {
        self.try_abs(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an absolute value (abs a). Arg must be Int or Real.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_abs(&mut self, a: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("abs", a)?;
        self.expect_arith("abs", a)?;
        let result = self.terms_mut().mk_abs(a_id);
        Ok(self.wrap_term(result))
    }

    /// Create minimum of two values (min a b). Panics if sorts don't match.
    pub fn min(&mut self, a: Term, b: Term) -> Term {
        self.try_min(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create minimum of two values. Both args must be same arithmetic sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_min(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("min", a)?;
        let b_id = self.resolve_term("min", b)?;
        self.expect_same_arith_sort("min", a, b)?;
        let result = self.terms_mut().mk_min(a_id, b_id);
        Ok(self.wrap_term(result))
    }

    /// Create maximum of two values (max a b). Panics if sorts don't match.
    pub fn max(&mut self, a: Term, b: Term) -> Term {
        self.try_max(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create maximum of two values. Both args must be same arithmetic sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_max(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("max", a)?;
        let b_id = self.resolve_term("max", b)?;
        self.expect_same_arith_sort("max", a, b)?;
        let result = self.terms_mut().mk_max(a_id, b_id);
        Ok(self.wrap_term(result))
    }

    /// Create an exponentiation (a ^ b). Panics if sorts don't match.
    pub fn power(&mut self, a: Term, b: Term) -> Term {
        self.try_power(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an exponentiation (a ^ b). Both args must be same arithmetic sort.
    ///
    /// The result is `Real` for every arithmetic sort, as in Z3 (whose
    /// `Z3_mk_power` is this method's consumer): an integer power with a
    /// negative exponent is not an integer, so Z3 types `Int ^ Int` as `Real`
    /// (measured, z3 5.1: `(a**2).sort()` is `Real`, and `(a**2)/2` is real
    /// division). An `Int`-sorted power would turn the caller's `/` into
    /// integer `div` and flip verdicts (`a = 3, a^2 / 2 = 4` is unsat in Z3).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_power(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("power", a)?;
        let b_id = self.resolve_term("power", b)?;
        self.expect_same_arith_sort("power", a, b)?;
        let sort = Sort::Real;
        let result = self
            .terms_mut()
            .mk_app(Symbol::named("^"), vec![a_id, b_id], sort);
        Ok(self.wrap_term(result))
    }
}
