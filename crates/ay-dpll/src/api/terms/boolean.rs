// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create a logical AND of two terms.
    ///
    /// # Panics
    /// Panics if arguments are not Bool. Use [`Self::try_and`] for a fallible version.
    pub fn and(&mut self, a: Term, b: Term) -> Term {
        self.try_and(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`and`](Solver::and). Returns an error instead of panicking.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not Bool.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_and(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_bool("and", a)?;
        self.expect_bool("and", b)?;
        Ok(Term(self.terms_mut().mk_and(vec![a.0, b.0])))
    }

    /// Create a logical AND of multiple terms.
    ///
    /// # Panics
    /// Panics if any argument is not Bool. Use [`Self::try_and_many`] for a fallible version.
    pub fn and_many(&mut self, terms: &[Term]) -> Term {
        self.try_and_many(terms).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`and_many`](Solver::and_many). Returns an error instead of panicking.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if any argument is not Bool.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_and_many(&mut self, terms: &[Term]) -> Result<Term, SolverError> {
        for t in terms {
            self.expect_bool("and_many", *t)?;
        }
        let ids: Vec<_> = terms.iter().map(|t| t.0).collect();
        Ok(Term(self.terms_mut().mk_and(ids)))
    }

    /// Create a logical OR of two terms.
    ///
    /// # Panics
    /// Panics if arguments are not Bool. Use [`Self::try_or`] for a fallible version.
    pub fn or(&mut self, a: Term, b: Term) -> Term {
        self.try_or(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`or`](Solver::or). Returns an error instead of panicking.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not Bool.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_or(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_bool("or", a)?;
        self.expect_bool("or", b)?;
        Ok(Term(self.terms_mut().mk_or(vec![a.0, b.0])))
    }

    /// Create a logical OR of multiple terms.
    ///
    /// # Panics
    /// Panics if any argument is not Bool. Use [`Self::try_or_many`] for a fallible version.
    pub fn or_many(&mut self, terms: &[Term]) -> Term {
        self.try_or_many(terms).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`or_many`](Solver::or_many). Returns an error instead of panicking.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if any argument is not Bool.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_or_many(&mut self, terms: &[Term]) -> Result<Term, SolverError> {
        for t in terms {
            self.expect_bool("or_many", *t)?;
        }
        let ids: Vec<_> = terms.iter().map(|t| t.0).collect();
        Ok(Term(self.terms_mut().mk_or(ids)))
    }

    /// Create an exclusive OR (a xor b).
    ///
    /// # Panics
    /// Panics if arguments are not Bool. Use [`Self::try_xor`] for a fallible version.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
    ///
    /// let mut solver = Solver::new(Logic::QfUf);
    /// let a = solver.declare_const("a", Sort::Bool);
    /// let b = solver.declare_const("b", Sort::Bool);
    ///
    /// let xor_ab = solver.xor(a, b);
    /// solver.assert_term(xor_ab);
    ///
    /// let true_val = solver.bool_const(true);
    /// let a_is_true = solver.eq(a, true_val);
    /// solver.assert_term(a_is_true);
    ///
    /// let true_val2 = solver.bool_const(true);
    /// let b_is_true = solver.eq(b, true_val2);
    /// solver.assert_term(b_is_true);
    ///
    /// assert!(solver.check_sat().is_unsat());
    /// ```
    pub fn xor(&mut self, a: Term, b: Term) -> Term {
        self.try_xor(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`xor`](Solver::xor). Returns an error instead of panicking.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not Bool.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_xor(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_bool("xor", a)?;
        self.expect_bool("xor", b)?;
        Ok(Term(self.terms_mut().mk_xor(a.0, b.0)))
    }

    /// Create a logical NOT.
    ///
    /// # Panics
    /// Panics if argument is not Bool. Use [`Self::try_not`] for a fallible version.
    pub fn not(&mut self, a: Term) -> Term {
        self.try_not(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`not`](Solver::not). Returns an error instead of panicking.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if argument is not Bool.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_not(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_bool("not", a)?;
        Ok(Term(self.terms_mut().mk_not(a.0)))
    }

    /// Create an implication (a => b).
    ///
    /// # Panics
    /// Panics if arguments are not Bool. Use [`Self::try_implies`] for a fallible version.
    pub fn implies(&mut self, a: Term, b: Term) -> Term {
        self.try_implies(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`implies`](Solver::implies). Returns an error instead of panicking.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not Bool.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_implies(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_bool("implies", a)?;
        self.expect_bool("implies", b)?;
        Ok(Term(self.terms_mut().mk_implies(a.0, b.0)))
    }

    /// Create a biconditional / logical equivalence (a <=> b).
    ///
    /// Equivalent to `(= a b)` when both are Bool, but validates that both arguments
    /// are Bool-sorted (unlike [`eq`](Solver::eq) which accepts any same-sort pair).
    ///
    /// # Panics
    /// Panics if either argument is not Bool. Use [`Self::try_iff`] for a fallible version.
    pub fn iff(&mut self, a: Term, b: Term) -> Term {
        self.try_iff(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`iff`](Solver::iff). Returns an error instead of panicking.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not Bool.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_iff(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_bool("iff", a)?;
        self.expect_bool("iff", b)?;
        Ok(Term(self.terms_mut().mk_eq(a.0, b.0)))
    }

    /// Create an if-then-else (ite cond then_val else_val).
    ///
    /// # Panics
    /// Panics if `cond` is not Bool or if `then_val` and `else_val` have different sorts.
    /// Use [`Self::try_ite`] for a fallible version.
    pub fn ite(&mut self, cond: Term, then_val: Term, else_val: Term) -> Term {
        self.try_ite(cond, then_val, else_val)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`ite`](Solver::ite). Returns an error instead of panicking.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if `cond` is not Bool or if
    /// `then_val` and `else_val` have different sorts.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_ite(
        &mut self,
        cond: Term,
        then_val: Term,
        else_val: Term,
    ) -> Result<Term, SolverError> {
        self.expect_bool("ite", cond)?;
        self.expect_same_sort("ite", then_val, else_val)?;
        Ok(Term(
            self.terms_mut().mk_ite(cond.0, then_val.0, else_val.0),
        ))
    }
}
