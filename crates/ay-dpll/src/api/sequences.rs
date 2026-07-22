// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequence operations for AY Solver API.
//!
//! Provides native term construction for SMT-LIB 2.6 sequence theory operations.
//! Each operation has a panicking variant and a fallible `try_*` counterpart.
//!
//! # Example
//!
//! ```
//! use ay_dpll::api::{Logic, Solver, Sort};
//!
//! let mut solver = Solver::new(Logic::QfSeq);
//! let s = solver.declare_const("s", Sort::seq(Sort::Int));
//! let t = solver.declare_const("t", Sort::seq(Sort::Int));
//! let len_s = solver.seq_len(s);
//! let concat = solver.seq_concat(s, t);
//! # let _ = (len_s, concat);
//! ```

use ay_core::term::Symbol;
use ay_core::Sort;

use super::types::{SolverError, Term};
use super::Solver;

// All public methods in this module are convenience wrappers that intentionally
// panic on error. Each has a fallible `try_*` counterpart.
#[allow(clippy::panic)]
impl Solver {
    // =========================================================================
    // Sort helpers
    // =========================================================================

    /// Check that a term has a Seq sort, returning the element sort.
    fn expect_seq(&self, operation: &'static str, t: Term) -> Result<Sort, SolverError> {
        let sort = self.terms().sort(t.0).clone();
        match sort {
            Sort::Seq(elem) => Ok(*elem),
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "Seq",
                got: vec![other],
            }),
        }
    }

    /// Check that two terms have the same Seq sort, returning the element sort.
    fn expect_same_seq(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<Sort, SolverError> {
        let elem_a = self.expect_seq(operation, a)?;
        let elem_b = self.expect_seq(operation, b)?;
        if elem_a != elem_b {
            return Err(SolverError::SortMismatch {
                operation,
                expected: "Seq (same element sort)",
                got: vec![Sort::seq(elem_a), Sort::seq(elem_b)],
            });
        }
        Ok(elem_a)
    }

    // =========================================================================
    // Sequence construction
    // =========================================================================

    /// Create an empty sequence constant (`seq.empty`) for the given element sort.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, Solver, Sort};
    ///
    /// let mut solver = Solver::new(Logic::QfSeq);
    /// let empty = solver.seq_empty(Sort::Int);
    /// # let _ = empty;
    /// ```
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn seq_empty(&mut self, element_sort: Sort) -> Term {
        let seq_sort = Sort::seq(element_sort);
        Term(
            self.terms_mut()
                .mk_app(Symbol::named("seq.empty"), vec![], seq_sort),
        )
    }

    /// Create a unit sequence (`seq.unit`) containing a single element.
    ///
    /// # Panics
    /// Panics on internal error.
    /// Use [`Self::try_seq_unit`] for a fallible version.
    pub fn seq_unit(&mut self, elem: Term) -> Term {
        self.try_seq_unit(elem).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a unit sequence (`seq.unit`).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_seq_unit(&mut self, elem: Term) -> Result<Term, SolverError> {
        let elem_sort = self.terms().sort(elem.0).clone();
        let seq_sort = Sort::seq(elem_sort);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("seq.unit"),
            vec![elem.0],
            seq_sort,
        )))
    }

    // =========================================================================
    // Sequence concatenation
    // =========================================================================

    /// Create a sequence concatenation (`seq.++`).
    ///
    /// # Panics
    /// Panics if the arguments are not sequences of the same element sort.
    /// Use [`Self::try_seq_concat`] for a fallible version.
    pub fn seq_concat(&mut self, a: Term, b: Term) -> Term {
        self.try_seq_concat(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a sequence concatenation (`seq.++`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if arguments are not matching Seq sorts.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_seq_concat(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let elem = self.expect_same_seq("seq.++", a, b)?;
        let seq_sort = Sort::seq(elem);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("seq.++"),
            vec![a.0, b.0],
            seq_sort,
        )))
    }

    // =========================================================================
    // Sequence length
    // =========================================================================

    /// Create a sequence length expression (`seq.len`), returning Int.
    ///
    /// # Panics
    /// Panics if the argument is not a Seq sort.
    /// Use [`Self::try_seq_len`] for a fallible version.
    pub fn seq_len(&mut self, s: Term) -> Term {
        self.try_seq_len(s).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a sequence length expression (`seq.len`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if the argument is not a Seq sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_seq_len(&mut self, s: Term) -> Result<Term, SolverError> {
        self.expect_seq("seq.len", s)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("seq.len"),
            vec![s.0],
            Sort::Int,
        )))
    }

    // =========================================================================
    // Element access
    // =========================================================================

    /// Create an element-at expression (`seq.nth`), returning the element sort.
    ///
    /// # Panics
    /// Panics if `s` is not a Seq sort or `idx` is not Int.
    /// Use [`Self::try_seq_nth`] for a fallible version.
    pub fn seq_nth(&mut self, s: Term, idx: Term) -> Term {
        self.try_seq_nth(s, idx).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an element-at expression (`seq.nth`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if sorts are wrong.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_seq_nth(&mut self, s: Term, idx: Term) -> Result<Term, SolverError> {
        let elem = self.expect_seq("seq.nth", s)?;
        self.expect_int("seq.nth", idx)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("seq.nth"),
            vec![s.0, idx.0],
            elem,
        )))
    }

    // =========================================================================
    // Subsequence extraction
    // =========================================================================

    /// Create a subsequence extraction (`seq.extract`).
    ///
    /// Returns the subsequence of `s` starting at `offset` with length `len`.
    ///
    /// # Panics
    /// Panics if `s` is not a Seq sort or `offset`/`len` are not Int.
    /// Use [`Self::try_seq_extract`] for a fallible version.
    pub fn seq_extract(&mut self, s: Term, offset: Term, len: Term) -> Term {
        self.try_seq_extract(s, offset, len)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a subsequence extraction (`seq.extract`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if sorts are wrong.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_seq_extract(
        &mut self,
        s: Term,
        offset: Term,
        len: Term,
    ) -> Result<Term, SolverError> {
        let elem = self.expect_seq("seq.extract", s)?;
        self.expect_int("seq.extract", offset)?;
        self.expect_int("seq.extract", len)?;
        let seq_sort = Sort::seq(elem);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("seq.extract"),
            vec![s.0, offset.0, len.0],
            seq_sort,
        )))
    }

    // =========================================================================
    // Sequence predicates
    // =========================================================================

    /// Create a sequence containment test (`seq.contains`), returning Bool.
    ///
    /// # Panics
    /// Panics if the arguments are not sequences of the same element sort.
    /// Use [`Self::try_seq_contains`] for a fallible version.
    pub fn seq_contains(&mut self, s: Term, t: Term) -> Term {
        self.try_seq_contains(s, t)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a sequence containment test (`seq.contains`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if arguments are not matching Seq sorts.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_seq_contains(&mut self, s: Term, t: Term) -> Result<Term, SolverError> {
        self.expect_same_seq("seq.contains", s, t)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("seq.contains"),
            vec![s.0, t.0],
            Sort::Bool,
        )))
    }

    /// Create a sequence prefix test (`seq.prefixof`), returning Bool.
    ///
    /// # Panics
    /// Panics if the arguments are not sequences of the same element sort.
    /// Use [`Self::try_seq_prefixof`] for a fallible version.
    pub fn seq_prefixof(&mut self, prefix: Term, s: Term) -> Term {
        self.try_seq_prefixof(prefix, s)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a sequence prefix test (`seq.prefixof`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if arguments are not matching Seq sorts.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_seq_prefixof(&mut self, prefix: Term, s: Term) -> Result<Term, SolverError> {
        self.expect_same_seq("seq.prefixof", prefix, s)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("seq.prefixof"),
            vec![prefix.0, s.0],
            Sort::Bool,
        )))
    }

    /// Create a sequence suffix test (`seq.suffixof`), returning Bool.
    ///
    /// # Panics
    /// Panics if the arguments are not sequences of the same element sort.
    /// Use [`Self::try_seq_suffixof`] for a fallible version.
    pub fn seq_suffixof(&mut self, suffix: Term, s: Term) -> Term {
        self.try_seq_suffixof(suffix, s)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a sequence suffix test (`seq.suffixof`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if arguments are not matching Seq sorts.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_seq_suffixof(&mut self, suffix: Term, s: Term) -> Result<Term, SolverError> {
        self.expect_same_seq("seq.suffixof", suffix, s)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("seq.suffixof"),
            vec![suffix.0, s.0],
            Sort::Bool,
        )))
    }

    // =========================================================================
    // Sequence search
    // =========================================================================

    /// Create a sequence index-of expression (`seq.indexof`), returning Int.
    ///
    /// Returns the index of the first occurrence of `t` in `s` starting from
    /// position `start`, or -1 if not found.
    ///
    /// # Panics
    /// Panics if `s`/`t` are not matching Seq sorts or `start` is not Int.
    /// Use [`Self::try_seq_indexof`] for a fallible version.
    pub fn seq_indexof(&mut self, s: Term, t: Term, start: Term) -> Term {
        self.try_seq_indexof(s, t, start)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a sequence index-of expression (`seq.indexof`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if sorts are wrong.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_seq_indexof(&mut self, s: Term, t: Term, start: Term) -> Result<Term, SolverError> {
        self.expect_same_seq("seq.indexof", s, t)?;
        self.expect_int("seq.indexof", start)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("seq.indexof"),
            vec![s.0, t.0, start.0],
            Sort::Int,
        )))
    }

    // =========================================================================
    // Sequence replacement
    // =========================================================================

    /// Create a sequence replacement (`seq.replace`).
    ///
    /// Replaces the first occurrence of `from` in `s` with `to`.
    ///
    /// # Panics
    /// Panics if the arguments are not sequences of the same element sort.
    /// Use [`Self::try_seq_replace`] for a fallible version.
    pub fn seq_replace(&mut self, s: Term, from: Term, to: Term) -> Term {
        self.try_seq_replace(s, from, to)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a sequence replacement (`seq.replace`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if the arguments are not matching Seq sorts.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_seq_replace(&mut self, s: Term, from: Term, to: Term) -> Result<Term, SolverError> {
        let elem = self.expect_same_seq("seq.replace", s, from)?;
        let to_elem = self.expect_seq("seq.replace", to)?;
        if elem != to_elem {
            return Err(SolverError::SortMismatch {
                operation: "seq.replace",
                expected: "Seq (same element sort for all arguments)",
                got: vec![Sort::seq(elem), Sort::seq(to_elem)],
            });
        }
        let seq_sort = Sort::seq(elem);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("seq.replace"),
            vec![s.0, from.0, to.0],
            seq_sort,
        )))
    }
}
