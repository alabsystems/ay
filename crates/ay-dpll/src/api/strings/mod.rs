// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String and regex operations for AY Solver API.
//!
//! Provides native term construction for SMT-LIB 2.6 string theory operations.
//! Each operation has a panicking variant and a fallible `try_*` counterpart.
//!
//! # Example
//!
//! ```
//! use ay_dpll::api::{Logic, Solver, Sort};
//!
//! let mut solver = Solver::new(Logic::QfSlia);
//! let s = solver.string_var("s");
//! let t = solver.string_var("t");
//! let hello = solver.string_const("hello");
//! let len_s = solver.str_len(s);
//! let concat = solver.str_concat(s, t);
//! # let _ = (hello, len_s, concat);
//! ```

mod regex;

use ay_core::term::Symbol;
use ay_core::Sort;

use super::types::{SolverError, Term};
use super::Solver;

// All public methods in this module are convenience wrappers that intentionally
// panic on error. Each has a fallible `try_*` counterpart.
#[allow(clippy::panic)]
impl Solver {
    // =========================================================================
    // String variable and constant construction
    // =========================================================================

    /// Declare a string constant (0-arity) variable.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, Solver};
    ///
    /// let mut solver = Solver::new(Logic::QfSlia);
    /// let s = solver.string_var("s");
    /// # let _ = s;
    /// ```
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn string_var(&mut self, name: &str) -> Term {
        self.declare_const(name, Sort::String)
    }

    /// Create a string literal constant.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, Solver};
    ///
    /// let mut solver = Solver::new(Logic::QfSlia);
    /// let hello = solver.string_const("hello");
    /// # let _ = hello;
    /// ```
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn string_const(&mut self, value: &str) -> Term {
        let result = self.terms_mut().mk_string(value.to_string());
        self.wrap_term(result)
    }

    // =========================================================================
    // String concatenation
    // =========================================================================

    /// Create a string concatenation (`str.++`).
    ///
    /// # Panics
    /// Panics if either argument is not of sort `String`.
    /// Use [`Self::try_str_concat`] for a fallible version.
    pub fn str_concat(&mut self, a: Term, b: Term) -> Term {
        self.try_str_concat(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a string concatenation (`str.++`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not `String`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_concat(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("str.++", a)?;
        let b_id = self.resolve_term("str.++", b)?;
        self.expect_string("str.++", a)?;
        self.expect_string("str.++", b)?;
        let result =
            self.terms_mut()
                .mk_app(Symbol::named("str.++"), vec![a_id, b_id], Sort::String);
        Ok(self.wrap_term(result))
    }

    // =========================================================================
    // String length
    // =========================================================================

    /// Create a string length expression (`str.len`), returning Int.
    ///
    /// # Panics
    /// Panics if the argument is not of sort `String`.
    /// Use [`Self::try_str_len`] for a fallible version.
    pub fn str_len(&mut self, s: Term) -> Term {
        self.try_str_len(s).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a string length expression (`str.len`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if the argument is not `String`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_len(&mut self, s: Term) -> Result<Term, SolverError> {
        let s_id = self.resolve_term("str.len", s)?;
        self.expect_string("str.len", s)?;
        let result = self
            .terms_mut()
            .mk_app(Symbol::named("str.len"), vec![s_id], Sort::Int);
        Ok(self.wrap_term(result))
    }

    // =========================================================================
    // String character access
    // =========================================================================

    /// Create a character-at expression (`str.at`), returning a length-1 String.
    ///
    /// # Panics
    /// Panics if `s` is not `String` or `idx` is not `Int`.
    /// Use [`Self::try_str_at`] for a fallible version.
    pub fn str_at(&mut self, s: Term, idx: Term) -> Term {
        self.try_str_at(s, idx).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a character-at expression (`str.at`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if sorts are wrong.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_at(&mut self, s: Term, idx: Term) -> Result<Term, SolverError> {
        let s_id = self.resolve_term("str.at", s)?;
        let idx_id = self.resolve_term("str.at", idx)?;
        self.expect_string("str.at", s)?;
        self.expect_int("str.at", idx)?;
        let result =
            self.terms_mut()
                .mk_app(Symbol::named("str.at"), vec![s_id, idx_id], Sort::String);
        Ok(self.wrap_term(result))
    }

    // =========================================================================
    // Substring extraction
    // =========================================================================

    /// Create a substring expression (`str.substr`).
    ///
    /// Returns the substring of `s` starting at `offset` with length `len`.
    ///
    /// # Panics
    /// Panics if `s` is not `String` or `offset`/`len` are not `Int`.
    /// Use [`Self::try_str_substr`] for a fallible version.
    pub fn str_substr(&mut self, s: Term, offset: Term, len: Term) -> Term {
        self.try_str_substr(s, offset, len)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a substring expression (`str.substr`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if sorts are wrong.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_substr(
        &mut self,
        s: Term,
        offset: Term,
        len: Term,
    ) -> Result<Term, SolverError> {
        let s_id = self.resolve_term("str.substr", s)?;
        let offset_id = self.resolve_term("str.substr", offset)?;
        let len_id = self.resolve_term("str.substr", len)?;
        self.expect_string("str.substr", s)?;
        self.expect_int("str.substr", offset)?;
        self.expect_int("str.substr", len)?;
        let result = self.terms_mut().mk_app(
            Symbol::named("str.substr"),
            vec![s_id, offset_id, len_id],
            Sort::String,
        );
        Ok(self.wrap_term(result))
    }

    // =========================================================================
    // String predicates
    // =========================================================================

    /// Create a string containment test (`str.contains`), returning Bool.
    ///
    /// # Panics
    /// Panics if either argument is not `String`.
    /// Use [`Self::try_str_contains`] for a fallible version.
    pub fn str_contains(&mut self, s: Term, t: Term) -> Term {
        self.try_str_contains(s, t)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a string containment test (`str.contains`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not `String`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_contains(&mut self, s: Term, t: Term) -> Result<Term, SolverError> {
        let s_id = self.resolve_term("str.contains", s)?;
        let t_id = self.resolve_term("str.contains", t)?;
        self.expect_string("str.contains", s)?;
        self.expect_string("str.contains", t)?;
        let result =
            self.terms_mut()
                .mk_app(Symbol::named("str.contains"), vec![s_id, t_id], Sort::Bool);
        Ok(self.wrap_term(result))
    }

    /// Create a string prefix test (`str.prefixof`), returning Bool.
    ///
    /// # Panics
    /// Panics if either argument is not `String`.
    /// Use [`Self::try_str_prefixof`] for a fallible version.
    pub fn str_prefixof(&mut self, prefix: Term, s: Term) -> Term {
        self.try_str_prefixof(prefix, s)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a string prefix test (`str.prefixof`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not `String`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_prefixof(&mut self, prefix: Term, s: Term) -> Result<Term, SolverError> {
        let prefix_id = self.resolve_term("str.prefixof", prefix)?;
        let s_id = self.resolve_term("str.prefixof", s)?;
        self.expect_string("str.prefixof", prefix)?;
        self.expect_string("str.prefixof", s)?;
        let result = self.terms_mut().mk_app(
            Symbol::named("str.prefixof"),
            vec![prefix_id, s_id],
            Sort::Bool,
        );
        Ok(self.wrap_term(result))
    }

    /// Create a string suffix test (`str.suffixof`), returning Bool.
    ///
    /// # Panics
    /// Panics if either argument is not `String`.
    /// Use [`Self::try_str_suffixof`] for a fallible version.
    pub fn str_suffixof(&mut self, suffix: Term, s: Term) -> Term {
        self.try_str_suffixof(suffix, s)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a string suffix test (`str.suffixof`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not `String`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_suffixof(&mut self, suffix: Term, s: Term) -> Result<Term, SolverError> {
        let suffix_id = self.resolve_term("str.suffixof", suffix)?;
        let s_id = self.resolve_term("str.suffixof", s)?;
        self.expect_string("str.suffixof", suffix)?;
        self.expect_string("str.suffixof", s)?;
        let result = self.terms_mut().mk_app(
            Symbol::named("str.suffixof"),
            vec![suffix_id, s_id],
            Sort::Bool,
        );
        Ok(self.wrap_term(result))
    }

    // =========================================================================
    // String search
    // =========================================================================

    /// Create a string index-of expression (`str.indexof`), returning Int.
    ///
    /// Returns the index of the first occurrence of `t` in `s` starting from
    /// position `start`, or -1 if not found.
    ///
    /// # Panics
    /// Panics if `s`/`t` are not `String` or `start` is not `Int`.
    /// Use [`Self::try_str_indexof`] for a fallible version.
    pub fn str_indexof(&mut self, s: Term, t: Term, start: Term) -> Term {
        self.try_str_indexof(s, t, start)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a string index-of expression (`str.indexof`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if sorts are wrong.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_indexof(&mut self, s: Term, t: Term, start: Term) -> Result<Term, SolverError> {
        let s_id = self.resolve_term("str.indexof", s)?;
        let t_id = self.resolve_term("str.indexof", t)?;
        let start_id = self.resolve_term("str.indexof", start)?;
        self.expect_string("str.indexof", s)?;
        self.expect_string("str.indexof", t)?;
        self.expect_int("str.indexof", start)?;
        let result = self.terms_mut().mk_app(
            Symbol::named("str.indexof"),
            vec![s_id, t_id, start_id],
            Sort::Int,
        );
        Ok(self.wrap_term(result))
    }

    // =========================================================================
    // String replacement
    // =========================================================================

    /// Create a string replacement (`str.replace`).
    ///
    /// Replaces the first occurrence of `from` in `s` with `to`.
    ///
    /// # Panics
    /// Panics if any argument is not `String`.
    /// Use [`Self::try_str_replace`] for a fallible version.
    pub fn str_replace(&mut self, s: Term, from: Term, to: Term) -> Term {
        self.try_str_replace(s, from, to)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a string replacement (`str.replace`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if any argument is not `String`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_replace(&mut self, s: Term, from: Term, to: Term) -> Result<Term, SolverError> {
        let s_id = self.resolve_term("str.replace", s)?;
        let from_id = self.resolve_term("str.replace", from)?;
        let to_id = self.resolve_term("str.replace", to)?;
        self.expect_string("str.replace", s)?;
        self.expect_string("str.replace", from)?;
        self.expect_string("str.replace", to)?;
        let result = self.terms_mut().mk_app(
            Symbol::named("str.replace"),
            vec![s_id, from_id, to_id],
            Sort::String,
        );
        Ok(self.wrap_term(result))
    }

    /// Create a replace-all expression (`str.replace_all`).
    ///
    /// # Panics
    /// Panics if any argument is not `String`.
    /// Use [`Self::try_str_replace_all`] for a fallible version.
    pub fn str_replace_all(&mut self, s: Term, from: Term, to: Term) -> Term {
        self.try_str_replace_all(s, from, to)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a replace-all expression (`str.replace_all`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if any argument is not `String`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_replace_all(
        &mut self,
        s: Term,
        from: Term,
        to: Term,
    ) -> Result<Term, SolverError> {
        let s_id = self.resolve_term("str.replace_all", s)?;
        let from_id = self.resolve_term("str.replace_all", from)?;
        let to_id = self.resolve_term("str.replace_all", to)?;
        self.expect_string("str.replace_all", s)?;
        self.expect_string("str.replace_all", from)?;
        self.expect_string("str.replace_all", to)?;
        let result = self.terms_mut().mk_app(
            Symbol::named("str.replace_all"),
            vec![s_id, from_id, to_id],
            Sort::String,
        );
        Ok(self.wrap_term(result))
    }

    // =========================================================================
    // String ↔ Int conversions
    // =========================================================================

    /// Convert a string to an integer (`str.to_int`), returning Int.
    ///
    /// Returns -1 if the string does not represent a non-negative integer.
    ///
    /// # Panics
    /// Panics if the argument is not `String`.
    /// Use [`Self::try_str_to_int`] for a fallible version.
    pub fn str_to_int(&mut self, s: Term) -> Term {
        self.try_str_to_int(s).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert a string to an integer (`str.to_int`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if the argument is not `String`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_to_int(&mut self, s: Term) -> Result<Term, SolverError> {
        let s_id = self.resolve_term("str.to_int", s)?;
        self.expect_string("str.to_int", s)?;
        let result = self
            .terms_mut()
            .mk_app(Symbol::named("str.to_int"), vec![s_id], Sort::Int);
        Ok(self.wrap_term(result))
    }

    /// Convert an integer to a string (`str.from_int`), returning String.
    ///
    /// Returns the empty string for negative integers.
    ///
    /// # Panics
    /// Panics if the argument is not `Int`.
    /// Use [`Self::try_str_from_int`] for a fallible version.
    pub fn str_from_int(&mut self, n: Term) -> Term {
        self.try_str_from_int(n).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert an integer to a string (`str.from_int`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if the argument is not `Int`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_from_int(&mut self, n: Term) -> Result<Term, SolverError> {
        let n_id = self.resolve_term("str.from_int", n)?;
        self.expect_int("str.from_int", n)?;
        let result =
            self.terms_mut()
                .mk_app(Symbol::named("str.from_int"), vec![n_id], Sort::String);
        Ok(self.wrap_term(result))
    }
}
