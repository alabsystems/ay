// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regex construction helpers for the native solver API.

use ay_core::term::Symbol;
use ay_core::Sort;

use crate::api::types::{SolverError, Term};
use crate::api::Solver;

// All public methods in this module are convenience wrappers that intentionally
// panic on error. Each has a fallible `try_*` counterpart.
#[allow(clippy::panic)]
impl Solver {
    /// Convert a string to a regex matching exactly that string (`str.to_re`).
    ///
    /// # Panics
    /// Panics if the argument is not `String`.
    /// Use [`Self::try_str_to_re`] for a fallible version.
    pub fn str_to_re(&mut self, s: Term) -> Term {
        self.try_str_to_re(s).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert a string to a regex (`str.to_re`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if the argument is not `String`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_to_re(&mut self, s: Term) -> Result<Term, SolverError> {
        self.expect_string("str.to_re", s)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("str.to_re"),
            vec![s.0],
            Sort::RegLan,
        )))
    }

    /// Test string membership in a regex (`str.in_re`), returning Bool.
    ///
    /// # Panics
    /// Panics if `s` is not `String` or `re` is not `RegLan`.
    /// Use [`Self::try_str_in_re`] for a fallible version.
    pub fn str_in_re(&mut self, s: Term, re: Term) -> Term {
        self.try_str_in_re(s, re).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to test string membership in a regex (`str.in_re`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if sorts are wrong.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_str_in_re(&mut self, s: Term, re: Term) -> Result<Term, SolverError> {
        self.expect_string("str.in_re", s)?;
        self.expect_reglan("str.in_re", re)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("str.in_re"),
            vec![s.0, re.0],
            Sort::Bool,
        )))
    }

    /// Create the Kleene star of a regex (`re.*`), returning RegLan.
    ///
    /// # Panics
    /// Panics if the argument is not `RegLan`.
    /// Use [`Self::try_re_star`] for a fallible version.
    pub fn re_star(&mut self, re: Term) -> Term {
        self.try_re_star(re).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create the Kleene star of a regex (`re.*`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if the argument is not `RegLan`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_re_star(&mut self, re: Term) -> Result<Term, SolverError> {
        self.expect_reglan("re.*", re)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("re.*"),
            vec![re.0],
            Sort::RegLan,
        )))
    }

    /// Create the Kleene plus of a regex (`re.+`), returning RegLan.
    ///
    /// # Panics
    /// Panics if the argument is not `RegLan`.
    /// Use [`Self::try_re_plus`] for a fallible version.
    pub fn re_plus(&mut self, re: Term) -> Term {
        self.try_re_plus(re).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create the Kleene plus of a regex (`re.+`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if the argument is not `RegLan`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_re_plus(&mut self, re: Term) -> Result<Term, SolverError> {
        self.expect_reglan("re.+", re)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("re.+"),
            vec![re.0],
            Sort::RegLan,
        )))
    }

    /// Create the union of two regexes (`re.union`), returning RegLan.
    ///
    /// # Panics
    /// Panics if either argument is not `RegLan`.
    /// Use [`Self::try_re_union`] for a fallible version.
    pub fn re_union(&mut self, a: Term, b: Term) -> Term {
        self.try_re_union(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create the union of two regexes (`re.union`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not `RegLan`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_re_union(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_reglan("re.union", a)?;
        self.expect_reglan("re.union", b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("re.union"),
            vec![a.0, b.0],
            Sort::RegLan,
        )))
    }

    /// Create the concatenation of two regexes (`re.++`), returning RegLan.
    ///
    /// # Panics
    /// Panics if either argument is not `RegLan`.
    /// Use [`Self::try_re_concat`] for a fallible version.
    pub fn re_concat(&mut self, a: Term, b: Term) -> Term {
        self.try_re_concat(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create the concatenation of two regexes (`re.++`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not `RegLan`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_re_concat(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_reglan("re.++", a)?;
        self.expect_reglan("re.++", b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("re.++"),
            vec![a.0, b.0],
            Sort::RegLan,
        )))
    }

    /// Create the optional regex (`re.opt`, matches the empty string or the
    /// argument), returning RegLan.
    ///
    /// # Panics
    /// Panics if the argument is not `RegLan`.
    /// Use [`Self::try_re_opt`] for a fallible version.
    pub fn re_opt(&mut self, re: Term) -> Term {
        self.try_re_opt(re).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create the optional regex (`re.opt`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if the argument is not `RegLan`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_re_opt(&mut self, re: Term) -> Result<Term, SolverError> {
        self.expect_reglan("re.opt", re)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("re.opt"),
            vec![re.0],
            Sort::RegLan,
        )))
    }

    /// Create the complement regex (`re.comp`, matches every string the
    /// argument does not), returning RegLan.
    ///
    /// # Panics
    /// Panics if the argument is not `RegLan`.
    /// Use [`Self::try_re_comp`] for a fallible version.
    pub fn re_comp(&mut self, re: Term) -> Term {
        self.try_re_comp(re).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create the complement regex (`re.comp`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if the argument is not `RegLan`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_re_comp(&mut self, re: Term) -> Result<Term, SolverError> {
        self.expect_reglan("re.comp", re)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("re.comp"),
            vec![re.0],
            Sort::RegLan,
        )))
    }

    /// Create the intersection of two regexes (`re.inter`), returning RegLan.
    ///
    /// # Panics
    /// Panics if either argument is not `RegLan`.
    /// Use [`Self::try_re_inter`] for a fallible version.
    pub fn re_inter(&mut self, a: Term, b: Term) -> Term {
        self.try_re_inter(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create the intersection of two regexes (`re.inter`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not `RegLan`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_re_inter(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_reglan("re.inter", a)?;
        self.expect_reglan("re.inter", b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("re.inter"),
            vec![a.0, b.0],
            Sort::RegLan,
        )))
    }

    /// Create the range regex (`re.range`) over two single-character strings,
    /// matching every character between `lo` and `hi` inclusive. Returns RegLan.
    ///
    /// # Panics
    /// Panics if either argument is not `String`.
    /// Use [`Self::try_re_range`] for a fallible version.
    pub fn re_range(&mut self, lo: Term, hi: Term) -> Term {
        self.try_re_range(lo, hi).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create the range regex (`re.range`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if either argument is not `String`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_re_range(&mut self, lo: Term, hi: Term) -> Result<Term, SolverError> {
        self.expect_string("re.range", lo)?;
        self.expect_string("re.range", hi)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("re.range"),
            vec![lo.0, hi.0],
            Sort::RegLan,
        )))
    }

    /// Create the bounded-repetition regex (`(_ re.loop lo hi) re`), matching
    /// between `lo` and `hi` repetitions of `re`. Returns RegLan.
    ///
    /// # Panics
    /// Panics if the argument is not `RegLan`.
    /// Use [`Self::try_re_loop`] for a fallible version.
    pub fn re_loop(&mut self, re: Term, lo: u32, hi: u32) -> Term {
        self.try_re_loop(re, lo, hi)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create the bounded-repetition regex (`(_ re.loop lo hi) re`).
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if the argument is not `RegLan`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_re_loop(&mut self, re: Term, lo: u32, hi: u32) -> Result<Term, SolverError> {
        self.expect_reglan("re.loop", re)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("re.loop", vec![lo, hi]),
            vec![re.0],
            Sort::RegLan,
        )))
    }

    /// Create the empty-language regex (`re.none`), returning RegLan.
    pub fn re_none(&mut self) -> Term {
        Term(
            self.terms_mut()
                .mk_app(Symbol::named("re.none"), vec![], Sort::RegLan),
        )
    }

    /// Create the universal-language regex (`re.all`), returning RegLan.
    pub fn re_all(&mut self) -> Term {
        Term(
            self.terms_mut()
                .mk_app(Symbol::named("re.all"), vec![], Sort::RegLan),
        )
    }

    /// Create the any-single-character regex (`re.allchar`), returning RegLan.
    pub fn re_allchar(&mut self) -> Term {
        Term(
            self.terms_mut()
                .mk_app(Symbol::named("re.allchar"), vec![], Sort::RegLan),
        )
    }
}
