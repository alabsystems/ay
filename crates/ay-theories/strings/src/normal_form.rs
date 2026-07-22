// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Normal form data structures for word equation solving.
//!
//! A normal form represents a string term as a sequence of "base" terms
//! (variables, constants, or irreducible concats), with dependency-tracked
//! explanations recording which equalities were used to derive each step.
//!
//! Reference: Liang et al., "A DPLL(T) Theory Solver for a Theory of Strings
//! and Regular Expressions", CAV 2014.
//! Reference: `reference/cvc5/src/theory/strings/normal_form.h`

use ay_core::term::TermId;

/// An explanation entry: a pair of terms whose equality was used.
///
/// Used internally for NF dependency tracking. The inference manager
/// converts these to `TheoryLit` when building conflict explanations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ExplainEntry {
    /// Left-hand side of the equality used.
    pub lhs: TermId,
    /// Right-hand side of the equality used.
    pub rhs: TermId,
}

/// A normal form for a single equivalence class of string terms.
///
/// The normal form is a flattened sequence of "base" terms such that
/// the concatenation of all base terms equals any member of the equivalence
/// class. Each base term is either a string variable, a string constant,
/// or an irreducible sub-expression.
///
/// The `deps` vector records which equalities were used in the derivation,
/// enabling conflict-relevant explanations.
#[derive(Debug, Clone, Default)]
pub(crate) struct NormalForm {
    /// The base terms, in order. The full string is their concatenation.
    pub base: Vec<TermId>,
    /// The representative term whose normal form this is.
    pub rep: Option<TermId>,
    /// The source term from which this normal form was derived.
    ///
    /// For concat-derived NFs, this is the concat term whose children produced
    /// `base`. For singleton NFs, this is the singleton term itself.
    pub source: Option<TermId>,
    /// Dependencies: equalities used to derive this normal form.
    pub deps: Vec<ExplainEntry>,
}

impl NormalForm {
    /// Create an empty normal form.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Create a normal form from a single base term (a variable or constant).
    pub(crate) fn singleton(term: TermId) -> Self {
        Self {
            base: vec![term],
            rep: Some(term),
            source: Some(term),
            deps: Vec::new(),
        }
    }

    /// Create a normal form for the empty string.
    #[cfg(test)]
    pub(crate) fn empty(rep: TermId) -> Self {
        Self {
            base: Vec::new(),
            rep: Some(rep),
            source: Some(rep),
            deps: Vec::new(),
        }
    }

    /// Number of base terms.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.base.len()
    }

    /// Whether the normal form is empty (represents the empty string).
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// Add an explanation dependency.
    pub(crate) fn add_dep(&mut self, lhs: TermId, rhs: TermId) {
        self.deps.push(ExplainEntry { lhs, rhs });
    }

    /// Merge explanation dependencies from another normal form.
    pub(crate) fn merge_deps(&mut self, other: &Self) {
        self.deps.extend_from_slice(&other.deps);
    }
}

#[cfg(test)]
#[path = "normal_form_tests.rs"]
mod tests;
