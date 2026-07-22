// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term and function declaration handles.

use ay_core::{Sort, TermId};

/// A handle to a term in the solver
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Term(pub(crate) TermId);

impl Term {
    /// Get the underlying term ID.
    ///
    /// This is a stable handle for comparison, hashing, and diagnostics. It is
    /// only meaningful with the solver that created this term.
    pub fn id(self) -> TermId {
        self.0
    }

    /// Create a Term from a raw u32 handle.
    /// Used by FFI layers to reconstitute Term handles from opaque integer IDs.
    ///
    /// # Safety (logical)
    /// The caller must ensure `raw` corresponds to a valid term in the solver
    /// that created it. Using an invalid or stale handle is undefined behavior
    /// at the solver level (may panic or produce incorrect results).
    #[must_use]
    pub fn from_raw(raw: u32) -> Self {
        Self(TermId(raw))
    }

    /// Extract the raw u32 handle from a Term.
    /// Used by FFI layers to pass Term handles across the C ABI boundary.
    #[must_use]
    pub fn to_raw(self) -> u32 {
        self.0 .0
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Term({})", self.0)
    }
}

/// A declared function (n-arity) that can be applied to arguments.
///
/// For 0-arity functions (constants), use `Solver::declare_const` instead.
/// For higher arity functions, use `Solver::declare_fun` to create a `FuncDecl`,
/// then `Solver::apply` to create application terms.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncDecl {
    /// Function name
    pub(crate) name: String,
    /// Argument sorts (domain)
    pub(crate) domain: Vec<Sort>,
    /// Return sort (range)
    pub(crate) range: Sort,
}

impl FuncDecl {
    /// Create a new function declaration.
    ///
    /// Used by FFI layers to construct synthetic func_decl handles for
    /// built-in operators and model constant declarations.
    #[must_use]
    pub fn new(name: String, domain: Vec<Sort>, range: Sort) -> Self {
        Self {
            name,
            domain,
            range,
        }
    }

    /// Get the function name
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the function arity (number of arguments)
    #[must_use]
    pub fn arity(&self) -> usize {
        self.domain.len()
    }

    /// Get the domain sorts
    #[must_use]
    pub fn domain(&self) -> &[Sort] {
        &self.domain
    }

    /// Get the range sort
    #[must_use]
    pub fn range(&self) -> &Sort {
        &self.range
    }
}

impl std::fmt::Display for FuncDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.domain.is_empty() {
            // 0-arity: name : range
            write!(f, "{} : {}", self.name, self.range)
        } else {
            // n-arity: name : (domain1, domain2, ...) -> range
            write!(f, "{} : (", self.name)?;
            for (i, sort) in self.domain.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{sort}")?;
            }
            write!(f, ") -> {}", self.range)
        }
    }
}
