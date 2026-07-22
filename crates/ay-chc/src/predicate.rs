// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Predicates (uninterpreted relations) in CHC problems

use crate::ChcSort;
use std::fmt;

/// Opaque identifier for a predicate declared in a CHC problem.
///
/// `PredicateId` values are unique only within a single [`crate::ChcProblem`]
/// instance. They are used throughout the solver as dense indices/keys (for
/// example in vectors or hash maps) and are intentionally lightweight.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PredicateId(pub(crate) u32);

impl PredicateId {
    /// Create a new predicate ID
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw ID value
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for PredicateId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "P{}", self.0)
    }
}

/// A predicate (uninterpreted relation) declaration.
///
/// A predicate symbol has the (conceptual) type:
/// `S1 × ... × Sn -> Bool`, where `arg_sorts = [S1, ..., Sn]`.
///
/// During CHC solving, the solver synthesizes an interpretation for each
/// predicate (typically as an invariant over its arguments). Predicate
/// applications appear in [`crate::ClauseBody::predicates`] and
/// [`crate::ClauseHead::Predicate`].
#[derive(Debug, Clone)]
pub struct Predicate {
    /// Unique identifier
    pub id: PredicateId,
    /// Human-readable name
    pub name: String,
    /// Sorts of arguments
    pub arg_sorts: Vec<ChcSort>,
}

impl Predicate {
    /// Create a new predicate
    pub fn new(id: PredicateId, name: impl Into<String>, arg_sorts: Vec<ChcSort>) -> Self {
        Self {
            id,
            name: name.into(),
            arg_sorts,
        }
    }

    /// Get the arity (number of arguments)
    pub fn arity(&self) -> usize {
        self.arg_sorts.len()
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.name)?;
        for (i, sort) in self.arg_sorts.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{sort:?}")?;
        }
        write!(f, ")")
    }
}
