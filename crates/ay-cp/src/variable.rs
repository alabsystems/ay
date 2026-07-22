// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer variable identifiers and metadata.

use crate::domain::Domain;

/// Identifier for an integer variable in the CP model.
///
/// This is an index into the engine's variable store, not a SAT variable.
/// The [`IntegerEncoder`](crate::encoder::IntegerEncoder) maps between
/// `IntVarId` and SAT `Literal`s.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IntVarId(pub(crate) u32);

impl IntVarId {
    /// Get the raw index.
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// An integer variable with its initial domain and optional name.
#[derive(Debug, Clone)]
pub struct IntVariable {
    /// Unique identifier
    pub id: IntVarId,
    /// Human-readable name (from FlatZinc or model)
    pub name: Option<String>,
    /// Initial domain at creation time
    pub initial_domain: Domain,
}

/// Boolean variable in the CP model.
///
/// Booleans are integers with domain {0, 1}. This is a convenience alias
/// that maps directly to a SAT variable in the encoder.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoolVarId(pub(crate) IntVarId);

impl BoolVarId {
    /// Get the underlying integer variable.
    #[inline]
    pub fn as_int(self) -> IntVarId {
        self.0
    }
}
