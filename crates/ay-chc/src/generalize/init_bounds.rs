// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Bounds on initial values for a variable.
///
/// Represents the range `[min, max]` of values a variable can take in the
/// initial state. Used by init-bound-aware generalizers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct InitBounds {
    /// Minimum value in initial state
    pub(crate) min: i64,
    /// Maximum value in initial state
    pub(crate) max: i64,
}

impl InitBounds {
    /// Create bounds for a range.
    pub(crate) fn range(min: i64, max: i64) -> Self {
        Self { min, max }
    }

    /// Check if this represents an exact value (min == max).
    pub(crate) fn is_exact(&self) -> bool {
        self.min == self.max
    }
}

#[cfg(test)]
impl InitBounds {
    /// Create bounds for a single value.
    pub(crate) fn exact(val: i64) -> Self {
        Self { min: val, max: val }
    }

    /// Create unbounded (for variables with no init constraints).
    pub(crate) fn unbounded() -> Self {
        Self {
            min: i64::MIN,
            max: i64::MAX,
        }
    }

    /// Check if a value is within these bounds.
    pub(crate) fn contains(&self, val: i64) -> bool {
        val >= self.min && val <= self.max
    }
}
