// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// A satisfying assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Solution {
    /// Assignment indexed by the backend's native variable identifiers.
    ///
    /// Internal-backend solutions are 1-based and retain an unused entry zero;
    /// external-backend solutions are 0-based and contain only user variables.
    pub assignment: Vec<bool>,
    indexing: SolutionIndexing,
}

/// Variable indexing used by a solution's originating backend.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SolutionIndexing {
    /// Variables are numbered `1..assignment.len()`, with entry zero unused.
    OneBased,
    /// Variables are numbered `0..assignment.len()`.
    ZeroBased,
}

impl std::fmt::Display for SolutionIndexing {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OneBased => f.write_str("1-based"),
            Self::ZeroBased => f.write_str("0-based"),
        }
    }
}

/// A solution variable or literal cannot be accessed unambiguously.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SolutionLiteralError {
    /// Signed clause encoding reserves zero and supports variables only through
    /// `i32::MAX`.
    VariableOutOfRange(u32),
    /// The requested variable is not present in this assignment.
    VariableMissing(u32),
    /// Signed literals are a 1-based API but this solution is 0-based.
    IndexingMismatch(SolutionIndexing),
}

impl std::fmt::Display for SolutionLiteralError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::VariableOutOfRange(variable) => write!(
                f,
                "variable {variable} is outside signed-literal range 1..=i32::MAX"
            ),
            Self::VariableMissing(variable) => {
                write!(f, "variable {variable} is not present in this assignment")
            }
            Self::IndexingMismatch(indexing) => write!(
                f,
                "signed-literal conversion requires a 1-based solution, got {indexing}"
            ),
        }
    }
}

impl std::error::Error for SolutionLiteralError {}

impl Solution {
    pub(super) fn new(assignment: Vec<bool>, indexing: SolutionIndexing) -> Self {
        Self {
            assignment,
            indexing,
        }
    }

    /// Return this solution's variable-indexing convention.
    pub fn indexing(&self) -> SolutionIndexing {
        self.indexing
    }

    /// Get the value of a variable in this solution.
    pub fn get(&self, var: u32) -> Option<bool> {
        if self.indexing == SolutionIndexing::OneBased && var == 0 {
            return None;
        }
        self.assignment.get(var as usize).copied()
    }

    /// Return whether a variable is true, or `None` when it is absent.
    ///
    /// This is an explicit alias for [`get`](Self::get); a missing variable is
    /// never silently treated as false.
    pub fn is_true(&self, var: u32) -> Option<bool> {
        self.get(var)
    }

    /// Check if a 1-indexed signed literal is satisfied by this solution.
    ///
    /// Returns an error for zero, an unrepresentable literal, or a variable
    /// absent from this assignment. In particular, an absent negative literal
    /// is not silently treated as satisfied.
    pub fn satisfies(&self, lit: i32) -> Result<bool, SolutionLiteralError> {
        if self.indexing != SolutionIndexing::OneBased {
            return Err(SolutionLiteralError::IndexingMismatch(self.indexing));
        }
        let var = lit.unsigned_abs();
        if var == 0 || var > i32::MAX as u32 {
            return Err(SolutionLiteralError::VariableOutOfRange(var));
        }
        let value = self
            .get(var)
            .ok_or(SolutionLiteralError::VariableMissing(var))?;
        Ok(value == (lit > 0))
    }

    /// Convert 1-indexed variables to signed literals representing this
    /// assignment. Returns a positive literal if true and a negative literal
    /// if false.
    ///
    /// Signed clause encoding cannot represent external-backend variable zero;
    /// callers using that backend should retain its native 0-indexed values or
    /// translate them into a separate 1-indexed assignment first.
    pub fn to_literals(&self, vars: &[u32]) -> Result<Vec<i32>, SolutionLiteralError> {
        if self.indexing != SolutionIndexing::OneBased {
            return Err(SolutionLiteralError::IndexingMismatch(self.indexing));
        }
        vars.iter()
            .map(|&var| {
                let literal = i32::try_from(var)
                    .ok()
                    .filter(|&literal| literal != 0)
                    .ok_or(SolutionLiteralError::VariableOutOfRange(var))?;
                let value = self
                    .get(var)
                    .ok_or(SolutionLiteralError::VariableMissing(var))?;
                Ok(if value { literal } else { -literal })
            })
            .collect()
    }
}
