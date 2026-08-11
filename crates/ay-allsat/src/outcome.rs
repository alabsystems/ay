// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Termination status for model enumeration.

/// How an AllSAT enumeration terminated.
///
/// This is important for consumers that rely on complete enumeration (e.g.,
/// interpolant computation). A truncated enumeration produces a weaker result
/// that may still be sound but is not exact.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub enum AllSatOutcome {
    /// Enumeration has not yet reached a terminal result.
    #[default]
    InProgress,
    /// All solutions were enumerated; the result is exact.
    Exhaustive,
    /// Enumeration was truncated because the `max_solutions` cap was reached.
    Capped,
    /// Enumeration stopped because the callback requested early termination.
    CallbackStopped,
    /// The SAT backend stopped without proving satisfiable or unsatisfiable.
    SolverUnknown,
    /// Enumeration did not start because an input was invalid.
    InvalidInput,
    /// An iterator was dropped before it reached a terminal solver result.
    IteratorDropped,
    /// An exact enumeration-derived counter could not represent the result.
    CountOverflow,
}

/// Invalid input supplied to an AllSAT operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum AllSatInputError {
    /// A signed clause contained zero or `i32::MIN`, neither of which is a
    /// representable internal literal.
    InvalidClauseLiteral(i32),
    /// Signed clauses can only be added to the internal backend. An external
    /// solver's native 0-based formula must be loaded before `from_solver`.
    ClauseAdditionUnsupportedBackend,
    /// A declared 1-based variable count can only be registered on the
    /// internal backend. External solvers already own their variable set.
    VariableRegistrationUnsupportedBackend,
    /// A projected variable is outside the internal backend's 1-based range.
    InternalProjectionVariableOutOfRange {
        /// Invalid projected variable.
        variable: u32,
        /// Largest valid internal variable, or zero when there are none.
        max_variable: u32,
    },
    /// A projected variable is outside the external backend's 0-based range.
    ExternalProjectionVariableOutOfRange {
        /// Invalid projected variable.
        variable: u32,
        /// Number of external user variables.
        variable_count: u32,
    },
    /// A projection listed the same variable more than once.
    DuplicateProjectionVariable(u32),
    /// A backend variable count cannot be represented safely by this API.
    BackendVariableCountOutOfRange(usize),
    /// A supposedly complete backend model omitted a variable needed for a
    /// blocking clause.
    BackendModelMissingVariable(u32),
    /// The external SAT backend failed to retract the enumeration scope.
    BackendScopePopFailed,
    /// The internal backend's max-index allocation would exceed its explicit
    /// resource-safety limit.
    InternalVariableIndexExceedsLimit {
        /// Requested 1-based variable identifier.
        variable: u32,
        /// Largest accepted 1-based identifier.
        max_variable: u32,
    },
    /// A declared internal variable count exceeds the same dense-allocation
    /// safety limit used for signed clause identifiers.
    InternalVariableCountExceedsLimit {
        /// Requested number of 1-based variables.
        variable_count: usize,
        /// Largest accepted variable count.
        max_variable: u32,
    },
}

impl std::fmt::Display for AllSatInputError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidClauseLiteral(literal) => {
                write!(f, "signed clause literal {literal} is not representable")
            }
            Self::ClauseAdditionUnsupportedBackend => write!(
                f,
                "signed clauses cannot be added after constructing from an external solver"
            ),
            Self::VariableRegistrationUnsupportedBackend => write!(
                f,
                "a declared variable count cannot be registered on an external solver"
            ),
            Self::InternalProjectionVariableOutOfRange {
                variable,
                max_variable,
            } => write!(
                f,
                "internal projection variable {variable} is outside 1..={max_variable}"
            ),
            Self::ExternalProjectionVariableOutOfRange {
                variable,
                variable_count,
            } => write!(
                f,
                "external projection variable {variable} is outside 0..{variable_count}"
            ),
            Self::DuplicateProjectionVariable(variable) => {
                write!(f, "projection variable {variable} is listed more than once")
            }
            Self::BackendVariableCountOutOfRange(count) => {
                write!(f, "backend variable count {count} is not representable")
            }
            Self::BackendModelMissingVariable(variable) => {
                write!(f, "backend model omitted projected variable {variable}")
            }
            Self::BackendScopePopFailed => {
                f.write_str("external SAT backend failed to retract the enumeration scope")
            }
            Self::InternalVariableIndexExceedsLimit {
                variable,
                max_variable,
            } => write!(
                f,
                "internal variable {variable} exceeds the resource-safety limit {max_variable}"
            ),
            Self::InternalVariableCountExceedsLimit {
                variable_count,
                max_variable,
            } => write!(
                f,
                "internal variable count {variable_count} exceeds the resource-safety limit {max_variable}"
            ),
        }
    }
}

impl std::error::Error for AllSatInputError {}

/// Statistics for ALL-SAT solving.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct AllSatStats {
    /// Number of SAT solver calls.
    pub sat_calls: u64,
    /// Number of solutions found.
    pub solutions_found: u64,
    /// Number of blocking clauses added.
    pub blocking_clauses: u64,
    /// Number of times enumeration reached its configured solution cap.
    pub allsat_cap_hits: u64,
    /// How the most recent enumeration terminated.
    pub outcome: AllSatOutcome,
    /// Typed input error when `outcome` is [`AllSatOutcome::InvalidInput`].
    pub input_error: Option<AllSatInputError>,
}

/// A definitive enumeration-derived answer was unavailable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AllSatIncomplete {
    /// Why enumeration stopped before proving exhaustion.
    pub outcome: AllSatOutcome,
    /// Number of valid solutions found before it stopped.
    pub solutions_found: u64,
    /// Typed input error when `outcome` is [`AllSatOutcome::InvalidInput`].
    pub input_error: Option<AllSatInputError>,
}

impl std::fmt::Display for AllSatIncomplete {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "AllSAT enumeration stopped as {:?} after {} solutions{}",
            self.outcome,
            self.solutions_found,
            self.input_error
                .map(|error| format!(": {error}"))
                .unwrap_or_default()
        )
    }
}

impl std::error::Error for AllSatIncomplete {}
