// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sealed verification reports and their derived verdicts.

use super::OptimalityCheck;

mod check;

pub(super) use check::verify_with_checker;

/// Why a solver claim could not be fully verified.
///
/// An unverified claim has not been disproved, but it is not authoritative and
/// must not be presented as a verification pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum UnverifiedReason {
    /// The solver output contained no status line.
    MissingStatus,
    /// The solver reported `UNKNOWN`.
    UnknownStatus,
    /// The status is not supported by this result checker.
    UnsupportedStatus,
    /// An UNSAT claim had no independently checked proof.
    UnsatisfiableWithoutProof,
    /// An optimum claim omitted its objective value.
    MissingClaimedObjective,
    /// An optimum claim was made for an instance with no objective.
    MissingInstanceObjective,
    /// The independent optimum check was disabled or unavailable.
    OptimalityCheckSkipped,
    /// The independent optimum check did not reach a conclusion.
    OptimalityCheckInconclusive,
    /// A strict improvement over the claimed value is outside the `i128` range.
    OptimalityBoundOutOfRange,
}

/// Why a solver claim was rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum VerificationFailure {
    /// A model-bearing status had no model.
    MissingModel,
    /// At least one original constraint rejected the reported model.
    InfeasibleModel,
    /// The reported and independently computed objective values differed.
    ObjectiveMismatch,
    /// The model's exact objective value is outside the `i128` range.
    ObjectiveOverflow,
    /// The independent checker found a strictly better feasible solution.
    OptimalityRefuted,
}

/// Authority carried by a [`VerifyReport`].
///
/// Only the first two variants are fully verified. `Unverified` is a
/// fail-closed partial result; `Rejected` means a concrete check disproved part
/// of the solver output.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum VerificationVerdict {
    /// A SAT claim has an independently checked feasible model.
    VerifiedSatisfiable,
    /// An OPTIMUM claim has a checked model/objective and confirmed optimality.
    VerifiedOptimal,
    /// The available evidence was insufficient for a verification pass.
    Unverified(UnverifiedReason),
    /// A concrete verification check failed.
    Rejected(VerificationFailure),
}

impl VerificationVerdict {
    /// Stable label for reports and command-line summaries.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::VerifiedSatisfiable | Self::VerifiedOptimal => "VERIFIED",
            Self::Unverified(_) => "UNVERIFIED",
            Self::Rejected(_) => "REJECTED",
        }
    }

    /// Whether this verdict is fully verified.
    #[must_use]
    pub const fn is_verified(self) -> bool {
        matches!(self, Self::VerifiedSatisfiable | Self::VerifiedOptimal)
    }

    /// Whether this verdict is incomplete rather than disproved.
    #[must_use]
    pub const fn is_unverified(self) -> bool {
        matches!(self, Self::Unverified(_))
    }

    /// Whether a concrete check rejected the solver output.
    #[must_use]
    pub const fn is_rejected(self) -> bool {
        matches!(self, Self::Rejected(_))
    }
}

/// Immutable report produced by [`super::verify`].
///
/// The report has no public constructor or mutable fields. Its authority is
/// derived by the checker and exposed through [`Self::verdict`].
///
/// ```compile_fail
/// # fn forge(mut report: ay_pb_core::VerifyReport) {
/// report.verdict = ay_pb_core::VerificationVerdict::VerifiedOptimal;
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct VerifyReport {
    status: Option<String>,
    checked_model: bool,
    total_constraints: usize,
    violated_constraints: usize,
    claimed_objective: Option<i128>,
    computed_objective: Option<i128>,
    objective_matches: Option<bool>,
    optimality: OptimalityCheck,
    verdict: VerificationVerdict,
    messages: Vec<String>,
}

impl VerifyReport {
    /// Solver status text carried by the untrusted input.
    #[must_use]
    pub fn status(&self) -> Option<&str> {
        self.status.as_deref()
    }

    /// Whether a reported model was independently checked.
    #[must_use]
    pub const fn checked_model(&self) -> bool {
        self.checked_model
    }

    /// Number of original constraints considered by the model check.
    #[must_use]
    pub const fn total_constraints(&self) -> usize {
        self.total_constraints
    }

    /// Number of original constraints violated by the reported model.
    #[must_use]
    pub const fn violated_constraints(&self) -> usize {
        self.violated_constraints
    }

    /// Objective value claimed on the last `o` line.
    #[must_use]
    pub const fn claimed_objective(&self) -> Option<i128> {
        self.claimed_objective
    }

    /// Objective value independently computed from the reported model.
    #[must_use]
    pub const fn computed_objective(&self) -> Option<i128> {
        self.computed_objective
    }

    /// Whether claimed and computed objective values agree, when both exist.
    #[must_use]
    pub const fn objective_matches(&self) -> Option<bool> {
        self.objective_matches
    }

    /// Result of the independent optimum check.
    #[must_use]
    pub const fn optimality(&self) -> &OptimalityCheck {
        &self.optimality
    }

    /// Typed, checker-derived verification authority.
    #[must_use]
    pub const fn verdict(&self) -> VerificationVerdict {
        self.verdict
    }

    /// Whether the solver claim is fully verified.
    #[must_use]
    pub const fn is_verified(&self) -> bool {
        self.verdict.is_verified()
    }

    /// Human-readable findings in evaluation order.
    #[must_use]
    pub fn messages(&self) -> &[String] {
        &self.messages
    }
}
