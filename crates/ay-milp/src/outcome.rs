// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solve outcomes.

use num_rational::BigRational;

use crate::cert::{FarkasCertificate, OptimalityCertificate};
use crate::tree_cert::MilpInfeasibilityCertificate;

mod checked;

pub use checked::{CheckedOutcome, EvidenceShape, OutcomeCheckError};

/// Why a solve could not produce a verdict.
///
/// Anything the engine cannot warrant is `Unknown { reason }`; the API does
/// not encode an unsupported or interrupted solve as a definitive verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum UnknownReason {
    /// The deadline or time limit expired.
    Timeout,
    /// The caller's interrupt fired.
    Interrupted,
    /// An internal iteration/node budget was exhausted without a proof.
    IterationLimit,
    /// A memory budget was exhausted.
    MemoryLimit,
    /// `require_certificates` was set and the verdict's certificate could
    /// not be produced.
    CertificateUnavailable,
    /// The underlying solver answered `unknown` for its own reasons.
    SolverIncomplete {
        /// The solver's stated reason, when available.
        detail: String,
    },
    /// A verdict's own witness failed independent re-validation against the
    /// model, so the verdict was withheld rather than returned.
    ///
    /// This never fires on a correct solver: it means a lane produced an
    /// infeasible primal point, a value its point does not attain, or a dual
    /// bound that contradicts its own primal. Emitting `Unknown` keeps the
    /// wrong answer off the API (contract property 1) and leaves the bug
    /// loud rather than silent.
    WitnessRejected {
        /// What failed re-validation.
        detail: String,
    },
}

/// The result of a solve.
///
/// Verdict-bearing variants carry their evidence (contract property 2:
/// "evidence is data"). Model-value vectors are indexed by column insertion
/// order, exact `BigRational` end-to-end. Publicly constructed or recombined
/// values are untrusted claims until [`Outcome::check_against`] returns a
/// sealed [`CheckedOutcome`].
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use]
pub enum Outcome {
    /// A proven optimum. `model_values` is a feasible point achieving
    /// `value`; `cert` (when present) is an independently checkable dual
    /// bound. It completes optimality only when its exact offset-adjusted bound
    /// meets the checked primal value; a trailing integral relaxation bound
    /// remains search-dependent.
    Optimal {
        /// The optimal objective value (including the model's offset).
        value: BigRational,
        /// A feasible point achieving `value`.
        model_values: Vec<BigRational>,
        /// Dual-bound evidence, when the certificate lane could produce it.
        cert: Option<OptimalityCertificate>,
    },
    /// A feasible point without an optimality claim.
    Feasible {
        /// The feasible point.
        model_values: Vec<BigRational>,
        /// True when the point is an incumbent from an interrupted
        /// optimization (a better point may exist).
        incumbent_only: bool,
        /// A rigorous dual bound on the optimum from the interrupted tree —
        /// the weakest Neumaier–Shcherbina/exact bound among the open
        /// subproblems and the incumbent, in the model's frame (lower bound
        /// for Minimize, upper for Maximize, offset included). `None` when
        /// any part of the tree was discarded without proof. Unlike an
        /// exported certificate, this bound is not independently checkable.
        dual_bound: Option<BigRational>,
    },
    /// Proven infeasible. `cert` (when present) is the exact root-LP Farkas
    /// witness — the PREFERRED evidence when available (one combination to
    /// check instead of a tree). `tree_cert` is the whole-tree case-split
    /// witness for infeasibility the relaxation alone cannot see. When both
    /// are absent the verdict rests on the exact solver without exported
    /// evidence.
    Infeasible {
        /// Exact root-LP infeasibility evidence, when available. Preferred
        /// over `tree_cert` when present.
        cert: Option<FarkasCertificate>,
        /// Whole-tree case-split evidence, when branch-and-bound could capture
        /// and re-derive its tree in the caller's model frame.
        tree_cert: Option<MilpInfeasibilityCertificate>,
    },
    /// The objective is unbounded in its optimization direction.
    Unbounded,
    /// A rigorous or heuristic dual bound without a full proof (native
    /// engine; interior nodes). `rigorous` is only set for
    /// Neumaier–Shcherbina-corrected or exact bounds.
    Bound {
        /// The dual bound (lower bound for Minimize, upper for Maximize).
        dual_bound: BigRational,
        /// Whether the bound is rigorous (directed-rounding-corrected or
        /// exact). Callers must not use a non-rigorous bound to exclude
        /// feasible points.
        rigorous: bool,
    },
    /// No verdict. NEVER a silent wrong value.
    Unknown {
        /// Why.
        reason: UnknownReason,
    },
}

impl Outcome {
    /// True for `Optimal` / `Feasible`.
    #[must_use]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Optimal { .. } | Self::Feasible { .. })
    }

    /// True for `Infeasible`.
    #[must_use]
    pub fn is_infeasible(&self) -> bool {
        matches!(self, Self::Infeasible { .. })
    }

    /// True for `Unknown`.
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown { .. })
    }
}

/// COMPILE-TIME COVERAGE GUARD FOR THE CLI's `--format json`.
///
/// `Outcome` and `UnknownReason` are `#[non_exhaustive]`, so `src/bin/ay-milp.rs`
/// — a different crate — must carry a wildcard arm and cannot be told by the
/// compiler that a new variant exists. Its status/JSON coverage list would just
/// go on passing while the new variant fell into the untested `OTHER {other:?}`
/// arm.
///
/// These matches live in the DEFINING crate, where `non_exhaustive` does not
/// apply and the compiler checks them. Adding a variant breaks this build, and
/// the fix is to add it here AND to `every_outcome` / `every_unknown_reason` in
/// `src/bin/ay-milp.rs`'s `json_output_tests`.
#[cfg(test)]
mod cli_json_coverage {
    use super::*;

    /// The status token `verdict_line` must print. Keep in step with the binary.
    fn status_token(o: &Outcome) -> &'static str {
        match o {
            Outcome::Optimal { .. } => "OPTIMAL",
            Outcome::Feasible { .. } => "FEASIBLE",
            Outcome::Infeasible { .. } => "INFEASIBLE",
            Outcome::Unbounded => "UNBOUNDED",
            Outcome::Bound { .. } => "BOUND",
            Outcome::Unknown { .. } => "UNKNOWN",
        }
    }

    /// Whether this reason's `Debug` carries free text — i.e. whether it can
    /// break a hand-rolled JSON writer. Exhaustive on purpose.
    fn carries_free_text(r: &UnknownReason) -> bool {
        match r {
            UnknownReason::Timeout
            | UnknownReason::Interrupted
            | UnknownReason::IterationLimit
            | UnknownReason::MemoryLimit
            | UnknownReason::CertificateUnavailable => false,
            UnknownReason::SolverIncomplete { .. } | UnknownReason::WitnessRejected { .. } => true,
        }
    }

    #[test]
    fn the_binarys_status_vocabulary_is_closed() {
        let o = Outcome::Unknown {
            reason: UnknownReason::SolverIncomplete {
                detail: String::new(),
            },
        };
        assert_eq!(status_token(&o), "UNKNOWN");
        assert!(carries_free_text(&UnknownReason::SolverIncomplete {
            detail: String::new()
        }));
        assert!(!carries_free_text(&UnknownReason::Timeout));
    }
}

#[cfg(test)]
mod tests;
