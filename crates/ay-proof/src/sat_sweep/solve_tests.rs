// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Which ends of a sweep's solver call its counts, a stop or its deadline
//! decided, and which its environment may have.

use super::*;
use ay_sat::{ResolutionProofPhase, ResolutionProofResource, ResolutionValidationResource};

#[test]
fn a_call_ended_by_its_counts_a_stop_or_its_deadline_is_counted() {
    use ResolutionProofError as E;
    let unknown = |reason| {
        Err(E::SolverUnknown {
            reason: Some(reason),
        })
    };
    for outcome in [
        Ok(ResolutionSolveOutcome::Sat(vec![true])),
        Err(E::Satisfiable),
        Err(E::LimitExceeded {
            resource: ResolutionProofResource::Conflicts,
            limit: 100,
            actual: 100,
        }),
        Err(E::Cancelled),
        Err(E::DeadlineExceeded {
            phase: ResolutionProofPhase::Solve,
        }),
        Err(E::Validation(ResolutionValidationError::DeadlineExceeded)),
        unknown(SatUnknownReason::DeadlineExceeded),
        unknown(SatUnknownReason::ResourceBudget),
    ] {
        assert!(ended_as_counted(&outcome), "{outcome:?}");
    }
}

#[test]
fn a_failed_allocation_or_an_interrupt_is_not() {
    use ResolutionProofError as E;
    for outcome in [
        Err(E::AllocationFailed {
            resource: ResolutionProofResource::ProofOutputBytes,
        }),
        Err(E::Validation(ResolutionValidationError::AllocationFailed {
            resource: ResolutionValidationResource::Bytes,
        })),
        // ay-sat's process-memory interrupt ends a solve so.
        Err(E::SolverUnknown {
            reason: Some(SatUnknownReason::Interrupted),
        }),
        Err(E::SolverUnknown { reason: None }),
        Err(E::ProofWriterUnavailable),
    ] {
        assert!(!ended_as_counted(&outcome), "{outcome:?}");
    }
}
