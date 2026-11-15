// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Live-source-bound retained certificates and one original CHC request owner.
//!
//! The offline v4 reader verifies a snapshot, not external source authority.
//! Only this module's live exact-query export can mint the bound capabilities.
//! Logical cumulative accounting is not allocator-exact RSS or hard latency;
//! parser, search, arithmetic and destruction retain guarded opaque intervals.

use super::{ReplayLimit, ReplayMemory};
use ay_core::{time::Instant, TermId};
use ay_dpll::api::{RetainedProofBundle, RetainedProofTransportLimits};
use std::rc::Rc;

mod discharge;
mod progress;
mod transport;
pub(crate) use discharge::check_plain_unsat_retained_native_with_progress;
pub(crate) use progress::{RetainedReplayProgress, Settlement};

/// A complete third replay of a v4 owner exported from a LIVE exact query.
/// Neither raw documents nor detached recheck reports can construct this type.
pub(crate) struct BoundRetainedProof {
    query: Vec<u8>,
    bundle: RetainedProofBundle,
    request: Rc<()>,
    strict_verdict: ay_dpll::api::StrictProofVerdict,
    // Declared last: fields drop in order, so this obligation's transient
    // proof bytes return only after the proof owner above is gone.
    settlement: Settlement,
}

/// Exact original query and actual-v4 bytes, still paired by live authority.
/// Read access does not authorize substitution or create a new bound owner.
pub(crate) struct BoundRetainedProofBytes {
    query: Vec<u8>,
    bundle: Vec<u8>,
    request: Rc<()>,
    strict_verdict: ay_dpll::api::StrictProofVerdict,
}

#[cfg(test)]
mod fee_census;
#[cfg(test)]
mod tests;
