// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded admission for proof-ledger rollback snapshots.

use crate::executor::Executor;
use crate::executor_types::UnknownOrigin;
use crate::proof_tracker::checkpoint_budget::CheckpointCloneError;
use crate::proof_tracker::ProofTrackerCheckpoint;

const DEFAULT_CHECKPOINT_CLONE_BUDGET_BYTES: usize = 128 * 1024 * 1024;

/// Query-owned cumulative envelope. It deliberately does not live in
/// `ProofTracker`: nested verification swaps trackers while remaining inside
/// the same public query.
#[derive(Debug)]
pub(in crate::executor) struct ProofCheckpointBudget {
    remaining: usize,
}

#[derive(Clone, Copy)]
pub(super) struct CheckpointAllowance {
    pub(super) scan_limit: usize,
    pub(super) memory_available: usize,
}

impl Default for ProofCheckpointBudget {
    fn default() -> Self {
        Self {
            remaining: DEFAULT_CHECKPOINT_CLONE_BUDGET_BYTES,
        }
    }
}

impl ProofCheckpointBudget {
    pub(super) fn begin_external_query(&mut self) {
        self.remaining = DEFAULT_CHECKPOINT_CLONE_BUDGET_BYTES;
    }

    pub(super) fn reject_limit_exceeded(
        &mut self,
        memory_available: usize,
        query_available: usize,
    ) -> UnknownOrigin {
        if memory_available < query_available {
            UnknownOrigin::MemoryBudget
        } else {
            // Query is limiting (including a tie), so latch exhaustion and
            // avoid rescanning the same attacker-controlled ledger.
            self.remaining = 0;
            UnknownOrigin::DeterministicResourceBudget
        }
    }

    #[cfg(test)]
    pub(super) fn set_remaining(&mut self, bytes: usize) {
        self.remaining = bytes;
    }

    #[cfg(test)]
    pub(super) fn remaining(&self) -> usize {
        self.remaining
    }
}

impl Executor {
    /// Re-arm the allocation envelope at the outer API/command query boundary.
    /// Internal authority restarts and nested solves must not call this.
    pub(in crate::executor) fn begin_external_proof_checkpoint_budget(&mut self) {
        self.proof_checkpoint_budget.begin_external_query();
    }

    /// Admit a snapshot under active memory headroom and the cumulative query
    /// envelope. A decline never clones or mutates the proof ledger, though a
    /// query-bound decline latches the cumulative meter as exhausted.
    pub(in crate::executor) fn bounded_proof_rollback_checkpoint(
        &mut self,
    ) -> Result<ProofTrackerCheckpoint, UnknownOrigin> {
        if self.proof_checkpoint_budget.remaining == 0 {
            return Err(UnknownOrigin::DeterministicResourceBudget);
        }
        let process_limit = ay_sys::get_process_memory_limit();
        let executor_limit = self.memory_limit();
        let query_available = self.proof_checkpoint_budget.remaining;
        let sampled_current =
            (process_limit != 0 || executor_limit.is_some()).then(current_process_memory);
        let allowance = plan_checkpoint_allowance(
            query_available,
            executor_limit,
            process_limit,
            sampled_current,
        )?;
        let (checkpoint, charge) = match self
            .proof_tracker
            .rollback_checkpoint_bounded(allowance.scan_limit)
        {
            Ok(snapshot) => snapshot,
            Err(CheckpointCloneError::UnsupportedPayload) => {
                self.proof_checkpoint_budget.remaining = 0;
                return Err(UnknownOrigin::DeterministicResourceBudget);
            }
            Err(CheckpointCloneError::LimitExceeded) => {
                return Err(self
                    .proof_checkpoint_budget
                    .reject_limit_exceeded(allowance.memory_available, query_available));
            }
        };
        let Some(remaining) = self.proof_checkpoint_budget.remaining.checked_sub(charge) else {
            self.proof_checkpoint_budget.remaining = 0;
            return Err(UnknownOrigin::DeterministicResourceBudget);
        };
        self.proof_checkpoint_budget.remaining = remaining;
        Ok(checkpoint)
    }

    /// Whether a bulk clone has best-effort observed headroom under every
    /// active memory envelope.
    ///
    /// Requiring room for another whole observed footprint is conservative
    /// when live allocation accounting is available and useful predictive
    /// backpressure otherwise. It is not a capacity census or a process-wide
    /// reservation; clone-specific deterministic meters and the allocator/
    /// process hard limit remain authoritative.
    pub(in crate::executor) fn bulk_state_clone_fits_memory(&self) -> bool {
        let process_limit = ay_sys::get_process_memory_limit();
        let executor_limit = self.memory_limit();
        if process_limit == 0 && executor_limit.is_none() {
            return true;
        }
        let current = current_process_memory();
        bulk_clone_fits_allowances(current, executor_limit, process_limit)
    }
}

pub(super) fn bulk_clone_fits_allowances(
    current: usize,
    executor_limit: Option<usize>,
    process_limit: usize,
) -> bool {
    current != 0
        && process_memory_available(current, process_limit) >= current
        && executor_memory_available(current, executor_limit) >= current
}

pub(super) fn plan_checkpoint_allowance(
    query_available: usize,
    executor_limit: Option<usize>,
    process_limit: usize,
    sampled_current: Option<usize>,
) -> Result<CheckpointAllowance, UnknownOrigin> {
    let current = if process_limit == 0 && executor_limit.is_none() {
        0
    } else {
        let current = sampled_current.ok_or(UnknownOrigin::MemoryBudget)?;
        if current == 0 {
            return Err(UnknownOrigin::MemoryBudget);
        }
        current
    };
    let memory_available = process_memory_available(current, process_limit)
        .min(executor_memory_available(current, executor_limit));
    if memory_available == 0 {
        return Err(UnknownOrigin::MemoryBudget);
    }
    Ok(CheckpointAllowance {
        scan_limit: query_available.min(memory_available),
        memory_available,
    })
}

pub(super) fn process_memory_available(current: usize, raw_limit: usize) -> usize {
    if raw_limit == 0 {
        usize::MAX
    } else {
        let target = (raw_limit as u128 * 95 / 100) as usize;
        target.saturating_sub(current)
    }
}

pub(super) fn executor_memory_available(current: usize, limit: Option<usize>) -> usize {
    limit.map_or(usize::MAX, |limit| limit.saturating_sub(current))
}

fn current_process_memory() -> usize {
    // This is a best-effort observation, not a reservation. Sample the cheap
    // live ledger on both sides of the OS read so concurrent growth during the
    // syscall cannot be hidden by the earlier sample.
    let live_before = ay_sys::current_live_bytes();
    let footprint = ay_sys::current_footprint_bytes();
    let live = live_before.max(ay_sys::current_live_bytes());
    if footprint == 0 {
        live.max(ay_sys::current_rss_bytes())
    } else {
        live.max(footprint)
    }
}

#[cfg(test)]
pub(super) fn observed_memory_for_test(live: usize, footprint: usize, peak: usize) -> usize {
    if footprint == 0 {
        live.max(peak)
    } else {
        live.max(footprint)
    }
}
