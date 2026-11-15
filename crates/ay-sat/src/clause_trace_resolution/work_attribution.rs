// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fixed-size diagnostic partition of the existing conversion work counter.
//!
//! Only coarse phase boundaries update this ledger. It performs no allocation,
//! clock reads, control polls or resource debits and never influences acceptance.
//! Counters measure charged work, not time, heap usage or independent DAG replay.

use std::fmt;

const PHASE_COUNT: usize = 10;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(usize)]
pub(super) enum ConversionPhase {
    #[default]
    Other,
    Preflight,
    Namespace,
    Originals,
    Derived,
    Compaction,
    RootSetup,
    RootedRepair,
    Synthesis,
    Finalize,
}

impl ConversionPhase {
    fn name(self) -> &'static str {
        match self {
            Self::Other => "other",
            Self::Preflight => "preflight",
            Self::Namespace => "namespace",
            Self::Originals => "originals",
            Self::Derived => "derived",
            Self::Compaction => "compaction",
            Self::RootSetup => "root_setup",
            Self::RootedRepair => "rooted_repair",
            Self::Synthesis => "synthesis",
            Self::Finalize => "finalize",
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct WorkAttribution {
    counts: [u64; PHASE_COUNT],
    phase: ConversionPhase,
    last_work: u64,
    complete: bool,
}

impl Default for WorkAttribution {
    fn default() -> Self {
        Self {
            counts: [0; PHASE_COUNT],
            phase: ConversionPhase::Other,
            last_work: 0,
            complete: true,
        }
    }
}

impl WorkAttribution {
    /// Normal conversion work is monotone and checked before publication, so
    /// each delta and each exclusive subtotal fit in its u64 total. If that
    /// invariant is ever broken, discard attribution rather than panic, alter
    /// a solver result or silently saturate; retain the exact total as Other
    /// and explicitly mark the diagnostic incomplete.
    fn record(&mut self, work: u64) {
        let next = work
            .checked_sub(self.last_work)
            .and_then(|delta| self.counts[self.phase as usize].checked_add(delta));
        match next {
            Some(value) => self.counts[self.phase as usize] = value,
            None => {
                self.counts = [0; PHASE_COUNT];
                self.counts[ConversionPhase::Other as usize] = work;
                self.complete = false;
            }
        }
        self.last_work = work;
    }

    pub(super) fn switch(&mut self, next: ConversionPhase, work: u64) -> ConversionPhase {
        self.record(work);
        let previous = self.phase;
        self.phase = next;
        previous
    }

    /// Include the active phase's pending delta, including a failing debit,
    /// without changing the live ledger or performing another meter operation.
    pub(super) fn snapshot(&self, work: u64) -> WorkSnapshot {
        let mut ledger = *self;
        ledger.record(work);
        WorkSnapshot(ledger)
    }
}

pub(super) struct WorkSnapshot(WorkAttribution);

impl fmt::Display for WorkSnapshot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ledger = &self.0;
        let [other, preflight, namespace, originals, derived, compaction, root_setup, rooted_repair, synthesis, finalize] =
            ledger.counts;
        write!(
            f,
            "total={} phase={} complete={} other={other} preflight={preflight} namespace={namespace} originals={originals} derived={derived} compaction={compaction} root_setup={root_setup} rooted_repair={rooted_repair} synthesis={synthesis} finalize={finalize}",
            ledger.last_work,
            ledger.phase.name(),
            ledger.complete
        )
    }
}

#[cfg(test)]
mod tests;
