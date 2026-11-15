// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::collections::VecDeque;

use super::*;

pub(super) const INITIAL_SLICE: Duration = Duration::from_millis(25);
pub(super) const MICROSTEPS_PER_CANDIDATE: usize = 32;
// A yield interval, not a search-prefix cutoff: later stages resume the same
// generator. Discovery must not postpone all pending retries indefinitely.
pub(super) const MAX_DISCOVERY_MICROSTEPS: usize = 256;

struct Pending<C> {
    candidate: C,
    allowance: Duration,
}

/// Common production/test policy. Logical slice allocation is deterministic
/// in `now`, which production takes from the searching thread's CPU clock
/// (`super::clock`); opaque native parse/print/drop intervals are not a hard
/// wall-time guarantee, and the caller's wall deadline is enforced by `control`
/// and by each probe's backstop.
pub(super) fn explore<C>(
    deadline: Instant,
    control: &SourceControl<'_>,
    mut now: impl FnMut() -> Instant,
    mut discover: impl FnMut() -> Option<Discovery<C>>,
    mut probe: impl FnMut(&C, Instant) -> Probe,
) -> Option<C> {
    let result = worker(deadline, control, &mut now, &mut discover, &mut probe);
    // The worker's pending FIFO has been destroyed before final admission.
    control.poll()?;
    (now() < deadline).then_some(())?;
    result
}

fn worker<C>(
    deadline: Instant,
    control: &SourceControl<'_>,
    now: &mut impl FnMut() -> Instant,
    discover: &mut impl FnMut() -> Option<Discovery<C>>,
    probe: &mut impl FnMut(&C, Instant) -> Probe,
) -> Option<C> {
    let mut pending = VecDeque::new();
    let mut exhausted = false;
    let mut quota = 1usize;
    loop {
        control.poll()?;
        (now() < deadline).then_some(())?;
        discover_stage(
            quota,
            deadline,
            control,
            now,
            discover,
            &mut pending,
            &mut exhausted,
        )?;
        let count = pending.len();
        if exhausted && count == 0 {
            return None;
        }
        for remaining_jobs in (1..=count).rev() {
            control.charge(1)?;
            let mut entry = pending.pop_front()?;
            let observed = now();
            let remaining = deadline.saturating_duration_since(observed);
            let slots = remaining_jobs.checked_add(usize::from(!exhausted))?;
            let share = remaining.checked_div(u32::try_from(slots).ok()?)?;
            let allowance = if exhausted && count == 1 {
                remaining
            } else {
                entry.allowance.min(share)
            };
            if allowance.is_zero() {
                return None;
            }
            let child_deadline = observed.checked_add(allowance)?.min(deadline);
            let verdict = probe(&entry.candidate, child_deadline);
            control.poll()?;
            let after = now();
            if after >= deadline {
                return None;
            }
            // Even a callback claiming SAT/UNSAT cannot commit a late result.
            // An expired local slice is not cancellation of the parent search.
            let verdict = match verdict {
                Probe::Terminal => return None,
                _ if after >= child_deadline => Probe::Inconclusive,
                other => other,
            };
            match verdict {
                Probe::Sat => return Some(entry.candidate),
                Probe::Unsat => {}
                Probe::Inconclusive => {
                    entry.allowance = entry.allowance.saturating_mul(2);
                    // This slot was just removed; reinsertion cannot increase
                    // capacity or copy the retained derivation/script payload.
                    pending.push_back(entry);
                }
                Probe::Terminal => return None,
            }
        }
        // Increasing discovery quotas precede increasing retries. A hard early
        // candidate cannot double its time allocation on every single decoy.
        quota = quota.saturating_mul(2);
    }
}

#[allow(clippy::too_many_arguments)]
fn discover_stage<C>(
    quota: usize,
    deadline: Instant,
    control: &SourceControl<'_>,
    now: &mut impl FnMut() -> Instant,
    discover: &mut impl FnMut() -> Option<Discovery<C>>,
    pending: &mut VecDeque<Pending<C>>,
    exhausted: &mut bool,
) -> Option<()> {
    let mut found = 0usize;
    let microsteps = quota
        .saturating_mul(MICROSTEPS_PER_CANDIDATE)
        .min(MAX_DISCOVERY_MICROSTEPS);
    for _ in 0..microsteps {
        if *exhausted || found == quota {
            break;
        }
        control.charge(1)?;
        (now() < deadline).then_some(())?;
        match discover()? {
            Discovery::Pending => {}
            Discovery::Exhausted => *exhausted = true,
            Discovery::Candidate(candidate) => {
                control.bytes(std::mem::size_of::<Pending<C>>().checked_mul(2)?)?;
                pending.try_reserve_exact(1).ok()?;
                pending.push_back(Pending {
                    candidate,
                    allowance: INITIAL_SLICE,
                });
                found += 1;
            }
        }
    }
    control.poll()
}

#[cfg(test)]
mod tests;
