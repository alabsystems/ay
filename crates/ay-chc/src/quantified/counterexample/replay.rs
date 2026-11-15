// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A synthesized derivation uses internal native SAT authority, never authored permits.

use std::time::Duration;

use super::SourceControl;
use crate::CancellationToken;
use ay_core::time::Instant;
use ay_dpll::api::{Logic, ModelValue, ScalarFunctionModel, Solver};
use ay_sys::thread_clock::ThreadCpuClock;

mod complete;
pub(super) use complete::extract as extract_complete;

/// Search-only scheduling facts, not public proof grades. UNSAT retires one
/// source derivation; it never establishes safety of the complete Horn problem.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Probe {
    Sat,
    Unsat,
    Inconclusive,
    Terminal,
}

/// Where one native probe must stop.
///
/// `until` is a wall deadline. A work limit additionally bounds the CPU the
/// probing thread may spend, and `until` is then only the enclosing search's
/// backstop: a search slice measured on the wall is also spent by every
/// interval in which the scheduler ran another thread, so under CPU contention
/// it expired before the probe had done the work that decides it.
#[derive(Clone, Copy, Debug)]
pub(super) struct Budget {
    until: Instant,
    work: Option<WorkLimit>,
}

#[derive(Clone, Copy, Debug)]
struct WorkLimit {
    clock: ThreadCpuClock,
    until: Duration,
}

impl Budget {
    pub(super) fn wall(until: Instant) -> Self {
        Self { until, work: None }
    }

    /// Stop once the thread behind `clock` has consumed `until` of CPU, or at
    /// the wall `backstop`, whichever comes first.
    pub(super) fn work(backstop: Instant, clock: ThreadCpuClock, until: Duration) -> Self {
        Self {
            until: backstop,
            work: Some(WorkLimit { clock, until }),
        }
    }

    /// An unreadable CPU clock counts as spent: fail closed, never unbounded.
    fn spent(&self) -> bool {
        Instant::now() >= self.until
            || self
                .work
                .is_some_and(|work| work.clock.elapsed().is_none_or(|cpu| cpu >= work.until))
    }
}

pub(super) fn validate(
    obligation: &str,
    deadline: Instant,
    memory: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
) -> bool {
    probe(
        obligation,
        Budget::wall(deadline),
        memory,
        cancellation,
        control,
    ) == Probe::Sat
}

pub(super) fn probe(
    obligation: &str,
    budget: Budget,
    memory: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
) -> Probe {
    let result = match native_solve(obligation, budget, memory, cancellation, control) {
        Ok(solver) => {
            drop(solver);
            Probe::Sat
        }
        Err(result) => result,
    };
    // native_solve and the success arm destroyed all native contexts first.
    // Local slice expiry is retryable and must not cancel the shared search.
    finish(result, budget, control)
}

fn finish(result: Probe, budget: Budget, control: &SourceControl<'_>) -> Probe {
    if control.poll().is_none() || result == Probe::Terminal {
        Probe::Terminal
    } else if budget.spent() {
        Probe::Inconclusive
    } else {
        result
    }
}

/// Acquire one exact typed batch while this validated model is still alive.
/// Values alone are not replay evidence; the caller must pin and revalidate them.
pub(super) fn extract(
    obligation: &str,
    names: &[&str],
    function_names: &[&str],
    deadline: Instant,
    memory: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
) -> Option<(Vec<ModelValue>, Vec<ScalarFunctionModel>)> {
    if names.len() > 4096 || function_names.len() > 4096 {
        return None;
    }
    // Conservative earmark for admitted response text (8 MiB) plus the typed
    // decoder's retained-value allowance (16 MiB). This is not total native
    // allocation accounting: pre-admission model printing, S-expression AST
    // overhead and numeric scratch remain independently bounded/opaque. The
    // caller separately charges conversion, manifest and pin-output copies.
    control.bytes(24 * 1024 * 1024)?;
    // Function extraction reads a separate bounded whole-model response. Its
    // allowance is cumulative across the complete requested function batch,
    // never reset per declaration. Empty registries preserve the old cost.
    if !function_names.is_empty() {
        control.bytes(24 * 1024 * 1024)?;
    }
    let result = attempt(
        obligation,
        deadline,
        memory,
        cancellation,
        control,
        |solver| {
            let values = solver.try_get_named_values(names).ok()?;
            control.poll()?;
            (Instant::now() < deadline).then_some(())?;
            // Both batches come from this one immutable, validated model.
            // Missing functions cannot trigger another solve or partial return.
            let functions = if function_names.is_empty() {
                Vec::new()
            } else {
                solver
                    .try_get_named_scalar_function_models(function_names)
                    .ok()?
            };
            Some((values, functions))
        },
    );
    // Native model printing/decoding has bounded admission but opaque intervals.
    // Drop the solver first; no late cancellation can mint a retained trace.
    control.poll()?;
    (Instant::now() < deadline).then_some(())?;
    result
}

fn attempt<T>(
    obligation: &str,
    deadline: Instant,
    memory: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
    read: impl FnOnce(&Solver) -> Option<T>,
) -> Option<T> {
    let budget = Budget::wall(deadline);
    let solver = native_solve(obligation, budget, memory, cancellation, control).ok()?;
    control.poll()?;
    if Instant::now() >= deadline {
        return None;
    }
    let result = read(&solver)?;
    control.poll()?;
    if Instant::now() >= deadline
        || memory.is_some_and(|limit| solver.instance_term_bytes() > limit)
    {
        return None;
    }
    Some(result)
}

fn native_solve(
    obligation: &str,
    budget: Budget,
    memory: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
) -> Result<Solver, Probe> {
    control.poll().ok_or(Probe::Terminal)?;
    if memory == Some(0) {
        return Err(Probe::Terminal);
    }
    if budget.spent() {
        return Err(Probe::Inconclusive);
    }
    // The renderer owns this exact header and plain-hard grammar. Removing
    // only that prefix avoids a second set-logic and allocates no script copy.
    let body = obligation
        .strip_prefix("(set-logic ALL)\n")
        .ok_or(Probe::Inconclusive)?;
    let mut solver = Solver::try_new(Logic::All).map_err(|_| Probe::Inconclusive)?;
    solver.set_term_memory_limit(memory);
    control.poll().ok_or(Probe::Terminal)?;
    if memory.is_some_and(|limit| solver.instance_term_bytes() > limit) {
        return Err(Probe::Inconclusive);
    }
    // Native parsing has opaque intervals: the setter installs its exact
    // term ceiling at check-sat, not here. Bounded source preparation and
    // boundary checks are not a claim of actively limited parsing RSS.
    let assertions = solver
        .parse_smtlib2(body)
        .map_err(|_| Probe::Inconclusive)?;
    let nonempty = !assertions.is_empty();
    drop(assertions);
    control.poll().ok_or(Probe::Terminal)?;
    if !nonempty
        || budget.spent()
        || memory.is_some_and(|limit| solver.instance_term_bytes() > limit)
    {
        return Err(Probe::Inconclusive);
    }
    // The solver's own wall timeout is the backstop; a work limit is enforced
    // by the watchdog reading this thread's CPU clock.
    solver.set_timeout(Some(budget.until.saturating_duration_since(Instant::now())));
    let attempt = cancellation.sticky_child();
    let verdict = solver.check_sat_interruptible_internal_query(move || {
        attempt.is_cancelled() || budget.spent() || ay_core::TermStore::global_memory_exceeded()
    });
    control.poll().ok_or(Probe::Terminal)?;
    if budget.spent() || memory.is_some_and(|limit| solver.instance_term_bytes() > limit) {
        return Err(Probe::Inconclusive);
    }
    if verdict.is_sat() && verdict.was_model_validated() && verdict.has_sat_emission_witness() {
        Ok(solver)
    } else if verdict.is_unsat() {
        Err(Probe::Unsat)
    } else {
        Err(Probe::Inconclusive)
    }
}

#[cfg(test)]
mod tests;
