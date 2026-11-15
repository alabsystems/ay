// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Verdict-only searches: the executors they build skip the proof cycle.
//!
//! [`new_search_executor`](super::new_search_executor) builds every executor
//! a CHC engine uses for its own SMT queries. A plain solve keeps those
//! executors proof-carrying: each UNSAT records a proof and mints and
//! strictly checks a certificate before it is answered.
//!
//! Some searches cannot use that work at all. The counterexample replay
//! (`BmcSolver::replay_confirm_unsafe_on_problem`) is one:
//!
//! * Its Safe and its Unknown both mean "not confirmed".
//! * Its Unsafe is accepted only afterwards, outside this scope, by
//!   `PdrSolver::try_confirm_counterexample`. That check accepts only on
//!   ground evaluation of a derivation over the clauses: the bounded
//!   per-clause solves it may use to propose witness values are checked by
//!   that evaluation, and an SMT verdict can only refute. (BMC's own witness
//!   gate runs the same check inside the search, under the guard; what it
//!   accepts there is a candidate the replay checks again outside it.)
//!
//! So an UNSAT inside the replay only prunes one branch of the search for a
//! counterexample. A wrong one could hide a counterexample (the fail-closed
//! direction), but it cannot create a claim. Still, the replay paid a full
//! certificate per UNSAT. On model-checker-consumer's realloc-grow twin (all 39 error
//! rules) the 11 UNSAT branches before the SAT one took 10.2 s of executor
//! time proof-carrying and 0.26 s without the cycle. In a plain solve the
//! probe has 15 s, so the twin went `unknown`.
//!
//! [`ScopedVerdictOnlySearch`] marks such a search on the current thread.
//! While a guard is alive, `new_search_executor` builds its executors in
//! the shedding posture (`Executor::set_competition_mode`). This is the same
//! posture `--no-proof` gives every search executor. The independent model
//! gate and every wrong-answer guard stay on, and an UNSAT goes through the
//! scope-authenticated raw admission lane.
//!
//! Install a guard only around a search whose every verdict is search
//! guidance, as above. Never install one around a verifier, a certificate
//! lane, or a search whose UNSAT or Safe answer is published. The raw
//! SMT-LIB script channels, whose `unsat` can be published, build their
//! executors without consulting the guard (`new_script_executor`), and the
//! certificate lanes never build theirs through `new_search_executor`.
//!
//! The guard is per thread and `!Send`. A thread the search spawns does not
//! inherit it, so its executors stay proof-carrying, which costs time but is
//! never unsound.

use std::cell::Cell;
use std::marker::PhantomData;

thread_local! {
    /// Depth of live [`ScopedVerdictOnlySearch`] guards on this thread.
    static VERDICT_ONLY_DEPTH: Cell<u32> = const { Cell::new(0) };
    /// Search executors built under a guard on this thread (tests).
    #[cfg(test)]
    static SHED_BUILDS: Cell<usize> = const { Cell::new(0) };
}

/// RAII guard: while it is alive, the search executors this thread builds
/// skip the proof cycle (see the module doc for when that is allowed).
///
/// Guards nest through a depth counter. The guard is `!Send`, so the depth
/// can only be decremented on the thread that raised it.
#[must_use = "the search sheds the proof cycle only while the guard is alive"]
pub(crate) struct ScopedVerdictOnlySearch {
    _not_send: PhantomData<*const ()>,
}

impl ScopedVerdictOnlySearch {
    /// Mark the enclosing scope as a verdict-only search.
    pub(crate) fn install() -> Self {
        VERDICT_ONLY_DEPTH.with(|depth| depth.set(depth.get().saturating_add(1)));
        Self {
            _not_send: PhantomData,
        }
    }
}

impl Drop for ScopedVerdictOnlySearch {
    fn drop(&mut self) {
        VERDICT_ONLY_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
    }
}

/// Whether a search executor built now should skip the proof cycle because a
/// [`ScopedVerdictOnlySearch`] guard is alive on this thread.
pub(super) fn search_sheds_proof_cycle() -> bool {
    let active = VERDICT_ONLY_DEPTH.with(Cell::get) > 0;
    #[cfg(test)]
    if active {
        SHED_BUILDS.with(|builds| builds.set(builds.get().saturating_add(1)));
    }
    active
}

/// Whether a guard is alive on this thread (tests).
#[cfg(test)]
pub(crate) fn verdict_only_search_active() -> bool {
    VERDICT_ONLY_DEPTH.with(Cell::get) > 0
}

/// Search executors this thread has built under a guard (tests).
#[cfg(test)]
pub(crate) fn shed_search_executors_built() -> usize {
    SHED_BUILDS.with(Cell::get)
}

#[cfg(test)]
mod tests;
