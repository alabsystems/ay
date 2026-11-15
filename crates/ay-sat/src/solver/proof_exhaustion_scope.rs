// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Keeping the proof-mode inprocessing controls after #A2b exhaustion, for
//! solvers that re-decide a verdict as evidence.
//!
//! When a solver's search-time proof bookkeeping budget is exhausted,
//! [`Solver::degrade_proof_bookkeeping_after_exhaustion`] drops the LRAT
//! trace and, by default, restores the controls proof mode had disabled
//! (BVE, decompose, factor, SBVA, congruence and sweep: the transforms with no
//! LRAT support), so the search continues at full `--no-proof` power.
//!
//! An embedder that runs a solve to CHECK another one may want the opposite:
//! the bookkeeping meter, for its cost, but not the transforms the checked
//! solve's degraded search ran, so that the check does not walk the same
//! unproved simplification path. A solver whose budget is set while a
//! [`keep_proof_inprocessing_after_exhaustion`] scope is open on the current
//! thread latches that choice and, on exhaustion, keeps its proof-mode
//! controls. ay-dpll opens the scope around the deferred-trust discharge's
//! fresh re-decisions (`unsat_cert/screened_reconfirmation.rs`).
//!
//! The choice is latched when the budget is set, not read when the budget
//! runs out, so where the search later runs does not matter. A solver whose
//! budget is set on another thread does not latch it, and degrades as before.
//! Verdicts are unaffected either way: this only decides which optional
//! simplifications the rest of the search may run.

use std::cell::Cell;
use std::marker::PhantomData;
use std::rc::Rc;

use super::Solver;

thread_local! {
    /// Open [`keep_proof_inprocessing_after_exhaustion`] scopes on this thread.
    // None means nesting overflowed: conservatively keep the clamp until the
    // thread exits, since subsequent drops cannot recover the exact depth.
    static KEEP_PROOF_INPROCESSING_DEPTH: Cell<Option<u32>> = const { Cell::new(Some(0)) };
}

/// An open [`keep_proof_inprocessing_after_exhaustion`] scope; dropping it
/// closes the scope on the same thread. The guard cannot move between threads:
/// its destructor restores thread-local state, not the solver's latched state.
///
/// ```compile_fail
/// let guard = ay_sat::keep_proof_inprocessing_after_exhaustion();
/// std::thread::spawn(move || drop(guard));
/// ```
#[must_use = "the scope closes when this guard is dropped"]
#[derive(Debug)]
pub struct ProofInprocessingKeptAfterExhaustion {
    _thread_bound: PhantomData<Rc<()>>,
}

/// Open a scope in which every solver that sets a proof bookkeeping budget on
/// this thread keeps its proof-mode inprocessing controls when that budget is
/// exhausted (module documentation). Scopes nest. If their nesting count
/// overflows, the thread conservatively retains this restriction until exit.
pub fn keep_proof_inprocessing_after_exhaustion() -> ProofInprocessingKeptAfterExhaustion {
    KEEP_PROOF_INPROCESSING_DEPTH
        .with(|depth| depth.set(depth.get().and_then(|value| value.checked_add(1))));
    ProofInprocessingKeptAfterExhaustion {
        _thread_bound: PhantomData,
    }
}

impl Drop for ProofInprocessingKeptAfterExhaustion {
    fn drop(&mut self) {
        KEEP_PROOF_INPROCESSING_DEPTH
            .with(|depth| depth.set(depth.get().map(|value| value.saturating_sub(1))));
    }
}

/// Whether a [`keep_proof_inprocessing_after_exhaustion`] scope is open on
/// this thread.
pub(in crate::solver) fn proof_inprocessing_kept_after_exhaustion() -> bool {
    KEEP_PROOF_INPROCESSING_DEPTH.with(|depth| depth.get() != Some(0))
}

#[cfg(test)]
mod counter_tests;

impl Solver {
    /// Whether this solver keeps its proof-mode inprocessing controls when its
    /// proof bookkeeping budget is exhausted (module documentation).
    #[must_use]
    pub fn keeps_proof_inprocessing_after_exhaustion(&self) -> bool {
        self.cold.proof_exhaustion_keeps_proof_inprocessing
    }
}
