//! #warm-theory: thread-local flag marking that the current incremental QF_LRA
//! solve is running the warm-theory lane, so the shared persistent-theory
//! pipeline macro (`solve_incremental_theory_pipeline!`, generic over theory
//! type) reuses a theory solver persisted across check-sats instead of
//! rebuilding it from scratch every check.
//!
//! Set ONLY by `solve_lra_incremental` when the warm lane is enabled
//! (`--lra-warm-theory`). Every other caller of that macro — LIA, and the mock
//! `incremental_conflict_gate_tests` (whose `$self` is not the Executor) — leaves
//! it `false`, so their behaviour is byte-identical. Default OFF.

use std::cell::Cell;

thread_local! {
    static WARM_THEORY_ACTIVE: Cell<bool> = const { Cell::new(false) };
}

pub(crate) fn get() -> bool {
    WARM_THEORY_ACTIVE.with(|c| c.get())
}

fn set(active: bool) {
    WARM_THEORY_ACTIVE.with(|c| c.set(active));
}

/// RAII guard: sets the flag on construction, restores the previous value on
/// drop, so the warm lane cannot leak into a nested or subsequent solve.
pub(crate) struct WarmTheoryGuard(bool);

impl WarmTheoryGuard {
    pub(crate) fn new(active: bool) -> Self {
        let prev = get();
        set(active);
        WarmTheoryGuard(prev)
    }
}

impl Drop for WarmTheoryGuard {
    fn drop(&mut self) {
        set(self.0);
    }
}
