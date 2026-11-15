// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared utility helpers for CHC engines.

use crate::engine_config::ChcEngineConfig;
use crate::smt::{SmtContext, SmtResult};
use crate::ChcExpr;
use ay_core::time::Instant;
use std::time::Duration;

/// Run a single SMT satisfiability query with a timeout.
///
/// Engine-side helper (IMC, DAR, PDKind, interpolation): Search lane (Rung 0).
///
/// INV-S2 (#horn-smt-session §7.2): this helper also serves the Craig
/// validation of interpolants (`interpolation_cascade`, `interpolant_command`,
/// `farkas/interpolant`), so it is pinned off the `HornSmt` session. A fresh
/// context per call would gain nothing from a session anyway (Rung 4 wires
/// the persistent engine contexts).
#[inline]
pub(crate) fn check_sat_with_timeout(constraint: &ChcExpr, timeout: Duration) -> SmtResult {
    let _verification_pin = crate::smt::lane::ScopedVerificationMode::install();
    let mut smt = SmtContext::new_search();
    smt.check_sat_with_timeout(constraint, timeout)
}

thread_local! {
    /// Rung 4: this thread's persistent `Search`-lane context for
    /// [`search_check_sat_with_timeout`] (its `HornSmt` session survives
    /// `reset()`). Engine threads are per-engine in the portfolio; a thread
    /// that runs several engines shares one session, which is sound — a
    /// session query activates exactly its own conjuncts.
    static SEARCH_SMT: std::cell::RefCell<Option<SmtContext>> =
        const { std::cell::RefCell::new(None) };
}

/// Engine SEARCH query with a timeout (IMC / DAR / PDKind search sites;
/// #horn-smt-session Rung 4). With the session off, or for a query no session
/// theory can take, this is exactly [`check_sat_with_timeout`] minus the pin:
/// a fresh `Search`-lane context per call. With `--chc-session` >= 1 an
/// eligible query runs on this thread's persistent `Search` context, so its
/// session answers it (the legacy bridge runs on fall-through, on a reset
/// context).
///
/// NEVER for a Craig check, an invariant validation, or any other check whose
/// answer is published — those use the pinned [`check_sat_with_timeout`]
/// (INV-S2). A live `ScopedVerificationMode` on the thread closes the gate
/// here too.
pub(crate) fn search_check_sat_with_timeout(constraint: &ChcExpr, timeout: Duration) -> SmtResult {
    // Session off, or a query the session cannot take (Int, arrays, ...):
    // exactly the legacy fresh context, so those queries behave as before.
    if crate::smt::lane::session_mode() == 0
        || !crate::smt::session::shim::session_eligible(constraint)
    {
        let mut smt = SmtContext::new_search();
        return smt.check_sat_with_timeout(constraint, timeout);
    }
    // Take the context out for the duration of the call: a re-entrant call
    // (none today) gets a fresh context instead of a `RefCell` panic.
    let mut smt = SEARCH_SMT
        .with(|c| c.borrow_mut().take())
        .unwrap_or_else(SmtContext::new_search);
    smt.reset();
    let result = smt.check_sat_with_timeout(constraint, timeout);
    SEARCH_SMT.with(|c| *c.borrow_mut() = Some(smt));
    result
}

/// `true` when this thread's persistent search context holds a `HornSmt`
/// session (tests).
#[cfg(test)]
pub(crate) fn thread_search_smt_has_session() -> bool {
    SEARCH_SMT.with(|c| c.borrow().as_ref().is_some_and(SmtContext::has_session))
}

/// Returns true when engine execution should stop due to cancellation or timeout.
#[inline]
pub(crate) fn search_budget_exhausted(
    base_config: &ChcEngineConfig,
    start: Instant,
    total_timeout: Duration,
) -> bool {
    base_config.is_cancelled() || start.elapsed() >= total_timeout
}
