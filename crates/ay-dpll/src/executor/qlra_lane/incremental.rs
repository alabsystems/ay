// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The lane in an INCREMENTAL session (#qlra-nested-cegqi milestone M4).
//!
//! WHERE IT RUNS. Neither the QSAT route nor (before M4) this lane runs under
//! `incremental_mode`, so an incremental quantified-LRA check-sat is decided
//! by the legacy quantifier path alone. In the 2025 Incremental LRA family
//! (Kopczynski LOIS) that path answers almost every query and is
//! THROUGHPUT-bound — the file the selection weighs most (`incremental4`)
//! times out after ~2,700 of 3,397 check-sats — while the lane, run first,
//! costs 0.5–3.8 s on late `incremental4` queries the legacy path decides in
//! 0.03–0.2 s (measured one-shot on extracted queries, `--no-qsat`). So the
//! lane runs on the `Unknown` FALLBACK of an incremental check-sat, after
//! every other procedure of `check_sat_guarded` (the whole `Unknown` cascade
//! of `cegar_refine_solve`, the unrewritten fallback, the model-rejection
//! re-solves and the CE-free rescue): it can only turn an `unknown` into a
//! verdict, and a query anything else answers never pays for it. (Placed
//! inside the `cegar_refine_solve` cascade instead, it ran — and was wasted —
//! on LOIS `incremental3` queries the unrewritten fallback then decided,
//! 0.8–0.9 s each.)
//!
//! HOW. The fallback runs one more primary solve (`solve_and_emit_primary`,
//! as the unrewritten fallback does) with
//! [`QlraLaneState::incremental_retry`](super::QlraLaneState) set. Its
//! `check_sat_internal` captures the epoch's authored window, sets aside the
//! persistent incremental solver state and restores it on exit exactly as
//! any quantified incremental check-sat does; the lane is the only
//! quantified procedure of that pass (a declined lane answers `unknown` at
//! once, and `cegar_refine_solve` runs no cascade behind it), and its
//! verdict goes through the ordinary UNSAT-proof and SAT-emission steps. Its search may use at most
//! [`INCREMENTAL_LANE_BUDGET`], since the session's deadline belongs to every
//! later check-sat too.
//!
//! WHEN IT STAYS INERT. Exactly where the non-incremental lane is inert: a
//! query whose window is not the authored scope (objectives, soft
//! constraints, a MaxSMT relaxation or any other transient hard root),
//! `check-sat-assuming` (not shown sound for the lane's authored-scope
//! publication), disposable probes and the gates' own sub-solves.
//!
//! PUBLICATION is unchanged: a `sat` only through the quantified model gate
//! on the authored window, an `unsat` only through the strict installation
//! boundary (consequence replay or expansion certificate).
//!
//! The session cache (`cegqi/lra_nested/session.rs`) carries each node's
//! instance log and exact flag from one check-sat's search to the next.

use std::time::Duration;

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::TermId;

use super::super::Executor;
use super::nested::NestedSearch;
use super::recognize;
use crate::ematching::contains_quantifier;
use crate::executor_types::{Result, SolveResult, UnknownReason};

/// The most one incremental fallback search may spend.
pub(in crate::executor) const INCREMENTAL_LANE_BUDGET: Duration = Duration::from_secs(5);

impl Executor {
    /// Whether an incremental `Unknown` may be retried through the lane:
    /// the lane is enabled and admissible apart from `incremental_mode`, the
    /// query window `authored` is exactly the epoch's authored scope, and
    /// that scope is a quantified LRA problem the lane recognizes.
    fn qlra_incremental_retry_applies(&self, authored: &[TermId]) -> bool {
        if !self.incremental_mode
            || self.qlra_lane.incremental_retry
            || self.qlra_lane.nested_inert
            || !crate::quant_unit_authority::qlra_cegqi_enabled()
            || self.in_alternation_validation
            || self.in_quantified_model_gate
            || self.in_closed_universal_precheck
            || !self.last_assumptions.as_ref().is_none_or(Vec::is_empty)
            || !self.ctx.objectives().is_empty()
            || !self.ctx.soft_constraints().is_empty()
        {
            return false;
        }
        let roots = self.exact_concrete_authored_scope();
        if roots.is_empty() {
            return false;
        }
        let scope: HashSet<TermId> = roots.iter().copied().collect();
        let window: HashSet<TermId> = authored.iter().copied().collect();
        scope == window
            && roots
                .iter()
                .any(|&root| contains_quantifier(&self.ctx.terms, root))
            && recognize::qlra_problem_shape(&self.ctx.terms, &roots)
    }

    /// The incremental `Unknown` fallback (see the module docs): `result` is
    /// the check's verdict after every other procedure ran. On entry
    /// `ctx.assertions` is the check's assertion window; it is restored on
    /// every exit. A retry that stays `unknown` leaves the first answer and
    /// its reason in place.
    pub(in crate::executor) fn qlra_incremental_unknown_retry(
        &mut self,
        result: SolveResult,
    ) -> Result<SolveResult> {
        if !matches!(result, SolveResult::Unknown) || !self.incremental_mode {
            return Ok(result);
        }
        let authored = self.ctx.assertions.clone();
        if !self.qlra_incremental_retry_applies(&authored)
            || self.should_abort_theory_loop()
            || !self.qpf_probe_preflight()
        {
            return Ok(result);
        }
        tracing::debug!(target: "ay::qlra", "incremental fallback: retry");
        let reason = self.last_unknown_reason;
        // A fresh primary solve, as `resolve_without_simplifier` starts one:
        // its emission gates react to this pass, not to the first.
        self.reset_public_query_solve_state();
        self.cegqi_ce_free_stash = None;
        self.last_unknown_reason = None;
        self.last_result = None;
        self.last_model = None;
        self.qlra_lane.incremental_retry = true;
        // Under competition shedding the lane certifies an `unsat` only on a
        // trace-armed pass (`nested_publish.rs`): a shed pass parks its
        // certificate for `quantified_trace_arming_unknown_retry`. That retry
        // already ran, so this pass IS the trace-armed one: borrow the same
        // posture, and latch the trace retry so the lane installs instead of
        // parking for a pass that never comes.
        let borrowed = (crate::quant_unit_authority::quantified_shedding_yield_enabled()
            && self.competition_shedding_active())
        .then(|| self.arm_quantified_trace_for_retry());
        let trace_latch = std::mem::replace(&mut self.quantified_trace_retry_armed, true);
        // Panic containment as in `deep_qe_retry_solve`: never leave the
        // pass flags armed, the posture borrowed or the window rewritten.
        let retry = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.solve_and_emit_primary()
        }));
        self.quantified_trace_retry_armed = trace_latch;
        if let Some(borrowed) = borrowed {
            self.disarm_quantified_trace_after_retry(borrowed);
        }
        self.qlra_lane.incremental_retry = false;
        self.ctx.assertions = authored;
        let retry = match retry {
            Ok(retry) => retry,
            Err(panic) => std::panic::resume_unwind(panic),
        };
        self.last_statistics.set_int("qlra.incremental_retry", 1);
        match retry {
            Ok(definite @ (SolveResult::Sat | SolveResult::Unsat(_))) => Ok(definite),
            Ok(_) => {
                self.last_unknown_reason = reason;
                Ok(result)
            }
            Err(err) => Err(err),
        }
    }

    /// Record what a nested search learned in the session cache. Only for a
    /// pass that KEPT its terms: a rolled-back pass recycled them.
    pub(super) fn qlra_session_record(&mut self, learned: &NestedSearch) {
        self.qlra_lane.session.record(
            &self.ctx.terms,
            &learned.tree,
            &learned.gamma,
            &learned.exact,
        );
        let nodes = self.qlra_lane.session.len() as u64;
        self.last_statistics.set_int("qlra.session_nodes", nodes);
    }

    /// Whether the session cache holds nodes bound to the live store
    /// (`session.rs`; tests only).
    #[cfg(test)]
    pub(crate) fn qlra_session_cache_is_live(&self) -> bool {
        self.qlra_lane.session.len() > 0 && self.qlra_lane.session.is_valid_for(&self.ctx.terms)
    }

    /// The incremental fallback pass declined: answer `unknown` without
    /// running the legacy path a second time.
    pub(in crate::executor) fn qlra_incremental_decline(&mut self) -> Result<SolveResult> {
        self.last_unknown_reason = Some(UnknownReason::Incomplete);
        Ok(SolveResult::Unknown)
    }
}
