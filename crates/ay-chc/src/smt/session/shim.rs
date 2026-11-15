// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `check_conjunction` — the compatibility shim (design §2.7; owner WP-3 / C).
//!
//! Serves the ~213 stateless "one conjunction per query" call sites without
//! touching them: split, stage (eligibility for EVERY conjunct first — nothing
//! asserted for a rejected query), diff against the live set (`plan_delta`),
//! assert the delta as `Shim`-origin assertions, activate exactly the query's
//! set, check through `check_assuming_unverified` (the router verifies the
//! ORIGINAL expr with `sat_or_unknown`), then apply retention: every
//! `Shim`-origin live assertion unused for `cfg.kill_after_queries` queries is
//! unit-killed (`HornSmt::kill_assertion`), and `rebuild()` runs when
//! `should_rebuild()`.
//!
//! "Persistent set" for the shim = `Shim`-origin assertions used within the last
//! `kill_after_queries` (4) queries — in PDR that is the transition relation
//! and the current frame's lemmas; cube conjuncts die after 4 queries (or are
//! revived if the same cube recurs). `Api`-origin assertions are never killed
//! by the shim.
//!
//! # Router insertion (design §2.11) — lands AFTER the Rung 0 merge
//!
//! `chc-bridge-hygiene-2026-09` adds `SmtLane` to `SmtContext` and reshapes
//! `check_sat`'s dispatch, so the gate is NOT in `smt/check_sat/mod.rs` yet.
//! Everything it needs is exported from this file; paste the block below into
//! `SmtContext::check_sat` AFTER the three fail-closed guards (no-progress
//! breaker, term memory, bit-blast budget) and BEFORE the executor-first
//! branch, once `SmtContext` has `lane: SmtLane` and
//! `session: Option<Box<session::HornSmt>>` (preserved by `reset()`) and
//! `smt/lane.rs` (C6, WP-4) exists:
//!
//! ```ignore
//! if self.lane == SmtLane::Search && !lane::verification_mode_active() && lane::session_mode() > 0 {
//!     let mut session = self.session.take().unwrap_or_else(|| session::shim::new_session_for(self));
//!     let routed = session::shim::try_session(&mut session, self, expr, lane::session_mode());
//!     self.session = Some(session);
//!     if let Some(result) = routed { return result; }
//! }
//! ```
//!
//! `try_session` folds the context's `check_timeout` / `global_deadline` into
//! the session budget (`session_budget`), answers an expired scoped SMT
//! deadline with the legacy-identical instant `Unknown`, splits, runs
//! `check_conjuncts`, and maps `HornCheck` -> `SmtResult` (§2.11): `Sat` through
//! `sat_or_unknown` (strict evaluation of the ORIGINAL expr, INV-S3), `Unsat`
//! to `UnsatWithCore` when the query has >= 2 conjuncts (the `cnf.rs` rule)
//! else `Unsat`, `Budget` to `Unknown`, and `Unsupported | Poisoned |
//! TheoryIncomplete` to `None` in mode 1 (legacy fall-through) or `Unknown` in
//! mode 2 (harness). The `take()`/put-back keeps the borrow of `self` for
//! `sat_or_unknown` and the deadline cells disjoint from the session.

use std::sync::Arc;
use std::time::Duration;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;

use super::convert_memo::{
    eligible, split_conjuncts, ConjunctKey, ConvertMemo, Rung, TriviallyFalse,
};
use super::{
    AssertId, AssertOrigin, AssertState, BudgetKind, HornCheck, HornSmt, SessionConfig, TheoryKind,
    UnknownReason, UnsupportedKind,
};
use crate::smt::types::{Partition, SmtResult, SmtValue, UnsatCore};
use crate::smt::SmtContext;
use crate::ChcExpr;

pub(crate) struct DeltaPlan {
    /// Already live (any scope) -> activate.
    pub(crate) reuse: Vec<AssertId>,
    /// `Dead` (unit-killed) ids structurally equal to a conjunct of the query.
    /// Diagnostic: the conjunct is re-asserted as a NEW `AssertId` (the kill
    /// unit is permanent), so its expr is ALSO listed in `fresh`; the memo and
    /// the Tseitin `encoded` cache make the re-encoding a term/root-literal
    /// reuse plus one fresh activation var and one guard clause.
    pub(crate) revive: Vec<AssertId>,
    /// Encode now (fresh conjuncts and revived ones alike; deduplicated by
    /// structural key within the query).
    pub(crate) fresh: Vec<Arc<ChcExpr>>,
}

impl HornSmt {
    /// Diff the query's conjunct set against the session: a conjunct whose
    /// structural key names a LIVE assertion with an `==`-equal expr is
    /// `reuse`; otherwise it is `fresh` (and `revive` records a `Dead`
    /// assertion with the same expr, if any). Duplicates within the query
    /// collapse to one plan entry. `O(|conjuncts|)` key computations plus, on
    /// the first miss, one scan of the assertion table for the dead index.
    pub(crate) fn plan_delta(&self, conjuncts: &[Arc<ChcExpr>]) -> DeltaPlan {
        let mut plan = DeltaPlan {
            reuse: Vec::new(),
            revive: Vec::new(),
            fresh: Vec::new(),
        };
        // First conjunct seen under each key this query (within-query dedup;
        // a same-key different-expr pair — a collision — is planned twice).
        let mut seen: FxHashMap<ConjunctKey, Arc<ChcExpr>> = FxHashMap::default();
        let mut dead_by_key: Option<FxHashMap<ConjunctKey, AssertId>> = None;
        for c in conjuncts {
            let key = ConvertMemo::key_of(c);
            if seen.get(&key).is_some_and(|first| **first == **c) {
                continue;
            }
            if let Some(&id) = self.by_key().get(&key) {
                let a = self.assertion(id);
                if a.state == AssertState::Live && *a.expr == **c {
                    plan.reuse.push(id);
                    seen.insert(key, Arc::clone(c));
                    continue;
                }
            }
            let dead = dead_by_key.get_or_insert_with(|| {
                let mut m: FxHashMap<ConjunctKey, AssertId> = FxHashMap::default();
                for (i, a) in self.assertions().iter().enumerate() {
                    if a.state == AssertState::Dead {
                        m.insert(a.key, AssertId(i as u32));
                    }
                }
                m
            });
            if let Some(&id) = dead.get(&key) {
                if *self.assertion(id).expr == **c {
                    plan.revive.push(id);
                }
            }
            plan.fresh.push(Arc::clone(c));
            seen.insert(key, Arc::clone(c));
        }
        plan.reuse.sort_unstable();
        plan.reuse.dedup();
        plan
    }

    /// Compatibility shim (§2.7). Splits, stages, diffs, activates exactly the
    /// query's set, checks; `phase_seed` is the caller's `phase_seed_model`.
    ///
    /// Rung 1: the seed has no path through `check_assuming_unverified`
    /// (`BridgeParts.phase_seed` is `None`, WP-1 status report); it is accepted
    /// and ignored until the `pub(super)` seeded variant lands.
    ///
    /// A trivially false conjunction is answered `Unsat { core: [], .. }`
    /// without touching the solver (the router short-circuits it before the
    /// session; this arm serves the `Backend` harness). An all-`true`
    /// conjunction is `Sat({})` without touching the solver (`value()` is
    /// `None` afterwards; the router verifies the original expr).
    pub(crate) fn check_conjunction(
        &mut self,
        expr: &ChcExpr,
        budget: Option<Duration>,
        phase_seed: Option<&FxHashMap<String, SmtValue>>,
    ) -> HornCheck {
        let _ = phase_seed;
        match split_conjuncts(expr) {
            Err(TriviallyFalse) => {
                let stats = self.stats_mut();
                stats.queries += 1;
                stats.unsat += 1;
                HornCheck::Unsat {
                    core: Vec::new(),
                    over_approximate: false,
                }
            }
            Ok(conjuncts) => self.check_conjuncts(&conjuncts, budget),
        }
    }

    /// The shim over an already split conjunct list (shared by
    /// `check_conjunction` and the router's `try_session`, which splits once
    /// to learn the conjunct count for the `UnsatWithCore` rule).
    ///
    /// Staging commit: eligibility of EVERY conjunct is checked before anything
    /// is asserted; a conversion failure after that unit-kills the conjuncts
    /// staged by THIS query (the kill unit is permanent — the closest the
    /// solver offers to "nothing stays asserted"; killed staging entries are
    /// counted in `unit_kills`/`dead_vars` like any other kill).
    ///
    /// The rebuild check runs BEFORE staging: `check_assuming_unverified`
    /// rebuilds at its top and carries only live `Api` assertions and the
    /// recent-active set — a fresh `Shim` conjunct staged before that rebuild
    /// would come back as a `Tombstone` and the query would be
    /// `Poisoned(ScopeMismatch)`.
    pub(super) fn check_conjuncts(
        &mut self,
        conjuncts: &[Arc<ChcExpr>],
        budget: Option<Duration>,
    ) -> HornCheck {
        if self.should_rebuild() {
            self.rebuild();
        }
        if conjuncts.is_empty() {
            let stats = self.stats_mut();
            stats.queries += 1;
            stats.sat += 1;
            return HornCheck::Sat(FxHashMap::default());
        }
        // A one-shot conjunction of thousands of conjuncts (an unrolled
        // transition relation) gains nothing from a persistent session and
        // would pollute it with thousands of assertions to unit-kill; the
        // legacy bridge converts it in one pass (mode 1 falls through).
        if conjuncts.len() > self.cfg().max_query_conjuncts {
            return self.reject(UnknownReason::Unsupported(
                UnsupportedKind::ConversionBudget,
            ));
        }
        // Staging is not free (conversion + Tseitin per fresh conjunct), so
        // the query's deadline is polled while staging: a budgeted query
        // must not overrun by the staging time (WP-4 board: 5-8 s overruns
        // on 10k-40k-conjunct queries before this).
        // (Polled every 32 fresh conjuncts only: a small query always stages,
        // and `check_assuming_unverified` answers an expired deadline itself
        // after advancing the query clock — the WP-3 locks rely on that.)
        let deadline = self.effective_deadline(budget);
        let expired = || deadline.is_some_and(|d| Instant::now() >= d);

        // 2. Eligibility for EVERY conjunct first (nothing asserted otherwise).
        let kind = self.cfg().theory;
        for c in conjuncts {
            if let Err(k) = eligible(c, kind, Rung::Rung1) {
                return self.reject(UnknownReason::Unsupported(k));
            }
        }

        // 3. Delta plan; assert the fresh conjuncts as `Shim`-origin.
        let plan = self.plan_delta(conjuncts);
        let mut active: Vec<AssertId> = plan.reuse;
        let mut staged: Vec<AssertId> = Vec::new();
        for (i, c) in plan.fresh.iter().enumerate() {
            if i % 32 == 31 && expired() {
                // Staging commit: nothing of this query stays live.
                for id in staged {
                    self.kill_assertion(id);
                }
                return self.reject(UnknownReason::Budget(BudgetKind::Deadline));
            }
            let before = self.assertions().len();
            match self.assert_with_origin(c, Partition::AB, AssertOrigin::Shim) {
                Ok(id) => {
                    if id.0 as usize >= before {
                        staged.push(id);
                    }
                    active.push(id);
                }
                Err(reason) => {
                    // Staging commit: nothing of this query stays live.
                    for id in staged {
                        self.kill_assertion(id);
                    }
                    return self.reject(reason);
                }
            }
        }
        self.stats_mut().delta_conjuncts += staged.len() as u64;
        if self.should_rebuild() {
            // Pathological: the rebuild above did not clear the condition (the
            // hot set alone exceeds `rebuild_terms_after`). The rebuild at the
            // top of `check_assuming_unverified` would tombstone the staged
            // conjuncts and poison the query; refuse it as a resource Unknown.
            for id in staged {
                self.kill_assertion(id);
            }
            return self.reject(UnknownReason::Budget(BudgetKind::Memory));
        }

        // 4. Activation set = exactly the query's conjuncts.
        active.sort_unstable();
        active.dedup();

        // 5. The check (the router verifies SAT models on the ORIGINAL expr).
        let outcome = self.check_assuming_unverified(&active, &[], budget);

        // LRU stamp on every exit path (an instant-deadline exit returns
        // before the session's own stamping).
        for &id in &active {
            self.note_used(id);
        }

        // 6. Retention. (7. `should_rebuild` runs at the top of the next check.)
        self.retain_shim_assertions();
        outcome
    }

    /// A query refused before the solver was touched: counted like any other
    /// Unknown of its class (the `< 5 %` bar of the Rung-1 exit counts
    /// `unknown_unsupported`); the solver's query clock does not advance.
    fn reject(&mut self, reason: UnknownReason) -> HornCheck {
        let stats = self.stats_mut();
        stats.queries += 1;
        match reason {
            UnknownReason::Budget(_) => stats.unknown_budget += 1,
            UnknownReason::Unsupported(_) => stats.unknown_unsupported += 1,
            UnknownReason::TheoryIncomplete => stats.unknown_theory_incomplete += 1,
            UnknownReason::Poisoned(_) => stats.unknown_poisoned += 1,
        }
        HornCheck::Unknown(reason)
    }

    /// Retention step (§2.7 step 6, §6.2 item 3): every `Shim`-origin LIVE
    /// assertion unused for more than `kill_after_queries` queries is
    /// unit-killed. `Api`-origin assertions are never touched.
    fn retain_shim_assertions(&mut self) {
        let now = self.query_no();
        let kill_after = self.cfg().kill_after_queries;
        let victims: Vec<AssertId> = self
            .assertions()
            .iter()
            .enumerate()
            .filter(|(_, a)| {
                a.origin == AssertOrigin::Shim
                    && a.state == AssertState::Live
                    && now.saturating_sub(a.last_used_query) > kill_after
            })
            .map(|(i, _)| AssertId(i as u32))
            .collect();
        for id in victims {
            self.kill_assertion(id);
        }
    }
}

/// Every conjunct of `expr` passes the current rung's eligibility (Rung 1:
/// `TheoryKind::Lra`). A cheap pre-filter for Rung-4 callers that hold a
/// long-lived background; the shim re-checks every query anyway.
pub(crate) fn session_eligible(expr: &ChcExpr) -> bool {
    match split_conjuncts(expr) {
        Err(TriviallyFalse) => true,
        Ok(conjuncts) => conjuncts
            .iter()
            .all(|c| eligible(c, TheoryKind::Lra, Rung::Rung1).is_ok()),
    }
}

/// The session the router creates lazily on the first Search-lane query.
/// Rung 1 is `TheoryKind::Lra` only (eligibility rejects every Int var, so an
/// Int problem falls through to the legacy bridge on every query at the cost
/// of one feature scan); the problem's sorts pick `Lia` from Rung 2. Datatype
/// declarations are not carried (DT is not eligible).
pub(crate) fn new_session_for(_ctx: &SmtContext) -> Box<HornSmt> {
    Box::new(HornSmt::new(SessionConfig::new(TheoryKind::Lra), None))
}

/// The caller context's contribution to the session budget: `check_timeout`
/// (a per-check budget) and `global_deadline` (an absolute end time), folded to
/// one `Duration` from now. The thread-scoped deadlines are folded by the
/// session itself (§3.5).
pub(crate) fn session_budget(ctx: &SmtContext) -> Option<Duration> {
    let mut budget = ctx.check_timeout.get();
    if let Some(deadline) = ctx.global_deadline.get() {
        let remaining = deadline.saturating_duration_since(Instant::now());
        budget = Some(budget.map_or(remaining, |b| b.min(remaining)));
    }
    budget
}

/// The router body (§2.11): `None` means "not answered here — run the legacy
/// bridge". `mode` is `lane::session_mode()`: 0 off, 1 session with legacy
/// fall-through on `Unsupported | Poisoned | TheoryIncomplete`, 2 session only.
pub(crate) fn try_session(
    session: &mut HornSmt,
    ctx: &SmtContext,
    expr: &ChcExpr,
    mode: u8,
) -> Option<SmtResult> {
    if mode == 0 {
        return None;
    }
    // Legacy-identical: an expired scoped SMT deadline is an instant Unknown.
    if crate::smt::smt_deadline_expired() {
        return Some(SmtResult::Unknown);
    }
    let conjuncts = match split_conjuncts(expr) {
        // The legacy preprocessor's shape for a `false` conjunct
        // (`check_sat/preprocess.rs`): the session never sees it.
        Err(TriviallyFalse) => {
            return Some(SmtResult::UnsatWithCore(UnsatCore {
                conjuncts: vec![ChcExpr::Bool(false)],
                ..Default::default()
            }));
        }
        Ok(conjuncts) => conjuncts,
    };
    let conjunct_count = conjuncts.len();
    let budget = session_budget(ctx);
    match session.check_conjuncts(&conjuncts, budget) {
        HornCheck::Sat(model) => {
            let probe = super::session_trace().then(|| model.clone());
            let result = SmtContext::sat_or_unknown(expr, model, "horn-session");
            if let (Some(model), SmtResult::Unknown) = (probe, &result) {
                trace_router_demotion(expr, &model);
            }
            Some(result)
        }
        HornCheck::Unsat { core, .. } => {
            if conjunct_count >= 2 {
                let conjuncts: Vec<ChcExpr> = core
                    .iter()
                    .map(|&id| (*session.assertion(id).expr).clone())
                    .collect();
                Some(SmtResult::UnsatWithCore(UnsatCore {
                    conjuncts,
                    farkas_conflicts: Vec::new(),
                    diagnostics: Default::default(),
                }))
            } else {
                Some(SmtResult::Unsat)
            }
        }
        HornCheck::Unknown(UnknownReason::Budget(_)) => Some(SmtResult::Unknown),
        HornCheck::Unknown(
            UnknownReason::Unsupported(_)
            | UnknownReason::Poisoned(_)
            | UnknownReason::TheoryIncomplete,
        ) => {
            if mode >= 2 {
                Some(SmtResult::Unknown)
            } else {
                None
            }
        }
    }
}

/// `--chc-session-trace` diagnostic for a session `Sat` that the router's
/// strict evaluation of the ORIGINAL expression demoted to `Unknown`: every
/// top-level conjunct that does not evaluate `Valid`, with the model values of
/// its variables, then the whole query as an SMT-LIB script.
fn trace_router_demotion(expr: &ChcExpr, model: &FxHashMap<String, SmtValue>) {
    use crate::smt::model_verify::verify_sat_model_strict_with_mod_retry;
    use crate::smt::types::ModelVerifyResult;
    let whole = verify_sat_model_strict_with_mod_retry(expr, model);
    let mut lines = vec![format!(
        "[CHC-SESSION-DEMOTION] whole={whole:?} conjuncts={} model_vars={}",
        expr.conjuncts().len(),
        model.len()
    )];
    for (i, c) in expr.conjuncts().into_iter().enumerate() {
        let verdict = verify_sat_model_strict_with_mod_retry(c, model);
        if matches!(verdict, ModelVerifyResult::Valid) {
            continue;
        }
        let vals: Vec<String> = c
            .vars()
            .iter()
            .map(|v| match model.get(&v.name) {
                Some(x) => format!("{}={x:?}", v.name),
                None => format!("{}=MISSING", v.name),
            })
            .collect();
        let text = crate::pdr::model::InvariantModel::expr_to_smtlib(c);
        lines.push(format!(
            "[CHC-SESSION-DEMOTION]   #{i} {verdict:?} {} | {}",
            &text[..text.len().min(600)],
            vals.join(" ")
        ));
    }
    lines.push(super::dump::script_for(expr, false));
    ay_core::safe_eprintln!("{}", lines.join("\n"));
}
