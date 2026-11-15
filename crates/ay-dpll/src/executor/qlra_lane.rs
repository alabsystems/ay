// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Executor glue for the nested-CEGQI quantified-LRA lane
//! (#qlra-nested-cegqi, plan milestone M1).
//!
//! PROBE, NOT PRE-EMPT. The lane runs after the quantified preprocessing
//! passes (vacuity, deep-QE candidates, the QE alternation route) and before
//! the closed-universal precheck and `process_quantifiers`. It answers only
//! when a publication route
//! independently re-derives its result; on every other outcome it returns
//! `None` with `ctx.assertions` untouched and the legacy quantifier path runs.
//!
//! SHARED STATE A DECLINING LANE TOUCHES (exhaustive; audited against the
//! #qlra-nested-cegqi review):
//!
//! * the term store (Risk R11): a declined pass ROLLS BACK every term it
//!   minted (`rollback.rs`, the #dt-lazy-isolation discipline), so the
//!   legacy path's whole-store scans never see lane scaffolding. The store is
//!   kept only when a holder may reference those terms: after the SAT route's
//!   in-place solve, after an installed-but-unpublished proof, or when a
//!   checked holder (proof tracker, quantifier manager, store stamp) moved.
//!   A rollback also restores the array-default sidecars and the thread-local
//!   LIA probe hint, and clears the eval memo and store-indexed caches;
//! * the consequence replay's per-query ATTEMPT ledger
//!   (`consequence_replay_attempts`, `consequence_replay_direct_state`):
//!   consumed by the UNSAT route's replay call and RESTORED on decline, so the
//!   legacy replay keeps its full `MAX_REPLAY_ATTEMPTS` (before the restore,
//!   the first pass plus the memo retry exhausted it and a base-`unsat`
//!   problem published `unknown`);
//! * two query-wide WALL envelopes, NOT restored because they must bound
//!   every scope's cumulative spend: the consequence-replay probe envelope
//!   (UNSAT route) and the quantified-gate probe envelope (SAT route). Both
//!   are net-refunded, so only wall actually spent is withheld;
//!   `qlra.replay_probe_ms` (net grant) and `qlra.gate_ms` (arm wall, an
//!   upper bound) report it;
//! * the SAT route's one in-place `solve_for_category(QfLra)` of
//!   `ground ∧ Γ`: it rewrites the per-solve outcome fields (result, proof,
//!   model sidecars, solver statistics) exactly as a legacy refinement round
//!   does; a decline clears `last_model`/`last_model_validated` and restores
//!   `last_unknown_reason`; the legacy path's own solves rewrite the rest,
//!   and anything left over could only reach publication through the
//!   authored-scope strict proof gate or the quantified model gate;
//! * wall time: at most the lane deadline (4/5 of the remaining budget, with
//!   a max(1 s, 15%) reserve) plus the publication attempt, per pass; an
//!   internal retry after a rolled-back VERDICT re-runs the search (a
//!   declined search is never re-run);
//! * `last_statistics` gains `qlra.*` keys.
//!
//! PUBLICATION (M1 with no new proof code; M3a adds one PRODUCER).
//!
//! * Nested UNSAT (M3a; the nested search is on unless `--no-qlra-nested`): only through the expansion
//!   certificate (`nested_publish.rs`, `proof/authored_expansion_certificate.rs`)
//!   installed through the same strict boundary. With the nested search on, a
//!   depth-1 UNSAT the replay below could not certify gets the same route.
//! * UNSAT: the logged instances become `ForallInstantiationProvenance`
//!   records (plus `NegatedExistsDual` sources for authored `(not (exists
//!   ...))` roots and `SkolemInstanceRecord`s for Skolemized `exists` roots)
//!   handed to the authored consequence replay. That producer re-solves the
//!   consequence set on a disposable probe, stitches it onto authored-scope
//!   `forall_inst`/`qnt_neg_exists`/`sko_ex` derivations, and installs it only
//!   through the strict installation boundary. The mandatory certification
//!   mint re-checks it before publication.
//! * SAT: one in-place ground solve of `ground ∧ Γ` installs a candidate
//!   model; the quantified model gate (universal-prefix route: a checked
//!   `pins ∧ ¬matrix[sk⃗]` UNSAT) must confirm every authored quantified
//!   conjunct. The lane asks the gate BEFORE answering so a refusal falls back
//!   to the legacy path instead of losing its verdict; the ordinary SAT
//!   emission then runs the same gate again.
//! * Nested SAT (M3b): the same gate on a model of the
//!   search's final main query, with the instance log installed as UNTRUSTED
//!   expansion hints (`hints.rs`) for the gate's confirm-only expansion
//!   route (`model/independent_gate/expansion_route.rs`).
//!
//! The lane never conjoins a counterexample formula into `ctx.assertions`,
//! never sets `quantified_proof_translation_incomplete`, never pushes
//! support axioms, and records no `entailed_forall` authority.

mod hints;
mod hints_origin;
mod incremental;
mod nested;
mod nested_presentation;
mod nested_publish;
mod probe_oracle;
mod publish;
mod recognize;
mod rollback;

pub(in crate::executor) use rollback::QlraLaneEntry;

#[cfg(test)]
mod nested_tests;
#[cfg(test)]
mod tests;

use ay_core::time::Instant;
use ay_core::TermId;
use std::time::Duration;

use super::Executor;
use crate::cegqi::lra_nested::{
    self, caps::M1_PUBLISHABLE_INSTANCES, InstanceLog, QlraOutcome, QlraTree,
};
use crate::executor_types::{Result, SolveResult, StatValue};

/// Lane share of the remaining wall budget.
const LANE_SHARE_NUM: u32 = 4;
const LANE_SHARE_DEN: u32 = 5;
/// Budget used when the query has no deadline at all.
const NO_DEADLINE_LANE_BUDGET: Duration = Duration::from_secs(10);
/// Reserve left for certification and gating: max(1 s, 15% of remaining).
const MIN_RESERVE: Duration = Duration::from_secs(1);

fn stat_label(outcome: &QlraOutcome) -> &'static str {
    match outcome {
        QlraOutcome::Unsat => "unsat",
        QlraOutcome::Sat => "sat",
        QlraOutcome::Decline(_) => "decline",
    }
}

/// The lane's per-executor state.
#[derive(Default)]
pub(in crate::executor) struct QlraLaneState {
    /// This public solve's search (see [`QlraLaneMemo`]); cleared by
    /// `begin_public_solve`.
    pub(in crate::executor) memo: Option<Box<QlraLaneMemo>>,
    /// A nested UNSAT whose pass KEPT its terms (see
    /// [`nested_publish::NestedUnsatLog`]): the `expansion_cert` leg of the
    /// quantified-UNSAT firewall may still build its certificate. Cleared by
    /// `begin_public_solve` and by every rollback.
    pub(in crate::executor) unsat_log: Option<Box<nested_publish::NestedUnsatLog>>,
    /// This executor is a disposable probe (`qpf_probe_executor`) or a
    /// derived re-decision (`new_derived_query_executor`): the nested search
    /// does not run in it. Its verdict is about
    /// the AUTHORED problem; re-running it on every internal probe's derived
    /// query would spend that query's budget for nothing.
    pub(in crate::executor) nested_inert: bool,
    /// Standalone QF_LRA solves of this executor build their `LraSolver` with
    /// implied-bounds derivation off (`LraSolver::set_no_implied_bounds`).
    /// Set only on the nested search's oracle probes, whose counterexample
    /// queries are wide disjunctions over a few variables; default off.
    pub(in crate::executor) probe_lra_no_implied_bounds: bool,
    /// The nested SAT route's per-root instance hints for the quantified
    /// model gate's expansion route (`hints.rs`); untrusted data bound to
    /// the query epoch, roots and store prefix. Cleared by
    /// `begin_public_solve` and by every lane rollback.
    pub(in crate::executor) expansion_hints: Option<Box<super::expansion::ExpansionHints>>,
    /// M4: what the nested search learned per quantifier node, kept across
    /// the check-sats of a session (`cegqi/lra_nested/session.rs`). Bound to
    /// the store snapshot it was written at; NOT cleared per public solve.
    pub(in crate::executor) session: lra_nested::session::NestedSessionCache,
    /// M4: this `check_sat_internal` pass is the incremental `Unknown`
    /// fallback (`incremental.rs`): the lane is admissible under
    /// `incremental_mode` and is the only quantified procedure the pass runs.
    pub(in crate::executor) incremental_retry: bool,
}

/// One public solve's lane run: the search result and its statistics.
///
/// Internal retries of the same public check-sat (the quantified-trace and
/// deep-QE `Unknown` retries) re-enter the hook. Under competition shedding
/// the first pass has no proof tracker and the consequence replay declines,
/// while the trace-armed retry can certify the very same refutation, so a
/// retry re-attempts publication. A declined search is final. Cleared by
/// `begin_public_solve`.
pub(in crate::executor) struct QlraLaneMemo {
    roots: Vec<TermId>,
    stats: Vec<(String, StatValue)>,
    /// A search whose terms are still LIVE in the store (the pass kept
    /// them): a retry publishes from it directly.
    search: Option<LaneSearch>,
    /// The search reached a verdict but its declining pass rolled its terms
    /// back (`rollback.rs`): a retry re-runs it. The search is deterministic
    /// in the authored roots.
    rerun: bool,
}

/// A lane search result.
enum LaneSearch {
    /// M1: the depth-1 tree, its instance log and the search outcome.
    Depth1(QlraTree, InstanceLog, QlraOutcome),
    /// M2/M3 (unless `--no-qlra-nested`): the nested search's result. A `Sat`
    /// publishes only through the SAT route's model gate (its tree and
    /// instance log installed as untrusted expansion hints, `hints.rs`,
    /// M3b), an `Unsat` only through its expansion certificate
    /// (`nested_publish.rs`, M3a).
    Nested(Box<nested::NestedSearch>),
}

impl Executor {
    /// Whether this solve may run the lane at all.
    fn qlra_lane_admissible(&self) -> bool {
        crate::quant_unit_authority::qlra_cegqi_enabled()
            && (!self.incremental_mode || self.qlra_lane.incremental_retry)
            && !self.in_alternation_validation
            && !self.in_quantified_model_gate
            && !self.in_closed_universal_precheck
            && self.last_assumptions.as_ref().is_none_or(Vec::is_empty)
    }

    /// Why the public query is NOT exactly the authored scope the lane
    /// decides, or `None` when it is. The lane solves and certifies the
    /// authored roots only, so it must not answer a query that differs:
    ///
    /// * objectives or soft constraints: the optimizer drives its own
    ///   bound/relaxation probes and consumes their models (M1 is plain
    ///   `check-sat`; `maxsmt_oll_quantified_hard_falls_back` lost its `sat`
    ///   when the lane answered a MaxSMT probe);
    /// * the check's query window (`independent_gate_authored_assertions`,
    ///   captured at `check_sat_internal` entry) is not the authored scope as
    ///   a set: a MaxSMT relaxation clause `(or soft relax)`, an optimization
    ///   bound or any other transient hard root is outside it. A lane `sat`
    ///   of the weaker authored set is no model of that query (the gate
    ///   withholds it: `unknown`), and a window narrower than the authored
    ///   scope would make a lane `unsat` wrong.
    pub(in crate::executor) fn qlra_query_is_not_authored_scope(
        &self,
        roots: &[TermId],
    ) -> Option<&'static str> {
        if !self.ctx.objectives().is_empty() || !self.ctx.soft_constraints().is_empty() {
            return Some("optimization-query");
        }
        let Some(window) = self.independent_gate_authored_assertions.as_deref() else {
            return Some("no-query-window");
        };
        let authored: ay_core::kani_compat::DetHashSet<TermId> = roots.iter().copied().collect();
        let query: ay_core::kani_compat::DetHashSet<TermId> = window.iter().copied().collect();
        (authored != query).then_some("query-window-not-authored")
    }

    /// The lane's own deadline: min(outer, now + 4/5·remaining), keeping a
    /// reserve of max(1 s, 15%) for certificate and gate work.
    fn qlra_lane_deadline(&self) -> Instant {
        let now = Instant::now();
        let Some(outer) = self.solve_deadline.get() else {
            return now + NO_DEADLINE_LANE_BUDGET;
        };
        let remaining = outer.saturating_duration_since(now);
        let share = remaining * LANE_SHARE_NUM / LANE_SHARE_DEN;
        let reserve = (remaining * 3 / 20).max(MIN_RESERVE);
        let mut budget = share.min(remaining.saturating_sub(reserve));
        if self.qlra_lane.incremental_retry {
            // An incremental session's deadline is the whole script's; one
            // fallback search must not spend the later check-sats' share.
            budget = budget.min(incremental::INCREMENTAL_LANE_BUDGET);
        }
        now + budget
    }

    /// Run the lane. `Some(result)` is a published verdict; `None` hands the
    /// query back to the legacy path with the assertion window untouched and,
    /// whenever no holder kept them, the pass's scratch terms rolled back.
    pub(in crate::executor) fn try_qlra_lane(&mut self) -> Option<Result<SolveResult>> {
        if !self.qlra_lane_admissible() {
            return None;
        }
        let roots = self.exact_concrete_authored_scope();
        if let Some(reason) = self.qlra_query_is_not_authored_scope(&roots) {
            self.last_statistics.set_string("qlra.inert", reason);
            return None;
        }
        let live = match self.qlra_lane.memo.take() {
            Some(memo) if memo.roots == roots => {
                for (key, value) in memo.stats.clone() {
                    self.last_statistics.extra.insert(key, value);
                }
                self.last_statistics.set_int("qlra.retry", 1);
                if memo.search.is_none() && !memo.rerun {
                    // A declined search: nothing to publish or re-run.
                    self.qlra_lane.memo = Some(memo);
                    return None;
                }
                memo.search
            }
            _ => {
                if roots.is_empty()
                    || !self.qpf_probe_preflight()
                    || !recognize::qlra_problem_shape(&self.ctx.terms, &roots)
                {
                    return None;
                }
                None
            }
        };
        // A fresh search mints scratch terms: open the rollback bracket.
        let (search, entry) = match live {
            Some(search) => (Some(search), None),
            None => {
                let entry = self.qlra_lane_entry();
                (self.qlra_lane_search(&roots), Some(entry))
            }
        };
        let mut search = search;
        let (published, rollback_allowed) = self.qlra_lane_publish(&roots, &mut search);
        let rerun = self.qlra_lane_settle(&roots, &mut search, &published, rollback_allowed, entry);
        tracing::debug!(
            target: "ay::qlra",
            "lane: published={} decline={:?} cert={:?} gate={:?} rollback={:?}",
            published.is_some(),
            self.last_statistics.get_string("qlra.decline"),
            self.last_statistics.get_string("qlra.cert"),
            self.last_statistics.get_string("qlra.gate"),
            self.last_statistics.get_string("qlra.rollback"),
        );
        let stats = self.qlra_lane_statistics();
        self.qlra_lane.memo = Some(Box::new(QlraLaneMemo {
            roots,
            stats,
            search,
            rerun,
        }));
        published
    }

    /// Publication attempt for a search result: the pass's answer and
    /// whether its scratch terms may be rolled back.
    fn qlra_lane_publish(
        &mut self,
        roots: &[TermId],
        search: &mut Option<LaneSearch>,
    ) -> (Option<Result<SolveResult>>, bool) {
        let (published, rollback_allowed) = match search {
            Some(LaneSearch::Depth1(tree, log, QlraOutcome::Unsat)) => {
                let (published, installed) = self.qlra_publish_unsat(tree, log);
                (published, !installed)
            }
            // The SAT route's in-place ground solve leaves TermId-bearing
            // solver state behind: never roll back after it.
            Some(LaneSearch::Depth1(tree, log, QlraOutcome::Sat)) => {
                (self.qlra_publish_sat(tree, log), false)
            }
            Some(LaneSearch::Nested(nested)) => match nested.outcome {
                QlraOutcome::Sat => {
                    let source = hints::HintSource {
                        tree: &nested.tree,
                        gamma: &nested.gamma,
                    };
                    let main = nested.main.clone();
                    let published = self.qlra_publish_sat_working(main, Some((roots, &source)));
                    (published, false)
                }
                QlraOutcome::Unsat => {
                    let (published, keep) = self.qlra_publish_nested_unsat(roots, nested);
                    (published, !keep)
                }
                QlraOutcome::Decline(_) => (None, true),
            },
            _ => (None, true),
        };
        if published.is_none()
            && rollback_allowed
            && matches!(search, Some(LaneSearch::Depth1(_, _, QlraOutcome::Unsat)))
        {
            if let Some(fallback) = self.qlra_depth1_expansion_fallback(roots, search) {
                return fallback;
            }
        }
        (published, rollback_allowed)
    }

    /// Settle the pass: decide which search the memo keeps, roll an
    /// unpublished pass back when no holder kept its terms, and hand a live
    /// nested UNSAT to the firewall's `expansion_cert` leg. Returns whether a
    /// retry must re-run the (rolled-back) search.
    ///
    /// A nested SAT is final: its shadow verdict is recorded and re-gating
    /// it on an internal retry buys nothing. A nested UNSAT that did not
    /// publish is kept like a depth-1 one: under competition shedding the
    /// first pass's strict check has no complete authored problem scope, and
    /// the trace-armed retry installs the certificate the first pass parked
    /// (or, when the pass was rolled back, re-runs the search).
    fn qlra_lane_settle(
        &mut self,
        roots: &[TermId],
        search: &mut Option<LaneSearch>,
        published: &Option<Result<SolveResult>>,
        rollback_allowed: bool,
        entry: Option<QlraLaneEntry>,
    ) -> bool {
        let definite = matches!(
            published,
            Some(Ok(SolveResult::Sat | SolveResult::Unsat(_)))
        );
        // M4: recorded below unless the pass rolls its terms back.
        let learned = match search {
            Some(LaneSearch::Nested(nested)) => Some(nested.clone()),
            _ => None,
        };
        if let Some(LaneSearch::Nested(nested)) = search {
            if definite || !matches!(nested.outcome, QlraOutcome::Unsat) {
                *search = None;
            }
        }
        let mut rerun = false;
        let mut rolled_back = false;
        if let (None, true, Some(entry)) = (published, rollback_allowed, entry) {
            rolled_back = self.qlra_lane_roll_back(entry, "qlra.rollback");
            if rolled_back {
                rerun = match search {
                    Some(LaneSearch::Depth1(_, _, outcome)) => {
                        matches!(outcome, QlraOutcome::Unsat | QlraOutcome::Sat)
                    }
                    // Only an UNSAT nested search survives to here.
                    Some(LaneSearch::Nested(_)) => true,
                    None => false,
                };
                *search = None;
            }
        }
        if let (false, Some(learned)) = (rolled_back, learned) {
            self.qlra_session_record(&learned);
        }
        self.qlra_lane.unsat_log = match search {
            Some(LaneSearch::Nested(nested)) => {
                Some(Box::new(nested_publish::NestedUnsatLog::new(
                    roots.to_vec(),
                    (**nested).clone(),
                    self.ctx.terms.snapshot_stamp(),
                )))
            }
            _ => None,
        };
        rerun
    }

    /// Recognized problem: build the tree and run the search. `None` when
    /// the tree builder declined the shape.
    fn qlra_lane_search(&mut self, roots: &[TermId]) -> Option<LaneSearch> {
        let started = Instant::now();
        self.last_statistics.set_int("qlra.recognized", 1);
        let search = match lra_nested::build_depth1_tree(&mut self.ctx.terms, roots) {
            Ok(tree) => {
                self.last_statistics
                    .set_int("qlra.nodes", tree.nodes.len() as u64);
                self.last_statistics.set_int("qlra.max_depth", 1);
                let deadline = self.qlra_lane_deadline();
                let (outcome, log, stats) = {
                    let mut host = probe_oracle::ExecutorQlraHost::new(self, deadline);
                    lra_nested::solve_depth1(&mut host, &tree, M1_PUBLISHABLE_INSTANCES)
                };
                let extra = &mut self.last_statistics;
                extra.set_int("qlra.rounds", stats.rounds as u64);
                extra.set_int("qlra.oracle_calls", stats.oracle_calls as u64);
                extra.set_int("qlra.instances", log.len() as u64);
                extra.set_string("qlra.shadow_verdict", stat_label(&outcome));
                if let QlraOutcome::Decline(decline) = outcome {
                    extra.set_string("qlra.decline", decline.label());
                }
                Some(LaneSearch::Depth1(tree, log, outcome))
            }
            Err(decline)
                if crate::quant_unit_authority::qlra_nested_enabled()
                    && !self.qlra_lane.nested_inert =>
            {
                self.last_statistics
                    .set_string("qlra.depth1_decline", format!("shape-{decline:?}"));
                self.qlra_nested_search(roots)
            }
            Err(decline) => {
                self.last_statistics
                    .set_string("qlra.decline", format!("shape-{decline:?}"));
                None
            }
        };
        let seconds = Instant::now()
            .saturating_duration_since(started)
            .as_secs_f64();
        let previous = match self.last_statistics.extra.get("qlra.seconds") {
            Some(StatValue::Float(previous)) => *previous,
            _ => 0.0,
        };
        self.last_statistics
            .set_float("qlra.seconds", previous + seconds);
        search
    }

    /// This pass's `qlra.*` statistics, for internal retries.
    fn qlra_lane_statistics(&self) -> Vec<(String, StatValue)> {
        self.last_statistics
            .extra
            .iter()
            .filter(|(key, _)| key.starts_with("qlra."))
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect()
    }
}

/// Distinct terms of `a` followed by those of `b` not already present.
fn concat_distinct(a: &[TermId], b: &[TermId]) -> Vec<TermId> {
    let mut out = a.to_vec();
    for &term in b {
        if !out.contains(&term) {
            out.push(term);
        }
    }
    out
}
