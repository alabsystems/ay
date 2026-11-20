// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground-first scheduling for quantified check-sat (QE milestone 0,
//! #qe-ground-first).
//!
//! # The defect
//!
//! A quantified check-sat reached its first decision only after the
//! instantiation pipeline had rewritten the problem: E-matching rounds, CEGQI
//! counterexample lemmas (`¬B[c̄]`, hypotheses rather than consequences),
//! guarded instances, and the fail-closed gates behind them. When the
//! refutation needs none of the query's axioms, that pipeline could still exit
//! first. Measured by the 2026-09-29 roadmap critic (section B): dropping every
//! top-level universal from the 103 quantified gap files z3 refutes makes AY
//! refute 19 of them, 16 in <= 0.08 s, while the full problems end `unknown` —
//! the AUFNIRA nasa files after 5 CEGQI ce-lemmas and 4 E-matching instances in
//! 0.02 s. z3 gets these for free: quantifiers are atoms of its search, so a
//! conflict among the other assertions arrives before any instantiation.
//!
//! # The mechanism
//!
//! Decide the query WITHOUT ITS AXIOMS: the authored roots minus every
//! top-level universal (`forall`, or the negation of an `exists`). What remains
//! is the ground part together with the goal — typically a negated `forall`,
//! which Skolemization grounds, and whose own hypotheses the ordinary pipeline
//! handles. Dropping roots only removes constraints, so an UNSAT of the rest is
//! an UNSAT of the query (monotonicity).
//!
//! The decision runs on a disposable probe — a pruned clone of the context with
//! that subset installed as its roots and the proof cycle shed — under a
//! bounded share of the remaining budget. The share is a deadline fixed when
//! the pass starts, so cloning the context counts against it, and the stop
//! watchdog raises the probe's interrupt flag when it passes. Only its UNSAT
//! is used. SAT and unknown leave this executor exactly as it was.
//!
//! # Where it runs, per posture
//!
//! * Competition shedding (`--z3-mode`): FIRST, before any preprocessing,
//!   quantifier lane or instantiation round. The posture publishes no evidence,
//!   so nothing is displaced: the probe's UNSAT is the ordinary pipeline's
//!   published verdict on a subset of the query — including that pipeline's
//!   own quantified-refutation firewall, for a goal whose hypotheses it
//!   instantiated — so it is returned directly and the ordinary
//!   `CompetitionRaw` admission authenticates the query scope.
//! * Every other posture: LAST, as a fallback, only once the ordinary pipeline
//!   — every re-solve and last resort in `check_sat_guarded` included — has
//!   answered `unknown`, and only on the last stack of a definitional-adoption
//!   fallback chain. A query the pipeline decides therefore keeps exactly the
//!   verdict and the evidence it had without this pass. Measured on the
//!   2026-09-30 verification (report
//!   the development design notes at `9598c4206`): running first in this posture
//!   replaced carcara-valid certificates with documents carcara rejects.
//!
//! # Publication in the fallback slot
//!
//! First the ordinary proof of the remainder (`ground_first/publication.rs`):
//! a same-context probe refutes exactly those authored roots through the whole
//! pipeline, and its strict-complete proof is installed — together with the
//! source-syntax spellings the probe recorded for those roots — only if the
//! document it renders assumes nothing but the problem's own assertions as
//! written. Otherwise a certifying probe refutes the subset through its own
//! mandatory funnel ([`Executor::checked_exact_unsat_solve`]) and the
//! refutation is sealed as the authored-subset theorem
//! (`unsat_cert/authored_subset.rs`), which inherits that probe's admission
//! class and publishes no document. An invalid document is never the price of
//! a verdict. Explicit proof and proof-checking modes skip the pass, and so
//! does a remainder too large to certify within the pass's budget.
//!
//! # What it is not
//!
//! Not a lane: it selects no logic, recognizes no problem shape, and publishes
//! nothing the ordinary pipeline would not publish for the axiom-free part on
//! its own. It is the scheduling z3's architecture gives for free, and the
//! first milestone of the in-search quantifier engine (roadmap component QE).

use std::time::Duration;

use ay_core::time::Instant;
use ay_core::{TermData, TermId, TermStore};

use super::Executor;
use crate::ematching::contains_quantifier;
use crate::executor_types::{Result, SolveResult, Statistics, UnknownOrigin, UnknownReason};

mod publication;

/// The presolve DECISION is speculative — most remainders are satisfiable — so
/// it may take at most this fraction (1/N) of the remaining solve budget,
/// capped at [`MAX_DECISION`]. Measured on the headline sample (`--z3-mode`,
/// load 40-90): 34 of 35 refutations decided in <= 0.24 s and the slowest in
/// 1.01 s, while a 1/4 share let 23 satisfiable-or-hard remainders each burn
/// 2.5 s of a 10 s query for nothing.
const DECISION_SHARE: u32 = 10;
/// Cap on the presolve decision, context clone included.
const MAX_DECISION: Duration = Duration::from_secs(1);
/// The FALLBACK decision runs after the pipeline has given up, so the only
/// work left behind it is its own publication: a larger share, capped.
const FALLBACK_DECISION_SHARE: u32 = 3;
/// Cap on the fallback decision.
const MAX_FALLBACK_DECISION: Duration = Duration::from_secs(3);
/// PUBLICATION is the query's last work: all that remains but this 1/N (the
/// admission funnel's re-check), capped at [`MAX_PUBLICATION`]. With half,
/// P828 `t.ads_11_4` (-T:10) refuted in the fallback and published nothing.
const PUBLICATION_RESERVE_SHARE: u32 = 8;
/// Cap on publication.
const MAX_PUBLICATION: Duration = Duration::from_secs(5);
/// Below this share of budget a step does not start.
const MIN_BUDGET: Duration = Duration::from_millis(20);
/// Largest remainder a certified publication is attempted for. Certification
/// cost grows with the refutation and is not bounded by the probe's search
/// deadline; the consequence replay bounds the same certifying probe by the
/// same set size (`MAX_CONSEQUENCES`). Measured: a 596-root javafe remainder
/// decides in 0.03 s and then certifies past the whole query budget, and the
/// supervisor kills the solve. Competition shedding certifies nothing and has
/// no such bound.
const MAX_CERTIFIED_REMAINDER: usize = 256;
/// Probes that ran out of budget without a verdict, per executor, before the
/// pass stands down: an incremental script must not re-pay a subset that has
/// already proven too hard for its share (the residue rescue's rule).
const MAX_INDECISIVE_PROBES: u32 = 2;

/// Per-public-decision counters, published as `quantifier.ground_first.*`.
#[derive(Debug, Default, Clone, Copy)]
pub(in crate::executor) struct GroundFirstStats {
    /// Decisions attempted.
    probes: u64,
    /// Decisions whose probe refuted the axiom-free part.
    refuted: u64,
    /// Refutations this pass returned as the query's result.
    published: u64,
    /// Authored roots in the decided part.
    ground_roots: u64,
    /// Top-level universal axioms set aside.
    dropped_roots: u64,
    /// Wall time spent in the pass.
    seconds: f64,
}

/// Where in the check-sat the pass runs (module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Slot {
    /// Before anything else: competition shedding only.
    Presolve,
    /// After the ordinary pipeline answered `unknown`: every other posture.
    Fallback,
}

/// What the disposable probe decided about the axiom-free part.
pub(super) enum Decision {
    Unsat,
    Sat,
    /// Out of budget, stopped, refused, or an executor error.
    Indecisive,
}

/// A refuted axiom-free part, awaiting publication.
struct Refuted {
    /// The query's authored roots.
    roots: Vec<TermId>,
    /// Positions of the remainder in the authored roots.
    subset: Vec<usize>,
    /// The remainder's roots.
    remainder: Vec<TermId>,
    started: Instant,
}

/// The pipeline's `unknown` as the fallback slot found it, restored exactly
/// when the pass does not publish.
struct PipelineUnknown {
    reason: Option<UnknownReason>,
    origin: Option<UnknownOrigin>,
    statistics: Statistics,
    phase: Option<String>,
    cost_center: Option<String>,
}

impl PipelineUnknown {
    fn capture(executor: &Executor) -> Self {
        Self {
            reason: executor.last_unknown_reason,
            origin: executor.last_unknown_origin,
            statistics: executor.last_statistics.clone(),
            phase: executor.active_solve_phase.clone(),
            cost_center: executor.active_solve_cost_center.clone(),
        }
    }

    fn restore(self, executor: &mut Executor) {
        executor.last_unknown_reason = self.reason;
        executor.last_unknown_origin = self.origin;
        executor.last_statistics = self.statistics;
        executor.active_solve_phase = self.phase;
        executor.active_solve_cost_center = self.cost_center;
    }

    /// Keep the pipeline's counters beneath what publication recorded, minus
    /// the `unknown.*` attribution of the verdict this pass replaced.
    fn merge_statistics_into(self, executor: &mut Executor) {
        let published = std::mem::replace(&mut executor.last_statistics, self.statistics);
        let statistics = &mut executor.last_statistics;
        statistics
            .extra
            .retain(|name, _| !name.starts_with("unknown."));
        statistics.extra.extend(published.extra);
        executor.active_solve_phase = self.phase;
        executor.active_solve_cost_center = self.cost_center;
    }
}

/// Kill switch (`--no-ground-first`, #qe-ground-first). Off, the pass never
/// runs and the quantifier pipeline runs exactly as it did before it landed.
fn ground_first_enabled() -> bool {
    !ay_core::misc_cli_flags().no_ground_first
}

/// Whether `root` is a top-level universal axiom: a `forall`, or the negation
/// of an `exists` (the same universal, spelled dually).
pub(super) fn is_universal_axiom(terms: &TermStore, root: TermId) -> bool {
    match terms.get(root) {
        TermData::Forall(..) => true,
        TermData::Not(inner) => matches!(terms.get(*inner), TermData::Exists(..)),
        _ => false,
    }
}

impl Executor {
    /// Competition shedding: decide the current query without its top-level
    /// universal axioms before anything else runs, and return the probe's
    /// refutation (module docs).
    ///
    /// `Some` only with the result the caller returns as the check-sat's;
    /// `None` leaves every output of this executor as it was.
    pub(super) fn try_ground_first_refutation(&mut self) -> Option<Result<SolveResult>> {
        if !self.competition_shedding_active() {
            return None;
        }
        let Some(refuted) = self.ground_first_refutes(Slot::Presolve) else {
            // The check-sat continues; its own phases attribute what follows.
            self.clear_active_solve_phase();
            return None;
        };
        // The same entry the presolve exact-semantic lane takes.
        if self.prepare_check_sat_internal_state() {
            self.ground_first_stats.seconds += refuted.started.elapsed().as_secs_f64();
            self.finalize_array_ext_shadow();
            self.finalize_unknown_diagnostics();
            return Some(Ok(SolveResult::Unknown));
        }
        // The probe's verdict, admitted downstream as `CompetitionRaw`.
        self.last_unknown_reason = None;
        self.ground_first_published(&refuted);
        self.finalize_array_ext_shadow();
        self.finalize_unknown_diagnostics();
        Some(Ok(SolveResult::unsat()))
    }

    /// Every posture but competition shedding: once the ordinary pipeline has
    /// answered `unknown`, decide the query without its top-level universal
    /// axioms and publish a certified refutation of it (module docs).
    ///
    /// `Some` only with the UNSAT the caller adopts as the check-sat's result;
    /// `None` restores the pipeline's `unknown` exactly as it was recorded.
    pub(super) fn try_ground_first_fallback(&mut self) -> Option<SolveResult> {
        if self.competition_shedding_active() || self.ground_first_awaits_fallback_stack {
            return None;
        }
        let unknown = PipelineUnknown::capture(self);
        let Some(refuted) = self.ground_first_refutes(Slot::Fallback) else {
            unknown.restore(self);
            return None;
        };
        // The proof authority `begin_public_solve` froze for this query: the
        // pipeline's lanes may have left their own window provenance behind,
        // and the export of a proof over the authored roots reads it.
        let pipeline_provenance = self.proof_problem_assertion_provenance.take();
        let published = if self.prepare_check_sat_internal_state() {
            None
        } else {
            self.install_proof_source_provenance(&refuted.roots);
            let publication = self
                .current_solve_deadline()
                .map_or(MAX_PUBLICATION, |deadline| {
                    let left = deadline.saturating_duration_since(Instant::now());
                    left.saturating_sub(left / PUBLICATION_RESERVE_SHARE)
                })
                .min(MAX_PUBLICATION);
            self.ground_first_publish_certified(
                &refuted.subset,
                &refuted.remainder,
                Instant::now() + publication,
            )
        };
        let Some(result) = published else {
            self.ground_first_stats.seconds += refuted.started.elapsed().as_secs_f64();
            self.proof_problem_assertion_provenance = pipeline_provenance;
            unknown.restore(self);
            return None;
        };
        unknown.merge_statistics_into(self);
        self.ground_first_published(&refuted);
        Some(result)
    }

    /// Decide the axiom-free part of the current query in `slot`, once per
    /// public decision. `Some` only when the probe refuted it; the pass's
    /// counters are updated either way.
    fn ground_first_refutes(&mut self, slot: Slot) -> Option<Refuted> {
        if self.ground_first_spent || !self.ground_first_admissible() {
            return None;
        }
        let certified = slot == Slot::Fallback;
        // Neither publication route is open where a translated artifact is
        // demanded; do not pay for a probe whose refutation could not publish.
        if certified && self.strict_unsat_presentation_required() {
            return None;
        }
        let roots = self.plain_hard_query_roots()?.to_vec();
        let subset: Vec<usize> = (0..roots.len())
            .filter(|&position| !is_universal_axiom(&self.ctx.terms, roots[position]))
            .collect();
        let dropped = roots.len() - subset.len();
        // No axiom: the ordinary pipeline decides exactly this problem.
        // Nothing but axioms: there is no remainder to decide.
        if subset.is_empty() || dropped == 0 {
            return None;
        }
        if certified && subset.len() > MAX_CERTIFIED_REMAINDER {
            return None;
        }
        let (share, cap) = match slot {
            Slot::Presolve => (DECISION_SHARE, MAX_DECISION),
            Slot::Fallback => (FALLBACK_DECISION_SHARE, MAX_FALLBACK_DECISION),
        };
        let budget = self.ground_first_budget(share, cap)?;
        // Once per public decision: the unknown retries and nested re-entries
        // of the same decision see a remainder that has already been decided.
        self.ground_first_spent = true;

        let remainder: Vec<TermId> = subset.iter().map(|&position| roots[position]).collect();
        let started = Instant::now();
        self.ground_first_stats.probes += 1;
        self.ground_first_stats.ground_roots += remainder.len() as u64;
        self.ground_first_stats.dropped_roots += dropped as u64;
        self.set_active_solve_phase("quantifier-ground-first", "ground-first");

        match self.ground_first_decide(&remainder, started + budget) {
            Decision::Unsat => {
                self.ground_first_stats.refuted += 1;
                Some(Refuted {
                    roots,
                    subset,
                    remainder,
                    started,
                })
            }
            decision => {
                if matches!(decision, Decision::Indecisive) {
                    self.ground_first_indecisive = self.ground_first_indecisive.saturating_add(1);
                }
                self.ground_first_stats.seconds += started.elapsed().as_secs_f64();
                None
            }
        }
    }

    /// Record that the pass's refutation is this check-sat's result.
    fn ground_first_published(&mut self, refuted: &Refuted) {
        self.ground_first_stats.seconds += refuted.started.elapsed().as_secs_f64();
        self.ground_first_stats.published += 1;
        // The verdict every solve exit records for its consumers (the API's
        // model accessors read it); the sealed route's emit already did.
        self.last_result = Some(SolveResult::unsat());
        // The nested-array quarantine withholds an UNSAT whose refutation MAY
        // rest on the distrusted nested-array theory combination without one
        // of its checked authorities. This refutation is not the outer
        // solve's: it is the probe's, and every probe here decided its roots
        // through `check_sat`, whose `check_sat_with_authority` applies that
        // same quarantine to exactly the obligation refuted — with the
        // authorities it accepts, or trivially when the obligation holds no
        // nested array (the justification registry's argument for this
        // consume-once marker, `quantifier_loop/result_mapping/justification.rs`).
        // A subset refutation admitted there needs no second admission for the
        // superset it refutes.
        self.nested_array_free_justification_unsat = true;
        self.publish_ground_first_statistics();
    }

    /// The pass applies to a plain public decision: no unsat-core or
    /// unsat-assumption request (a published refutation must then name its
    /// core, which this pass does not compute), no objective or soft
    /// constraint, not inside a nested validation probe, and not after the
    /// executor's indecisive-probe allowance is spent. Assumptions and
    /// solver-declared extensions are excluded by
    /// [`Executor::plain_hard_query_roots`].
    fn ground_first_admissible(&self) -> bool {
        ground_first_enabled()
            && self.ground_first_indecisive < MAX_INDECISIVE_PROBES
            && !self.in_alternation_validation
            && !self.in_nested_array_residue_probe
            && !self.produce_unsat_cores_enabled()
            && !matches!(
                self.ctx.get_option("produce-unsat-assumptions"),
                Some(ay_frontend::OptionValue::Bool(true))
            )
            && self.ctx.objectives().is_empty()
            && self.ctx.soft_constraints().is_empty()
    }

    /// `share`-th of the remaining solve budget, capped at `cap` (`cap` alone
    /// when no deadline is installed); `None` below `MIN_BUDGET`.
    fn ground_first_budget(&self, share: u32, cap: Duration) -> Option<Duration> {
        let budget = match self.current_solve_deadline() {
            Some(deadline) => (deadline.saturating_duration_since(Instant::now()) / share).min(cap),
            None => cap,
        };
        (budget >= MIN_BUDGET).then_some(budget)
    }

    /// Decide `remainder` on a disposable executor over a pruned clone of the
    /// context, by `deadline`. Nothing the probe computes crosses back except
    /// its verdict.
    ///
    /// `deadline` was fixed when the pass started and is the probe's own solve
    /// deadline, so the clone is paid from the same cap as the search: a probe
    /// that would start with less than [`MIN_BUDGET`] left does not start.
    ///
    /// The probe sheds the proof cycle: its answer only selects whether this
    /// executor publishes, and a publication that needs evidence obtains it
    /// from a certifying probe of its own.
    pub(super) fn ground_first_decide(
        &mut self,
        remainder: &[TermId],
        deadline: Instant,
    ) -> Decision {
        if self.should_abort_theory_loop() || !self.qpf_probe_preflight() {
            return Decision::Indecisive;
        }
        let Some(probe_ctx) = self.pruned_isolated_probe_context(remainder) else {
            return Decision::Indecisive;
        };
        let left = deadline.saturating_duration_since(Instant::now());
        if left < MIN_BUDGET {
            return Decision::Indecisive;
        }
        let mut probe = self.qpf_probe_executor(probe_ctx, duration_ms(left));
        probe.original_problem_had_quantifiers = remainder
            .iter()
            .any(|&root| contains_quantifier(&self.ctx.terms, root));
        probe.incremental_mode = false;
        probe.set_self_check(false);
        probe.set_competition_mode(true);
        probe.begin_public_solve(false);
        probe.bind_unsat_query_assumptions(&[]);
        // The cap is enforced by the executor's stop watchdog as well as by
        // the deadline: the watchdog raises the probe's interrupt flag the
        // moment the cap passes. Measured on the five slowest non-refuting
        // probes of the verification sweep (`--z3-mode`, cap 1 s): 1.36-4.36 s
        // with the deadline alone, 1.00-1.67 s with the watchdog. What remains
        // is a SAT search's own polling interval (a 455,717-variable FP
        // bit-blast answers the flag up to 0.7 s late).
        let raw = probe.with_interruptible_publication_controls(
            move || Instant::now() >= deadline,
            Executor::check_sat,
        );
        drop(probe);
        if self.should_abort_theory_loop() {
            return Decision::Indecisive;
        }
        match raw {
            Ok(SolveResult::Unsat(_)) => Decision::Unsat,
            Ok(SolveResult::Sat) => Decision::Sat,
            Ok(SolveResult::Unknown) | Err(_) => Decision::Indecisive,
        }
    }

    /// Publish the per-decision counters (see [`GroundFirstStats`]).
    pub(in crate::executor) fn publish_ground_first_statistics(&mut self) {
        let stats = self.ground_first_stats;
        if stats.probes == 0 {
            return;
        }
        let statistics = &mut self.last_statistics;
        statistics.set_int("quantifier.ground_first.probes", stats.probes);
        statistics.set_int("quantifier.ground_first.refuted", stats.refuted);
        statistics.set_int("quantifier.ground_first.published", stats.published);
        statistics.set_int("quantifier.ground_first.ground_roots", stats.ground_roots);
        statistics.set_int("quantifier.ground_first.dropped_roots", stats.dropped_roots);
        statistics.set_float("time.quantifier.ground_first_seconds", stats.seconds);
    }
}

fn duration_ms(duration: Duration) -> u64 {
    u64::try_from(duration.as_millis())
        .unwrap_or(u64::MAX)
        .max(1)
}

#[cfg(test)]
#[path = "ground_first_tests.rs"]
mod tests;
