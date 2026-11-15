// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The QSAT route (roadmap component QS): quantified check-sat for problems
//! whose whole assertion set is quantified linear `Int`/`Real` arithmetic
//! over `Bool` connectives, with no uninterpreted functions.
//!
//! The engine (`crate::qsat`) plays the prenex game on the authored roots
//! with a ground kernel (`kernel.rs`: disposable probe executors). Its
//! verdict is a HINT; publication re-derives it through strict routes:
//!
//! * `sat`: the level-0 witness pins the authored free constants; one ground
//!   solve installs that model, and the ordinary SAT emission's quantified
//!   model gate must confirm every authored quantified conjunct. For an
//!   alternation the gate's strategy route Skolemizes the conjunct with the
//!   ∃ player's strategy (installed here as data) and confirms by a checked
//!   ground refutation. A `sat` the gate refuses was not published: the
//!   query is solved once more without the route (`refused_sat.rs`).
//! * `unsat`: instances and Skolem witnesses for the authored consequence
//!   replay (`unsat.rs`, `expansion.rs`), which derives an authored-scope
//!   strict proof or declines; the proof is spelled over the problem file
//!   (`surface.rs`). In the default posture the `unsat` is published only
//!   with its complete authored Alethe document, and in the shed posture
//!   only when it meets any certificate the caller demanded (`evidence.rs`);
//!   otherwise the route declines and the legacy path decides.
//!
//! When the route PUBLISHES a verdict, the deep-QE `Unknown` retry and the
//! nested-CEGQI search do not run: the game is the decision procedure for the
//! fragment. A declined or unpublishable run hands the query to the legacy
//! path, every lane of it, with the pass's scratch terms rolled back.
//!
//! Budget: the route may use `ROUTE_SHARE` of the remaining wall budget, but a
//! single kernel query only `1/QUERY_CAP_DEN` of the route's share (or, on a
//! long deadline, all of it but `LEGACY_FLOOR`). The game
//! declines on the first undecided query, so a declined game leaves the
//! legacy path most of the deadline (a stalled ground query used to consume
//! the whole share, measured as lost verdicts the legacy path answers in
//! 0.03 s).

mod closed_terms;
mod evidence;
mod expansion;
mod kernel;
mod refused_sat;
mod route_stats;
mod skolem;
mod surface;
mod unsat;

pub(in crate::executor) use evidence::ProofStateSnapshot;
pub(in crate::executor) use skolem::skolemize_binders;

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::time::Instant;
use ay_core::{Sort, TermId, TermStore};
use std::time::Duration;

use super::Executor;
use crate::executor_types::{Result, SolveResult, StatValue};
use crate::logic_detection::LogicCategory;
use crate::qsat::{self, Game, KernelAnswer, Outcome, QsatHost, Run, Val};

/// Route share of the remaining wall budget (the rest is the publication
/// reserve).
const ROUTE_SHARE_NUM: u32 = 4;
const ROUTE_SHARE_DEN: u32 = 5;
const NO_DEADLINE_BUDGET: Duration = Duration::from_secs(10);
const MIN_RESERVE: Duration = Duration::from_secs(1);
/// One kernel query (decision, core and confirmation) may use this fraction
/// of the route's share. A third, not a quarter: measured on the fresh
/// 300-file set at -T:10, a quarter (2 s) cut an LRA game (scholl RNDPRE_3_44)
/// whose first query needs ~1.3 s under one formulation (the plain one, in
/// the latest trace); at -T:5 a third still leaves the legacy path ~3.6 s.
const QUERY_CAP_DEN: u32 = 3;
/// On a long deadline a query may instead take the share less this much: the
/// legacy path keeps it on top of the reserve (at least 5 s in all). The
/// legacy path was measured needing up to ~3.5 s (4.4-4.8 s loaded) on the
/// files a stalled query lost, while at -T:10 the third (2.7 s) was measured
/// too little for an LRA game whose first query the plain formulation
/// decides in ~0.8 s under `--z3-mode` and only the split one, in ~1.3 s
/// after the plain one's slice, in the default posture (scholl RNDPRE_3_44).
const LEGACY_FLOOR: Duration = Duration::from_secs(4);
/// Floor of the per-query cap (never above the route's share itself).
const MIN_QUERY_CAP: Duration = Duration::from_millis(200);

/// Per-executor state of the route.
#[derive(Default)]
pub(in crate::executor) struct QsatRouteState {
    /// This public solve's authored root vector (internal retries re-enter
    /// the hook, and the game runs once), whether the route published a
    /// verdict for it, and the route's `qsat.*` statistics (an internal
    /// re-solve resets the statistics; `qsat_restore_statistics` puts the
    /// route's back). Cleared by `begin_public_solve`.
    memo: Option<QsatMemo>,
    /// The route PUBLISHED a verdict for this public solve's problem: the
    /// deep-QE `Unknown` retry and the nested-CEGQI lane stand down. A
    /// declined, refused or unpublishable game leaves it clear, so every
    /// legacy lane still runs (a game `unsat` the replay cannot carry was
    /// measured losing verdicts the deep-QE retry decides). A `sat` the
    /// emission's gate refuses clears it again (`refused_sat.rs`).
    pub(in crate::executor) applied: bool,
    /// This executor is a disposable probe: the route never runs in it.
    pub(in crate::executor) inert: bool,
    /// The ∃ player's strategy of a published `sat` run, kept for the rest
    /// of the public solve. Data for the gate's strategy route, which
    /// re-derives every obligation itself.
    pub(in crate::executor) strategy: Option<qsat::strategy::StrategyCert>,
    /// This public solve's route `sat` went to the SAT emission, whose gate
    /// decides it; taken by `qsat_refused_sat_resolve` (`refused_sat.rs`).
    sat_handed_off: bool,
    /// The kernel formulation that last decided a query (`kernel.rs`).
    prefer_split: bool,
    /// The formulation that decided the most recent kernel query (`true`:
    /// split), so a decisive answer's confirmation can try the other one.
    last_decided_split: Option<bool>,
    /// The quantified-route statistics (`qsat.*`, `qlra.*`, `eq_qe.*`) of
    /// every earlier `check_sat_internal` pass of this public solve (see
    /// [`Executor::carry_route_statistics`]). Cleared by `begin_public_solve`.
    route_stats: Vec<(String, StatValue)>,
    /// A pass of this public solve already ran, so the statistics a reset
    /// discards are this solve's own (the first pass's reset discards the
    /// previous public solve's).
    route_stats_live: bool,
}

/// See [`QsatRouteState::memo`].
struct QsatMemo {
    roots: Vec<TermId>,
    published: bool,
    stats: Vec<(String, StatValue)>,
}

impl QsatRouteState {
    pub(in crate::executor) fn begin_public_solve(&mut self) {
        self.memo = None;
        self.applied = false;
        self.strategy = None;
        self.sat_handed_off = false;
        self.route_stats.clear();
        self.route_stats_live = false;
    }
}

/// The executor-backed kernel.
struct ExecutorQsatHost<'a> {
    executor: &'a mut Executor,
    /// The route's deadline.
    deadline: Instant,
    /// The most one kernel query may take (see the module docs).
    query_cap: Duration,
    kernel_ms: u64,
}

impl ExecutorQsatHost<'_> {
    /// The deadline of a query starting now: the per-query cap, never past
    /// the route's deadline. `None` when the route's time is spent.
    fn query_deadline(&self) -> Option<Instant> {
        let now = Instant::now();
        if now >= self.deadline {
            return None;
        }
        Some((now + self.query_cap).min(self.deadline))
    }

    fn charge(&mut self, started: Instant) {
        let spent = Instant::now().saturating_duration_since(started);
        self.kernel_ms = self
            .kernel_ms
            .saturating_add(u64::try_from(spent.as_millis()).unwrap_or(u64::MAX));
    }
}

impl QsatHost for ExecutorQsatHost<'_> {
    fn terms(&mut self) -> &mut TermStore {
        &mut self.executor.ctx.terms
    }

    fn check(
        &mut self,
        formulas: &[TermId],
        assumptions: &[TermId],
        targets: &[TermId],
        want_core: bool,
    ) -> KernelAnswer {
        let Some(deadline) = self.query_deadline() else {
            return KernelAnswer::Unknown;
        };
        let started = Instant::now();
        let answer =
            self.executor
                .qsat_kernel_check(formulas, assumptions, targets, deadline, want_core);
        self.charge(started);
        answer
    }

    fn confirm_unsat(&mut self, formulas: &[TermId], targets: &[TermId]) -> bool {
        let Some(deadline) = self.query_deadline() else {
            return false;
        };
        let started = Instant::now();
        let confirmed = self
            .executor
            .qsat_kernel_confirm_unsat(formulas, targets, deadline);
        self.charge(started);
        confirmed
    }

    fn should_stop(&self) -> bool {
        Instant::now() >= self.deadline || (self.executor.make_should_stop())()
    }
}

fn outcome_label(outcome: &Outcome) -> &'static str {
    match outcome {
        Outcome::Sat => "sat",
        Outcome::Unsat => "unsat",
        Outcome::Decline(d) => d.label(),
    }
}

impl Executor {
    /// Record a route statistic.
    fn qsat_note(&mut self, key: &'static str, value: &'static str) {
        tracing::debug!(target: "ay::qsat", key, value, "route");
        self.last_statistics.set_string(key, value);
    }

    /// Whether the route may run in this executor (`--no-qsat` removes it).
    fn qsat_route_admissible(&self) -> bool {
        !ay_core::misc_cli_flags().no_qsat
            && !self.qsat_route.inert
            && !self.qlra_lane.nested_inert
            && !self.incremental_mode
            && !self.in_alternation_validation
            && !self.in_quantified_model_gate
            && !self.in_closed_universal_precheck
            && self.last_assumptions.as_ref().is_none_or(Vec::is_empty)
    }

    /// Whether the route recognized this public solve's problem.
    pub(in crate::executor) fn qsat_route_applied(&self) -> bool {
        self.qsat_route.applied
    }

    /// The route's share of the remaining wall budget.
    fn qsat_share(&self) -> Duration {
        let Some(outer) = self.solve_deadline.get() else {
            return NO_DEADLINE_BUDGET;
        };
        let remaining = outer.saturating_duration_since(Instant::now());
        let share = remaining * ROUTE_SHARE_NUM / ROUTE_SHARE_DEN;
        let reserve = (remaining * 3 / 20).max(MIN_RESERVE);
        share.min(remaining.saturating_sub(reserve))
    }

    /// The per-query cap for a route `share` (see the module docs).
    fn qsat_query_cap(share: Duration) -> Duration {
        (share / QUERY_CAP_DEN)
            .max(share.saturating_sub(LEGACY_FLOOR))
            .max(MIN_QUERY_CAP)
            .min(share)
    }

    /// The authored roots this query decides, or `None` when the route does
    /// not apply (or already ran for this public solve).
    fn qsat_route_roots(&mut self) -> Option<Vec<TermId>> {
        if !self.qsat_route_admissible() {
            return None;
        }
        let roots = self.exact_concrete_authored_scope();
        if roots.is_empty()
            || self.qlra_query_is_not_authored_scope(&roots).is_some()
            || self.qsat_roots_complementary(&roots)
        {
            return None;
        }
        if let Some(memo) = &self.qsat_route.memo {
            if memo.roots == roots {
                // An internal retry: the game already ran for this query.
                // Only a PUBLISHED verdict stands the other lanes down.
                if memo.published {
                    self.qsat_route.applied = true;
                }
                return None;
            }
        }
        if !self.qpf_probe_preflight() {
            return None;
        }
        // Direct, exactly expandable universals already have a finite ground
        // search and an authored forall-instantiation proof path. Let that
        // path handle the whole query before starting a quantified game.
        let mut finite_forall = false;
        for &root in &roots {
            if matches!(self.ctx.terms.get(root), TermData::Forall(..))
                && crate::skolemize::bounded_expansion_grounds_all_quantifiers(
                    &self.ctx.terms,
                    root,
                )
            {
                finite_forall = true;
            } else if crate::ematching::contains_quantifier(&self.ctx.terms, root) {
                return Some(roots);
            }
        }
        if finite_forall {
            self.qsat_note("qsat.decline", "exact-finite-expansion");
            return None;
        }
        Some(roots)
    }

    /// A conjunct beside its own negation is a propositional refutation the
    /// ordinary path certifies by one resolution of the two authored
    /// premises, not a game.
    fn qsat_roots_complementary(&self, roots: &[TermId]) -> bool {
        let closure = unsat::and_closure(self, roots);
        let set: HashSet<TermId> = closure.iter().copied().collect();
        closure
            .iter()
            .any(|&c| matches!(self.ctx.terms.get(c), TermData::Not(inner) if set.contains(inner)))
    }

    fn qsat_record_run(&mut self, game: &Game, run: &Run, kernel_ms: u64, started: Instant) {
        tracing::debug!(
            target: "ay::qsat",
            verdict = outcome_label(&run.outcome),
            levels = game.levels.len(),
            rounds = run.stats.rounds,
            kernel_calls = run.stats.kernel_calls,
            kernel_ms,
            lemmas_exists = run.stats.lemmas_exists,
            lemmas_forall = run.stats.lemmas_forall,
            "run"
        );
        let s = &mut self.last_statistics;
        s.set_int("qsat.levels", game.levels.len() as u64);
        s.set_int("qsat.rounds", run.stats.rounds as u64);
        s.set_int("qsat.kernel_calls", run.stats.kernel_calls as u64);
        s.set_int("qsat.kernel_ms", kernel_ms);
        s.set_int("qsat.lemmas_exists", run.stats.lemmas_exists as u64);
        s.set_int("qsat.lemmas_forall", run.stats.lemmas_forall as u64);
        s.set_string("qsat.verdict", outcome_label(&run.outcome));
        s.set_float(
            "qsat.seconds",
            Instant::now()
                .saturating_duration_since(started)
                .as_secs_f64(),
        );
    }

    /// Run the route. `Some` is a published verdict; `None` hands the query
    /// to the legacy path with the pass's scratch terms rolled back.
    pub(in crate::executor) fn try_qsat_route(&mut self) -> Option<Result<SolveResult>> {
        let roots = self.qsat_route_roots()?;
        let entry = self.qlra_lane_entry();
        let game = match qsat::build_game(&mut self.ctx.terms, &roots) {
            Ok(game) => game,
            Err(decline) => {
                tracing::debug!(target: "ay::qsat", decline = decline.label(), "shape");
                self.qlra_lane_roll_back(entry, "qsat.rollback");
                self.last_statistics
                    .set_string("qsat.decline", decline.label());
                self.qsat_route.memo = Some(QsatMemo {
                    roots,
                    published: false,
                    stats: self.qsat_statistics(),
                });
                return None;
            }
        };
        let started = Instant::now();
        let share = self.qsat_share();
        let (run, kernel_ms) = {
            let mut host = ExecutorQsatHost {
                executor: self,
                deadline: started + share,
                query_cap: Self::qsat_query_cap(share),
                kernel_ms: 0,
            };
            let run = qsat::solve(&mut host, &game, qsat::Caps::default());
            (run, host.kernel_ms)
        };
        self.qsat_record_run(&game, &run, kernel_ms, started);
        // Recorded before publication, which may re-enter the hook: the game
        // never runs twice for one query.
        self.qsat_route.memo = Some(QsatMemo {
            roots: roots.clone(),
            published: false,
            stats: self.qsat_statistics(),
        });
        let sat = matches!(run.outcome, Outcome::Sat);
        let (published, keep) = match run.outcome {
            Outcome::Sat => (self.qsat_publish_sat(&game, &run), true),
            Outcome::Unsat => self.qsat_publish_unsat(&roots, &game, &run),
            Outcome::Decline(_) => (None, false),
        };
        let applied = published.is_some();
        self.qsat_route.applied = applied;
        self.qsat_route.sat_handed_off = sat && applied;
        if published.is_none() && !keep {
            self.qlra_lane_roll_back(entry, "qsat.rollback");
        }
        self.qsat_route.memo = Some(QsatMemo {
            roots,
            published: applied,
            stats: self.qsat_statistics(),
        });
        published
    }

    /// Put this public solve's route statistics back after an internal
    /// re-solve reset them (`prepare_check_sat_internal_state`): a declined
    /// route now lets the legacy retries run, and their reset must not erase
    /// what the route did.
    pub(in crate::executor) fn qsat_restore_statistics(&mut self) {
        if let Some(memo) = &self.qsat_route.memo {
            for (key, value) in &memo.stats {
                self.last_statistics
                    .extra
                    .insert(key.clone(), value.clone());
            }
        }
    }

    /// The route's `qsat.*` statistics.
    fn qsat_statistics(&self) -> Vec<(String, StatValue)> {
        self.last_statistics
            .extra
            .iter()
            .filter(|(key, _)| key.starts_with("qsat."))
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect()
    }

    /// Run `replay` (the UNSAT publication's consequence replay) with its
    /// ground probe ingesting the instances' undistributed arithmetic as is,
    /// exactly like the nested lane's expansion-certificate probe
    /// (`Executor::proof_probe_skips_som`). A strategy term is a projection's
    /// composed linear term, `(* (+ (* sk 2) (* sk' -7/8) -23/8) -19)`; the
    /// SOM rewrite of such an instance is no probe assertion, so its leaf
    /// demoted to a premiseless `trust` and the probe's own strict check
    /// refused a correct refutation (measured: mjollnir2/formula_199, probe
    /// proof `t0: trust (cl false)`). Proof shape only: the probe still has
    /// to refute, and its proof still has to pass every strict gate.
    fn qsat_without_som<T>(&mut self, replay: impl FnOnce(&mut Self) -> T) -> T {
        let skips_som = std::mem::replace(&mut self.proof_probe_skips_som, true);
        let out = replay(self);
        self.proof_probe_skips_som = skips_som;
        out
    }

    /// SAT: pin the authored free constants to the level-0 witness, install
    /// that model by one ground solve, and leave the decision to the
    /// ordinary SAT emission's quantified model gate.
    fn qsat_publish_sat(&mut self, game: &Game, run: &Run) -> Option<Result<SolveResult>> {
        let mut pins = Vec::with_capacity(game.free.len());
        let (mut ints, mut reals) = (false, false);
        for &c in &game.free {
            let value = run.model.vals.get(&c)?;
            let v = match (self.ctx.terms.sort(c).clone(), value) {
                (Sort::Bool, Val::Bool(b)) => self.ctx.terms.mk_bool(*b),
                (Sort::Int, Val::Num(n)) if n.is_integer() => {
                    ints = true;
                    self.ctx.terms.mk_int(n.to_integer())
                }
                (Sort::Real, Val::Num(n)) => {
                    reals = true;
                    self.ctx.terms.mk_rational(n.clone())
                }
                _ => return None,
            };
            pins.push(self.ctx.terms.mk_eq(c, v));
        }
        let category = match (ints, reals) {
            (true, true) => LogicCategory::QfLira,
            (true, false) => LogicCategory::QfLia,
            _ => LogicCategory::QfLra,
        };
        // The certificate stays installed for the rest of this public solve:
        // the ordinary SAT emission runs the gate. A refused installation
        // drops it (its terms may be rolled back).
        self.qsat_route.strategy = qsat::strategy::extract(&mut self.ctx.terms, game, run);
        let published = self.qsat_install_sat_model(pins, category);
        if published.is_none() {
            self.qsat_route.strategy = None;
        }
        self.qsat_note(
            "qsat.publish",
            if published.is_some() {
                "sat-gated"
            } else {
                "sat-refused"
            },
        );
        published
    }

    /// Install the witness model by one ground solve of the pins.
    fn qsat_install_sat_model(
        &mut self,
        pins: Vec<TermId>,
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        let saved_reason = self.last_unknown_reason;
        let window = std::mem::replace(&mut self.ctx.assertions, pins);
        let solved = self.solve_for_category(category);
        self.ctx.assertions = window;
        if !matches!(solved, Ok(SolveResult::Sat)) || self.last_model.is_none() {
            self.last_model = None;
            self.last_model_validated = false;
            self.last_unknown_reason = saved_reason;
            return None;
        }
        self.last_model_validated = false;
        self.last_unknown_reason = None;
        Some(Ok(SolveResult::Sat))
    }
}
