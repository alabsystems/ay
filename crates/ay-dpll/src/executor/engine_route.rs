// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The CDCL(T) kernel as the engine of its families: the strangler steps
//! (design the development design notes §10, M1; roadmap D6).
//!
//! `route_to_solver` asks the kernel first ([`Executor::solve_on_kernel`])
//! for the check-sats of the families it owns: one ay-sat search (`ay-cdclt`)
//! over the dispatch window, with the solve's whole budget. Every outcome the
//! kernel cannot publish — a give-up, a stop, a model the checks refuse, an
//! `unsat` the posture needs evidence for — hands the check to the family's
//! lane with the budget that is left, and the lane owns the verdict from
//! there.
//!
//! **What the kernel publishes.**
//! - `sat`: only a model that the kernel's exact model check
//!   (`Engine::check_model`, over the searched window and the dispatch
//!   window) accepts, installed through the lanes' model channel
//!   (`solve_and_store_model_with_theories`), so every model gate the lanes'
//!   answers pass runs unchanged on it, and `get-model` / `get-value` read
//!   it. The translation is `engine_route/model.rs`.
//! - `unsat`: only where no checked certificate can be asked of the verdict,
//!   the `--z3-mode` posture with no proof demand and no proof tracker armed
//!   (`competition_shedding_active`). The default posture mints a checked
//!   certificate for every `unsat` from the proof the lane records; the
//!   kernel's `ProofHint`s do not yet form that document (design P1), and
//!   it records nothing at all for a check with hub work. So there a kernel
//!   `unsat` goes to the lane, which re-derives it with its certificate: the
//!   evidence contract is kept, not weakened. A lane `sat` against a kernel
//!   `unsat` is a disagreement (`engine.disagree`); the lane's gated model
//!   stands.
//!
//! **Which families** (`KernelFamily`; the measurements behind each are in
//! the development design notes §14):
//! - QF_UF and QF_UFLRA (stage 0 of the migration, §10.4), and QF_UFLIA,
//!   whose kernel-first arm (`--engine=own:uflia`) decides more than its
//!   lane with no wrong answer: in both postures and in incremental
//!   sessions. Each check-sat is one search over the current assertion
//!   stack, so push/pop and repeated check-sats need no session state.
//! - QF_LRA (the first strangler step) and QF_UFIDL, in the `--z3-mode`
//!   posture only. In the default posture QF_UFIDL's kernel-first arm
//!   decided less than its lane: every kernel `unsat` there is decided
//!   twice, and the second decision starts late. QF_LRA also keeps its
//!   persistent lane in push/pop sessions.
//!
//! Never under `check-sat-assuming` (failed-assumption cores and their
//! certificate are the lane's) or when preprocessing removed quantifiers
//! (quantified refutations publish through their own proof path, and the
//! quantified families move with the quantifier engine, design §10.4).
//!
//! **A check with a resource limit keeps the lane** (`:rlimit`, or
//! `Executor::set_resource_limit`; DR-36 in the development design notes). The lane
//! arms that count on its SAT solves; the kernel's guard has only a deadline
//! and a stop, and it cannot yet read ay-sat's search ticks, so no check that
//! asked for a count runs without one. The conjunct goes once the kernel
//! charges its node through `SolverContext::search_ticks` (GuardTree S4) and
//! single-worker determinism (M7) passes on the kernel's families.
//!
//! `--engine=lane` (measurement only) keeps every family on its lane;
//! `--engine=shadow` implies it, because the shadow compares the two.
//! `--engine=own:<families>` gives the kernel exactly the listed families,
//! in both postures (the posture still decides whether a kernel `unsat`
//! publishes), so that the arm can be measured where production keeps the
//! lane.

mod model;
#[cfg(test)]
mod tests;

use std::sync::atomic::Ordering;
use std::sync::OnceLock;
use std::time::Instant;

use ay_cdclt::{Engine, EngineConfig, EngineStats, Guard, ModelVerdict, Verdict};
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{TermId, TseitinResult};
use ay_sat::SatResult;

use super::theories::preprocess_lra;
use super::theories::solve_harness::TheoryModels;
use super::Executor;
use crate::executor_types::SolveResult;
use crate::logic_detection::LogicCategory;
use model::ExtractedModel;

/// A family of check-sats the kernel can own (design §10.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelFamily {
    /// QF_LRA (not QF_RDL, not `is_int` over reals).
    QfLra,
    /// Uninterpreted functions and sorts.
    QfUf,
    /// QF_UF with linear real arithmetic.
    QfUflra,
    /// QF_UF with linear integer arithmetic.
    QfUflia,
    /// QF_UF with integer difference logic (the QF_UFIDL division).
    QfUfidl,
}

impl KernelFamily {
    /// Every family, in the order `--engine=own:` names them.
    pub const ALL: [Self; 5] = [
        Self::QfLra,
        Self::QfUf,
        Self::QfUflra,
        Self::QfUflia,
        Self::QfUfidl,
    ];

    /// The family's name in `--engine=own:<families>`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::QfLra => "lra",
            Self::QfUf => "uf",
            Self::QfUflra => "uflra",
            Self::QfUflia => "uflia",
            Self::QfUfidl => "ufidl",
        }
    }

    /// The family named `name` in `--engine=own:<families>`.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|family| family.name() == name)
    }

    /// The family of a dispatch, if the kernel serves it: the detected
    /// category, and the declared division where its content is the
    /// arithmetic alone (a QF_UFLRA script without an uninterpreted
    /// function is still QF_UFLRA's). QF_RDL and `is_int` over reals keep
    /// their dedicated lanes.
    pub(in crate::executor) fn for_route(
        category: LogicCategory,
        logic: Option<&str>,
        has_is_int_real: bool,
    ) -> Option<Self> {
        match (category, logic) {
            (LogicCategory::QfLra, Some("QF_UFLRA")) => Some(Self::QfUflra),
            (LogicCategory::QfLra, _) if !has_is_int_real && logic != Some("QF_RDL") => {
                Some(Self::QfLra)
            }
            (LogicCategory::QfUf, _) => Some(Self::QfUf),
            (LogicCategory::QfUflra, _) => Some(Self::QfUflra),
            (LogicCategory::QfUflia | LogicCategory::QfLia, Some("QF_UFIDL")) => {
                Some(Self::QfUfidl)
            }
            (LogicCategory::QfUflia, _) | (LogicCategory::QfLia, Some("QF_UFLIA")) => {
                Some(Self::QfUflia)
            }
            _ => None,
        }
    }
}

/// `--engine=own:<families>`, set once per process by the CLI.
static OWNED: OnceLock<Vec<KernelFamily>> = OnceLock::new();

/// `--engine=own:<families>` (measurement only, design §10.1): the kernel
/// owns exactly `families` in this process. `false` when already set.
pub fn set_kernel_owned_families(families: Vec<KernelFamily>) -> bool {
    OWNED.set(families).is_ok()
}

/// Who gave a family to the kernel.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Owner {
    /// The production routing table (no `--engine`).
    Production,
    /// `--engine=own:<families>`: the kernel-first arm in either posture.
    Measured,
}

/// Whether the routing table gives `family` to the kernel at all, and how.
fn family_owner(family: KernelFamily) -> Option<Owner> {
    let flags = ay_core::misc_cli_flags();
    if flags.engine_lanes || flags.engine_shadow {
        return None;
    }
    match OWNED.get() {
        Some(owned) => owned.contains(&family).then_some(Owner::Measured),
        None => Some(Owner::Production),
    }
}

/// How `route_to_solver`'s kernel-first step ended.
pub(in crate::executor) enum KernelFirst {
    /// The kernel's verdict, published.
    Answered(SolveResult),
    /// The lane decides; `kernel_unsat` when the kernel said `unsat`
    /// without the evidence the posture asks for.
    Lane { kernel_unsat: bool },
}

/// Why the kernel handed a check to the lane.
enum Declined {
    /// The kernel answered `unknown` (a give-up, a timeout, a stop).
    Unknown(String),
    /// The kernel answered `sat` and a model check refused its model.
    ModelRefused(String),
    /// The kernel answered `unsat` where the posture asks for a checked
    /// certificate the kernel cannot supply.
    UnsatNeedsEvidence,
}

impl Declined {
    fn label(&self) -> String {
        match self {
            Self::Unknown(reason) => reason.clone(),
            Self::ModelRefused(why) => format!("model refused: {why}"),
            Self::UnsatNeedsEvidence => "unsat needs the lane's certificate".to_string(),
        }
    }
}

impl Executor {
    /// `route_to_solver`'s kernel-first step for a dispatch of `family`.
    pub(in crate::executor) fn solve_on_kernel(&mut self, family: KernelFamily) -> KernelFirst {
        if !self.kernel_owns(family) {
            return KernelFirst::Lane {
                kernel_unsat: false,
            };
        }
        // An interrupt, an expired deadline or an observed evaluation stop
        // ends the check here, as it would end the lane's.
        if self.should_abort_theory_loop() {
            return KernelFirst::Answered(SolveResult::Unknown);
        }
        match self.kernel_check(family) {
            Ok(result) => KernelFirst::Answered(result),
            Err(declined) => {
                self.last_statistics
                    .set_string("engine.fallback", declined.label());
                KernelFirst::Lane {
                    kernel_unsat: matches!(declined, Declined::UnsatNeedsEvidence),
                }
            }
        }
    }

    /// After the lane decided a check the kernel called `unsat`: a lane `sat`
    /// (a gated model) is a disagreement, recorded; the model stands.
    pub(in crate::executor) fn note_lane_after_kernel_unsat(&mut self, lane: &SolveResult) {
        if lane.is_sat() {
            self.last_statistics.set_int("engine.disagree", 1);
            tracing::warn!("kernel unsat against a gated lane sat model");
        }
    }

    /// Whether the kernel takes this check of `family` (see the module doc).
    fn kernel_owns(&self, family: KernelFamily) -> bool {
        let Some(owner) = family_owner(family) else {
            return false;
        };
        if self.last_assumptions.is_some() || self.original_problem_had_quantifiers {
            return false;
        }
        // DR-36: a check that asked for a count (`:rlimit`) keeps the lane,
        // whatever the family and whoever owns it, until the kernel charges
        // its search ticks (module doc).
        if self.resource_limit.is_some() {
            return false;
        }
        match (family, owner) {
            (KernelFamily::QfLra, _) if self.incremental_mode => false,
            // Production keeps the lane where the posture asks for a
            // certificate the kernel's `unsat` cannot carry and the measured
            // kernel-first arm decides less than the lane (module doc).
            (KernelFamily::QfLra | KernelFamily::QfUfidl, Owner::Production) => {
                self.kernel_unsat_admissible()
            }
            _ => true,
        }
    }

    /// Whether a kernel `unsat` may be published: only where no checked
    /// certificate can be asked of it.
    fn kernel_unsat_admissible(&self) -> bool {
        self.competition_shedding_active() && !self.produce_proofs_enabled()
    }

    /// One kernel check over the current assertion window. On `sat` the model
    /// is checked, installed and gated; on a published `unsat` the verdict is
    /// recorded. Anything else leaves the verdict state as it found it.
    fn kernel_check(&mut self, family: KernelFamily) -> Result<SolveResult, Declined> {
        let started = Instant::now();
        let original = self.ctx.assertions.clone();
        let window = self.kernel_window(family, &original);
        let guard = self.kernel_guard();
        let mut engine = Engine::new(EngineConfig::default());
        for &assertion in &window {
            engine.assert(assertion);
        }
        let outcome = engine.check(&mut self.ctx.terms, &[], &guard);
        self.record_kernel_statistics(&outcome.stats, outcome.verdict, started);
        match outcome.verdict {
            Verdict::Unsat if self.kernel_unsat_admissible() => {
                self.pending_sat_unknown_reason = None;
                self.last_result = Some(SolveResult::unsat());
                Ok(SolveResult::unsat())
            }
            Verdict::Unsat => Err(Declined::UnsatNeedsEvidence),
            Verdict::Sat => {
                let searched: HashSet<TermId> = window.iter().copied().collect();
                let mut checked = window;
                checked.extend(original.iter().filter(|&a| !searched.contains(a)));
                self.adopt_kernel_model(&mut engine, &checked)
            }
            Verdict::Unknown => Err(Declined::Unknown(outcome.reason.unwrap_or_default())),
        }
    }

    /// The window the kernel searches. QF_LRA gets the lane's LRA
    /// preprocessing. A window with hub content gets its term-level `ite`s
    /// named here, under the condition the kernel names them itself, so the
    /// applications the kernel values are terms of this window and its model
    /// can be read back over it. The names are the term store's
    /// (`__ay_ite_def_{TermId}`), not the kernel's content-keyed ones (KC9),
    /// so on this route the kernel's name-derived order still follows
    /// interning.
    fn kernel_window(&mut self, family: KernelFamily, original: &[TermId]) -> Vec<TermId> {
        if family == KernelFamily::QfLra {
            return preprocess_lra(&mut self.ctx.terms, original.to_vec());
        }
        if !model::has_hub_content(&self.ctx.terms, original) {
            return original.to_vec();
        }
        let mut definitions = Vec::new();
        let mut named = self
            .ctx
            .terms
            .name_non_bool_ites_all(original, &mut definitions);
        named.extend(definitions);
        named
    }

    /// The solve's deadline and stop conditions, for the kernel.
    fn kernel_guard(&self) -> Guard {
        let interrupt = self.solve_interrupt.clone();
        let live_deadline = self.solve_deadline.clone();
        Guard::new()
            .with_deadline(self.solve_deadline.get())
            .with_stop(move || {
                interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(Ordering::Relaxed))
                    || live_deadline.expired()
            })
    }

    /// A kernel `sat`: the exact model check over `checked`, then the model
    /// in the executor's channels and its gates.
    fn adopt_kernel_model(
        &mut self,
        engine: &mut Engine,
        checked: &[TermId],
    ) -> Result<SolveResult, Declined> {
        let verdict = engine.check_model(&mut self.ctx.terms, checked);
        if verdict != ModelVerdict::Satisfied {
            let label = match verdict {
                ModelVerdict::Violated(term) => format!("violated {}", term.0),
                ModelVerdict::Unchecked(why) => format!("unchecked: {why}"),
                ModelVerdict::Satisfied => String::new(),
            };
            self.last_statistics
                .set_string("engine.model_check", label.clone());
            return Err(Declined::ModelRefused(label));
        }
        let extracted =
            model::extract(engine, &mut self.ctx.terms, checked).map_err(Declined::ModelRefused)?;
        let assignment = engine.sat_assignment().to_vec();
        let encoded: Vec<(TermId, u32)> = engine.encoded_terms().collect();
        self.install_kernel_model(assignment, &encoded, extracted, checked)
    }

    /// Install a kernel `sat` model through the lanes' model channel and run
    /// the gates. A refusal is undone, so the lane starts from a clean state.
    fn install_kernel_model(
        &mut self,
        assignment: Vec<bool>,
        encoded: &[(TermId, u32)],
        extracted: ExtractedModel,
        checked: &[TermId],
    ) -> Result<SolveResult, Declined> {
        let mut term_to_var = std::collections::BTreeMap::new();
        let mut var_to_term = std::collections::BTreeMap::new();
        for &(term, var) in encoded {
            // The executor's model keys are 1-based CNF variables.
            term_to_var.insert(term, var + 1);
            var_to_term.insert(var + 1, term);
        }
        let num_vars = u32::try_from(assignment.len())
            .map_err(|_| Declined::ModelRefused("too many variables".to_string()))?;
        let tseitin = TseitinResult::new(Vec::new(), term_to_var, var_to_term, 1, num_vars);
        let models = TheoryModels {
            lra: (!extracted.lra.values.is_empty() || extracted.euf.is_none())
                .then_some(extracted.lra),
            lia: extracted.lia,
            euf: extracted.euf,
            ..TheoryModels::default()
        };
        let saved_reason = self.last_unknown_reason.take();
        // No counterexample minimization: the model passed the exact check
        // as it is, and the minimizer rewrites arithmetic values that the
        // function tables' rows were read at, which left `get-model` printing
        // tables that are not functions (hub hunt, QF_UFLRA_g11_0208).
        let saved_defer = std::mem::replace(&mut self.defer_counterexample_minimization, true);
        // The tables' rows are the window's applications, which the query's
        // own row filter would drop.
        self.function_row_roots = checked.to_vec();
        let stored =
            self.solve_and_store_model_with_theories(SatResult::Sat(assignment), &tseitin, models);
        self.function_row_roots.clear();
        match stored {
            Ok(SolveResult::Sat) => Ok(SolveResult::Sat),
            _ => {
                self.defer_counterexample_minimization = saved_defer;
                self.last_statistics.set_int("engine.model_refused", 1);
                self.last_model = None;
                self.last_model_validated = false;
                self.last_result = None;
                self.last_unknown_reason = saved_reason;
                for key in [
                    "unknown.reason",
                    "unknown.phase",
                    "unknown.cost_center",
                    "unknown.detail",
                ] {
                    self.last_statistics.extra.remove(key);
                }
                Err(Declined::ModelRefused("a model gate".to_string()))
            }
        }
    }

    /// The kernel's structural counters (design §11), on every exit.
    fn record_kernel_statistics(
        &mut self,
        stats: &EngineStats,
        verdict: Verdict,
        started: Instant,
    ) {
        let st = &mut self.last_statistics;
        // The SAT counters of the one search; theory conflicts stay under
        // `engine.theory_conflicts` (a level-0 theory conflict is not a SAT
        // conflict, so `theory_conflicts <= conflicts` would not hold).
        st.conflicts = stats.sat_conflicts;
        st.decisions = stats.sat_decisions;
        st.set_string(
            "engine.kernel",
            match verdict {
                Verdict::Sat => "sat",
                Verdict::Unsat => "unsat",
                Verdict::Unknown => "unknown",
            },
        );
        st.set_float("engine.seconds", started.elapsed().as_secs_f64());
        for (key, value) in [
            ("engine.solve_calls", stats.solve_calls),
            ("engine.propagate_calls", stats.propagate_calls),
            ("engine.final_checks", stats.final_checks),
            ("engine.theory_conflicts", stats.conflicts),
            ("engine.lemmas", stats.lemmas),
            ("engine.definitions", stats.definitions),
            ("engine.minted_atoms", stats.minted_atoms),
            ("engine.eager_propagations", stats.eager_propagations),
            ("engine.lazy_propagations", stats.lazy_propagations),
            ("engine.lazy_explained", stats.lazy_explained),
            ("engine.give_ups", stats.give_ups),
            ("engine.hub_merges", stats.hub_merges),
        ] {
            st.set_int(key, value);
        }
    }
}
