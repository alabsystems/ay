// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The preprocessing pipeline that runs once per `check-sat`, before routing
//! (architecture roadmap 2026-09-29, component S; milestone 1 is quantifier
//! preprocessing).
//!
//! z3 decides a class of quantified problems without any search because its
//! `asserted_formulas` preprocessing (NNF + Skolemization, DER inside the
//! rewriter, `elim_unused_vars`, qe-lite, propagate-values, macro finder)
//! reduces them to `false` or to a small ground problem. This module is AY's
//! counterpart: ONE ordered pipeline of passes over the assertion window, in
//! front of every quantified route, instead of shape-specific rescues inside
//! individual lanes.
//!
//! # The pass contract
//!
//! Every [`Pass`] declares two things before it may touch the window:
//!
//! * **Preservation** ([`Preservation`]): whether its output has exactly the
//!   models of its input over the same signature, or only preserves
//!   satisfiability. A satisfiability-preserving pass MUST record, in the
//!   [`ModelConverter`], how a model of its output becomes a model of its
//!   input (Skolem symbols to drop, eliminated functions to define).
//! * **Justification** ([`Justification`]): whether the pass can emit the
//!   proof step that connects its input to its output. The posture decides
//!   what that buys: under [`Posture::ProofCarrying`] (the default posture:
//!   every UNSAT is certified by a checked refutation) a pass that cannot
//!   justify its step is SKIPPED — it never runs and its step is never trusted
//!   silently. Under [`Posture::Raw`] (the explicit `--z3-mode` /
//!   competition opt-in, where the proof cycle is shed and UNSAT publishes
//!   without a checked refutation) passes run as trusted preprocessing, as
//!   z3's do; every application is counted in the solve statistics
//!   (`simplifier.<pass>.rewrites`), and every posture skip in
//!   `simplifier.<pass>.skipped`.
//!
//! No pass in milestone 1 emits proof steps yet, so under the default posture
//! the pipeline is the identity by construction. The justification slot is
//! the hook where each pass's rule (`sko_*`, `onepoint`, `qnt_rm_unused`, …)
//! plugs in once the proof layer records rewrite steps (roadmap D3).
//!
//! # Passes, in order
//!
//! The rewriter-level eliminations come first, as in z3, where DER and
//! `elim_unused_vars` run inside `th_rewriter` on every assertion before the
//! NNF/Skolem step (a Skolem function minted for `∀y ∃x. x = y ∧ p(x)` would
//! otherwise hide the equality DER resolves):
//!
//! 1. `der`: destructive equality resolution on every quantifier node.
//! 2. `elim-unused-vars`: unused bound variables dropped.
//! 3. `qe-lite`: arithmetic one-point elimination.
//! 4. `nnf-skolem`: NNF + Skolemization of the quantified assertions.
//! 5. `propagate-values`: top-level conjunction flattening + value propagation.
//! 6. `macro-finder`: function definitions eliminated by expansion.
//!
//! The sequence repeats until a round changes nothing (at most
//! [`MAX_ROUNDS`]), so a Skolemized goal gets a second rewriter round. Work is
//! bounded by a [`WorkBudget`] that also polls the caller's stop flag; a pass
//! that runs out keeps the assertions it had not finished unchanged, so an
//! exhausted budget is always a sound stop.
//!
//! # The tactic surface
//!
//! The API `der` tactic runs the DER pass itself ([`der_tactic`]), so each
//! rewrite has one implementation. The `qe-light` tactic is a different
//! algorithm: Cooper elimination of one `Int` existential
//! (`crate::preprocess::QeLight`), not the one-point `qe-lite` pass here.

mod fold;
mod linear_solve;
mod macro_finder;
mod model_converter;
mod nnf_skolem;
mod propagate;
mod quantifier_rules;
mod terms;

#[cfg(test)]
mod tactic_tests;
#[cfg(test)]
mod tests;

use ay_core::{TermId, TermStore};

pub(crate) use model_converter::{ConverterEntry, ModelConverter};

/// Upper bound on pipeline rounds.
pub(crate) const MAX_ROUNDS: usize = 4;

/// Default node-visit budget for one pipeline run.
pub(crate) const DEFAULT_WORK_LIMIT: u64 = 2_000_000;

/// What the solve's publication posture demands of a preprocessing step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Posture {
    /// Every UNSAT carries a checked refutation: only justified steps may run.
    ProofCarrying,
    /// The proof cycle is shed by explicit opt-in: trusted preprocessing.
    Raw,
}

/// Whether a pass can emit the proof step for its rewrite.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Justification {
    /// No proof step is emitted: the pass is skipped under
    /// [`Posture::ProofCarrying`].
    Unjustified,
}

/// The semantic relation a pass preserves between its input and output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Preservation {
    /// Same models over the same signature; no converter entries.
    Equivalence,
    /// Satisfiability, with converter entries reconstructing input models.
    SatisfiabilityWithConverter,
}

impl Justification {
    fn admitted_in(self, posture: Posture) -> bool {
        match (self, posture) {
            (Justification::Unjustified, Posture::Raw) => true,
            (Justification::Unjustified, Posture::ProofCarrying) => false,
        }
    }
}

/// A node-visit budget that also polls the caller's stop flag.
pub(crate) struct WorkBudget<'s> {
    remaining: u64,
    stop: &'s dyn Fn() -> bool,
    since_poll: u32,
    exhausted: bool,
}

impl<'s> WorkBudget<'s> {
    pub(crate) fn new(limit: u64, stop: &'s dyn Fn() -> bool) -> Self {
        Self {
            remaining: limit,
            stop,
            since_poll: 0,
            exhausted: false,
        }
    }

    /// Spend one unit. `false` once the budget or the caller's patience is gone.
    pub(crate) fn tick(&mut self) -> bool {
        self.charge(1)
    }

    /// Spend `units`. `false` once the budget or the caller's patience is gone.
    pub(crate) fn charge(&mut self, units: u64) -> bool {
        if self.exhausted {
            return false;
        }
        if self.remaining < units {
            self.exhausted = true;
            return false;
        }
        self.remaining -= units;
        self.since_poll = self.since_poll.saturating_add(1);
        if self.since_poll >= 1024 {
            self.since_poll = 0;
            if (self.stop)() {
                self.exhausted = true;
                return false;
            }
        }
        true
    }

    pub(crate) fn exhausted(&self) -> bool {
        self.exhausted
    }
}

/// Everything a pass may read or change.
pub(crate) struct PassContext<'a, 's> {
    terms: &'a mut TermStore,
    window: &'a mut Vec<TermId>,
    converter: &'a mut ModelConverter,
    budget: &'a mut WorkBudget<'s>,
    /// `symbols(name, arity)`: is `name/arity` a user-declared uninterpreted
    /// function (so a macro may eliminate it)?
    symbols: &'a dyn Fn(&str, usize) -> bool,
}

/// One pipeline stage.
pub(crate) trait Pass {
    /// Stable name used in statistics.
    fn name(&self) -> &'static str;
    /// What the rewrite preserves.
    fn preservation(&self) -> Preservation;
    /// Whether the rewrite can be justified by a proof step.
    fn justification(&self) -> Justification;
    /// Rewrite the window in place; return the number of rewrites committed.
    fn run(&mut self, cx: &mut PassContext<'_, '_>) -> usize;
}

/// A [`quantifier_rules::QuantifierRule`] applied to every quantifier node.
struct RulePass<R> {
    name: &'static str,
    rule: R,
}

impl<R: quantifier_rules::QuantifierRule> Pass for RulePass<R> {
    fn name(&self) -> &'static str {
        self.name
    }

    fn preservation(&self) -> Preservation {
        Preservation::Equivalence
    }

    fn justification(&self) -> Justification {
        Justification::Unjustified
    }

    fn run(&mut self, cx: &mut PassContext<'_, '_>) -> usize {
        quantifier_rules::rewrite_window(cx.terms, cx.window, &mut self.rule, cx.budget)
    }
}

/// Per-pass outcome of one pipeline run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PassReport {
    pub(crate) name: &'static str,
    /// Rewrites committed across all rounds.
    pub(crate) rewrites: usize,
    /// Set when the posture refused the pass.
    pub(crate) skipped_unjustified: bool,
}

/// The result of one pipeline run.
pub(crate) struct PipelineOutcome {
    /// The rewritten window (unchanged when nothing applied).
    pub(crate) window: Vec<TermId>,
    /// How to turn a model of `window` into a model of the input.
    pub(crate) converter: ModelConverter,
    pub(crate) reports: Vec<PassReport>,
    /// Whether any pass changed the window.
    pub(crate) changed: bool,
    /// The window is `[false]`: the input is unsatisfiable.
    pub(crate) refuted: bool,
    /// The budget or the stop flag ended the run early.
    pub(crate) budget_exhausted: bool,
    pub(crate) rounds: usize,
    /// `(round, pass, window after the pass)` for every pass that changed the
    /// window; recorded only when the caller asks for a trace.
    pub(crate) trace: Vec<(usize, &'static str, Vec<TermId>)>,
}

/// The milestone-1 quantifier preprocessing pipeline, in z3's order.
fn quantifier_passes() -> Vec<Box<dyn Pass>> {
    vec![
        Box::new(RulePass {
            name: "der",
            rule: quantifier_rules::DerRule,
        }),
        Box::new(RulePass {
            name: "elim-unused-vars",
            rule: quantifier_rules::ElimUnusedVarsRule,
        }),
        Box::new(RulePass {
            name: "qe-lite",
            rule: quantifier_rules::QeLiteRule,
        }),
        Box::new(nnf_skolem::NnfSkolem),
        Box::new(propagate::Propagate),
        Box::new(macro_finder::MacroFinder),
    ]
}

/// Names of the quantifier passes `posture` refuses (all of them, today, under
/// [`Posture::ProofCarrying`]). When every pass is refused the caller can skip
/// the run entirely.
pub(crate) fn refused_quantifier_passes(posture: Posture) -> Vec<&'static str> {
    quantifier_passes()
        .iter()
        .filter(|pass| !pass.justification().admitted_in(posture))
        .map(|pass| pass.name())
        .collect()
}

/// Whether `posture` admits no quantifier pass at all.
pub(crate) fn refuses_every_quantifier_pass(posture: Posture) -> bool {
    refused_quantifier_passes(posture).len() == quantifier_passes().len()
}

/// z3's `der` tactic on the API tactic surface: the pipeline's DER pass,
/// applied bottom-up to every quantifier node of `formulas`, with nothing
/// else of the pipeline around it. One implementation serves both surfaces.
///
/// No posture gate: a tactic rewrites a DETACHED goal, which is printed or
/// re-checked but never publication authority, and DER is an equivalence.
/// The default work budget applies; an assertion the budget does not cover
/// keeps its shape (the sound identity). Returns whether a formula changed.
pub(crate) fn der_tactic(terms: &mut TermStore, formulas: &mut [TermId]) -> bool {
    let never = || false;
    let mut budget = WorkBudget::new(DEFAULT_WORK_LIMIT, &never);
    let before = formulas.to_vec();
    quantifier_rules::rewrite_window(terms, formulas, &mut quantifier_rules::DerRule, &mut budget);
    formulas[..] != before[..]
}

/// Run the quantifier preprocessing pipeline over `window`.
///
/// `symbols(name, arity)` answers whether a function may be eliminated by a
/// macro; `stop` is polled by the work budget.
pub(crate) fn run_quantifier_pipeline(
    terms: &mut TermStore,
    window: &[TermId],
    posture: Posture,
    symbols: &dyn Fn(&str, usize) -> bool,
    stop: &dyn Fn() -> bool,
    work_limit: u64,
    record_trace: bool,
) -> PipelineOutcome {
    let mut passes = quantifier_passes();
    let mut current = window.to_vec();
    let mut converter = ModelConverter::new();
    let mut budget = WorkBudget::new(work_limit, stop);
    let mut reports: Vec<PassReport> = passes
        .iter()
        .map(|pass| PassReport {
            name: pass.name(),
            rewrites: 0,
            skipped_unjustified: !pass.justification().admitted_in(posture),
        })
        .collect();
    let mut rounds = 0;
    let mut trace = Vec::new();
    let mut contract_violation = false;
    let false_term = terms.false_term();
    while rounds < MAX_ROUNDS {
        rounds += 1;
        let mut round_changed = false;
        for (pass, report) in passes.iter_mut().zip(reports.iter_mut()) {
            if report.skipped_unjustified || budget.exhausted() {
                continue;
            }
            let before = current.clone();
            let entries_before = converter.entries().len();
            let mut cx = PassContext {
                terms: &mut *terms,
                window: &mut current,
                converter: &mut converter,
                budget: &mut budget,
                symbols,
            };
            let rewrites = pass.run(&mut cx);
            // Contract: an equivalence records nothing. A pass that breaks it
            // voids the whole run (the caller keeps its window).
            if pass.preservation() == Preservation::Equivalence
                && converter.entries().len() != entries_before
            {
                debug_assert!(false, "{} recorded converter entries", pass.name());
                contract_violation = true;
                break;
            }
            if current != before {
                round_changed = true;
                report.rewrites += rewrites.max(1);
                if record_trace {
                    trace.push((rounds, report.name, current.clone()));
                }
            }
            if current.contains(&false_term) {
                break;
            }
        }
        if contract_violation
            || !round_changed
            || current.contains(&false_term)
            || budget.exhausted()
        {
            break;
        }
    }
    if contract_violation {
        current = window.to_vec();
        converter = ModelConverter::new();
    }
    let refuted = current.contains(&false_term);
    if refuted {
        current = vec![false_term];
    }
    debug_assert!(converter.bodies_are_closed(terms));
    PipelineOutcome {
        changed: current != window,
        window: current,
        converter,
        reports,
        refuted,
        budget_exhausted: budget.exhausted(),
        rounds,
        trace,
    }
}
