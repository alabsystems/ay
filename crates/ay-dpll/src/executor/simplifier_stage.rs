// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The quantified `check-sat` entry's preprocessing stage: one run of
//! [`crate::simplifier::run_quantifier_pipeline`] over the working window,
//! before any quantified route sees it.
//!
//! # Posture
//!
//! The stage asks the pipeline for [`Posture::Raw`] only when this public
//! solve sheds the proof cycle by explicit opt-in
//! ([`Executor::competition_shedding_active`]: `--z3-mode`, `--no-proof`,
//! competition mode, with no proof demand in scope). Every other solve —
//! the default posture, any proof request, self-check, and every
//! proof-producing API session — gets [`Posture::ProofCarrying`], under which
//! a pass that cannot justify its step never runs.
//!
//! # Restoration
//!
//! The rewrite is a SOLVE-TIME window. The caller keeps the pre-stage window
//! and restores it on every exit (see [`SimplifierStage::Rewritten`]), so the
//! scope-frame `assertion_count` invariant holds, later `check-sat`s start
//! from the authored assertions, and every SAT verdict is still validated
//! against them: a model of the rewritten window is published only when the
//! ordinary gates confirm it against the restored assertions.
//!
//! # The unrewritten fallback (#simplifier-sat-fallback)
//!
//! Adopting a rewrite is a bet that the rewritten problem is easier. It can
//! lose a verdict the unrewritten route decides: the rewrite removes the
//! quantified structure the SAT confirmations key on (Skolem-witness records,
//! E-matching instances, the quantified gate's nested solves over terms of
//! the authored window), so a model of the rewritten window can fail every
//! confirmation against the restored assertions. On 820 generated files that
//! was 21 `sat` answers the unrewritten route publishes. The recorded model
//! converter does not close that gap: 7 of those 21 rewrites record no entry
//! at all (DER, qe-lite and value propagation are equivalences), and a macro
//! definition needs a symbolic function interpretation the model, its gates
//! and its printer do not carry.
//!
//! So adoption is revocable. When a public `check-sat` adopted a rewrite and
//! its primary solve publishes no verdict, `check_sat_guarded` re-runs the
//! primary solve ONCE with the stage suspended
//! ([`Executor::resolve_without_simplifier`]), from the same per-query state,
//! and that solve's verdict goes through the same emission gates. Nothing is
//! published unconfirmed: the fallback only replaces an `unknown`, and only
//! with a verdict the unrewritten route reaches on its own. The pipeline's
//! refutations and decided rewrites are untouched.
//!
//! # Queries the stage declines
//!
//! `check-sat-assuming` and unsat-core solves: the assumption and named-core
//! machinery identifies assertions by term, and a rewritten window would
//! detach them.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::TermId;

use crate::ematching::contains_quantifier;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::simplifier::{self, ConverterEntry, ModelConverter, Posture};

use super::Executor;

/// Whether the quantified entry adopts a rewrite that still has quantifiers.
///
/// Measured 2026-09-30 on the 396 quantified files of the headline sample
/// (`--z3-mode -T:10`): a partial rewrite changes the shapes the quantifier
/// loop's instantiation and proxy machinery keys on (flattened conjunctions
/// expose guarded universals as top-level axioms). It lost a decided file
/// (`binary_trees.adb_75_36`: 0.6 s to timeout), and the only file a partial
/// rewrite alone decided needed a quantified macro body, which the macro
/// finder now refuses. Until the in-search quantifier engine replaces that
/// machinery, only decisive outcomes are adopted: a refutation, or a window
/// with no quantifier left.
const ADOPT_PARTIAL_REWRITES: bool = false;

/// What the stage did to the working window.
pub(in crate::executor) enum SimplifierStage {
    /// The window is unchanged.
    Unchanged,
    /// The window was rewritten. `pre_stage` is the window the caller must
    /// restore and validate SAT against.
    Rewritten { pre_stage: Vec<TermId> },
    /// The pipeline reduced the window to `false`.
    Refuted,
}

impl Executor {
    /// Run the quantifier preprocessing pipeline on `self.ctx.assertions`
    /// when the window has a quantifier.
    pub(in crate::executor) fn run_simplifier_stage(
        &mut self,
        quantified: bool,
    ) -> SimplifierStage {
        if !quantified {
            return SimplifierStage::Unchanged;
        }
        if self.simplifier_stage_suspended {
            self.last_statistics.set_int("simplifier.suspended", 1);
            return SimplifierStage::Unchanged;
        }
        let posture = if self.competition_shedding_active() {
            Posture::Raw
        } else {
            Posture::ProofCarrying
        };
        let unsat_cores = matches!(
            self.ctx.get_option("produce-unsat-cores"),
            Some(ay_frontend::OptionValue::Bool(true))
        );
        if self.last_assumptions.is_some() || unsat_cores {
            self.last_statistics
                .set_int("simplifier.declined_assumptions", 1);
            return SimplifierStage::Unchanged;
        }
        if simplifier::refuses_every_quantifier_pass(posture) {
            for name in simplifier::refused_quantifier_passes(posture) {
                self.last_statistics
                    .set_int(&format!("simplifier.{name}.skipped"), 1);
            }
            return SimplifierStage::Unchanged;
        }
        let pre_stage = self.ctx.assertions.clone();
        let eliminable = self.macro_eliminable_heads(&pre_stage);
        let symbols = |name: &str, arity: usize| eliminable.contains(&(name.to_string(), arity));
        let stop = self.make_should_stop();
        let outcome = simplifier::run_quantifier_pipeline(
            &mut self.ctx.terms,
            &pre_stage,
            posture,
            &symbols,
            &stop,
            simplifier::DEFAULT_WORK_LIMIT,
            tracing::enabled!(target: "ay::simplifier", tracing::Level::DEBUG),
        );
        self.record_pipeline_run(&outcome);
        if !outcome.changed {
            return SimplifierStage::Unchanged;
        }
        self.last_statistics
            .set_int("simplifier.rounds", outcome.rounds as u64);
        if outcome.refuted {
            self.last_statistics.set_int("simplifier.refuted", 1);
            return SimplifierStage::Refuted;
        }
        let ground = !outcome
            .window
            .iter()
            .any(|&assertion| contains_quantifier(&self.ctx.terms, assertion));
        if !ground && !ADOPT_PARTIAL_REWRITES {
            self.last_statistics
                .set_int("simplifier.partial_declined", 1);
            return SimplifierStage::Unchanged;
        }
        self.last_statistics.set_int(
            if ground {
                "simplifier.ground"
            } else {
                "simplifier.partial"
            },
            1,
        );
        self.record_converter_statistics(&outcome.converter);
        self.ctx.assertions = outcome.window;
        self.simplifier_rewrite_adopted = true;
        SimplifierStage::Rewritten { pre_stage }
    }

    /// Trace the run's rewrites (target `ay::simplifier`, debug) and count
    /// every pass's rewrites or posture skip in the solve statistics.
    fn record_pipeline_run(&mut self, outcome: &simplifier::PipelineOutcome) {
        for (round, pass, window) in &outcome.trace {
            for &assertion in window {
                tracing::debug!(
                    target: "ay::simplifier",
                    round,
                    pass,
                    assertion = %ay_proof::render_term_canonical(&self.ctx.terms, assertion),
                );
            }
        }
        for report in &outcome.reports {
            if report.skipped_unjustified {
                self.last_statistics
                    .set_int(&format!("simplifier.{}.skipped", report.name), 1);
            } else if report.rewrites > 0 {
                self.last_statistics.set_int(
                    &format!("simplifier.{}.rewrites", report.name),
                    report.rewrites as u64,
                );
            }
        }
        if outcome.budget_exhausted {
            self.last_statistics
                .set_int("simplifier.budget_exhausted", 1);
        }
    }

    /// Whether the unrewritten fallback may run for this public `check-sat`:
    /// the stage adopted a rewrite, no fallback is running, and the budget is
    /// not spent (the same timeout/interrupt guards as the other reactive
    /// re-solves of `check_sat_guarded`).
    pub(in crate::executor) fn simplifier_fallback_armed(&self) -> bool {
        self.simplifier_rewrite_adopted
            && !self.simplifier_stage_suspended
            && !self.ite_uf_definition_recovery.ready()
            && !matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::Timeout
                        | UnknownReason::ResourceLimit
                        | UnknownReason::MemoryLimit
                        | UnknownReason::Interrupted
                )
            )
            && self.external_stop_reason().is_none()
    }

    /// Re-run the primary solve of this public `check-sat` with the stage
    /// suspended (#simplifier-sat-fallback). The per-query state is reset as
    /// at the entry of `check_sat_guarded`, so the reactive re-solves after
    /// this one react to ITS rejections, and the verdict passes the same
    /// emission gates. The suspension lasts until the public call returns.
    pub(in crate::executor) fn resolve_without_simplifier(&mut self) -> Result<SolveResult> {
        self.simplifier_rewrite_adopted = false;
        self.simplifier_stage_suspended = true;
        self.reset_public_query_solve_state();
        self.array_ext_shadow.clear();
        self.cegqi_ce_free_stash = None;
        self.last_unknown_reason = None;
        self.last_result = None;
        self.last_model = None;
        let result = self.solve_and_emit_primary()?;
        self.last_statistics.set_int("simplifier.fallback", 1);
        Ok(result)
    }

    /// Publish the pipeline's refutation as this solve's UNSAT. The caller has
    /// restored the authored window.
    pub(in crate::executor) fn publish_simplifier_refutation(&mut self) -> SolveResult {
        self.defer_model_validation = false;
        self.last_unknown_reason = None;
        self.simplifier_refutation_unsat = true;
        SolveResult::unsat()
    }

    /// The model converter of an adopted rewrite. SAT is validated against
    /// the restored pre-stage window, so a model of the rewritten window is
    /// published only when the ordinary gates confirm it there; the entries
    /// are recorded, not applied (a macro-eliminated function leaves such a
    /// SAT unconfirmed, and the unrewritten fallback then re-decides the
    /// query).
    fn record_converter_statistics(&mut self, converter: &ModelConverter) {
        let (mut fresh, mut defined) = (0u64, 0u64);
        for entry in converter.entries() {
            match entry {
                ConverterEntry::Fresh { .. } => fresh += 1,
                ConverterEntry::Define { .. } => defined += 1,
            }
        }
        self.last_statistics
            .set_int("simplifier.converter.fresh", fresh);
        self.last_statistics
            .set_int("simplifier.converter.defined", defined);
    }

    /// The `(name, arity)` application heads in `roots` that a macro may
    /// eliminate: user-declared uninterpreted functions only (the same
    /// positive/negative filters the constant-interpretation certificate uses
    /// for "free symbol").
    fn macro_eliminable_heads(&self, roots: &[TermId]) -> HashSet<(String, usize)> {
        let mut heads: HashSet<(String, usize)> = HashSet::default();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots.to_vec();
        let terms = &self.ctx.terms;
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match terms.get(t) {
                TermData::App(sym, args) => {
                    if !args.is_empty() {
                        heads.insert((sym.name().to_string(), args.len()));
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, v)| *v));
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }
        heads
            .into_iter()
            .filter(|(name, arity)| self.const_interp_head_is_uninterpreted(name, *arity))
            .collect()
    }
}
