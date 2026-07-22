// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Houdini-style pruning of frame[1] to a (relatively) inductive core (#4751).
//!
//! Startup discovery admits some frame[1] lemmas through relative
//! inductiveness oracles that use must-summaries / reach facts as hypotheses.
//! Those lemmas can be true only for the sampled prefix (e.g. dillig12_m's
//! `(mod C 16) = 0`, `A = C` at depth <= 1) while being globally
//! non-inductive. They poison every model built from the frame — strict final
//! validation rejects the model — and slow every subsequent blocking query.
//!
//! When a Safe candidate is demoted by strict validation, this pass sweeps
//! frame[1] with the CLEAN per-lemma oracles (init-validity, transition
//! preservation relative to the current frame, cross-predicate
//! entry-inductiveness) and REMOVES every lemma that fails, iterating to a
//! fixpoint (standard Houdini argument: dropping a falsified conjunct can
//! only expose further falsified conjuncts, and the surviving set is
//! self-justifying).
//!
//! SOUNDNESS: frames over-approximate reachable states, so removing lemmas
//! only weakens the frame — never unsound. Any model built afterwards still
//! passes through strict final validation.

use super::super::{PdrResult, PdrSolver};
use crate::ChcExpr;

/// Wall-clock budget for one prune sweep.
const HOUDINI_PRUNE_BUDGET: std::time::Duration = std::time::Duration::from_secs(3);

/// Maximum Houdini rounds (each round re-checks survivors).
const HOUDINI_PRUNE_MAX_ROUNDS: usize = 4;

impl PdrSolver {
    /// Prune the frame immediately after a startup strict-validation demotion
    /// and retry the direct safety check once (#4751 follow-up, gj2007_m_3).
    ///
    /// The end-of-startup prune at the bottom of `run_startup_discovery` is
    /// unreachable for budget-capped engines: after a demotion they burn the
    /// remaining window in the post-fixpoint bound floods / nonfixpoint tail
    /// and get cancelled first. gj2007_m_3 regressed exactly this way — a
    /// guard-slack step-difference candidate (`B <= G + 1`) admitted through
    /// the optimistic entry-domain oracle poisons the converged frame, every
    /// Safe claim demotes, and the solve never concludes. Pruning at the
    /// demotion point evicts the junk while the cheap convergence-shaped
    /// safety argument is still available.
    ///
    /// Cost control: skipped when frame[1] is unchanged since the last sweep
    /// (`houdini_pruned_frame1_len`), so repeated demotions do not repeat the
    /// per-lemma SMT sweep.
    ///
    /// Scope: ALL solves (#4751 L4). This was previously gated to
    /// budget-capped solves on the theory that unbounded solves "cannot be
    /// starved by the post-demotion tail". That rationale was falsified by
    /// pdr_bouncy_two_counters_equality_safe: an UNBOUNDED solve carried a
    /// poisoned 40+-lemma frame[1] into the main loop after a demotion, where
    /// single blocking queries took tens of seconds and the test harness'
    /// wall clock starved the solve anyway. Unbounded solves are starved by
    /// the OUTER wall clock even when no internal budget exists, so the
    /// demotion-point prune runs unconditionally.
    ///
    /// SOUNDNESS: the prune only REMOVES lemmas (weakening an
    /// over-approximating frame, always sound), the convergence snapshot is
    /// invalidated because the pruned frame is no longer the converged one,
    /// and the retried model still passes strict final validation inside
    /// `finish_safe_or_continue`.
    pub(in crate::pdr::solver) fn demotion_prune_and_retry(
        &mut self,
        stage: &'static str,
    ) -> Option<PdrResult> {
        let frame1_len = self.frames.get(1).map_or(0, |f| f.lemmas.len());
        if frame1_len == 0
            || self.houdini_pruned_frame1_len == Some(frame1_len)
            || self.is_cancelled()
        {
            return None;
        }
        let removed = self.houdini_prune_frame1_to_inductive_core();
        self.houdini_pruned_frame1_len = Some(self.frames.get(1).map_or(0, |f| f.lemmas.len()));
        if removed == 0 || self.is_cancelled() {
            return None;
        }
        // The convergence snapshot described the pre-prune frame; the
        // convergence_proven fast-path must not fire for the pruned one.
        self.startup_converged_frame1_len = None;
        let model = self.check_invariants_prove_safety()?;
        if self.config.verbose {
            safe_eprintln!(
                "PDR: {stage}: direct safety check produced a model on the pruned frame (#4751)"
            );
        }
        self.finish_safe_or_continue(model, stage)
    }

    /// Prune frame[1] to a relatively-inductive core. Returns removed count.
    pub(in crate::pdr::solver) fn houdini_prune_frame1_to_inductive_core(&mut self) -> usize {
        if self.frames.len() <= 1 {
            return 0;
        }
        let start = ay_core::time::Instant::now();
        let is_multi = self.problem.predicates().len() > 1;

        // Source predicates first: derived-predicate entry checks consult the
        // source frames, which should already be pruned by then.
        let mut predicates: Vec<_> = self.problem.predicates().to_vec();
        predicates.sort_by_key(|pred| (!self.predicate_has_facts(pred.id), pred.id.index()));

        let mut total_removed = 0usize;
        'rounds: for _round in 0..HOUDINI_PRUNE_MAX_ROUNDS {
            let mut removed_this_round = 0usize;
            for pred in &predicates {
                let canonical_vars = match self.canonical_vars(pred.id) {
                    Some(v) => v.to_vec(),
                    None => continue,
                };
                let lemmas: Vec<ChcExpr> = self.frames[1]
                    .lemmas
                    .iter()
                    .filter(|l| l.predicate == pred.id)
                    .map(|l| l.formula.clone())
                    .collect();
                for formula in lemmas {
                    if start.elapsed() >= HOUDINI_PRUNE_BUDGET || self.is_cancelled() {
                        break 'rounds;
                    }
                    let blocking = ChcExpr::not(formula.clone());
                    let init_ok = !self.predicate_has_facts(pred.id)
                        || self.blocks_initial_states(pred.id, &blocking);
                    let self_ok = init_ok
                        && self.is_chc_expr_preserved_by_transitions(
                            pred.id,
                            &formula,
                            &canonical_vars,
                        );
                    // #4751 L4 (cand4 hardening): check entry-inductiveness at
                    // level 2, i.e. against the SURVIVING frame[1] conjuncts of
                    // the predecessor predicates (global relative induction),
                    // NOT the level-1 check whose prev_level==0 context is the
                    // init-only must-summary. The init-only context is the
                    // strongest possible hypothesis, so poison like `a0 <= 0`
                    // (true at depth <= 1 only) survives it — observed on
                    // bouncy. Because source predicates are pruned first and
                    // the sweep iterates to a fixpoint, the surviving set is
                    // mutually relatively inductive (standard Houdini
                    // argument). Using the weaker frame[1] hypothesis can only
                    // remove MORE lemmas — removal is always sound.
                    let entry_ok =
                        self_ok && (!is_multi || self.is_entry_inductive(&formula, pred.id, 2));
                    if !(init_ok && self_ok && entry_ok) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: houdini-prune: dropping frame[1] lemma for pred {}: {} (init_ok={}, self_ok={}, entry_ok={}) (#4751)",
                                pred.id.index(),
                                formula,
                                init_ok,
                                self_ok,
                                entry_ok
                            );
                        }
                        removed_this_round += self.frames[1].remove_lemmas_where(|l| {
                            l.predicate == pred.id && l.formula == formula
                        });
                    }
                }
            }
            total_removed += removed_this_round;
            if removed_this_round == 0 {
                break;
            }
        }

        if self.config.verbose && total_removed > 0 {
            safe_eprintln!(
                "PDR: houdini-prune: removed {} non-inductive frame[1] lemmas in {:?} (#4751)",
                total_removed,
                start.elapsed()
            );
        }
        total_removed
    }
}
