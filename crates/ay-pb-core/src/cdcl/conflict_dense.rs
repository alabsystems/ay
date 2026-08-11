// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Allocation-free DenseCp-based conflict analysis for `PbCdclSolver`.
//!
//! The `dense_*` family implements RoundingSat-style conflict analysis over the
//! solver-owned dense buffers (proof logging off). Extracted from `cdcl.rs` to
//! keep the core solver module focused; these remain methods on
//! [`super::PbCdclSolver`].

use super::*;
use crate::cp_dense::{DenseCp, HeuristicResolveCapture, ProvenResolveCapture};
use crate::cutting_planes::negate_lit;
use crate::propagation::LitValue;
use crate::types::PbLit;

impl PbCdclSolver {
    /// Allocation-free DenseCp-based conflict analysis (proof logging OFF).
    ///
    /// Mirrors [`Self::analyze_conflict_with_stop`]'s `CpConstraint` path
    /// op-for-op, but reuses the solver-owned `dense_*` buffers across conflicts
    /// and uses O(1) var-indexed level lookups for falsified counts. The
    /// `#[cfg(debug_assertions)]` differential check at the end re-runs the
    /// trusted `CpConstraint` path side-effect-free and asserts both produce an
    /// identical learned constraint and backjump level.
    pub(super) fn analyze_conflict_dense<S>(
        &mut self,
        conflict_cid: usize,
        should_stop: &mut S,
    ) -> ConflictAnalysisOutcome
    where
        S: ConflictStop,
    {
        debug_assert!(
            self.proof_writer.is_none(),
            "dense fast path must only run with proof logging off"
        );

        self.last_analysis_proof_id = None;
        self.root_refutation_proof_id = None;

        // Move the reusable dense buffers into locals so the borrow checker can
        // see they are disjoint from the rest of `self` (constraint storage,
        // propagator, trail). `take` leaves cheap empty placeholders behind; the
        // buffers are restored before returning. No allocation occurs: the
        // buffers keep their backing capacity across conflicts.
        let mut learned = std::mem::take(&mut self.dense_learned);
        let mut reason = std::mem::take(&mut self.dense_reason);
        let mut scratch = std::mem::take(&mut self.dense_scratch);
        let mut reduced = std::mem::take(&mut self.dense_reduced);

        let outcome = self.analyze_conflict_dense_inner(
            conflict_cid,
            should_stop,
            &mut learned,
            &mut reason,
            &mut scratch,
            &mut reduced,
        );

        // Restore the buffers for reuse on the next conflict.
        self.dense_learned = learned;
        self.dense_reason = reason;
        self.dense_scratch = scratch;
        self.dense_reduced = reduced;

        // PROOF TAP: every exit that did not close the frame via FINAL_FRAME
        // (interrupt, fail-closed give-up, capture degradation) aborts it here
        // so the serializer discards the buffered pol expression. No-op when
        // the frame closed normally or no tap is installed.
        if self.proof_tap.is_some() {
            self.tap_abort_frame_if_open();
        }

        outcome
    }

    fn analyze_conflict_dense_inner<S>(
        &mut self,
        conflict_cid: usize,
        should_stop: &mut S,
        learned: &mut DenseCp,
        reason: &mut DenseCp,
        scratch: &mut DenseCp,
        reduced: &mut DenseCp,
    ) -> ConflictAnalysisOutcome
    where
        S: ConflictStop,
    {
        // Load the conflict constraint into the reusable learned buffer.
        let loaded = match self.constraint_by_index(conflict_cid) {
            Some(pb) => learned.load_from_pb(pb).is_ok(),
            None => false,
        };
        if !loaded {
            return ConflictAnalysisOutcome::Learned((0, None));
        }

        // The conflict constraint participated in this conflict: bump it if it is
        // a learned lemma (no-op for original constraints / when opt-in is off).
        self.bump_learned_activity(conflict_cid);

        if should_stop.should_stop(self) {
            return ConflictAnalysisOutcome::Interrupted;
        }

        // Initial saturation of the conflict constraint.
        learned.saturate();

        // Conflict-side activity bumping (RoundingSat `assignActiveSet`): seed the
        // active set with the conflicting constraint's literals. Heuristic-only.
        for (lit, coeff) in learned.iter_terms() {
            self.bump_activity_weighted(lit.var, coeff);
        }

        // Build the reusable var -> trail-position map for the trail-shrinking
        // asserting test. Positions index `self.trail`; a var not on the trail
        // (preprocessing-fixed at level 0) keeps the sentinel and is treated as
        // always-present at level 0.
        self.dense_rebuild_var_trail_pos();

        // PROOF TAP (spec capture point conflict_dense BEGIN_FRAME): open a
        // micro-op frame for this analysis. `tap_frame` gates every capture
        // below; the plain path pays only this `is_none` check.
        let mut tap_frame = self.proof_tap.is_some() && self.tap_begin_conflict_frame(conflict_cid);

        let mut round_to_one_count = 0u64;
        let mut round_to_one_fallback_count = 0u64;
        let mut proven_round_to_one_count = 0u64;
        let mut proven_round_to_one_fallback_count = 0u64;
        let mut reduce_to_cardinality_count = 0u64;

        // RoundingSat-style conflict analysis (Solver::analyze): walk the trail
        // from the top, maintaining a SHRINKING view of the trail (`trail_top`
        // marks the boundary; positions >= trail_top are treated as undone). At
        // every trail literal that participates in the running conflict, use the
        // SLACK-BASED asserting test (`isAssertingBefore`) against the trail
        // truncated to just below the current decision level to decide whether to
        // stop (asserting), backjump a whole level (still falsified below the last
        // decision), or keep resolving. This replaces the previous count-based
        // stop against a static trail snapshot, which produced ~99% non-asserting
        // lemmas that were discarded (backtrack-to-0 churn, no progress).
        let mut trail_top = self.trail.len();
        loop {
            // Effective current decision level = level of the top present trail
            // entry; 0 (root) ends the loop.
            if trail_top == 0 {
                break;
            }
            let top_entry = &self.trail[trail_top - 1];
            let eff_dl = top_entry.level;
            if eff_dl == 0 {
                break;
            }

            if should_stop.should_stop(self) {
                return ConflictAnalysisOutcome::Interrupted;
            }

            let trail_lit = top_entry.lit;
            let reason_opt = top_entry.reason;

            // Does the conflict contain the negation of this true trail literal?
            let falsified_lit = dimacs_to_pb_lit(-trail_lit);
            if learned.coefficient(falsified_lit) == 0 {
                // Non-participating literal: just undo it (shrink the trail).
                trail_top -= 1;
                continue;
            }

            // Slack-based asserting test against the trail truncated to the level
            // BELOW the current decision level (RoundingSat isAssertingBefore).
            match self.dense_assertion_status_before(learned, eff_dl, trail_top) {
                DenseAssertionStatus::Asserting => break,
                DenseAssertionStatus::Falsified => {
                    // Already falsified by assignments below the last decision of
                    // this level: backjump a whole level and continue (undo all
                    // entries at level >= eff_dl). RoundingSat backjumpTo(dl-1).
                    trail_top = self.trail_lim[eff_dl as usize - 1];
                    continue;
                }
                DenseAssertionStatus::NonAsserting => {}
            }

            let Some(reason_cid) = reason_opt else {
                // Participating decision literal reported NON-asserting. By the
                // loop invariant this should not occur (a participating decision
                // with all this level's propagations resolved/undone is asserting
                // or falsified, never non-asserting), but if it ever does we
                // cannot resolve a decision; stop the loop and let the
                // end-of-analysis slack-based assertion level / fail-closed gate
                // decide. Never resolves on a missing reason (sound).
                break;
            };

            // Load the reason into the reusable reason buffer.
            let reason_loaded = match self.constraint_by_index(reason_cid) {
                Some(pb) => reason.load_from_pb(pb).is_ok(),
                None => false,
            };
            if !reason_loaded {
                // Reason unavailable: cannot resolve; undo and continue. Sound
                // (never ships a non-implied lemma); the asserting gate handles
                // any non-asserting tail.
                trail_top -= 1;
                continue;
            }

            // This reason is about to be resolved into the learned constraint:
            // bump it if it is a learned lemma (no-op for original constraints /
            // when opt-in is off), and refresh its LBD (kept only if improved).
            self.bump_learned_activity(reason_cid);
            self.refresh_learned_lbd_on_reason_use(reason_cid);

            let pivot = dimacs_to_pb_lit(trail_lit);

            // Resolve `learned` with `reason` on `pivot`, writing the resolvent
            // into `scratch`. We try, in order: PROVEN round-to-one (Alg. 5/6;
            // reduces the reason before adding -> strongest/smallest), the
            // heuristic round-to-one, and the reduce-to-cardinality overflow
            // fallback. CRUCIAL TIGHTNESS INVARIANT (RoundingSat `genericResolve`
            // postcondition `assert(hasNegativeSlack(level))`): the resolvent MUST
            // remain FALSIFIED under the full trail — its RoundingSat slack (sum
            // of non-falsified coeffs − degree) must be strictly negative. A loose
            // (non-negative-slack) resolvent breaks the conflict-analysis loop
            // invariant and prevents the slack-based asserting test from
            // converging, so we REJECT any resolvent with slack >= 0 and fall
            // through to the next (tighter) variant. If none yields a falsified
            // resolvent we FAIL CLOSED (give up this analysis), never continuing
            // with a loose conflict and never shipping a non-implied lemma.
            // PROOF TAP: resolve the reason's proof id up front. A cid->pid
            // miss aborts the frame synchronously (spec: the ring never
            // carries constraint indexes); the analysis continues UNLOGGED and
            // the lemma degrades to the RUP fallback.
            let tap_reason_pid = if tap_frame {
                match self.proof_id_for_constraint(reason_cid) {
                    Some(pid) => Some(pid),
                    None => {
                        self.tap_abort_frame_if_open();
                        tap_frame = false;
                        None
                    }
                }
            } else {
                None
            };

            let mut accepted = false;

            let mut proven_capture = tap_frame.then(ProvenResolveCapture::default);
            if self
                .dense_resolve_proven(
                    scratch,
                    reduced,
                    learned,
                    reason,
                    pivot,
                    trail_top,
                    proven_capture.as_mut(),
                )
                .is_some()
                && scratch.rs_slack(|lit| self.dense_eff_false_level(lit, trail_top).is_some()) < 0
            {
                proven_round_to_one_count += 1;
                accepted = true;
                if let (Some(capture), Some(reason_pid)) = (proven_capture.take(), tap_reason_pid) {
                    tap_frame = self.tap_capture_proven(reason_pid, capture);
                }
            }

            if !accepted {
                proven_round_to_one_fallback_count += 1;
                let asserting_candidate =
                    self.dense_asserting_candidate_shrunk(learned, pivot, eff_dl, trail_top);
                let mut heuristic_capture = tap_frame.then(HeuristicResolveCapture::default);
                if let Some(used_division) = self.dense_resolve_round_to_one(
                    scratch,
                    learned,
                    reason,
                    pivot,
                    asserting_candidate,
                    eff_dl,
                    trail_top,
                    heuristic_capture.as_mut(),
                ) {
                    if scratch.rs_slack(|lit| self.dense_eff_false_level(lit, trail_top).is_some())
                        < 0
                    {
                        if used_division {
                            round_to_one_count += 1;
                        } else {
                            round_to_one_fallback_count += 1;
                        }
                        accepted = true;
                        if let (Some(capture), Some(reason_pid)) =
                            (heuristic_capture.take(), tap_reason_pid)
                        {
                            tap_frame = self.tap_capture_heuristic(reason_pid, capture);
                        }
                    }
                }
            }

            if !accepted
                && self
                    .dense_resolve_cardinality_fallback(scratch, learned, reason, pivot, trail_top)
                    .is_some()
            {
                // The cardinality fallback already verifies rs_slack < 0 (shrunk).
                reduce_to_cardinality_count += 1;
                accepted = true;
                // PROOF TAP: CARD_RESOLVE has no single-op pol mapping in this
                // phase — abort the frame; the lemma takes the RUP fallback.
                // The weaken-to-cardinality pol-subchain is a DOCUMENTED
                // contingency that stays unbuilt because the cert corpus never
                // reaches this path (unit/small coefficients never overflow the
                // i128 round-to-one), pinned by the chaos tripwire
                // cardinality_fallback_corpus_is_clean in tests/proof_tap_chaos.rs.
                if tap_frame {
                    self.tap_abort_frame_if_open();
                    tap_frame = false;
                }
            }

            if !accepted {
                // No resolution variant produced a falsified resolvent. Continuing
                // with a loose conflict would corrupt the analysis loop invariant;
                // fail closed (give up this analysis). Sound: never ships a lemma.
                return ConflictAnalysisOutcome::Learned((0, None));
            }

            // RoundingSat-style conflict-side activity bumping: bump the activity
            // of every variable that participated in this resolution step (the
            // reason's literals), not just the final lemma's. This focuses VSIDS
            // on the conflict region (RoundingSat `addUsedLitsToActiveSet` ->
            // `bumpLiteralActivity`). Bumping is heuristic-only — it never affects
            // soundness — but materially improves decision quality and reduces the
            // conflict count.
            for (lit, coeff) in reason.iter_terms() {
                self.bump_activity_weighted(lit.var, coeff);
            }

            std::mem::swap(learned, scratch);

            // ALWAYS-ON soundness invariant (debug builds): after each accepted
            // resolution step the running conflict must REMAIN falsified under the
            // SHRINKING-trail view — its RoundingSat slack must be strictly
            // negative. This is the loop invariant of cutting-planes conflict
            // analysis (RoundingSat `genericResolve` postcondition
            // `assert(hasNegativeSlack(level))`).
            #[cfg(debug_assertions)]
            {
                let rs_slack =
                    learned.rs_slack(|lit| self.dense_eff_false_level(lit, trail_top).is_some());
                debug_assert!(
                    rs_slack < 0,
                    "conflict-analysis resolvent not falsified after resolution \
                     (RoundingSat shrunk slack = {rs_slack} >= 0); pivot = {pivot:?}"
                );
            }

            // RoundingSat removeLastAssignment(): the pivot has been resolved out
            // of the conflict, so undo this trail literal and advance the
            // shrinking view to the next.
            trail_top -= 1;
        }

        self.stats.round_to_one_count += round_to_one_count;
        self.stats.round_to_one_fallback_count += round_to_one_fallback_count;
        self.stats.proven_round_to_one_count += proven_round_to_one_count;
        self.stats.proven_round_to_one_fallback_count += proven_round_to_one_fallback_count;
        self.stats.reduce_to_cardinality_count += reduce_to_cardinality_count;

        if should_stop.should_stop(self) {
            return ConflictAnalysisOutcome::Interrupted;
        }

        // Snapshot before strengthening for stats tracking.
        let pre_strengthen_size = learned.len();
        let pre_strengthen_degree = learned.degree();

        // Strengthening pipeline: saturate + GCD, then conservative weaken (only
        // when the constraint is NOT currently falsified) + re-saturate + GCD.
        // The applied GCDs and weakened literals feed the tap's FINAL_FRAME so
        // the pol replay derives EXACTLY the stored lemma (this also logs the
        // previously-unlogged weaken_conservative pipeline).
        learned.saturate();
        let final_gcd1 = learned
            .gcd_divide()
            .expect("final learned PB constraint must support GCD division");

        if should_stop.should_stop(self) {
            return ConflictAnalysisOutcome::Interrupted;
        }

        // RoundingSat parity: do NOT weaken a learned constraint that is still
        // FALSIFIED under the trail. RoundingSat's `heuristicWeakening` bails
        // immediately when `slack < 0` (ConstrExp.cpp), so the just-derived
        // conflict lemma — which is always falsified (RoundingSat slack < 0) at
        // this point — is learned UNWEAKENED. AY previously weakened it
        // unconditionally, discarding non-asserting literals that carry future
        // propagation strength; the resulting lemmas were dramatically weaker
        // than RoundingSat's, so CP-hard cardinality DEC-LIN instances (e.g.
        // rand6reg) needed orders of magnitude more conflicts and timed out.
        // Gating on slack restores the strong PB lemma. Weakening still runs for
        // the (rare) non-falsified case, preserving the size-reduction benefit
        // where it is sound to apply. Soundness is unaffected: skipping a
        // weakening only ever keeps the lemma STRONGER (still implied, still
        // falsified, still asserting when the resolution loop converged).
        let propagator = &self.propagator;
        let rs_slack =
            learned.rs_slack(|lit| propagator.value(pb_lit_to_dimacs(lit)) == LitValue::False);
        let mut final_weaken_ran = false;
        let mut final_weakened: Vec<PbLit> = Vec::new();
        let mut final_gcd2: i128 = 0;
        if rs_slack >= 0 {
            let asserting_lit = self.dense_unique_current_level_falsified(learned);
            self.dense_weaken_conservative(
                learned,
                asserting_lit,
                tap_frame.then_some(&mut final_weakened),
            );

            if should_stop.should_stop(self) {
                return ConflictAnalysisOutcome::Interrupted;
            }

            learned.saturate();
            final_gcd2 = learned
                .gcd_divide()
                .expect("post-weakening GCD division must succeed");
            final_weaken_ran = true;
        }

        if should_stop.should_stop(self) {
            return ConflictAnalysisOutcome::Interrupted;
        }

        if learned.len() < pre_strengthen_size || learned.degree() < pre_strengthen_degree {
            self.stats.strengthened += 1;
        }

        // SLACK-BASED ASSERTION LEVEL (RoundingSat getAssertionLevel). The
        // trail-shrinking analysis loop above stops as soon as the running
        // conflict becomes ASSERTING below the current decision level. Here we
        // compute the exact backjump (assertion) level: the lowest decision level
        // at which the learned constraint propagates a literal. This replaces the
        // previous count-based "unique current-level falsified literal" backjump,
        // which could only describe lemmas asserting at the current decision level
        // and otherwise gave up (Learned((0, None)) -> backtrack-to-0 churn).
        //
        // The learned lemma is, at this point, FALSIFIED under the full trail
        // (RoundingSat slack < 0) — the loop invariant of conflict analysis. The
        // assertion-level computation reads the untouched per-variable
        // levels/positions (the analysis loop never mutated the propagator or
        // trail; it walked a purely local shrinking view), so it is exact.
        //
        // Soundness / fail-closed: every resolution step produced an IMPLIED
        // constraint (proven round-to-one entailment + reduce-to-cardinality
        // entailment, both exhaustively property-tested; per-step rs_slack<0
        // debug invariant). If the assertion-level computation reports the lemma
        // never propagates (NonAsserting / INF) or that it would not move the
        // decision level (>= conflict level), we FAIL CLOSED -> Learned((0, None))
        // (give up this analysis; the caller restarts/treats as Unknown). This
        // never ships a non-asserting or non-implied lemma and never panics.
        if learned.is_empty() {
            // Empty conflict (no terms). A positive degree is the contradiction
            // `false` — a root refutation: backtrack to level 0 and hand the
            // empty `>= degree` constraint back so the caller adds it and ordinary
            // level-0 propagation reports UNSAT. (DenseCp drops terms only when
            // degree <= 0, so an empty positive-degree conflict is genuinely
            // contradictory; this is RoundingSat's getAssertionLevel == -1 path.)
            // A non-positive degree is trivially satisfied — not a real conflict —
            // so we fail closed. This path is how some UNSAT proofs conclude
            // (e.g. CP-hard cardinality DEC-LIN), so it must NOT be discarded.
            if learned.degree() > 0 {
                // PROOF TAP: this root refutation IS learned — close the
                // frame so the contradiction `>= degree` carries a proof id.
                if tap_frame {
                    self.tap_final_frame_store(
                        final_gcd1,
                        final_weaken_ran,
                        final_weakened,
                        final_gcd2,
                    );
                    // The frame's lemma_pid IS a checker-verified contradiction
                    // (`0 >= degree>0`): hand it to handle_unsat_proof so it
                    // concludes UNSAT directly on this chain id rather than
                    // emitting a redundant fresh `rup >= 1 ;`. Only set when a
                    // chain id is available (tap + degree>0); the legacy/no-tap
                    // path leaves it None and falls back.
                    self.root_refutation_proof_id = self.last_analysis_proof_id;
                }
                let learned_pb = learned.to_pb_constraint();
                return ConflictAnalysisOutcome::Learned((0, Some(learned_pb)));
            }
            return ConflictAnalysisOutcome::Learned((0, None));
        }

        let backtrack_level = match self.dense_get_assertion_level(learned) {
            DenseAssertionLevel::Root => 0,
            DenseAssertionLevel::Level(level) if level < self.decision_level => level,
            // NonAsserting (INF) or a level that would not move the search:
            // fail closed.
            _ => {
                return ConflictAnalysisOutcome::Learned((0, None));
            }
        };

        // SOUNDNESS GATES (debug builds):
        // (a) the learned lemma is falsified at the conflict (current) level;
        // (b) backjumping to `backtrack_level` and adding the lemma makes it
        //     propagate — i.e. it is NOT falsified there and DOES become unit
        //     (its slack at that level is in [0, largestActiveCoef)).
        #[cfg(debug_assertions)]
        {
            let propagator = &self.propagator;
            let conflict_slack =
                learned.rs_slack(|lit| propagator.value(pb_lit_to_dimacs(lit)) == LitValue::False);
            debug_assert!(
                conflict_slack < 0,
                "learned lemma not falsified at conflict level (rs_slack = {conflict_slack} >= 0)"
            );
            debug_assert!(
                self.dense_lemma_propagates_after_backjump(learned, backtrack_level),
                "learned lemma does not propagate after backjump to level {backtrack_level}"
            );
        }

        // Activity for the conflict region was already bumped per resolution step
        // (RoundingSat actSet). Decay once per analysis (RoundingSat
        // `vDecayActivity` after `bumpLiteralActivity`).
        self.decay_activity();
        self.decay_learned_activity();

        // PROOF TAP: the lemma will be stored — close the frame (allocating
        // its proof id into `last_analysis_proof_id`).
        if tap_frame {
            self.tap_final_frame_store(final_gcd1, final_weaken_ran, final_weakened, final_gcd2);
        }

        let learned_pb = learned.to_pb_constraint();

        ConflictAnalysisOutcome::Learned((backtrack_level, Some(learned_pb)))
    }

    /// Resolves `learned` with `reason` on `pivot` using round-to-one, writing
    /// the resolvent into `scratch`. Mirrors
    /// [`Self::resolve_round_to_one_with_proof`] arithmetic exactly (minus proof
    /// logging). Returns `Some(used_division)` on success, `None` when the pivot
    /// is absent in the expected polarity or arithmetic overflows.
    #[allow(clippy::too_many_arguments)]
    fn dense_resolve_round_to_one(
        &self,
        scratch: &mut DenseCp,
        learned: &DenseCp,
        reason: &DenseCp,
        pivot: PbLit,
        asserting_lit: Option<PbLit>,
        eff_dl: u32,
        trail_top: usize,
        mut capture: Option<&mut HeuristicResolveCapture>,
    ) -> Option<bool> {
        // Build the (saturated) resolvent into `scratch`.
        dense_build_resolvent(scratch, learned, reason, pivot, capture.as_deref_mut())?;

        // Round-to-one division on the asserting literal, falling back to the
        // actual resolvent's unique current-level falsified literal under the
        // SHRINKING-trail view when the pre-resolution candidate's coefficient is
        // not > 1.
        let mut used_division = false;
        let division_lit = match asserting_lit {
            Some(alit) if scratch.coefficient(alit) > 1 => Some(alit),
            _ => self.dense_unique_level_falsified_shrunk(scratch, eff_dl, trail_top),
        };
        if let Some(alit) = division_lit {
            let a_coeff = scratch.coefficient(alit);
            if a_coeff > 1 && scratch.divide(a_coeff).is_ok() {
                used_division = true;
                scratch.saturate();
                if let Some(cap) = capture {
                    cap.div = Some(a_coeff);
                }
            }
        }

        Some(used_division)
    }

    /// Unique literal falsified at `eff_dl` under the shrinking-trail view, or
    /// `None` if there is not exactly one. Shrunk-view companion to
    /// [`Self::dense_unique_current_level_falsified`].
    fn dense_unique_level_falsified_shrunk(
        &self,
        constraint: &DenseCp,
        eff_dl: u32,
        trail_top: usize,
    ) -> Option<PbLit> {
        let mut found = None;
        for (lit, _) in constraint.iter_terms() {
            if self.dense_eff_false_level(lit, trail_top) != Some(eff_dl) {
                continue;
            }
            if found.is_some() {
                return None;
            }
            found = Some(lit);
        }
        found
    }

    /// The unique non-pivot literal that would be falsified at `eff_dl` after
    /// resolving on `pivot`, evaluated under the shrinking-trail view (positions
    /// `>= trail_top` undone). Used to pick the round-to-one division literal in
    /// the heuristic resolution fallback.
    fn dense_asserting_candidate_shrunk(
        &self,
        constraint: &DenseCp,
        pivot: PbLit,
        eff_dl: u32,
        trail_top: usize,
    ) -> Option<PbLit> {
        let mut candidate = None;
        let mut count = 0;
        for (lit, _) in constraint.iter_terms() {
            if lit.var == pivot.var {
                continue;
            }
            if self.dense_eff_false_level(lit, trail_top) != Some(eff_dl) {
                continue;
            }
            count += 1;
            if count > 1 {
                return None;
            }
            candidate = Some(lit);
        }
        candidate
    }

    /// PROVEN round-to-one resolution step (Elffers & Nordstrom, IJCAI-18,
    /// Alg. 5/6; RoundingSat/Exact). Resolves `learned` (the running conflict,
    /// carrying `~pivot`) with `reason` (which propagated `pivot` true) on
    /// `pivot`, writing the resolvent into `scratch`. Unlike the heuristic
    /// [`Self::dense_resolve_round_to_one`], it REDUCES THE REASON before adding
    /// (weaken non-falsified literals, then divide so the pivot coefficient is
    /// 1), yielding stronger, smaller learned constraints.
    ///
    /// Returns `Some(())` on success (`scratch` holds the saturated proven
    /// resolvent). Returns `None` on invalid pivot or arithmetic overflow; the
    /// caller MUST then fall back to the sound heuristic path — never panic,
    /// never ship a non-implied lemma. On `None` the callee has already CLEARED
    /// `scratch`, so no partial resolvent can leak into the fallback.
    #[allow(clippy::too_many_arguments)]
    fn dense_resolve_proven(
        &self,
        scratch: &mut DenseCp,
        reduced: &mut DenseCp,
        learned: &DenseCp,
        reason: &DenseCp,
        pivot: PbLit,
        trail_top: usize,
        capture: Option<&mut ProvenResolveCapture>,
    ) -> Option<()> {
        // Falsification is evaluated under the SHRINKING-trail view (positions
        // >= trail_top undone), exactly like RoundingSat's `Level` array during
        // analyze. Weakening non-falsified literals is always sound regardless of
        // which literals are considered falsified, so this preserves the proven
        // round-to-one entailment (C ∧ R ⊨ resolvent) while keeping the resolvent
        // tight under the shrunk trail (the loop invariant the asserting test
        // relies on).
        let falsified_fn = |lit: PbLit| self.dense_eff_false_level(lit, trail_top).is_some();
        // The resolvent is written DIRECTLY into `scratch`, and `reduced` is the
        // reason's working space. Both keep their backing capacity across steps.
        // This used to be `*scratch = resolvent`, which dropped `scratch`'s warm
        // buffers every step and replaced them with freshly allocated ones —
        // defeating the reuse the surrounding `mem::take` dance exists to
        // provide, and contradicting this module's own "no allocation occurs"
        // claim.
        let result = match capture {
            Some(cap) => learned.resolve_proven_round_to_one_captured_into(
                scratch,
                reduced,
                reason,
                pivot,
                falsified_fn,
                cap,
            ),
            None => learned.resolve_proven_round_to_one_into(
                scratch,
                reduced,
                reason,
                pivot,
                falsified_fn,
            ),
        };
        result.ok()
    }

    /// OVERFLOW FALLBACK for conflict analysis (RoundingSat `reduceToCardinality`,
    /// Elffers & Nordstrom IJCAI-18 Alg. 6 lines 9-10).
    ///
    /// Used ONLY when both the proven and heuristic round-to-one resolutions
    /// would overflow i128. Reduces the running conflict `learned` and the
    /// `reason` to their IMPLIED unit-coefficient cardinality constraints, then
    /// resolves those into `scratch` via plain PB resolution. Because both
    /// operands have unit coefficients, the resolution arithmetic is bounded by
    /// the number of literals and cannot overflow i128 — the entire point of the
    /// fallback.
    ///
    /// SOUNDNESS. [`DenseCp::reduce_to_cardinality`] yields a constraint implied
    /// by its input (proof there); plain PB resolution preserves implication, so
    /// the resolvent is implied by `learned_card ∧ reason_card`, which are
    /// implied by `learned ∧ reason`, hence by the originals. The fallback NEVER
    /// ships a non-implied lemma. (Entailment of the reduction itself is verified
    /// exhaustively by `reduce_to_cardinality_semantic_entailment`.)
    ///
    /// CONFLICT-DRIVEN GATE. `reduce_to_cardinality` is a WEAKENING and does not
    /// in general preserve the falsified-under-trail property, so we VERIFY the
    /// resolvent's RoundingSat slack (sum of non-falsified coefficients − degree)
    /// is strictly negative before accepting it. If it is not — the reduction was
    /// too weak to keep this a conflict — we FAIL CLOSED (`None`); the caller
    /// then keeps its existing safe behaviour (skip this trail literal). A
    /// non-asserting final result is additionally caught by the end-of-analysis
    /// asserting gate, which fails the whole analysis closed (no lemma learned).
    ///
    /// Returns `Some(())` on success (`scratch` holds the falsified cardinality
    /// resolvent) and `None` otherwise (invalid pivot or a non-falsified result).
    fn dense_resolve_cardinality_fallback(
        &self,
        scratch: &mut DenseCp,
        learned: &DenseCp,
        reason: &DenseCp,
        pivot: PbLit,
        trail_top: usize,
    ) -> Option<()> {
        // Reduce both operands to their implied unit-coefficient cardinality.
        let learned_card = learned.reduce_to_cardinality()?;
        let reason_card = reason.reduce_to_cardinality()?;

        // The pivot must still be present in the expected polarities after the
        // reduction; otherwise resolution is not defined and we fail closed.
        let negated_pivot = negate_lit(pivot);
        let pivot_present = (learned_card.coefficient(pivot) > 0
            && reason_card.coefficient(negated_pivot) > 0)
            || (learned_card.coefficient(negated_pivot) > 0 && reason_card.coefficient(pivot) > 0);
        if !pivot_present {
            return None;
        }

        // Plain PB resolution of the two cardinality constraints. With unit
        // coefficients this cannot overflow for any realistic literal count.
        // (No tap capture: CARD_RESOLVE aborts the frame in this phase.)
        dense_build_resolvent(scratch, &learned_card, &reason_card, pivot, None)?;

        // CONFLICT-DRIVEN GATE: the resolvent must remain falsified under the
        // SHRINKING-trail view (RoundingSat slack < 0). Fail closed otherwise.
        let rs_slack = scratch.rs_slack(|lit| self.dense_eff_false_level(lit, trail_top).is_some());
        if rs_slack >= 0 {
            return None;
        }

        Some(())
    }

    /// O(1) replacement for [`Self::false_literal_level`] using the propagator's
    /// var-indexed value/decision-level arrays. Equivalent to the trusted helper:
    /// every trail/fixed assignment is mirrored in the propagator at the same
    /// level (validated by the differential check).
    fn false_literal_level_fast(&self, lit: PbLit) -> Option<u32> {
        let dimacs = pb_lit_to_dimacs(lit);
        if self.propagator.value(dimacs) != LitValue::False {
            return None;
        }
        self.propagator.decision_level(dimacs)
    }

    /// Rebuilds the reusable var -> trail-position map for the trail-shrinking
    /// asserting test. Entry `usize::MAX` marks a variable not on the trail
    /// (unassigned, or preprocessing-fixed at level 0). Grows the buffer to cover
    /// the current variable count (runtime var-pool growth) without shrinking it.
    fn dense_rebuild_var_trail_pos(&mut self) {
        let needed = self.num_vars as usize + 1;
        if self.dense_var_trail_pos.len() < needed {
            self.dense_var_trail_pos.resize(needed, usize::MAX);
        }
        // Only entries written last conflict can be stale; reset every var that
        // is currently on the trail's complement. Resetting the whole map is O(V)
        // but simple and robust; the trail walk then overwrites live vars. Since
        // conflict analysis is already O(trail) per conflict and V is comparable,
        // this is not a hotspot regression.
        for slot in self.dense_var_trail_pos.iter_mut() {
            *slot = usize::MAX;
        }
        for (pos, entry) in self.trail.iter().enumerate() {
            let var = entry.lit.unsigned_abs() as usize;
            if var < self.dense_var_trail_pos.len() {
                self.dense_var_trail_pos[var] = pos;
            }
        }
    }

    /// Effective falsified level of `lit` under the shrinking-trail view
    /// (positions `>= trail_top` treated as undone). Returns the level at which
    /// `lit` is falsified, or `None` if it is not falsified in the shrunk view.
    /// Preprocessing-fixed literals (not on the trail) are always present at
    /// level 0. Mirrors RoundingSat `level[-l]`.
    #[inline]
    fn dense_eff_false_level(&self, lit: PbLit, trail_top: usize) -> Option<u32> {
        if self.propagator.value(pb_lit_to_dimacs(lit)) != LitValue::False {
            return None;
        }
        let pos = self.dense_var_trail_pos[lit.var as usize];
        if pos == usize::MAX {
            // Fixed at level 0, always present.
            Some(0)
        } else if pos < trail_top {
            Some(self.trail[pos].level)
        } else {
            // Undone by the shrinking view -> unassigned.
            None
        }
    }

    /// Effective true level of `lit` under the shrinking-trail view, or `None` if
    /// `lit` is not true in the shrunk view. Mirrors RoundingSat `level[l]`.
    #[inline]
    fn dense_eff_true_level(&self, lit: PbLit, trail_top: usize) -> Option<u32> {
        if self.propagator.value(pb_lit_to_dimacs(lit)) != LitValue::True {
            return None;
        }
        let pos = self.dense_var_trail_pos[lit.var as usize];
        if pos == usize::MAX {
            Some(0)
        } else if pos < trail_top {
            Some(self.trail[pos].level)
        } else {
            None
        }
    }

    /// Trail-shrinking slack-based asserting test — RoundingSat
    /// `ConstrExp::isAssertingBefore(Level, lvl)`. Reports the state of
    /// `constraint` as if every assignment at decision level `>= lvl` were undone
    /// (i.e. after backjumping to `lvl - 1`), using the shrinking-trail view
    /// bounded by `trail_top`:
    /// - `NonAsserting`: slack >= largest active coefficient (still loose).
    /// - `Asserting`: 0 <= slack < largest active coefficient (would propagate).
    /// - `Falsified`: slack < 0 (still conflicting below the last decision).
    ///
    /// "slack" here is RoundingSat's: `sum of coefficients of literals NOT
    /// falsified-below-lvl − degree`. "largest active coefficient" is the largest
    /// coefficient among literals that are not solidly TRUE below `lvl` (the
    /// would-be-unit candidates).
    fn dense_assertion_status_before(
        &self,
        constraint: &DenseCp,
        lvl: u32,
        trail_top: usize,
    ) -> DenseAssertionStatus {
        let degree = constraint.degree();
        let mut slack: i128 = -degree;
        let mut largest_coef: i128 = 0;
        for (lit, coeff) in constraint.iter_terms() {
            // Skip literals falsified solidly below `lvl` (they stay falsified
            // after backjumping to lvl-1 and contribute nothing to slack).
            if let Some(false_level) = self.dense_eff_false_level(lit, trail_top) {
                if false_level < lvl {
                    continue;
                }
            }
            // The literal is a would-be-unit candidate unless it is solidly TRUE
            // below `lvl` (already satisfied after backjump).
            let solidly_true_below = matches!(
                self.dense_eff_true_level(lit, trail_top),
                Some(true_level) if true_level < lvl
            );
            if !solidly_true_below {
                largest_coef = largest_coef.max(coeff);
            }
            slack += coeff;
            if slack >= degree {
                return DenseAssertionStatus::NonAsserting;
            }
        }
        if slack >= largest_coef {
            DenseAssertionStatus::NonAsserting
        } else if slack >= 0 {
            DenseAssertionStatus::Asserting
        } else {
            DenseAssertionStatus::Falsified
        }
    }

    /// Slack-based assertion (backjump) level — RoundingSat
    /// `ConstrExp::getAssertionLevel(Level, Pos)`. Returns the lowest decision
    /// level at which `constraint` propagates a literal, using the FULL,
    /// untouched per-variable levels/positions (the analysis loop only walked a
    /// local shrinking view; it never mutated the propagator or trail).
    ///
    /// Returns:
    /// - `Root` when the constraint is already conflicting at level 0,
    /// - `Level(l)` when it propagates a literal at level `l` after backjumping,
    /// - `NonAsserting` when it never propagates (RoundingSat `INF`).
    fn dense_get_assertion_level(&self, constraint: &DenseCp) -> DenseAssertionLevel {
        let degree = constraint.degree();
        // Slack at level 0: sum of all (positive) coefficients minus degree.
        // (DenseCp keeps all coefficients positive after normalization.) This is
        // the "no literal falsified" slack; rising decision levels falsify
        // literals and lower it.
        // Sum of all (positive) coefficients. On i128 overflow the exact level-0
        // slack is unrepresentable; fall back to the conservative `Root` assertion
        // level (a safe full backjump) rather than computing a wrong slack from a
        // wrapped sum — this keeps conflict analysis SOUND on large-coefficient
        // instances (the reduceToCardinality overflow fallback).
        let Some(total) = constraint
            .iter_terms()
            .try_fold(0i128, |acc, (_, c)| acc.checked_add(c))
        else {
            // Coefficient sum overflows i128: the exact assertion level is
            // unrepresentable. Report NonAsserting so the caller fails CLOSED
            // (learns nothing from this conflict) instead of risking a wrong
            // backjump level — keeps conflict analysis sound on large-coefficient
            // instances (the reduceToCardinality overflow fallback).
            return DenseAssertionLevel::NonAsserting;
        };
        let mut slack: i128 = total - degree;
        if slack < 0 {
            return DenseAssertionLevel::Root;
        }

        // Falsified literals, ordered by the decision level at which they were
        // falsified (ascending). Each entry contributes its coefficient to the
        // slack until the simulated level rises past its falsification level, at
        // which point its coefficient is subtracted.
        let mut falsified_by_level: Vec<(u32, i128)> = constraint
            .iter_terms()
            .filter_map(|(lit, coeff)| {
                self.false_literal_level_fast(lit)
                    .map(|level| (level, coeff))
            })
            .collect();
        falsified_by_level.sort_by_key(|&(level, _)| level);

        // Would-be-unit candidates: literals together with the decision level at
        // which they become ASSIGNED (true OR false), `None` if always unassigned.
        // A literal is a unit candidate at a simulated level only while it is
        // still unassigned there (assigned_level > simulated level). Sorted by
        // decreasing coefficient so the first non-skipped entry is the largest
        // candidate coefficient — the one that propagates first when slack drops
        // below it. (This is the crucial correction over a true-only skip: a
        // literal FALSIFIED at a low level is NOT a unit candidate and must be
        // skipped too, otherwise the candidate coefficient is overestimated and
        // the reported assertion level is wrong.)
        let mut active: Vec<(i128, Option<u32>)> = constraint
            .iter_terms()
            .map(|(lit, coeff)| {
                let assigned_level = match (
                    self.true_literal_level_fast(lit),
                    self.false_literal_level_fast(lit),
                ) {
                    (Some(t), _) => Some(t),
                    (None, Some(f)) => Some(f),
                    (None, None) => None,
                };
                (coeff, assigned_level)
            })
            .collect();
        active.sort_by_key(|entry| std::cmp::Reverse(entry.0));

        let mut pos_it = 0usize;
        let mut coef_it = 0usize;
        let mut assertion_level: u32 = 0;
        loop {
            // Subtract contributions of all literals falsified at <= assertion_level.
            while pos_it < falsified_by_level.len()
                && falsified_by_level[pos_it].0 <= assertion_level
            {
                slack -= falsified_by_level[pos_it].1;
                pos_it += 1;
            }
            if slack < 0 {
                return if assertion_level == 0 {
                    DenseAssertionLevel::Root
                } else {
                    DenseAssertionLevel::Level(assertion_level - 1)
                };
            }
            // Skip literals already assigned (true or false) at <= assertion_level
            // — they are not unassigned unit candidates at this simulated level.
            while coef_it < active.len()
                && active[coef_it].1.is_some_and(|al| al <= assertion_level)
            {
                coef_it += 1;
            }
            if coef_it >= active.len() {
                return DenseAssertionLevel::NonAsserting;
            }
            if slack < active[coef_it].0 {
                return DenseAssertionLevel::Level(assertion_level);
            }
            if pos_it >= falsified_by_level.len() {
                // Slack will no longer decrease, so no propagation will ever
                // happen at a higher level.
                return DenseAssertionLevel::NonAsserting;
            }
            assertion_level = falsified_by_level[pos_it].0;
        }
    }

    /// True level of `lit` under the full trail, or `None` if not true.
    /// Companion to [`Self::false_literal_level_fast`] (mirrors `level[l]`).
    #[inline]
    fn true_literal_level_fast(&self, lit: PbLit) -> Option<u32> {
        let dimacs = pb_lit_to_dimacs(lit);
        if self.propagator.value(dimacs) != LitValue::True {
            return None;
        }
        self.propagator.decision_level(dimacs)
    }

    /// Debug-only verification that the learned lemma, after backjumping to
    /// `backjump_level`, is NOT falsified there and DOES propagate (becomes unit)
    /// — the asserting contract. Computes the lemma's slack under the trail
    /// truncated to `backjump_level` and checks `0 <= slack < largest active
    /// coefficient` (or root-conflict at level 0).
    #[cfg(debug_assertions)]
    fn dense_lemma_propagates_after_backjump(
        &self,
        constraint: &DenseCp,
        backjump_level: u32,
    ) -> bool {
        let degree = constraint.degree();
        let mut slack: i128 = -degree;
        let mut largest_coef: i128 = 0;
        for (lit, coeff) in constraint.iter_terms() {
            // A literal stays falsified after backjump iff it is falsified at a
            // level <= backjump_level.
            let stays_false = matches!(
                self.false_literal_level_fast(lit),
                Some(level) if level <= backjump_level
            );
            if stays_false {
                continue;
            }
            // A literal stays true after backjump iff it is true at a level
            // <= backjump_level (already satisfied -> not a unit candidate).
            let stays_true = matches!(
                self.true_literal_level_fast(lit),
                Some(level) if level <= backjump_level
            );
            if !stays_true {
                largest_coef = largest_coef.max(coeff);
            }
            slack += coeff;
        }
        // Asserting: slack in [0, largest_coef). (At level 0 a root-conflict
        // slack<0 is also acceptable: it drives UNSAT via a level-0 conflict.)
        if backjump_level == 0 && slack < 0 {
            return true;
        }
        slack >= 0 && slack < largest_coef
    }

    fn dense_unique_current_level_falsified(&self, constraint: &DenseCp) -> Option<PbLit> {
        let mut asserting_lit = None;
        for (lit, _) in constraint.iter_terms() {
            if self.false_literal_level_fast(lit) != Some(self.decision_level) {
                continue;
            }
            if asserting_lit.is_some() {
                return None;
            }
            asserting_lit = Some(lit);
        }
        asserting_lit
    }

    /// Conservative weakening of `constraint`, mirroring the trusted path's
    /// `weaken_conservative` closure EXACTLY.
    ///
    /// The trusted closure (in `analyze_conflict_with_stop`) returns the level of
    /// a falsified literal looked up from the TRAIL ONLY — preprocessing-fixed
    /// literals are not on the trail, so the trusted closure returns `None` for
    /// them even though they are falsified at level 0. We reproduce that exact
    /// behavior here (using a reusable trail-level buffer, no per-conflict
    /// allocation) so the remaining-falsified-coefficient sum is identical. Note
    /// this differs from `false_literal_level_fast` (which mirrors the
    /// fixed→level-0 behavior of `level_of_var` used by the count/asserting/
    /// backtrack helpers); the trusted code is itself asymmetric here.
    fn dense_weaken_conservative(
        &mut self,
        constraint: &mut DenseCp,
        asserting_lit: Option<PbLit>,
        removed: Option<&mut Vec<PbLit>>,
    ) {
        // Rebuild the reusable trail-level buffer: var -> level for vars on the
        // trail. `clear()` preserves capacity, so steady-state is allocation-free.
        self.dense_trail_levels.clear();
        for entry in &self.trail {
            self.dense_trail_levels
                .push((entry.lit.unsigned_abs(), entry.level));
        }

        let propagator = &self.propagator;
        let trail_levels = &self.dense_trail_levels;
        constraint.weaken_conservative_captured(
            asserting_lit,
            |lit| {
                let dimacs = pb_lit_to_dimacs(lit);
                if propagator.value(dimacs) != LitValue::False {
                    return None;
                }
                // Trail-only level lookup (last matching entry == the var's single
                // trail level); `None` for fixed literals not on the trail.
                trail_levels
                    .iter()
                    .rev()
                    .find(|(var, _)| *var == lit.var)
                    .map(|(_, level)| *level)
            },
            removed,
        );
    }
}
