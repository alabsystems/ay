// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Abandon/commit bracket for the speculative `try_solve_dt_lazy` lane
//! (#dt-lazy-abandon-restore).
//!
//! # Why this module exists
//!
//! `try_solve_dt_lazy` is SPECULATIVE: it materializes scratch terms
//! (flatten/lift rewrites, the depth-1 selector-axiom slice, guarded-acyclicity
//! units, projection and domain-closure atoms, plus everything the inner solve
//! mints) and, if the attempt does not decide, hands the query back to the
//! eager lane as if the lane had never run. That handback is only honest if
//! the scratch material is GONE — otherwise the eager lane's whole-store
//! scanning miners axiomatize over leftover scaffolding and its models are
//! degraded to `unknown`.
//!
//! # The regression this guards against
//!
//! * `bd02cac11` localized the failure to the old `rollback_on_fallback`
//!   guard:
//!   ```ignore
//!   if this.produce_proofs_enabled()
//!       && this.proof_tracker.num_steps() != entry_proof_steps { return; }
//!   ```
//! * `66538b006f` made `proof_tracker.enable()` UNCONDITIONAL, so
//!   `produce_proofs_enabled()` became true on `--z3-mode` — the competition
//!   path. The guard therefore fired on every abandoned attempt that recorded
//!   a single proof step, and the rollback stopped happening.
//! * MEASURED cost on SQ QF_Datatypes: **394 solved -> 198 solved** (107
//!   `sat -> unknown`, 89 `unsat -> unknown`, 0 soundness flips), and 27.8x
//!   more CPU on the instances that survived; 99 answers on MV QF_Datatypes.
//!
//! # Why the guard could not simply be deleted
//!
//! `0f4f82337` recorded the hazard: [`ay_core::TermStore::rollback_to`]'s
//! contract is *"the caller must guarantee that NO `TermId >= checkpoint.len`
//! is retained anywhere — not in assertions, models, caches, proof trackers,
//! or theory state"*, and there is no debug assertion that catches a
//! violation. The proof tracker holds `TermId`s. Rolling the store back under
//! a live proof yields a proof about a different formula — silent aliasing,
//! not a loud failure.
//!
//! # What was measured, per lane
//!
//! * `67c8bea8e` (2026-08-05, `try_solve_dt_lazy`): re-keying THIS lane's
//!   guard to `user_requested_proofs` passed every hand-check and failed 92
//!   suite tests (interpolation, VERIFICATION_CONSUMER reduction and UNSAT certification
//!   read tracker steps that then referenced rolled-back ids). `444c2d6e6`
//!   measured the other end — dropping the unconditional `enable()` — at 795
//!   failures. Both findings apply to this lane and motivate the
//!   snapshot/restore design below rather than any re-keyed predicate.
//! * `71ab33c05` (2026-08-08, `try_solve_dt_lazy`): removed this lane's guard
//!   outright, clearing the attempt's one-shot emission certificates alongside
//!   its model so the rollback is self-consistent; measured IDENTICAL suite
//!   failure sets (38/38) and the MV reproducer `unknown -> sat`. It records
//!   that REMOVING the sibling `try_solve_dt_auflia_lazy` guard regresses
//!   FP/BV/NRA (14 FP failures).
//! * `15252d939` (2026-08-08, `try_solve_dt_auflia_lazy`): NARROWED the
//!   sibling lane's guard to `is_producing_proofs()` (user-requested proof
//!   output only) instead of removing it; measured 9016 passed / 37 failed
//!   against a same-day 9015 / 36 baseline with the single delta a known-flaky
//!   deadline test, the feared 14 FP failures absent, and the SQ reproducer
//!   `vlsat3_h91` back to `sat`. That lane KEEPS its narrowed guard and is
//!   deliberately NOT bracketed by this module.
//!
//! # What this module does
//!
//! Bracket the attempt in one affine transaction. At entry it takes every
//! snapshot the lane's rollback needs — the bounded proof-ledger checkpoint,
//! the term-store checkpoint, [`DtLazyProofState`], [`DtLazyAttemptState`],
//! the LIA probe state, the entry assertion window — and additionally pushes a
//! proof-tracker SPECULATIVE SCOPE, exactly as the UFLIA lazy detour does
//! (#detour-snapshot-extend). On the abandon path the scope is unwound first
//! (truncating every step, assumption-map and lemma-dedup entry the attempt
//! recorded), then the ledger checkpoint restores the exact entry prefix; on a
//! definitive verdict `commit_speculative_scope()` keeps the steps.
//!
//! The proof tracker was never the only holder: `6a55b4605` audited the old
//! rollback as *"restores 8 fields and misses at least 5"*. The bracket
//! restores every `TermId`-bearing executor field the attempt can dirty
//! (including `w7_defs` / `w7_int_defs` / `self_check_authored_assertions`,
//! which [`DtLazyAttemptState`] does not carry), resets the term-store-indexed
//! caches and their high-water marks (which alias silently after ids are
//! RECYCLED, without ever observing a shrink), and then applies a FAIL-SAFE:
//! the term-store rollback itself is skipped — everything else still restored
//! — whenever a holder this module cannot restore might have captured a
//! post-watermark id.

use super::lazy_proof_state::DtLazyProofState;
use super::{DtLazyAttemptState, Executor};
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermStoreRollbackCheckpoint;
use ay_core::TermId;

use crate::proof_tracker::ProofTrackerCheckpoint;

/// Entry snapshot of everything a `try_solve_dt_lazy` attempt can dirty, plus
/// the proof-tracker and term-store watermarks.
///
/// Captured by [`Executor::dt_lazy_capture_entry_state`], consumed by exactly
/// one of [`Executor::dt_lazy_discard_attempt`] /
/// [`Executor::dt_lazy_commit_attempt`]. Both consume the snapshot by value so
/// the entry ledgers are MOVED back rather than cloned after the inner solve
/// may have grown the corresponding structures, and a second close is a type
/// error rather than a stale-checkpoint panic.
pub(super) struct DtLazyEntryState {
    /// Entry assertion window; restored on abandon so the eager lane mines the
    /// ORIGINAL shapes (its pre-lift snapshot must not see an already-lifted
    /// list or the fuzz881 acyclicity units are lost).
    assertions: Vec<TermId>,
    /// `dt_pre_lift_assertions` at entry, taken (not cloned) so the lane's own
    /// pre-lift snapshot starts empty.
    pre_lift: Vec<TermId>,
    /// Term-store length at entry (trace only).
    terms_len: usize,
    /// Term-store rollback checkpoint (#dt-lazy-isolation).
    terms_checkpoint: TermStoreRollbackCheckpoint,
    /// Bounded proof-ledger checkpoint. Restoring it is what makes the store
    /// rollback legal under mandatory proof tracking: the exact entry prefix
    /// of steps, assumption/lemma/name maps and scope stack comes back, so no
    /// live step references a recycled id.
    proof_checkpoint: ProofTrackerCheckpoint,
    /// Proof-step count at entry. Used only as the fail-safe's post-condition
    /// check: after the scope unwind, the tracker must be back at or below it.
    proof_steps: usize,
    /// Proof-tracker scope-stack depth at entry (see
    /// [`crate::proof_tracker::ProofTracker::scope_depth`]).
    proof_scope_depth: usize,
    /// `true` when `quantifier_manager` was already `Some` at entry — see the
    /// fail-safe in [`Executor::dt_lazy_discard_attempt`].
    had_quantifier_manager: bool,
    lazy_proof_state: DtLazyProofState,
    attempt_state: DtLazyAttemptState,
    lia_probe_state: ay_lia::ProbeStateSnapshot,
    // --- TermId-bearing fields outside `DtLazyAttemptState`, restored
    // verbatim on abandon ---
    w7_defs: Option<HashMap<TermId, TermId>>,
    w7_int_defs: HashMap<TermId, TermId>,
    self_check_authored_assertions: Option<Vec<TermId>>,
}

impl Executor {
    /// `true` when the persistent incremental theory state carries content
    /// that a term-store rollback could alias.
    ///
    /// Identical predicate to the lane's `#dt-lazy-incremental-gate`
    /// (`has_persistent_dt_lazy_session` minus the `incremental_mode` flag),
    /// reused as a POST-condition: the gate proves it false at entry, this
    /// proves it still false at abandon time (an inner solve that populated
    /// persistent state would otherwise hold post-watermark ids across the
    /// rollback).
    fn dt_lazy_incremental_state_dirty(&self) -> bool {
        self.incr_theory_state.as_ref().is_some_and(|s| {
            s.scope_depth > 0
                || s.pending_push > 0
                || !s.encoded_assertions.is_empty()
                || !s.pre_push_assertions.is_empty()
                || s.persistent_sat.is_some()
                || s.lia_persistent_sat.is_some()
        })
    }

    /// Open the speculative bracket: snapshot the abandon-restore set and push
    /// a proof-tracker scope.
    ///
    /// Returns `None` when the bounded proof-ledger checkpoint is declined
    /// (`bounded_proof_rollback_checkpoint`); nothing has been mutated in that
    /// case and the optional lane must fall through to the eager authority.
    ///
    /// Every exit path below a `Some` MUST reach exactly one of
    /// [`Self::dt_lazy_discard_attempt`] or [`Self::dt_lazy_commit_attempt`],
    /// or the tracker's scope stack is left unbalanced (the by-value API makes
    /// a double close impossible; a leak is still the caller's to avoid).
    pub(super) fn dt_lazy_capture_entry_state(&mut self) -> Option<DtLazyEntryState> {
        let proof_checkpoint = self.bounded_proof_rollback_checkpoint().ok()?;
        let state = DtLazyEntryState {
            assertions: self.ctx.assertions.clone(),
            pre_lift: std::mem::take(&mut self.dt_pre_lift_assertions),
            terms_len: self.ctx.terms.len(),
            terms_checkpoint: self.ctx.terms.rollback_checkpoint(),
            proof_checkpoint,
            proof_steps: self.proof_tracker.num_steps(),
            proof_scope_depth: self.proof_tracker.scope_depth(),
            had_quantifier_manager: self.quantifier_manager.is_some(),
            lazy_proof_state: DtLazyProofState::capture(self),
            attempt_state: DtLazyAttemptState::capture(self),
            lia_probe_state: ay_lia::save_probe_state(),
            w7_defs: self.w7_defs.clone(),
            w7_int_defs: self.w7_int_defs.clone(),
            self_check_authored_assertions: self.self_check_authored_assertions.clone(),
        };
        // #dt-lazy-abandon-restore: the speculative scope. Its matching
        // `pop()` (abandon) truncates every step the attempt records; its
        // `commit_speculative_scope()` (decided) keeps them. The ledger
        // checkpoint above was taken BEFORE this push, so restoring it also
        // restores the pre-push scope stack.
        crate::incremental_state::IncrementalSubsystem::push(&mut self.proof_tracker);
        Some(state)
    }

    /// Close the bracket on a DEFINITIVE verdict (or an internal error the
    /// caller propagates): the attempt's proof steps are part of the accepted
    /// trajectory, so drop the watermark WITHOUT truncating, and leave every
    /// other field exactly as the attempt left it. The checkpoints are dropped
    /// unused.
    pub(super) fn dt_lazy_commit_attempt(&mut self, entry: DtLazyEntryState) {
        while self.proof_tracker.scope_depth() > entry.proof_scope_depth {
            self.proof_tracker.commit_speculative_scope();
        }
        drop(entry);
    }

    /// Close the bracket on ABANDON: erase the attempt.
    ///
    /// Returns `true` when the term store was rolled back, `false` when the
    /// proof ledger could not be restored or the fail-safe kept it (everything
    /// else is restored either way).
    ///
    /// # Fail-safe
    ///
    /// [`ay_core::TermStore::rollback_to`] recycles ids and its contract
    /// forbids retaining any of them. This function can only prove that for
    /// holders it restores. Two it cannot:
    ///
    /// * `incr_theory_state` — the persistent encoding (tseitin `term_to_var`,
    ///   theory atoms, recorded lemmas) is not cheaply clonable. The lane gates
    ///   itself off unless it is empty at entry; this re-checks the same
    ///   predicate at abandon time.
    /// * `quantifier_manager` — holds pattern/instance terms and has no cheap
    ///   snapshot. A manager that came into existence DURING the attempt may
    ///   hold post-watermark ids and suppresses the store rollback; one that
    ///   was already live at entry can only hold pre-watermark ids and does
    ///   not. The lane is quantifier-free by `dt_lazy_content_eligible`, so in
    ///   practice neither binds.
    ///
    /// Plus the post-condition that the proof-tracker unwind really did
    /// remove the attempt's steps (it cannot, if an inner solve called
    /// `reset()` and cleared the scope stack under us — in which case the
    /// ledger checkpoint also reports a moved ledger).
    pub(super) fn dt_lazy_discard_attempt(&mut self, entry: DtLazyEntryState, lane: &str) -> bool {
        let DtLazyEntryState {
            assertions,
            pre_lift,
            terms_len,
            terms_checkpoint,
            proof_checkpoint,
            proof_steps,
            proof_scope_depth,
            had_quantifier_manager,
            lazy_proof_state,
            attempt_state,
            lia_probe_state,
            w7_defs,
            w7_int_defs,
            self_check_authored_assertions,
        } = entry;

        // 1. Unwind the proof tracker DOWN TO the entry depth. `pop()`
        //    truncates `steps` and restores the `assumption_map` /
        //    `lemma_map` / `named_steps` snapshots paired with the watermark,
        //    so nothing the attempt recorded survives to reference a
        //    discarded TermId. The ledger checkpoint below then restores the
        //    exact entry prefix; this unwind is the cheap first line.
        while self.proof_tracker.scope_depth() > proof_scope_depth {
            crate::incremental_state::IncrementalSubsystem::pop(&mut self.proof_tracker);
        }

        // 2. The entry assertion window, moved back (affine transaction).
        self.ctx.assertions = assertions;
        self.dt_pre_lift_assertions = pre_lift;

        // 3. Verdict artifacts. Revoke only the discarded attempt's result
        //    artifacts (model, one-shot SAT/UNSAT emission certificates
        //    — #dt-lazy-cert-rollback, 71ab33c05 —, proof, clause trace,
        //    var/trail maps, validation stats); the active public UNSAT epoch
        //    and Pareto state belong to the enclosing query.
        self.revoke_dt_lazy_attempt_artifacts();
        self.clear_dt_theory_model();
        self.dt_egraph_assignment.replace(None);

        // 4. Every executor-owned field a discarded sub-solve may mutate
        //    (`DtLazyAttemptState`), the proof-provenance records
        //    (`DtLazyProofState`), the LIA probe state, and the TermId-bearing
        //    fields neither snapshot carries.
        let entry_array_ext_witness_cache = attempt_state.restore(self);
        ay_lia::restore_probe_state(lia_probe_state);
        crate::executor::model::eval_memo_clear();
        lazy_proof_state.restore(self);
        self.w7_defs = w7_defs;
        self.w7_int_defs = w7_int_defs;
        self.self_check_authored_assertions = self_check_authored_assertions;

        // 5. Term-store-INDEXED caches. These are the subtle ones: each keys
        //    on a `TermId` or a store-length high-water mark, and a rollback
        //    that RECYCLES ids can leave `len` back at the same value with
        //    different contents — so the "shrink forces a rebuild"
        //    self-healing in `select_by_array_index` never triggers. Reset
        //    them outright, before AND after the store rollback.
        self.clear_dt_lazy_rebuildable_term_indexes();

        // 6. The proof ledger. If the checkpoint's prefix was moved out by a
        //    nested proof reset/take, keep the speculative terms so no escaped
        //    proof can dangle; eager fallback remains sound, just less
        //    isolated. The proof-coupled witness cache is committed only
        //    after this succeeds.
        if !self.proof_tracker.rollback_to(proof_checkpoint) {
            if ay_core::misc_cli_flags().phase_trace {
                eprintln!("c phase-trace {lane}-rollback to={terms_len} store_rolled_back=false proof_ledger_moved=true");
            }
            return false;
        }

        // 7. Holders this module CANNOT restore. Deliberately NOT mutated —
        //    clearing a live `quantifier_manager` would be a new behaviour
        //    whose blast radius is the whole quantifier pipeline, and the
        //    requirement here is the opposite: when a holder cannot be proven
        //    clean, keep the STORE instead.
        let unrestorable_holder_dirty = self.dt_lazy_incremental_state_dirty()
            || (!had_quantifier_manager && self.quantifier_manager.is_some());
        let proof_truncated = self.proof_tracker.num_steps() <= proof_steps;

        // 8. The store rollback itself — LAST, and only when every holder is
        //    provably clean. Skipping it is the pre-#dt-lazy-isolation
        //    behaviour: sound, but scaffold-polluted (that is the 394 -> 198
        //    cost, so it must stay the rare path, not the default one).
        let rolled_back = if proof_truncated && !unrestorable_holder_dirty {
            self.array_ext_witness_cache = entry_array_ext_witness_cache;
            self.ctx.terms.rollback_to(terms_checkpoint);
            self.clear_dt_lazy_rebuildable_term_indexes();
            true
        } else {
            false
        };

        if ay_core::misc_cli_flags().phase_trace {
            eprintln!(
                "c phase-trace {lane}-rollback to={terms_len} store_rolled_back={rolled_back} proof_truncated={proof_truncated} unrestorable_holder_dirty={unrestorable_holder_dirty}"
            );
        }
        rolled_back
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::incremental_state::IncrementalTheoryState;
    use ay_core::Sort;

    /// THE REGRESSION (#dt-lazy-abandon-restore).
    ///
    /// Reproduces the exact configuration `66538b006f` created and
    /// `bd02cac11` localized: proof production ON (unconditional since
    /// 66538b006f, so this is the `--z3-mode` competition path) and the
    /// abandoned attempt HAS recorded proof steps. The old guard
    ///
    /// ```ignore
    /// if this.produce_proofs_enabled()
    ///     && this.proof_tracker.num_steps() != entry_proof_steps { return; }
    /// ```
    ///
    /// returned here, leaving the scratch terms in the store — measured at
    /// 394 -> 198 solved on SQ QF_Datatypes. The abandon path must instead
    /// TRUNCATE the attempt's proof steps and then roll the store back.
    #[test]
    fn abandon_rolls_back_the_store_when_the_attempt_recorded_proof_steps() {
        let mut ex = Executor::new();
        // The competition configuration.
        ex.proof_tracker.enable();
        // Pre-attempt material: must SURVIVE the abandon.
        let kept = ex.ctx.terms.mk_fresh_var("kept", Sort::Bool);
        ex.dt_solver_added_axiom_terms.insert(kept);
        ex.w7_int_defs.insert(kept, kept);
        let entry_len = ex.ctx.terms.len();
        let entry_steps = ex.proof_tracker.num_steps();
        let entry_scope_depth = ex.proof_tracker.scope_depth();

        let entry = ex
            .dt_lazy_capture_entry_state()
            .expect("an unbudgeted fresh executor admits the proof checkpoint");

        // The attempt: scratch terms, a recorded proof step over one of them,
        // and dirtied TermId-bearing fields the OLD rollback did not restore.
        let scratch = ex.ctx.terms.mk_fresh_var("dt_lazy_scratch", Sort::Bool);
        assert!(
            ex.proof_tracker.add_assumption(scratch, None).is_some(),
            "the tracker must actually record a step, or this test does not \
             reproduce the guard's precondition"
        );
        assert!(
            ex.proof_tracker.num_steps() > entry_steps,
            "precondition: the attempt recorded proof steps"
        );
        ex.dt_solver_added_axiom_terms.insert(scratch);
        ex.row_seeded_terms.insert(scratch);
        ex.cegar_pending_lemma = Some(scratch);
        ex.recorded_var_substitutions.insert(scratch, kept);
        ex.w7_int_defs.insert(scratch, scratch);
        ex.w7_defs = Some(HashMap::default());
        ex.self_check_authored_assertions = Some(vec![scratch]);
        ex.last_sat_certificate = None;

        let rolled_back = ex.dt_lazy_discard_attempt(entry, "dt-lazy-test");

        assert!(
            rolled_back,
            "the DT-lazy abandon path must roll the term store back on the \
             competition path (proofs enabled + steps recorded) — this is the \
             394 -> 198 regression from 66538b006f"
        );
        assert_eq!(
            ex.ctx.terms.len(),
            entry_len,
            "the attempt's scratch terms must be discarded"
        );
        assert_eq!(
            ex.proof_tracker.num_steps(),
            entry_steps,
            "the attempt's proof steps must be truncated, so no live step can \
             reference a recycled TermId (TermStore::rollback_to contract)"
        );
        assert_eq!(
            ex.proof_tracker.scope_depth(),
            entry_scope_depth,
            "the speculative scope must be balanced"
        );
        assert!(
            !ex.dt_solver_added_axiom_terms.contains(&scratch),
            "attempt content dropped (revoke clears the set; the entry set is \
             restored by DtLazyAttemptState)"
        );
        assert!(ex.row_seeded_terms.is_empty(), "row_seeded_terms restored");
        assert!(
            ex.cegar_pending_lemma.is_none(),
            "cegar_pending_lemma restored"
        );
        assert!(
            ex.recorded_var_substitutions.is_empty(),
            "recorded_var_substitutions restored"
        );
        assert_eq!(
            ex.w7_int_defs.get(&kept),
            Some(&kept),
            "pre-attempt w7_int_defs kept"
        );
        assert!(
            !ex.w7_int_defs.contains_key(&scratch),
            "attempt w7_int_defs dropped"
        );
        assert!(ex.w7_defs.is_none(), "w7_defs restored");
        assert!(
            ex.self_check_authored_assertions.is_none(),
            "self_check_authored_assertions restored"
        );
        assert!(
            ex.last_sat_certificate.is_none() && ex.last_unsat_certificate.is_none(),
            "#dt-lazy-cert-rollback: the attempt's certificates are cleared"
        );
    }

    /// The DECIDED path keeps everything: a lane verdict's proof steps and
    /// terms are part of the accepted trajectory.
    #[test]
    fn commit_keeps_the_attempts_terms_and_proof_steps() {
        let mut ex = Executor::new();
        ex.proof_tracker.enable();
        let entry_steps = ex.proof_tracker.num_steps();
        let entry_scope_depth = ex.proof_tracker.scope_depth();

        let entry = ex
            .dt_lazy_capture_entry_state()
            .expect("an unbudgeted fresh executor admits the proof checkpoint");
        let scratch = ex.ctx.terms.mk_fresh_var("dt_lazy_scratch", Sort::Bool);
        ex.proof_tracker.add_assumption(scratch, None);
        let after_len = ex.ctx.terms.len();
        let after_steps = ex.proof_tracker.num_steps();
        assert!(after_steps > entry_steps);

        ex.dt_lazy_commit_attempt(entry);

        assert_eq!(ex.ctx.terms.len(), after_len, "no store rollback on commit");
        assert_eq!(
            ex.proof_tracker.num_steps(),
            after_steps,
            "a decided lane keeps its proof steps"
        );
        assert_eq!(
            ex.proof_tracker.scope_depth(),
            entry_scope_depth,
            "the speculative scope must be balanced"
        );
    }

    /// The FAIL-SAFE: when a holder this module cannot snapshot became dirty
    /// during the attempt, everything else is still restored but the term
    /// store is KEPT — the store rollback is the one step that cannot be
    /// undone if a stale id survives somewhere.
    #[test]
    fn abandon_keeps_the_store_when_an_unrestorable_holder_is_dirty() {
        let mut ex = Executor::new();
        ex.proof_tracker.enable();
        let entry_len = ex.ctx.terms.len();
        let entry_scope_depth = ex.proof_tracker.scope_depth();

        let entry = ex
            .dt_lazy_capture_entry_state()
            .expect("an unbudgeted fresh executor admits the proof checkpoint");
        let scratch = ex.ctx.terms.mk_fresh_var("dt_lazy_scratch", Sort::Bool);
        ex.proof_tracker.add_assumption(scratch, None);
        ex.row_seeded_terms.insert(scratch);
        // Persistent incremental encoding populated under us: its tseitin map
        // would alias the recycled ids.
        let mut st = IncrementalTheoryState::new();
        st.encoded_assertions.insert(scratch, 1);
        ex.incr_theory_state = Some(st);

        let rolled_back = ex.dt_lazy_discard_attempt(entry, "dt-lazy-test");

        assert!(!rolled_back, "fail-safe: the store must be kept");
        assert!(
            ex.ctx.terms.len() > entry_len,
            "the store is deliberately NOT rolled back here"
        );
        assert!(
            ex.row_seeded_terms.is_empty(),
            "everything else is still restored"
        );
        assert_eq!(
            ex.proof_tracker.scope_depth(),
            entry_scope_depth,
            "the speculative scope must be balanced even when the store is kept"
        );
    }
}
