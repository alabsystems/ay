// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental scope helpers for combined theory solving.
//!
//! These helpers manage temporary assertion swaps and deferred model
//! postprocessing during combined theory routes (AUFLIA, LIRA, AUFLIRA).
//! Extracted from `combined.rs` to keep the solve routes focused on
//! theory-specific logic (#6731).

use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};

use crate::executor_types::{Result, SolveResult};
use crate::incremental_state::IncrementalTheoryState;
use ay_core::TermId;

use super::super::Executor;
use super::solve_harness::ProofProblemAssertionProvenance;

impl Executor {
    /// Run a closure with a fresh `IncrementalTheoryState`, restoring the
    /// original state afterward.
    ///
    /// Combined theory routes (UF+LRA, AUFLIA, …) each need an isolated
    /// split-loop that does not interfere with the outer incremental state
    /// used by `push`/`pop`.
    ///
    /// If `assertions` is `Some(new_assertions)`, the executor assertion list
    /// is also temporarily replaced for the duration of the closure.
    ///
    /// #c2-tracker-isolation: for every non-`Unsat` exit, the proof tracker is
    /// isolated like the incremental theory/BV state and every proof step the
    /// closure recorded is rolled back. A failed
    /// witness/pivot sub-solve used to leave its steps (including reject-stub
    /// tagged units such as `StringContentAxiom`) in the shared tracker, and
    /// the generic-unit alias in `ProofTracker::add_assumption` could later
    /// bind an assumption of the SAME `TermId` to the stale tagged step,
    /// pulling it into a published proof cone where strict validation
    /// hard-fails (C2_STRING_AXIOM_PROBE.md residual vector). Rolling the
    /// ledger back restores the pre-alias behavior — a later
    /// `add_assumption` mints a fresh `Assume` — which is total and
    /// decline-only with respect to publishing: the mint-time strict check
    /// and assumption authentication in `unsat_cert` are untouched. On
    /// `Unsat` the steps are KEPT verbatim (no behavior change): callers that
    /// use the inner refutation as their outer publication candidate need that
    /// proof. This closes the demonstrated stale-alias vector after a failed
    /// witness/pivot window; it is not a blanket claim that every speculative
    /// inner-`Unsat` consumer is isolated. Such callers require an explicit
    /// outcome-aware commit/rollback contract before this helper can roll their
    /// ledger back. Terms are never rolled back here, so truncated
    /// proof steps cannot leave dangling `TermId`s in any escaped artifact.
    pub(in crate::executor) fn with_isolated_incremental_state<F>(
        &mut self,
        assertions: Option<Vec<TermId>>,
        f: F,
    ) -> Result<SolveResult>
    where
        F: FnOnce(&mut Self) -> Result<SolveResult>,
    {
        let saved_state = self.incr_theory_state.take();
        self.incr_theory_state = Some(IncrementalTheoryState::new());
        // #qmg-incr-bv-scope-leak: the persistent BV incremental state must be
        // isolated exactly like the theory state — an inner solve encoding its
        // probe assertions into the OUTER persistent BV SAT registers scope
        // activations that a later outer check-sat replays (wrong UNSAT), and
        // conversely the probe would be solved under the outer scope's
        // activations (wrong probe verdicts). Take it for the duration; the BV
        // lane lazily creates a fresh state on demand.
        let saved_bv_state = self.incr_bv_state.take();
        // #c2-tracker-isolation: coherent proof-ledger snapshot (steps + dedup
        // maps + scope snapshots + ledger epoch). Captured unconditionally:
        // when the tracker is disabled the ledger is empty and the clone is
        // free, and a closure that self-enables proof production mid-window
        // is still rolled back on failure.
        let proof_window = self.proof_tracker.rollback_checkpoint();
        let saved_assertions = assertions
            .map(|new_assertions| std::mem::replace(&mut self.ctx.assertions, new_assertions));
        let result = catch_unwind(AssertUnwindSafe(|| f(self)));
        if let Some(original_assertions) = saved_assertions {
            self.ctx.assertions = original_assertions;
        }
        self.incr_theory_state = saved_state;
        self.incr_bv_state = saved_bv_state;
        // Keep the ledger only when the inner solve refuted: that proof is the
        // outer publication's candidate (status quo). Every other outcome —
        // Sat, Unknown, executor error, panic — discards the window's steps.
        let keep_proof_window = matches!(&result, Ok(Ok(r)) if r.is_unsat());
        if !keep_proof_window {
            // A `false` return means a nested `take_proof`/reset moved the
            // entry ledger during the window; `rollback_to` then clears the
            // replacement ledger (every step in it is post-checkpoint). The
            // moved-out proof is an owned value and is not affected. No term
            // rollback is paired with this checkpoint, so both outcomes need
            // no further action (contrast dt.rs, which must retain terms).
            let _ledger_intact = self.proof_tracker.rollback_to(proof_window);
        }
        match result {
            Ok(result) => result,
            Err(payload) => resume_unwind(payload),
        }
    }

    /// Solve with temporary preprocessed assertions while deferring model
    /// postprocessing (minimization + validation) to the outer executor boundary.
    ///
    /// Combined theory routes (AUFLIA, LIRA, AUFLIRA) install preprocessed
    /// assertions before solving, but model validation must run against the
    /// *original* assertion set. This helper:
    ///
    /// 1. Saves and replaces assertions with `temporary_assertions`
    /// 2. Suppresses inner minimization (`CounterexampleStyle::Any`) and inner
    ///    validation (`skip_model_eval = true`) so `solve_and_store_model_with_theories`
    ///    stores the model without postprocessing
    /// 3. Calls `with_isolated_incremental_state(None, f)` for the actual solve
    /// 4. Restores assertions and flags after the solve returns
    /// 5. Leaves `last_model_validated = false` so `check_sat()` /
    ///    `check_sat_assuming()` runs validation on the restored assertions
    ///
    /// Fixes #6731: inner validation against preprocessed assertions degraded
    /// trivially SAT AUFLIA formulas to `unknown`.
    pub(in crate::executor) fn with_deferred_postprocessing<F>(
        &mut self,
        temporary_assertions: Vec<TermId>,
        proof_provenance: ProofProblemAssertionProvenance,
        f: F,
    ) -> Result<SolveResult>
    where
        F: FnOnce(&mut Self) -> Result<SolveResult>,
    {
        // Save assertion-view-sensitive state
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, temporary_assertions);
        let saved_style = self.counterexample_style;
        let saved_skip = self.skip_model_eval;
        let saved_proof_provenance = self.proof_problem_assertion_provenance.clone();
        let proof_provenance =
            proof_provenance.preserving_authority_from(saved_proof_provenance.as_ref());

        // Suppress inner minimization (CounterexampleStyle::Any makes
        // minimize_counterexamples_enabled() return false) and inner
        // validation (skip_model_eval makes finalize_sat_model_validation
        // return Ok(Sat) immediately).
        self.counterexample_style = crate::CounterexampleStyle::Any;
        self.skip_model_eval = true;
        self.proof_problem_assertion_provenance = Some(proof_provenance);

        // Solve with isolated incremental state (None = no second assertion swap)
        let result = catch_unwind(AssertUnwindSafe(|| {
            self.with_isolated_incremental_state(None, f)
        }));

        // Restore original state before either returning or resuming a panic.
        self.ctx.assertions = saved_assertions;
        self.counterexample_style = saved_style;
        self.skip_model_eval = saved_skip;
        let should_restore_provenance = match &result {
            Ok(Ok(r)) => !r.is_unsat(),
            Ok(Err(_)) | Err(_) => true,
        };
        if should_restore_provenance {
            self.proof_problem_assertion_provenance = saved_proof_provenance;
        }

        // Run deferred minimization against restored assertions if applicable
        if matches!(result, Ok(Ok(SolveResult::Sat)))
            && self.minimize_counterexamples_enabled()
            && self.last_assumptions.is_none()
        {
            self.minimize_model_sat_preserving();
        }

        // Ensure outer boundary runs validation on restored assertions
        self.last_model_validated = false;

        if matches!(result, Ok(Ok(SolveResult::Sat))) && self.last_model.is_none() {
            tracing::debug!(
                "with_deferred_postprocessing: inner solve returned Sat WITHOUT storing \
                 last_model — outer validation will degrade to Unknown (#7956 diagnosis)"
            );
        }

        match result {
            Ok(result) => result,
            Err(payload) => resume_unwind(payload),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CounterexampleStyle;
    use ay_frontend::{parse, Command};
    use std::panic::{catch_unwind, AssertUnwindSafe};

    fn theory_scope_depth(exec: &Executor) -> usize {
        exec.incr_theory_state
            .as_ref()
            .map_or(0, |state| state.scope_depth)
    }

    fn executor_with_assertion() -> Executor {
        let commands = parse(
            r#"
            (set-logic QF_UF)
            (declare-const a Bool)
            (assert a)
            "#,
        )
        .expect("test SMT should parse");
        let mut exec = Executor::new();
        exec.execute_all(&commands)
            .expect("test SMT setup should execute");
        exec
    }

    #[test]
    fn isolated_incremental_state_restores_outer_push_after_panic() {
        let mut exec = Executor::new();
        exec.execute(&Command::Push(1)).expect("outer push");
        assert_eq!(theory_scope_depth(&exec), 1);

        let panic = catch_unwind(AssertUnwindSafe(|| {
            let _ = exec.with_isolated_incremental_state(None, |_exec| -> Result<SolveResult> {
                panic!("sentinel isolated-state panic");
            });
        }));

        assert!(panic.is_err(), "test panic should propagate");
        assert_eq!(
            theory_scope_depth(&exec),
            1,
            "outer incremental theory scope must be restored before unwind"
        );
        exec.execute(&Command::Pop(1))
            .expect("balanced outer pop should still succeed");
        assert_eq!(theory_scope_depth(&exec), 0);
    }

    #[test]
    fn isolated_incremental_state_restores_assertions_after_panic() {
        let mut exec = executor_with_assertion();
        let original_assertions = exec.ctx.assertions.clone();
        let mut original_state = IncrementalTheoryState::new();
        original_state.scope_depth = 2;
        exec.incr_theory_state = Some(original_state);

        let panic_result = catch_unwind(AssertUnwindSafe(|| {
            let _ = exec.with_isolated_incremental_state(Some(Vec::new()), |_this| -> Result<_> {
                panic!("synthetic isolated-state panic");
            });
        }));

        assert!(panic_result.is_err());
        assert_eq!(exec.ctx.assertions, original_assertions);
        assert_eq!(
            exec.incr_theory_state
                .as_ref()
                .map(|state| state.scope_depth),
            Some(2)
        );
    }

    /// #c2-tracker-isolation: the C2_STRING_AXIOM_PROBE.md residual-vector
    /// shape. A failed (non-Unsat) isolated sub-solve records a reject-stub
    /// tagged unit; before the fix the step survived in the shared tracker and
    /// `add_assumption` of the SAME TermId aliased to it via the generic-unit
    /// key, pulling a strict-hard-fail step into a published proof cone. After
    /// the fix the window is rolled back and a fresh `Assume` is minted (the
    /// pre-alias behavior).
    #[test]
    fn isolated_subsolve_proof_rollback_prevents_stale_tagged_unit_alias() {
        use ay_core::{ProofStep, TheoryLemmaKind};

        let mut exec = executor_with_assertion();
        exec.proof_tracker.enable();
        let term = *exec.ctx.assertions.first().expect("setup asserts one term");
        let steps_before = exec.proof_tracker.num_steps();

        // Failed witness/pivot sub-solve: records the tagged unit, then exits
        // without a refutation.
        let result = exec.with_isolated_incremental_state(None, |this| {
            let stale = this
                .proof_tracker
                .add_theory_lemma_with_kind(vec![term], TheoryLemmaKind::StringContentAxiom);
            assert!(stale.is_some(), "tagged unit must record inside the window");
            assert!(this.proof_tracker.num_steps() > steps_before);
            Ok(SolveResult::Unknown)
        });
        assert!(matches!(result, Ok(SolveResult::Unknown)));
        assert_eq!(
            exec.proof_tracker.num_steps(),
            steps_before,
            "failed sub-solve must not leave proof steps in the shared tracker"
        );

        // Re-registering the SAME TermId as an assumption (the SLIA retry
        // shape) must mint a fresh `Assume`, not alias to the stale step.
        let id = exec
            .proof_tracker
            .add_assumption(term, None)
            .expect("tracker is enabled");
        assert_eq!(
            exec.proof_tracker.num_steps(),
            steps_before + 1,
            "a fresh Assume must be appended (an alias would append nothing)"
        );
        let proof = exec.proof_tracker.take_proof();
        match proof.steps.get(id.0 as usize) {
            Some(ProofStep::Assume(assumed)) => assert_eq!(*assumed, term),
            other => panic!("expected a fresh Assume for the re-registered term, got {other:?}"),
        }
    }

    /// The publication-relevant path is unchanged: an inner `Unsat` keeps its
    /// proof window verbatim, and assumption registration still reuses the
    /// certified unit recorded inside it (the intended dedup alias).
    #[test]
    fn isolated_subsolve_unsat_keeps_proof_window() {
        let mut exec = executor_with_assertion();
        exec.proof_tracker.enable();
        let term = *exec.ctx.assertions.first().expect("setup asserts one term");
        let steps_before = exec.proof_tracker.num_steps();

        let mut recorded_id = None;
        let result = exec.with_isolated_incremental_state(None, |this| {
            recorded_id = this.proof_tracker.add_theory_lemma(vec![term]);
            assert!(recorded_id.is_some());
            Ok(SolveResult::unsat())
        });
        assert!(matches!(result, Ok(SolveResult::Unsat(_))));
        let steps_after = exec.proof_tracker.num_steps();
        assert!(
            steps_after > steps_before,
            "an inner refutation's proof steps must survive for the outer publication flow"
        );
        let id = exec
            .proof_tracker
            .add_assumption(term, None)
            .expect("tracker is enabled");
        assert_eq!(Some(id), recorded_id, "kept window must still dedup-alias");
        assert_eq!(exec.proof_tracker.num_steps(), steps_after);
    }

    /// A panicking sub-solve must also discard its proof window before the
    /// panic resumes, exactly like the incremental theory/BV state.
    #[test]
    fn isolated_subsolve_proof_window_rolled_back_after_panic() {
        use ay_core::TheoryLemmaKind;

        let mut exec = executor_with_assertion();
        exec.proof_tracker.enable();
        let term = *exec.ctx.assertions.first().expect("setup asserts one term");
        let steps_before = exec.proof_tracker.num_steps();

        let panic = catch_unwind(AssertUnwindSafe(|| {
            let _ = exec.with_isolated_incremental_state(None, |this| -> Result<SolveResult> {
                let _ = this
                    .proof_tracker
                    .add_theory_lemma_with_kind(vec![term], TheoryLemmaKind::StringContentAxiom);
                panic!("sentinel proof-window panic");
            });
        }));
        assert!(panic.is_err(), "test panic should propagate");
        assert_eq!(
            exec.proof_tracker.num_steps(),
            steps_before,
            "proof window must be rolled back before unwind"
        );
    }

    /// If a nested `take_proof` moves the ledger away inside a FAILED window,
    /// rollback cannot rebuild the entry prefix; the replacement ledger (all
    /// post-checkpoint steps) is cleared instead, and later assumption
    /// registration still mints a fresh `Assume`.
    #[test]
    fn isolated_subsolve_proof_rollback_survives_ledger_move_in_window() {
        use ay_core::{ProofStep, TheoryLemmaKind};

        let mut exec = executor_with_assertion();
        exec.proof_tracker.enable();
        let term = *exec.ctx.assertions.first().expect("setup asserts one term");

        let result = exec.with_isolated_incremental_state(None, |this| {
            let _ = this
                .proof_tracker
                .add_theory_lemma_with_kind(vec![term], TheoryLemmaKind::StringContentAxiom);
            // Nested publication attempt moves the ledger away…
            let _moved = this.proof_tracker.take_proof();
            // …and the window records more stale steps into the new ledger.
            let _ = this
                .proof_tracker
                .add_theory_lemma_with_kind(vec![term], TheoryLemmaKind::StringContentAxiom);
            Ok(SolveResult::Unknown)
        });
        assert!(matches!(result, Ok(SolveResult::Unknown)));
        assert_eq!(
            exec.proof_tracker.num_steps(),
            0,
            "post-move replacement ledger must be cleared on failed-window exit"
        );

        let id = exec
            .proof_tracker
            .add_assumption(term, None)
            .expect("tracker is enabled");
        assert_eq!(exec.proof_tracker.num_steps(), 1);
        let proof = exec.proof_tracker.take_proof();
        assert!(
            matches!(proof.steps.get(id.0 as usize), Some(ProofStep::Assume(t)) if *t == term),
            "expected a fresh Assume after the moved-ledger rollback"
        );
    }

    #[test]
    fn deferred_postprocessing_restores_outer_state_after_panic() {
        let mut exec = Executor::new();
        exec.execute(&Command::Push(1)).expect("outer push");
        assert_eq!(theory_scope_depth(&exec), 1);

        let panic = catch_unwind(AssertUnwindSafe(|| {
            let _ = exec.with_deferred_postprocessing(
                Vec::new(),
                ProofProblemAssertionProvenance::default(),
                |_exec| -> Result<SolveResult> {
                    panic!("sentinel deferred-postprocessing panic");
                },
            );
        }));

        assert!(panic.is_err(), "test panic should propagate");
        assert_eq!(
            theory_scope_depth(&exec),
            1,
            "deferred postprocessing must restore the outer theory scope"
        );
        assert!(
            !exec.skip_model_eval,
            "deferred postprocessing must restore skip_model_eval"
        );
        assert!(
            exec.proof_problem_assertion_provenance.is_none(),
            "proof provenance must be restored after unwind"
        );
        exec.execute(&Command::Pop(1))
            .expect("balanced outer pop should still succeed");
        assert_eq!(theory_scope_depth(&exec), 0);
    }

    #[test]
    fn deferred_postprocessing_restores_assertions_and_flags_after_panic() {
        let mut exec = executor_with_assertion();
        let original_assertions = exec.ctx.assertions.clone();
        let mut original_state = IncrementalTheoryState::new();
        original_state.scope_depth = 3;
        exec.incr_theory_state = Some(original_state);
        exec.counterexample_style = CounterexampleStyle::Minimal;
        exec.skip_model_eval = false;
        exec.read_pin_repair_done = false;

        let panic_result = catch_unwind(AssertUnwindSafe(|| {
            let _ = exec.with_deferred_postprocessing(
                Vec::new(),
                ProofProblemAssertionProvenance::default(),
                |_this| -> Result<_> {
                    panic!("synthetic deferred-postprocessing panic");
                },
            );
        }));

        assert!(panic_result.is_err());
        assert_eq!(exec.ctx.assertions, original_assertions);
        assert_eq!(
            exec.incr_theory_state
                .as_ref()
                .map(|state| state.scope_depth),
            Some(3)
        );
        assert_eq!(exec.counterexample_style, CounterexampleStyle::Minimal);
        assert!(!exec.skip_model_eval);
    }
}
