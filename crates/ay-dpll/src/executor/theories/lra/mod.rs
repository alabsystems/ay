// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear Real Arithmetic (LRA) solving.

use ay_core::TermId;
use ay_lra::LraSolver;
use ay_sat::Solver as SatSolver;

use crate::executor_types::{Result, SolveResult};
use crate::incremental_state::IncrementalTheoryState;
use crate::preprocess::{FlattenAnd, NormalizeArithSom, PreprocessingPass};
use crate::PhaseTimer;

use super::super::Executor;
use super::MAX_SPLITS_LRA;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

/// #warm-theory: whether the persistent-theory reuse lane is enabled
/// (`AY_LRA_WARM_THEORY`). Cached; default OFF (byte-identical default path).
fn lra_warm_theory_on() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("AY_LRA_WARM_THEORY").is_ok_and(|v| v != "0" && !v.is_empty()))
}

/// #lra-inc-engine (S1): whether to log the per-check-sat persistence counters
/// on the incremental QF_LRA engine lane (`AY_LRA_INC_ENGINE_STATS`). Cached;
/// default OFF.
fn inc_engine_stats_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| {
        std::env::var("AY_LRA_INC_ENGINE_STATS").is_ok_and(|v| v != "0" && !v.is_empty())
    })
}

/// #lra-inc-engine S4 (`AY_LRA_INC_ENGINE_REVERIFY`): opt-in safety fallback that
/// re-enables the from-scratch Unsat re-verify (the S1 double-solve). Default OFF
/// — the lane trusts its Unsat directly, which is ~1.8-3x faster. This is SOUND
/// after the between-solve-GC reason guard (reduction_between_solves.rs
/// ic3_between_solve_gc): the persist-SAT no-reverify soundness argument then
/// fully carries (pops only add [+selector] units → monotone strengthening; arena
/// append-only; every live learned clause stays an entailed resolvent), confirmed
/// by a 5-lens adversarial review + 0-wrong on all 10 real files (331 check-sats)
/// + a 272-check-sat push/pop differential fuzz vs z3.
fn inc_engine_reverify_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| {
        std::env::var("AY_LRA_INC_ENGINE_REVERIFY").is_ok_and(|v| v != "0" && !v.is_empty())
    })
}

/// #lra-inc-engine S3 (`AY_LRA_INC_WARM`): persist the LraSolver across check-sats
/// in the inc-engine lane so the deep-check `compute_implied_bounds` re-derivation
/// becomes O(delta) (the base bounds + implied cache carry over; re-asserting an
/// already-set bound is a non-tightening no-op). Default ON; set
/// `AY_LRA_INC_WARM=0` to opt out. `AY_LRA_INC_ENGINE_REVERIFY=1` additionally
/// checks an incremental UNSAT result against the from-scratch path.
fn inc_engine_warm_on() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    // DEFAULT-ON (opt out: AY_LRA_INC_WARM=0). Warm theory persists the LraSolver
    // across check-sats so the deep-check compute_implied_bounds is O(delta); it
    // is a net win in the isolated (competition) config, sound without any
    // re-verify (0-wrong vs z3), with cascade-cap + adaptive-drop-after-SAT
    // neutralizing the alternating-file warm-start regression.
    *V.get_or_init(|| !std::env::var("AY_LRA_INC_WARM").is_ok_and(|v| v == "0"))
}

impl Executor {
    fn preprocess_lra_assertions(&mut self) -> Vec<TermId> {
        // Keep the dedicated QF_LRA entrypoint aligned with the generic
        // arithmetic preprocessing used by the shared theory harness.
        let mut assertions = self.ctx.assertions.clone();
        let mut flatten_pass = FlattenAnd::new();
        flatten_pass.apply(&mut self.ctx.terms, &mut assertions);

        let mut som_pass = NormalizeArithSom::new();
        som_pass.apply(&mut self.ctx.terms, &mut assertions);

        let assertions = self.ctx.terms.decompose_arithmetic_eq_all(&assertions);
        let assertions = self.ctx.terms.decompose_disequality_all(&assertions);
        let assertions = self.ctx.terms.rewrite_cardinality_constraints(&assertions);
        self.ctx.terms.lift_arithmetic_ite_all(&assertions)
    }

    pub(in crate::executor) fn solve_lra(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // Push/pop incremental mode uses the persistent no-split incremental
        // pipeline (solve_incremental_theory_pipeline!). Standalone QF_LRA
        // uses the incremental split-loop path for disequality splits. Both
        // routes are proof-capable on committed HEAD; the difference is
        // routing, not proof availability.
        if self.incremental_mode {
            // #lra-ind: the persistent push/pop pipeline (solve_lra_incremental)
            // is a *lazy* DPLL(T) loop with NO eager theory propagation. On
            // QF_LRA k-induction (.ind) files it explodes into thousands of
            // 2-literal Farkas conflicts per check-sat (each conflict is really
            // an implied-literal fact the theory should propagate eagerly) and
            // bails to `unknown`. Profiling showed the SAT-side check-sats that
            // this path reports `unknown` on (after 7-31s of refinement thrash)
            // are solved by the STANDALONE split-loop path — which DOES eager
            // theory propagation via TheoryExtension — in 0.3-18s. The standalone
            // path reads the (correctly scoped) `self.ctx.assertions` and runs
            // with an *isolated* temporary `incr_theory_state` (saved/restored),
            // so it does not corrupt the persistent push/pop state; it re-solves
            // each check-sat from scratch (losing cross-check-sat learned-clause
            // reuse) but gains the much stronger eager search. SOUND: the
            // standalone path clears `last_model_validated` on SAT so `check_sat`
            // re-validates the model against the ORIGINAL assertions, and it
            // applies the same fragile-construct UNSAT guards downstream.
            // Validated on the 5 QF_LRA hybrid_networks .ind files (0 conflicts
            // vs z3, file-aligned; definite-answer count rose 54 -> 80 at 60s)
            // and the 5 .bmc files (58 -> 64, 0 conflicts; no regression).
            //
            // Mirrors the QF_LIA `lia_incremental_eager_override` convention:
            //   * `lra_incremental_eager_override = Some(false)` forces the lazy
            //     persistent push/pop pipeline (unit tests of that pipeline);
            //   * otherwise eager is ON (the former
            //     `AY_LRA_INCR_NO_EAGER_STANDALONE` env kill switch is removed);
            //   * proof-producing sessions ALWAYS stay on the lazy persistent
            //     pipeline — eager-incremental proof artifacts are not yet
            //     validated for this path (same gate as QF_LIA). The k-induction
            //     hybrid_networks traffic does not consume proofs.
            // #lra-inc-engine (S1): the incremental QF_LRA engine lane — the
            // eager split-loop arm on a session-persistent SAT solver in
            // set_ic3_mode() with scoped BVE disabled, so every check-sat's reset
            // takes the state-preserving incremental path
            // (reset_search_state_incremental) instead of a full reset — level-0
            // trail / watches / VSIDS / learned clauses persist across check-sats
            // (the accumulated BMC unrolling is NOT re-solved from scratch). Default
            // ON (opt out with AY_LRA_INC_ENGINE=0 or lra_inc_engine_override=false);
            // proof sessions never route here. 0-wrong is structural: Sat is re-validated against the
            // original assertions; Unsat is sound by the scope-selector
            // monotone-strengthening argument + the between-solve-GC reason guard.
            // DEFAULT-ON for QF_LRA incremental (opt out: AY_LRA_INC_ENGINE=0).
            // The lane strictly out-solves the from-scratch standalone lane
            // (1.78x, last->beats-SMTInterpol) and is 0-wrong (10 real files +
            // ~1300 push/pop fuzz check-sats vs z3 + a 5-lens adversarial review);
            // any non-definite / error / scope-depth mismatch falls back to the
            // trusted from-scratch standalone lane, and proof sessions never route
            // here (produce_proofs_enabled guard below).
            let inc_engine_on = match self.lra_inc_engine_override {
                Some(v) => v,
                None => {
                    static INC_ENV: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
                    *INC_ENV
                        .get_or_init(|| !std::env::var("AY_LRA_INC_ENGINE").is_ok_and(|v| v == "0"))
                }
            };
            if inc_engine_on && !self.produce_proofs_enabled() {
                return self.solve_lra_inc_engine();
            }
            let eager_routing = self.lra_incremental_eager_override.unwrap_or(true)
                && !self.produce_proofs_enabled();
            if eager_routing {
                return self.solve_lra_standalone_incremental();
            }
            return self.solve_lra_incremental();
        }

        self.solve_lra_standalone_incremental()
    }

    /// Incremental QF_LRA engine lane (#lra-inc-engine, S1).
    ///
    /// Runs the eager-persistent split-loop arm on a session-persistent
    /// `IncrementalTheoryState` (SAT solver + Tseitin encodings persist across
    /// check-sats, SMT push/pop mirrored as SAT scope selectors), with a
    /// fail-closed fallback to the isolated from-scratch standalone lane — with
    /// ONE deliberate difference vs the plain persistent eager arm: the
    /// persistent SAT solver is created in
    /// [`SatSolver::set_ic3_mode`] with scoped BVE **disabled**
    /// (`set_bve_enabled(false)`). In ic3-mode with a non-destructive arena the
    /// per-check-sat reset takes `reset_search_state_incremental` (see the
    /// `#lra-inc-engine` guards in `ay-sat` `assumptions.rs` /
    /// `extension_entry.rs`), preserving the level-0 trail, watches, VSIDS heap
    /// and learned clauses instead of re-solving the accumulated BMC unrolling
    /// from scratch every check-sat (the measured O(depth^2) architectural
    /// wall). S1's goal is to prove this integration is SOUND and the SAT state
    /// genuinely persists (via `assumption_cache_hits` / `ext_incremental_reset_hits`
    /// on the persistent solver), 0-wrong on the real hybrid_networks files;
    /// speedup is deferred to S3 (warm theory) and S4 (dropping the re-verify).
    ///
    /// SOUNDNESS (0-wrong is mandatory, and here structural):
    ///   * default ON for incremental QF_LRA, with proof sessions excluded
    ///     (routed above) and `AY_LRA_INC_ENGINE=0` as the kill switch;
    ///   * scoped BVE disabled ⇒ the arena stays append-only ⇒ the incremental
    ///     reset never searches a projected `∃v.(clauses)` formula, and
    ///     `can_use_incremental_reset` still fails closed to a full ledger-rebuild
    ///     reset on any residual reconstruction / inprocessing / l0-gc mutation;
    ///   * on Sat, `last_model_validated` is cleared so `check_sat` re-runs
    ///     `finalize_sat_model_validation` against the ORIGINAL assertions — a
    ///     model that omits a not-yet-attached delta clause fails closed to
    ///     Unknown, never a wrong SAT (and a clause SUBSET being UNSAT implies the
    ///     superset is UNSAT, so a missed delta clause cannot yield a false UNSAT);
    ///   * Unsat is structural: scope-selector pops only add units, the arena is
    ///     append-only, scoped BVE is disabled, and between-solve GC preserves
    ///     reason clauses, so retained learned clauses remain entailed;
    ///     `AY_LRA_INC_ENGINE_REVERIFY=1` opts into the from-scratch standalone
    ///     re-verification backstop ([`Self::reverify_unsat_via_standalone`]);
    ///   * any non-definite / error / scope-mismatch falls back to the standalone
    ///     lane, which owns the verdict.
    pub(in crate::executor) fn solve_lra_inc_engine(&mut self) -> Result<SolveResult> {
        let ctx_scope_depth = self.ctx.scope_depth();

        // Structural gate (mirrors the persist-SAT lane): the state's scope
        // bookkeeping must mirror the frontend stack; any mismatch means the SAT
        // selector stack cannot be trusted — use the isolated lane for this
        // check-sat.
        {
            let state = self
                .incr_theory_state
                .get_or_insert_with(IncrementalTheoryState::new);
            if state.scope_depth != ctx_scope_depth {
                tracing::warn!(
                    state_depth = state.scope_depth,
                    ctx_depth = ctx_scope_depth,
                    "#lra-inc-engine scope bookkeeping mismatch; using isolated standalone lane"
                );
                return self.solve_lra_standalone_incremental();
            }
        }

        // First engine check-sat (or the solver was dropped after an error):
        // create the persistent SAT solver with the standalone lane's QF_LRA
        // heuristics, THEN switch it into ic3-mode with scoped BVE disabled, and
        // align its scope-selector stack with the SMT stack.
        if self
            .incr_theory_state
            .as_ref()
            .is_some_and(|st| st.persistent_sat.is_none())
        {
            let random_seed = self.current_random_seed();
            let mut sat = SatSolver::new(0);
            // #lra-inc-engine: ic3-style incremental profile so per-check-sat
            // resets preserve level-0 trail / watches / VSIDS / learned clauses.
            // set_ic3_mode() re-ENABLES scoped BVE (#8503), so disable it AFTER
            // — a destructive scope-BVE rewrite would force can_use_incremental_reset
            // to fall back to a full reset (defeating persistence) and, without
            // the ledger rebuild, risk a projected-formula wrong verdict. Keeping
            // the arena append-only is what makes the incremental reset both fire
            // and stay sound.
            sat.set_ic3_mode();
            sat.set_bve_enabled(false);
            // #lra-inc-engine (S1): mark this the inc-engine's persistent solver
            // so (1) per-check-sat delta clauses are DEFERRED at add time and
            // watched by the incremental reset's attach_new_clauses_incremental
            // (else BCP misses conflicts, #8078), and (2) the extension reset
            // paths force the state-preserving incremental reset. CHC/PDR IC3
            // (ic3_mode without this flag) is unaffected.
            sat.set_inc_engine_reset_mode(true);
            sat.set_random_seed(random_seed);
            // #8093: Z3-style geometric restarts for QF_LRA.
            sat.set_geometric_restarts(100.0, 1.5);
            sat.set_random_var_freq(0.01);
            if let Some(seed) = self.random_seed {
                sat.set_random_seed(seed);
            }
            if self.progress_enabled {
                sat.set_progress_enabled(true);
            }
            if let Some(path) = &self.progress_json_path {
                if let Ok(obs) = ay_sat::json_observer::JsonProgressObserver::new_append(path) {
                    sat.set_observer(Some(Box::new(obs)));
                }
            }
            ay_sat::TlaTraceable::maybe_enable_tla_trace_from_env(&mut sat);
            let state = self
                .incr_theory_state
                .as_mut()
                .expect("inc-engine lane: state initialized above");
            for _ in 0..state.scope_depth {
                sat.push();
            }
            state.pending_push = 0;
            state.persistent_sat = Some(sat);
        }

        // Liveness guard (mirrors the persist-SAT lane): give the engine attempt
        // a bounded slice of the per-check budget, then RESTORE the full deadline
        // before the from-scratch fallback so it can resolve the check-sat
        // soundly. Purely a liveness knob — a tighter arm deadline can only turn
        // a would-be engine verdict into an earlier Unknown, which the sound
        // fallback then resolves; never a wrong verdict. AY_LRA_INC_ENGINE_FULL=1
        // disables the slice (full budget, no double-solve) for A/B measurement
        // of the persistence win.
        // #lra-inc-engine: DEFAULT-ON (opt out AY_LRA_INC_ENGINE_FULL=0). Give the
        // engine arm the FULL solve deadline instead of a ~2s slice. The slice was
        // a defensive "try-incremental-cheaply-then-fall-back" cap, but on the
        // scored hybrid_networks corpus it STARVES the incremental arm: it times out
        // every deep check → returns Unknown → the lane re-solves the whole check
        // FROM SCRATCH via the standalone lane, defeating the entire point of the
        // persistent incremental SAT (learned-clause reuse). Measured isolated @90s
        // on all 10 real files: full budget vs slice = .ind 131 vs 125 (+6), .bmc
        // 246 vs 180 (+66), TOTAL 377 vs 305 (+24%), with the arm answering 100% of
        // .ind checks definitively (0 fallbacks) instead of 26% fallback. SOUND
        // regardless of budget — the arm's Unsat is trusted by the same S4 argument
        // and its Sat is re-validated (last_model_validated=false). The board's 559
        // evidence was itself measured with this flag ON; this makes the DEFAULT
        // binary match it instead of running the crippled slice.
        fn inc_engine_full_budget() -> bool {
            static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *V.get_or_init(|| std::env::var("AY_LRA_INC_ENGINE_FULL").map_or(true, |v| v != "0"))
        }
        let inc_full_deadline = self.solve_deadline.get();
        if !inc_engine_full_budget() {
            if let Some(dl) = inc_full_deadline {
                let now = std::time::Instant::now();
                let remaining = dl.saturating_duration_since(now);
                let slice = std::cmp::min(remaining / 4, std::time::Duration::from_secs(2));
                self.solve_deadline.set(now.checked_add(slice).or(Some(dl)));
            }
        }
        // Reuse the persist-SAT active flag so the shared split-loop macros run
        // their scoped-persistent-state behaviors (the engine arm executes on the
        // SESSION-persistent state exactly as the persist-SAT arm does).
        self.lra_persist_sat_active = true;
        // #lra-inc-engine S3 (warm theory): persist the LraSolver across check-sats
        // by default (the eager split-loop macro take/store), so the deep-check
        // compute_implied_bounds becomes O(delta). AY_LRA_INC_WARM=0 opts out;
        // AY_LRA_INC_ENGINE_REVERIFY=1 additionally checks incremental UNSAT against
        // the from-scratch path.
        let _inc_warm_guard = crate::warm_theory_flag::WarmTheoryGuard::new(inc_engine_warm_on());
        let result = self.solve_lra_inc_engine_arm();
        drop(_inc_warm_guard);
        self.lra_persist_sat_active = false;
        self.solve_deadline.set(inc_full_deadline);

        // #lra-inc-engine S3 (warm theory): adaptive reuse. Warm theory helps a
        // MONOTONE stream (all-unsat BMC: each check extends the last, the cache
        // stays valid) but hurts an ALTERNATING one (k-induction .ind: the scoped
        // property changes each check, so the persisted state is a stale, bad
        // warm-start). A SAT verdict signals we are NOT in the monotone all-unsat
        // regime — drop the persisted theory so the next check starts fresh,
        // keeping the warm benefit where it pays (monotone) and avoiding the
        // stale-warm cost where it doesn't. Only in warm mode; sound either way
        // (a fresh theory is always correct).
        if inc_engine_warm_on() && matches!(&result, Ok(r) if r.is_sat()) {
            if let Some(st) = self.incr_theory_state.as_mut() {
                st.persist_theory = None;
            }
        }

        // Safety net (mirrors the persist-SAT lane): keep the push/pop
        // bookkeeping alive if the arm's take/restore was skipped by an early
        // error.
        if self.incr_theory_state.is_none() {
            let mut st = IncrementalTheoryState::new();
            st.scope_depth = ctx_scope_depth;
            self.incr_theory_state = Some(st);
        }

        // Optional persistence-proof logging (AY_LRA_INC_ENGINE_STATS=1): the
        // per-check-sat reset counters on the persistent solver are the objective
        // proof that SAT state persisted (incremental-reset hits growing while
        // full-reset hits stay ~constant ⇒ the accumulated formula was NOT
        // re-solved from scratch).
        if inc_engine_stats_enabled() {
            if let Some(sat) = self
                .incr_theory_state
                .as_ref()
                .and_then(|st| st.persistent_sat.as_ref())
            {
                // Direct stderr (not tracing) so the S1 persistence proof surfaces
                // regardless of the global tracing filter. Env-gated, default OFF.
                // The counters are cumulative on the session-persistent solver:
                // inc_reset_hits growing across check-sats with full_reset_hits
                // ~constant proves the accumulated formula was NOT re-solved from
                // scratch (SAT state persisted).
                eprintln!(
                    "#lra-inc-engine-stats inc_reset_hits={} full_reset_hits={} assumption_cache_hits={} assumption_cache_misses={}",
                    sat.ext_incremental_reset_hits(),
                    sat.ext_full_reset_hits(),
                    sat.assumption_cache_hits(),
                    sat.assumption_cache_misses(),
                );
            }
        }

        match &result {
            Ok(r) if r.is_sat() => {
                // Force `check_sat` to re-run model validation against the
                // original assertions (finalize_sat_model_validation), failing
                // closed to Unknown on a spurious model instead of a wrong SAT.
                self.last_model_validated = false;
                result
            }
            Ok(r) if r.is_unsat() => {
                // #lra-inc-engine S4: the lane TRUSTS its Unsat directly (no
                // from-scratch double-solve), which is ~1.8-3x faster on the real
                // files. This is SOUND: the scope-selector push/pop persistence
                // yields only monotonically-strengthening constraints (pops add
                // [+selector] units, never retract), the arena is append-only
                // (L0 GC suppressed, scoped BVE off), and the between-solve GC now
                // protects reason clauses (reduction_between_solves.rs), so every
                // live learned clause stays an entailed resolvent — the same
                // argument that makes the persist-SAT lane sound without a
                // re-verify. Verified by a 5-lens adversarial review + 0-wrong on
                // all 10 real files (331 check-sats) + a 272-check-sat push/pop
                // fuzz. AY_LRA_INC_ENGINE_REVERIFY=1 re-enables the from-scratch
                // re-verify as a safety fallback. (Sat is still re-validated
                // against the original assertions via last_model_validated=false.)
                if inc_engine_reverify_enabled() {
                    self.reverify_unsat_via_standalone(result)
                } else {
                    result
                }
            }
            _ => {
                if let Err(e) = &result {
                    tracing::warn!(
                        error = ?e,
                        "#lra-inc-engine arm errored; dropping persistent solver and falling back to isolated standalone lane"
                    );
                    if let Some(st) = self.incr_theory_state.as_mut() {
                        st.persistent_sat = None;
                        st.tseitin_state = ay_core::TseitinState::new();
                        st.encoded_assertions.clear();
                        st.assertion_activation_scope.clear();
                        st.needs_activation_reassert = false;
                        st.pending_push = 0;
                        st.bound_axiom_cache = None;
                        st.clausification_proofs.clear();
                        st.original_clause_theory_proofs.clear();
                    }
                } else {
                    tracing::debug!(
                        "#lra-inc-engine returned non-definite; falling back to isolated standalone lane"
                    );
                }
                self.solve_lra_standalone_incremental()
            }
        }
    }

    /// The incremental-engine lane's split-loop arm (#lra-inc-engine).
    ///
    /// Byte-identical macro invocation to [`Self::solve_lra_persistent_sat_arm`]
    /// (eager-persistent arm on `self.incr_theory_state` / `self.ctx.assertions`,
    /// tag "LRA-INC"); the only behavioral delta comes from the persistent SAT
    /// solver being in ic3-mode with scoped BVE disabled, which routes its
    /// per-solve reset through the incremental (state-preserving) path.
    /// `self.lra_persist_sat_active` must be set by the caller.
    fn solve_lra_inc_engine_arm(&mut self) -> Result<SolveResult> {
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();

        solve_incremental_split_loop_pipeline!(self,
            tag: "LRA-INC",
            persistent_sat_field: persistent_sat,
            create_theory: LraSolver::new(&self.ctx.terms),
            extract_models: |theory| {
                use super::solve_harness::TheoryModels;
                TheoryModels {
                    lra: Some(theory.extract_model()),
                    ..TheoryModels::default()
                }
            },
            max_splits: MAX_SPLITS_LRA,
            pre_theory_import: |_theory, _lc, _hc, _ds| {
                // LRA has no integer-specific learned state to import.
            },
            post_theory_export: |_theory| {
                // LRA has no integer-specific learned state to export.
                (vec![], Default::default(), Default::default())
            },
            persistent_theory: true,
            eager_extension: true,
            pre_iter_check: |_s| {
                solve_interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                || solve_deadline.expired()
            }
        )
    }

    /// Re-verify an incremental-engine Unsat via the trusted from-scratch
    /// standalone lane (#lra-inc-engine S1 backstop).
    ///
    /// Re-solves the current check-sat with [`Self::solve_lra_standalone_incremental`]
    /// (isolated state, from scratch — the exact default path when the engine
    /// lane is OFF) and returns the STANDALONE verdict. If the standalone lane
    /// does not confirm Unsat (a disagreement, i.e. the engine's Unsat was
    /// spurious — e.g. a persisted blocking clause or a retracted theory lemma),
    /// the sound standalone verdict wins. If the standalone lane is itself
    /// non-definite (budget/Unknown), fall back to the engine's original Unsat
    /// only when it was definite — but since the standalone lane is the trusted
    /// oracle we always prefer its verdict here; a standalone Unknown downgrades
    /// the check-sat to Unknown (fail-closed), never a wrong Unsat.
    fn reverify_unsat_via_standalone(
        &mut self,
        engine_result: Result<SolveResult>,
    ) -> Result<SolveResult> {
        let standalone = self.solve_lra_standalone_incremental();
        match &standalone {
            Ok(r) if r.is_unsat() => standalone,
            Ok(_) => {
                // Standalone disagrees (Sat/Unknown) — the engine's Unsat was not
                // confirmed by the trusted oracle. Take the standalone verdict.
                tracing::warn!(
                    engine = ?engine_result,
                    standalone = ?standalone,
                    "#lra-inc-engine Unsat NOT confirmed by standalone re-verify; taking standalone verdict (fail-closed)"
                );
                standalone
            }
            Err(_) => {
                tracing::warn!(
                    "#lra-inc-engine Unsat re-verify errored in standalone lane; downgrading to Unknown (fail-closed)"
                );
                Ok(SolveResult::Unknown)
            }
        }
    }

    /// Solve QF_LRA using the incremental split-loop pipeline with a local state.
    ///
    /// This uses `solve_incremental_split_loop_pipeline!` (the same macro as QF_LIA)
    /// to eliminate the full DpllT rebuild on each NeedDisequalitySplit. The SAT solver
    /// persists across split iterations, retaining all learned clauses, VSIDS scores,
    /// and phase saving.
    ///
    /// State isolation (#4919 design): Uses a temporary `IncrementalTheoryState` that
    /// is swapped into `self.incr_theory_state` for the duration of the solve, then
    /// discarded. This prevents the split-loop path from contaminating the push/pop
    /// incremental state when proof-enabled scripts route here (#6660).
    fn solve_lra_standalone_incremental(&mut self) -> Result<SolveResult> {
        let mut preprocess_time = std::time::Duration::default();
        let lifted_assertions = {
            let _preprocess_timer = PhaseTimer::new(&mut preprocess_time);
            self.preprocess_lra_assertions()
        };

        // Swap in a temporary isolated state for the standalone solve.
        // The macro reads from self.incr_theory_state, so we temporarily
        // replace it. The original state is restored after the solve.
        let saved_state = self.incr_theory_state.take();
        let mut temp_state = IncrementalTheoryState::new();

        // Pre-create the SAT solver with Z3-style geometric restarts and
        // random variable frequency. The macro's pipeline_incremental_setup!
        // will find this solver via state.persistent_sat and reuse it
        // (calling ensure_num_vars to resize). Without this, the standalone
        // path uses CaDiCaL-style stabilization restarts which are less
        // effective for theory-heavy QF_LRA benchmarks.
        {
            let random_seed = self.current_random_seed();
            let mut sat = SatSolver::new(0);
            sat.set_random_seed(random_seed);
            // #8093: Re-enable Z3-style geometric restarts for QF_LRA.
            // CaDiCaL-style restarts produce ~7500 restarts/5s on sc-23
            // vs Z3's 1 restart. Z3 uses RS_GEOMETRIC for QF_LRA —
            // growing intervals let simplex-guided search run deeper.
            sat.set_geometric_restarts(100.0, 1.5);
            sat.set_random_var_freq(0.01);
            if let Some(seed) = self.random_seed {
                sat.set_random_seed(seed);
            }
            if self.progress_enabled {
                sat.set_progress_enabled(true);
            }
            if let Some(path) = &self.progress_json_path {
                if let Ok(obs) = ay_sat::json_observer::JsonProgressObserver::new_append(path) {
                    sat.set_observer(Some(Box::new(obs)));
                }
            }
            ay_sat::TlaTraceable::maybe_enable_tla_trace_from_env(&mut sat);
            if self.produce_proofs_enabled() {
                sat.enable_clause_trace();
                sat.set_proof_bookkeeping_budget(self.search_proof_bookkeeping_budget());
            }
            temp_state.persistent_sat = Some(sat);
        }
        self.incr_theory_state = Some(temp_state);

        // Install preprocessed assertions for the macro to read.
        let original_assertions = std::mem::replace(&mut self.ctx.assertions, lifted_assertions);

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();

        let result = solve_incremental_split_loop_pipeline!(self,
            tag: "LRA",
            persistent_sat_field: persistent_sat,
            create_theory: LraSolver::new(&self.ctx.terms),
            extract_models: |theory| {
                use super::solve_harness::TheoryModels;
                TheoryModels {
                    lra: Some(theory.extract_model()),
                    ..TheoryModels::default()
                }
            },
            max_splits: MAX_SPLITS_LRA,
            pre_theory_import: |_theory, _lc, _hc, _ds| {
                // LRA has no integer-specific learned state to import.
            },
            post_theory_export: |_theory| {
                // LRA has no integer-specific learned state to export.
                (vec![], Default::default(), Default::default())
            },
            // #6590 Packet 3: Keep LraSolver alive across iterations with warm
            // simplex basis. soft_reset clears assertion/bound state; values
            // preserved by soft_reset_warm once correctness is verified.
            persistent_theory: true,
            // #6586: Enable eager theory-SAT interleaving via TheoryExtension.
            eager_extension: true,
            pre_iter_check: |_s| {
                solve_interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                || solve_deadline.expired()
            }
        );

        // Restore original state: discard the temporary state, put the original back.
        self.incr_theory_state = saved_state;
        self.ctx.assertions = original_assertions;

        // SOUNDNESS (#919-class false-SAT): the split-loop validated the model
        // against the *lifted* assertions (ITE Shannon-expanded into Boolean
        // ITEs), and may have set `last_model_validated = true`. The lifted
        // formula is only equisatisfiable with the original; a model that
        // satisfies the lifted Boolean-ITE skeleton can still violate the
        // ORIGINAL arithmetic ITE constraint (e.g. an arithmetic ITE whose
        // selected-branch equality is enforced only as a Boolean literal while
        // the simplex value drifted). Because we have now restored the original
        // assertions, clear `last_model_validated` on a SAT verdict so the
        // caller (`check_sat`) re-runs `finalize_sat_model_validation()` against
        // the ORIGINAL formula. If the model is spurious, validation fails
        // closed to Unknown instead of returning a wrong SAT. This caught
        // gasburner-prop3-{7,8,16} and pursuit-safety-3.
        if matches!(result, Ok(SolveResult::Sat)) {
            self.last_model_validated = false;
        }

        self.last_statistics
            .set_float("time.construct.preprocess", preprocess_time.as_secs_f64());
        result
    }

    /// Solve QF_LRA incrementally using SAT scope selectors.
    ///
    /// This method maintains a persistent SAT solver and TseitinState that retain
    /// learned clauses and term-to-var mappings across check-sat calls.
    /// Uses SAT scope selectors (push/pop) for correct scoping of assertion activations
    /// while keeping definitional clauses global for sound cached term→var reuse (#1432).
    pub(in crate::executor) fn solve_lra_incremental(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // #warm-theory: when AY_LRA_WARM_THEORY is set, mark this solve so the
        // persistent-theory pipeline reuses the LraSolver across check-sats. The
        // RAII guard restores the previous flag on return (incl. the internal
        // reverify's standalone call, which runs on a throwaway temp_state and so
        // stays a fresh, independent oracle). Default (unset) => flag false =>
        // byte-identical to before.
        let _warm_guard = crate::warm_theory_flag::WarmTheoryGuard::new(lra_warm_theory_on());

        let result = solve_incremental_theory_pipeline!(self,
            tag: "LRA",
            create_theory: LraSolver::new(&self.ctx.terms),
            extract_models: |theory| TheoryModels {
                lra: Some(theory.extract_model()),
                ..TheoryModels::default()
            },
            track_theory_stats: true,
            set_unknown_on_error: true,
            persistent_theory: true,
            pre_sat_solve: |sat_solver, _term_to_var| {
                // #8008: Use CaDiCaL-style restarts (default) instead of
                // geometric. See solve_lra() for rationale.
                sat_solver.set_random_var_freq(0.01);
            }
        );

        // SOUNDNESS (#9604-class false-UNSAT): the persistent push/pop QF_LRA
        // pipeline (this method) has a multi-arg-`distinct` + ITE + push
        // interaction that can derive a propositional UNSAT from individually
        // sound theory conflicts under a Boolean branch that is actually
        // satisfiable (the spurious UNSAT survives even after the assume_eqs
        // disequality-closure guard; the non-incremental STANDALONE path solves
        // the same constraints correctly). Concretely, the fuzzer found a
        // satisfiable formula with `(distinct (+ v3 v1) (* -3 v1) v1)` under two
        // nested pushes that this pipeline reported UNSAT while z3 (and AY's own
        // standalone path on the flattened conjunction) returns SAT.
        //
        // Re-verify any UNSAT verdict here against the independent standalone
        // split-loop path, which (a) is a genuinely different code path with the
        // C5 model-validation-failure guard, and (b) operates on the current
        // active assertion conjunction in `self.ctx.assertions`. We only do this
        // when an active assertion actually contains a `distinct` — the fragile
        // construct that drives the false-UNSAT — so pure k-induction QF_LRA
        // (hybrid_networks: no `distinct`/`ite`, multi-MB) is never re-solved and
        // completeness/throughput there is unaffected. If the independent check
        // disagrees (sat/unknown), we return that sound result instead of the
        // suspect UNSAT. Genuine distinct-contradiction UNSATs are preserved: the
        // standalone path returns UNSAT for them too (validated on the
        // (= a b)∧(= b c)∧(distinct a b c) family).
        //
        // The re-verification is UNCONDITIONAL: the former
        // AY_NO_LRA_INC_UNSAT_REVERIFY=1 kill switch (skip the re-check and
        // trust the incremental UNSAT directly) is removed — no environment
        // variable may turn off a soundness guard.
        if matches!(result, Ok(ref r) if r.is_unsat())
            && !self.should_abort_theory_loop()
            && self.lra_assertions_contain_disequality()
        {
            // The standalone path saves/restores incr_theory_state and
            // ctx.assertions internally, so calling it here does not disturb the
            // persistent incremental state used by later push/pop check-sats.
            let reverify = self.solve_lra_standalone_incremental();
            match reverify {
                Ok(ref r) if r.is_unsat() => {
                    // Independent confirmation — keep the original UNSAT.
                }
                Ok(other) => {
                    tracing::warn!(
                        "QF_LRA incremental UNSAT not confirmed by independent standalone re-check; \
                         downgrading suspect UNSAT (#9604 false-UNSAT guard)"
                    );
                    // self.last_result / last_model were set by the standalone
                    // re-solve; mirror its verdict so check_sat's model
                    // validation operates on the (sound) standalone outcome.
                    return Ok(other);
                }
                Err(_) => {
                    // Re-verification failed to run — fail closed to Unknown
                    // rather than emit an unconfirmed UNSAT.
                    self.last_unknown_reason =
                        Some(crate::executor_types::UnknownReason::Incomplete);
                    self.last_result = Some(SolveResult::Unknown);
                    return Ok(SolveResult::Unknown);
                }
            }
        }

        result
    }

    /// True when any currently-active assertion (transitively) contains a
    /// disequality — a `distinct` application, or a negated arithmetic equality
    /// `(not (= a b))` — the construct implicated in the persistent push/pop
    /// QF_LRA false-UNSAT (#9604). Note that by the time this pipeline runs, the
    /// frontend has already decomposed `(distinct a b c)` into a conjunction of
    /// `(not (= _ _))` pairwise disequalities, so the gate MUST recognise the
    /// `Not(=)` form (a bare `distinct`-name scan misses every decomposed case).
    ///
    /// Used to gate the independent UNSAT re-verification so pure-inequality
    /// k-induction QF_LRA (hybrid_networks: no distinct/disequality, multi-MB)
    /// is never re-solved and its throughput is unaffected.
    pub(in crate::executor) fn lra_assertions_contain_disequality(&self) -> bool {
        self.lra_roots_contain_disequality(&[])
    }

    /// Roots-based variant of [`Self::lra_assertions_contain_disequality`]:
    /// scans the active assertions PLUS `extra_roots`. The
    /// check-sat-assuming gate passes its assumption literals here — with
    /// `:produce-unsat-cores`, named assertions are moved out of
    /// `ctx.assertions` into the assumption set for the duration of the
    /// check, so scanning `ctx.assertions` alone would miss a fragile
    /// construct inside a named assertion (or an assumption literal) and let
    /// a suspect UNSAT through the #9604 fail-close gate.
    pub(in crate::executor) fn lra_roots_contain_disequality(
        &self,
        extra_roots: &[TermId],
    ) -> bool {
        use ay_core::term::{Symbol, TermData};
        let terms = &self.ctx.terms;
        let is_eq_app = |t: TermId| matches!(terms.get(t), TermData::App(Symbol::Named(name), _) if name == "=");
        let mut seen = std::collections::HashSet::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        stack.extend_from_slice(extra_roots);
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match terms.get(t) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == "distinct" {
                        return true;
                    }
                    // `(not (= a b))` rendered as an App("not", [eq]).
                    if name == "not" && args.len() == 1 && is_eq_app(args[0]) {
                        return true;
                    }
                    // #9604-followup: the persistent push/pop false-UNSAT also
                    // arises WITHOUT any disequality, via the ITE / disjunction
                    // Boolean-structure interaction (e.g. an empty-push re-check
                    // of an equality+ite+strict formula returned spurious unsat).
                    // Treat `ite`/`or` as fragile constructs that warrant the
                    // independent UNSAT re-verification. Pure-conjunctive-linear
                    // k-induction QF_LRA (hybrid_networks: only and/<=/</=/>=,
                    // no ite/or/distinct) is unaffected and stays on the fast path.
                    if name == "ite" || name == "or" {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => {
                    if is_eq_app(*inner) {
                        return true;
                    }
                    stack.push(*inner);
                }
                TermData::Ite(_, _, _) => {
                    return true;
                }
                TermData::Let(bindings, body) => {
                    stack.push(*body);
                    stack.extend(bindings.iter().map(|(_, v)| *v));
                }
                _ => {}
            }
        }
        false
    }

    /// Classify a fresh single `LraSolver::check()` of an assignment's theory
    /// atoms into "blocking this assignment is SOUND" vs "NOT sound".
    ///
    /// ROOT-CAUSE FIX (split-loop / eager-persistent QF_LRA false-UNSAT, the
    /// r7519 / minimized-core class where AY returned unsat but z3 returns sat):
    /// the model-validation-failure blocking guard (#9604) decided whether
    /// blocking a Boolean assignment was sound by calling `LraSolver::check()`
    /// ONCE and treating any *non-`Sat`* result as "genuinely UNSAT → safe to
    /// block". That classification is UNSOUND. Over the reals, a single `check()`
    /// of a linear-feasible atom set containing `distinct` / `(not (= ..))`
    /// disequalities returns `NeedDisequalitySplit` / `NeedExpressionSplit` —
    /// a "must case-split to decide" status, NOT a proof of unsatisfiability —
    /// whenever the chosen simplex vertex happens to land on a disequality
    /// hyperplane while the constraint still has slack. Such a set is
    /// SATISFIABLE (repair the witness by an epsilon shift off the hyperplane).
    /// Treating that as license to block removes a satisfiable region, and a
    /// later propositional UNSAT becomes a false-UNSAT.
    ///
    /// Only a definitive `Unsat` / `UnsatWithFarkas` from `check()` proves the
    /// assignment theory-UNSAT: the linear relaxation is infeasible, or a
    /// disequality is genuinely *pinned* (variables fixed onto the excluded
    /// hyperplane with no slack). Both are sound reasons to block. Every other
    /// status (`Sat`, `NeedDisequalitySplit`, `NeedExpressionSplit`, `NeedSplit`,
    /// lemmas, model-equality requests, `Unknown`, …) means the assignment is
    /// NOT proven theory-UNSAT, so blocking it would be unsound.
    ///
    /// Returns `true` iff the re-check is a definitive `Unsat`/`UnsatWithFarkas`
    /// (blocking is sound).
    pub(in crate::executor) fn lra_assignment_recheck_proves_unsat(
        &self,
        assignment_lits: &[ay_core::TheoryLit],
    ) -> bool {
        use ay_core::{TheoryResult, TheorySolver};
        if assignment_lits.is_empty() {
            return false;
        }
        let mut check_lra = LraSolver::new(&self.ctx.terms);
        for tl in assignment_lits {
            check_lra.assert_literal(tl.term, tl.value);
        }
        matches!(
            check_lra.check(),
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        )
    }

    /// Completeness recovery for the model-validation blocking guard: re-solve
    /// the conjunction of an assignment's theory-atom literals with the COMPLETE
    /// QF_LRA split-loop (which drives disequality/expression splits to a valid
    /// model), and return its verdict.
    ///
    /// Used only when the quick single-`check()` re-check did NOT prove the
    /// assignment theory-UNSAT, so blocking would be unsound. Rather than fail
    /// closed to Unknown (which would lose a genuine SAT answer — the r7519
    /// class), we obtain a sound, model-validated verdict here: the standalone
    /// split-loop resolves the disequalities and produces a witness that respects
    /// them, so a SATISFIABLE assignment is reported as `Sat` with a valid model.
    ///
    /// Returns `Ok(SolveResult)` and (on `Sat`) leaves `self.last_model` /
    /// `self.last_result` set to the recovered model so the caller can publish
    /// it. The standalone path saves/restores `incr_theory_state` internally; we
    /// additionally save/restore `ctx.assertions`. A re-entrancy flag
    /// (`lra_in_assignment_recheck`) makes the nested arm fail closed at its own
    /// guard, guaranteeing termination.
    pub(in crate::executor) fn lra_recover_assignment_verdict(
        &mut self,
        assignment_lits: &[ay_core::TheoryLit],
    ) -> Result<SolveResult> {
        if assignment_lits.is_empty() {
            return Ok(SolveResult::Unknown);
        }
        let mut conj: Vec<TermId> = Vec::with_capacity(assignment_lits.len());
        for tl in assignment_lits {
            let lit_term = if tl.value {
                tl.term
            } else {
                self.ctx.terms.mk_not(tl.term)
            };
            conj.push(lit_term);
        }
        let conjunction = if conj.len() == 1 {
            conj[0]
        } else {
            self.ctx.terms.mk_and(conj)
        };

        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, vec![conjunction]);
        let saved_recheck = self.lra_in_assignment_recheck;
        self.lra_in_assignment_recheck = true;

        let result = self.solve_lra_standalone_incremental();

        self.lra_in_assignment_recheck = saved_recheck;
        self.ctx.assertions = saved_assertions;

        result
    }
}
