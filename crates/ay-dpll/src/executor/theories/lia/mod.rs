// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear Integer Arithmetic (LIA) and Non-Linear Integer Arithmetic (NIA) solving.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
#[cfg(test)]
mod tests;

use ay_core::time::Instant;
use std::sync::atomic::Ordering;

use ay_core::TermId;
use ay_lia::{LiaModel, LiaSolver};
use ay_nia::NiaSolver;

use super::super::Executor;
// Re-export so `super::lia::recover_*` paths in combined.rs continue to work.
pub(in crate::executor) use super::lia_eval::{
    backfill_opaque_app_values_from_equalities, eval_lia_int_under_values,
    recompute_composite_int_values, reconcile_lia_select_congruence,
    recover_lia_equalities_from_assertions, recover_substituted_bool_values,
    recover_substituted_lia_values, recover_substituted_lia_values_protecting,
    recover_uninterpreted_equalities_from_assertions,
};
use super::MAX_SPLITS_LIA;
use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;
use crate::executor_types::{Result, SolveResult};
use crate::preprocess::VariableSubstitution;

impl Executor {
    /// Solve QF_LIA through the dedicated LIA split-loop pipeline.
    ///
    /// Standalone QF_LIA uses eager theory-SAT interleaving on the dedicated
    /// `lia_*` SAT/Tseitin state so bound and simplex propagations can prune
    /// search during BCP. Incremental push/pop sessions get the same eager
    /// arm through a temporary isolated state at scope depth 0 (Fix B1);
    /// proof-producing sessions fall back to the lazy model-enumeration arm.
    pub(in crate::executor) fn solve_lia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        self.solve_lia_incremental()
    }

    /// Solve QF_LIA incrementally using SAT scope selectors.
    ///
    /// Maintains persistent Tseitin mappings and SAT solver across check-sat calls.
    /// Scopes branch-and-bound split clauses to each `check-sat` via push/pop.
    /// Uses `solve_incremental_split_loop_pipeline!` for the DPLL(T) loop with
    /// branch-and-bound splits (NeedSplit, NeedDisequalitySplit, NeedExpressionSplit).
    pub(in crate::executor) fn solve_lia_incremental(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        let original_problem_assertions = self.ctx.assertions.clone();
        let artifacts = self.preprocess_lia_artifacts();
        let introduced_unconstrained_div_mod = artifacts.introduced_unconstrained_div_mod;
        if crate::features::StaticFeatures::collect(&self.ctx.terms, &artifacts.assertions)
            .has_int_div_mod
        {
            if let Some(result) = self.try_sat_via_mod_free_or_branch()? {
                return Ok(result);
            }
        }
        let current_scope_depth = self
            .incr_theory_state
            .as_ref()
            .map_or(0, |state| state.scope_depth);
        let source_depths = self.ctx.active_assertion_min_scope_depths();
        let mut derived_assertion_entries = Vec::new();
        for (&term, source_sets) in &artifacts.assertion_sources {
            for sources in source_sets {
                let activation_depth = sources
                    .iter()
                    .map(|source| {
                        source_depths
                            .get(source)
                            .copied()
                            .unwrap_or(current_scope_depth)
                    })
                    .max()
                    .unwrap_or(current_scope_depth);
                derived_assertion_entries.push((term, activation_depth, sources.clone()));
            }
        }

        {
            let state = self
                .incr_theory_state
                .get_or_insert_with(crate::incremental_state::IncrementalTheoryState::new);
            state.replace_lia_derived_assertions(derived_assertion_entries);
            state.retain_encoded_assertions(&artifacts.assertions);
        }

        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            original_problem_assertions,
            &artifacts.assertions,
            artifacts.assertion_sources.clone(),
        );

        // Packet 1 (#6698): Suppress minimization while the preprocessed
        // assertions are installed. The minimizer must run against the original
        // user-facing formula after substituted variables are recovered.
        let saved_style = self.counterexample_style();
        let saved_proof_provenance = self.proof_problem_assertion_provenance.clone();
        let proof_provenance =
            proof_provenance.preserving_authority_from(saved_proof_provenance.as_ref());
        self.set_counterexample_style(crate::CounterexampleStyle::Any);
        self.proof_problem_assertion_provenance = Some(proof_provenance);

        let original_assertions = std::mem::replace(&mut self.ctx.assertions, artifacts.assertions);
        let mut result = self.solve_lia_incremental_inner(Some(&artifacts.var_subst));

        // Restore original assertions and counterexample style before model
        // recovery and validation against the user-visible formula.
        self.ctx.assertions = original_assertions;
        self.set_counterexample_style(saved_style);
        if !matches!(result, Ok(ref r) if r.is_unsat()) {
            self.proof_problem_assertion_provenance = saved_proof_provenance;
        }

        if matches!(result, Ok(SolveResult::Sat)) {
            if let Some(model) = self
                .last_model
                .as_mut()
                .and_then(|model| model.lia_model.as_mut())
            {
                recover_substituted_lia_values(&self.ctx.terms, &artifacts.var_subst, model);
                recover_lia_equalities_from_assertions(
                    &self.ctx.terms,
                    &self.ctx.assertions,
                    model,
                );
            }

            // Recover Bool variables eliminated by VariableSubstitution.
            // E.g., (= p (> x 0)) substitutes p -> (> x 0); the SAT model
            // has no assignment for p, so model validation of the original
            // assertion fails. Evaluate the substitution RHS against the
            // recovered LIA model to compute p's Bool value.
            if let Some(ref full_model) = self.last_model {
                let lia_values = full_model
                    .lia_model
                    .as_ref()
                    .map(|m| &m.values)
                    .cloned()
                    .unwrap_or_default();
                let bool_overrides = recover_substituted_bool_values(
                    &self.ctx.terms,
                    &artifacts.var_subst,
                    &lia_values,
                );
                if !bool_overrides.is_empty() {
                    if let Some(ref mut full_model) = self.last_model {
                        full_model.bool_overrides.extend(bool_overrides);
                    }
                }
            }

            if self.minimize_counterexamples_enabled() && self.last_assumptions.is_none() {
                self.minimize_model_sat_preserving();
            }
            // #div0: When mod/div elimination introduced an unconstrained fresh
            // var for a (possibly) zero divisor, the standard model evaluator
            // returns Unknown on the original `(div a 0)` term and would degrade
            // this SAT to Unknown. Satisfiability follows soundly from the
            // rewritten constraints; route through the validation bypass (still
            // gated by the strict definitive-false oracle).
            if introduced_unconstrained_div_mod {
                self.sat_validated_by_mod_div_or_branch = true;
            }
            self.last_model_validated = false;
            result = self.finalize_sat_model_validation();
        }

        result
    }

    /// Solve QF_LIA with assumptions through the dedicated LIA pipeline (#6728).
    ///
    /// Applies the same preprocessing family as `solve_lia_incremental()`:
    /// VariableSubstitution, NormalizeArithSom, ITE lifting, mod/div elimination.
    /// Assumptions get the same treatment while preserving original-term identity
    /// for UNSAT-core and proof reporting.
    pub(in crate::executor) fn solve_lia_with_assumptions(
        &mut self,
        _assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // Note: _assertions param preserved for API parity with other assumption
        // solvers. Assertions come from self.ctx.assertions via preprocess_lia_artifacts().

        // Validate: all assumptions must be Bool-sorted.
        // Non-Bool assumptions are user errors that should surface as InternalError
        // (the API layer catches Err and maps to Unknown/InternalError).
        for &a in assumptions {
            if *self.ctx.terms.sort(a) != ay_core::Sort::Bool {
                return Err(crate::executor_types::ExecutorError::Dpll(
                    crate::DpllError::UnexpectedTheoryResult,
                ));
            }
        }

        // Eager differential probe (#nip, negative_int_pats class): the lazy
        // assume arm below does hundreds of theory round-trips on integer
        // pattern-match goals that the eager DPLL(T) arm solves in <1s, but
        // the eager arm historically only ran on the plain (non-assume)
        // path. Try two FRESH eager solves first; fall back to the lazy arm
        // (today's behavior, bit-for-bit) on anything but a certified UNSAT.
        if let Some(result) = self.try_lia_eager_assume_unsat_probe(assumptions)? {
            return Ok(result);
        }

        // Preprocess assertions (same family as plain check-sat)
        let mut artifacts = self.preprocess_lia_artifacts();

        // Preprocess assumptions using the same VariableSubstitution
        let assume_result = self.preprocess_lia_assumptions(assumptions, &mut artifacts.var_subst);

        // Merge constraint assertions from assumption mod/div elimination
        let mut all_assertions = artifacts.assertions;
        all_assertions.extend(assume_result.extra_assertions);

        let var_subst = artifacts.var_subst;
        // Extract Bool substitutions before var_subst is moved into the closure.
        // We only need the Bool-sorted entries for post-solve Bool recovery.
        let bool_substitutions: HashMap<TermId, TermId> = var_subst
            .substitutions()
            .iter()
            .filter(|(&from, _)| matches!(self.ctx.terms.sort(from), ay_core::Sort::Bool))
            .map(|(&from, &to)| (from, to))
            .collect();
        let final_assumptions = assume_result.assumptions;
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            self.ctx.assertions.clone(),
            &all_assertions,
            artifacts.assertion_sources.clone(),
        );

        let result = self.with_deferred_postprocessing(all_assertions, proof_provenance, |this| {
            solve_incremental_assume_split_loop_pipeline!(this,
                tag: "LIA-ASSUME",
                persistent_sat_field: persistent_sat,
                assumptions: &final_assumptions,
                create_theory: {
                    // #8749: Install the solve deadline on the theory so the
                    // IntSat probe honours `--timeout` instead of letting its
                    // BigInt conflict loop overshoot by seconds.
                    let mut theory = LiaSolver::new(&this.ctx.terms);
                    if let Some(dl) = solve_deadline.get() {
                        theory.set_deadline(dl);
                    }
                    // Executor-scoped propagation-off option (CHC BMC TS lane,
                    // sat-side-model-search diagnosis). Applied to the inner
                    // LraSolver of every LIA theory instance.
                    if this.no_lra_theory_propagation {
                        theory.lra_solver_mut().set_no_theory_propagation(true);
                    }
                    theory
                },
                extract_models: |theory| {
                    use super::solve_harness::TheoryModels;
                    let mut lia = theory.extract_model();
                    if let Some(model) = lia.as_mut() {
                        recover_substituted_lia_values(&this.ctx.terms, &var_subst, model);
                        recover_lia_equalities_from_assertions(
                            &this.ctx.terms,
                            &this.ctx.assertions,
                            model,
                        );
                    }
                    TheoryModels { lia, ..TheoryModels::default() }
                },
                max_splits: MAX_SPLITS_LIA,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(
                        std::mem::take(lc),
                        std::mem::take(hc),
                    );
                    theory.import_dioph_state(std::mem::take(ds));
                },
                post_theory_export: |theory| {
                    let (lc, hc) = theory.take_learned_state();
                    let ds = theory.take_dioph_state();
                    (lc, hc, ds)
                },
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(Ordering::Relaxed))
                    || solve_deadline.expired()
                }
            )
        });

        // Recover Bool variables eliminated by VariableSubstitution.
        // with_deferred_postprocessing has restored the original assertions;
        // model validation will run against those originals. Bool variables
        // like `p` in `(= p (> x 0))` need their values computed from the
        // LIA model so the evaluator can verify the equality.
        if matches!(result, Ok(SolveResult::Sat)) && !bool_substitutions.is_empty() {
            if let Some(ref full_model) = self.last_model {
                let lia_values = full_model
                    .lia_model
                    .as_ref()
                    .map(|m| &m.values)
                    .cloned()
                    .unwrap_or_default();
                let mut bool_overrides = HashMap::default();
                for (&from, &to) in &bool_substitutions {
                    if let Some(val) =
                        crate::executor::theories::lia_eval::eval_lia_bool_under_values(
                            &self.ctx.terms,
                            to,
                            &lia_values,
                        )
                    {
                        bool_overrides.insert(from, val);
                    }
                }
                if !bool_overrides.is_empty() {
                    if let Some(ref mut full_model) = self.last_model {
                        full_model.bool_overrides.extend(bool_overrides);
                    }
                }
            }
        }

        result
    }

    /// Eager UNSAT probe with deletion-minimized core, for the
    /// cores-redirect assume path (#nip, negative_int_pats class).
    ///
    /// The lazy assume arm below does hundreds of theory round-trips on
    /// integer pattern-match goals that the eager DPLL(T) arm solves in
    /// <1s, but the eager arm historically ran only on the plain
    /// (non-assume) path. This probe:
    ///
    /// 1. r1 = eager solve of (base UNION all assumptions-as-assertions).
    ///    Anything but UNSAT -> fall back to the lazy arm (bit-for-bit
    ///    today's behavior). UNSAT(base AND assumptions) == UNSAT of the
    ///    check-sat-assuming problem (conjunction semantics), and its
    ///    soundness is the existing eager pipeline's own guarantee
    ///    (theory-valid lemmas, #8727 tautological splits,
    ///    `_ext_partial > 0` escalates to Unknown inside the pipeline).
    /// 2. Deletion-based core minimization: for each assumption, re-solve
    ///    eagerly WITHOUT it; if still UNSAT the assumption is droppable.
    ///    Every removal is certified by an actual UNSAT solve, so the final
    ///    set S satisfies UNSAT(base UNION S) by construction -- a CORRECT
    ///    core. An irrelevant negated-goal assumption is therefore EXCLUDED
    ///    from the core, which makes verifier vacuity detection (goal-absent
    ///    == vacuous) WORK on this path -- stronger than both the lazy arm's
    ///    timeout behavior and the quantified path's all-assumptions cores.
    ///    A drop-test returning Unknown aborts minimization (keep the
    ///    last certified core; stay within budget).
    /// 3. Base-alone-UNSAT degenerates to S = [] -> stored as Some([]),
    ///    which `get-unsat-core` pads to all named assertions exactly like
    ///    today's lost-tracking paths (no semantic change, no new channel).
    ///
    /// Proofs-on sessions skip the probe (it materializes no proof
    /// artifacts; the lazy arm retains its full proof plumbing). Sessions
    /// with > 16 assumptions skip it (cost cap).
    ///
    /// State containment: every probe solve goes through
    /// `solve_lia_incremental`, which resets the dedicated `lia_*` SAT state
    /// at entry (#6853); the temporary `incremental_mode = false` window
    /// only routes these self-contained fresh solves to the eager arm. The
    /// shared `persistent_sat` field used by the assume/EUF/LRA pipelines is
    /// untouched, and `ctx.assertions` is temporarily extended exactly like
    /// the BV assume path does (assumption_solving.rs).
    /// Whether the eager probe should DECLINE a certified UNSAT so the lazy
    /// assume-split arm can harvest a real failed-assumption core, rather than
    /// publishing the padded all-assumptions core (see the call site).
    ///
    /// Two conditions make declining safe, and both are load-bearing:
    ///
    /// 1. **Only when cores are being produced.** This probe sits on the
    ///    GENERAL assumption path (`solve_lia_with_assumptions`), not a
    ///    UC-only one. Outside core production the unsat ANSWER is the entire
    ///    value, and declining stakes it on the lazy arm re-deriving what we
    ///    already proved — a real risk for no gain, since nothing reads the
    ///    core. Under `produce-unsat-cores` the padded core is worth zero, so
    ///    there is genuinely nothing to lose. The plain path therefore keeps
    ///    today's behaviour bit-for-bit.
    /// 2. **Only with budget to spare.** `r1` has already been paid once and
    ///    the lazy arm re-solves from scratch, so require the caller's restored
    ///    deadline to cover several more solves of that size. Note `r1`
    ///    returned UNSAT, so it completed inside its own 40%-of-remaining cap
    ///    and `r1_elapsed` is a true measure of the work rather than a
    ///    truncated one — a capped-out probe would have returned Unknown and
    ///    taken the earlier `!matches!(r1, Unsat)` exit.
    ///
    /// `AY_NO_UC_LIA_PROBE_FALLTHROUGH=1` restores the previous behaviour.
    fn uc_probe_should_decline(
        &self,
        r1_elapsed: std::time::Duration,
        deadline: Option<Instant>,
    ) -> bool {
        if !self.produce_unsat_cores_enabled() {
            return false;
        }
        if std::env::var_os("AY_NO_UC_LIA_PROBE_FALLTHROUGH").is_some() {
            return false;
        }
        deadline.is_none_or(|dl| Instant::now() + r1_elapsed.saturating_mul(4) < dl)
    }

    fn try_lia_eager_assume_unsat_probe(
        &mut self,
        assumptions: &[TermId],
    ) -> Result<Option<SolveResult>> {
        const MAX_PROBE_ASSUMPTIONS: usize = 8192;
        if assumptions.is_empty()
            || assumptions.len() > MAX_PROBE_ASSUMPTIONS
            || self.produce_proofs_enabled()
        {
            return Ok(None);
        }

        let saved_assertions = self.ctx.assertions.clone();
        let saved_incremental = self.incremental_mode;
        self.incremental_mode = false;
        // r1 budget cap: the probe must never consume the caller's whole
        // deadline on a hard SAT-shaped problem (the lazy arm needs the
        // remainder to conclude rejection — observed on verification-consumer 692.rs,
        // where an uncapped r1 turned a decisive should_fail rejection into
        // unknown). Give r1 at most ~40% of the remaining budget; restore
        // the original deadline for the fallback path.
        let saved_deadline = self.solve_deadline.get();
        if let Some(dl) = self.solve_deadline.get() {
            let remaining = dl.saturating_duration_since(Instant::now());
            let r1_budget = remaining
                .mul_f32(0.4)
                .max(std::time::Duration::from_millis(750));
            self.solve_deadline
                .set(Some(Instant::now() + r1_budget.min(remaining)));
        }
        // The eager split-loop refuses scope_depth != 0 ("requires isolated
        // scope depth 0") -- bookkeeping protection for layered persistent
        // activation state, which the probe's fresh solves do not use (the
        // lia_* state is reset at every solve_lia_incremental entry, #6853).
        // `ctx.assertions` is the live FLATTENED assertion set (frontend
        // push/pop maintains it), so a depth-0 fresh solve over it is exactly
        // the current semantic problem. Zero the depth for the probe window
        // and restore it after.
        let saved_scope_depth = self.incr_theory_state.as_ref().map(|st| st.scope_depth);
        if let Some(st) = self.incr_theory_state.as_mut() {
            st.scope_depth = 0;
        }

        let solve_with = |this: &mut Self, subset: &[TermId]| -> Result<SolveResult> {
            this.ctx.assertions = saved_assertions.clone();
            this.ctx.assertions.extend_from_slice(subset);
            this.solve_lia_incremental()
        };

        // r1: the full conjunction.
        let restore = |this: &mut Self, saved_inc: bool, saved_asserts: &Vec<TermId>| {
            this.incremental_mode = saved_inc;
            this.ctx.assertions = saved_asserts.clone();
            this.solve_deadline.set(saved_deadline);
            if let (Some(st), Some(depth)) = (this.incr_theory_state.as_mut(), saved_scope_depth) {
                st.scope_depth = depth;
            }
        };
        let probe_start = Instant::now();
        let r1 = match solve_with(self, assumptions) {
            Ok(r) => r,
            Err(e) => {
                restore(self, saved_incremental, &saved_assertions);
                return Err(e);
            }
        };
        if !matches!(r1, SolveResult::Unsat(_)) {
            restore(self, saved_incremental, &saved_assertions);
            return Ok(None);
        }

        // Deletion-based minimization: certified-UNSAT invariant on `core`.
        //
        // Budget guard: each drop-test re-solves the problem, so minimization
        // costs up to n * r1_time. Only minimize when the solve is CHEAP
        // (fast r1) and the remaining deadline budget can afford it;
        // otherwise keep the all-assumptions core -- the same conservative
        // over-approximation the quantified assumption path has always
        // reported (check_sat_assuming solve_quantified_assumptions), with
        // identical consumer semantics. Verifier vacuity precision is
        // retained exactly where it is affordable.
        let mut core: Vec<TermId> = assumptions.to_vec();
        let r1_elapsed = probe_start.elapsed();
        // n-cap: with thousands of assumptions, n drop-tests cost seconds
        // even at ~1ms each (observed: a preprocessing improvement made r1
        // fast on a 4105-assumption problem and the uncapped minimization
        // burned ~10s standalone, where no deadline bounds the work). Large
        // cores barely sharpen consumer vacuity attribution anyway.
        const MAX_MINIMIZE_ASSUMPTIONS: usize = 128;
        let budget_allows_minimization = assumptions.len() <= MAX_MINIMIZE_ASSUMPTIONS
            && r1_elapsed.as_millis() <= 1_000
            && self.solve_deadline.get().is_none_or(|dl| {
                let need = r1_elapsed
                    .saturating_mul(u32::try_from(assumptions.len().max(1)).unwrap_or(u32::MAX))
                    .saturating_mul(2);
                Instant::now() + need < dl
            });
        if budget_allows_minimization {
            for &candidate in assumptions {
                let trial: Vec<TermId> = core.iter().copied().filter(|&t| t != candidate).collect();
                match solve_with(self, &trial) {
                    Ok(SolveResult::Unsat(_)) => core = trial,
                    Ok(SolveResult::Sat) => {}
                    Ok(SolveResult::Unknown) => break,
                    Err(e) => {
                        restore(self, saved_incremental, &saved_assertions);
                        return Err(e);
                    }
                }
            }
        } else if self.uc_probe_should_decline(r1_elapsed, saved_deadline) {
            // We cannot afford to minimize, so the only core this arm can
            // publish is `assumptions.to_vec()` — every assumption, 100% of
            // them. That is CORRECT but worth exactly ZERO on the UnsatCore
            // metric, which scores `asserts - core_size`: a 100%-assumption
            // core and no answer at all earn the same nothing. Meanwhile the
            // lazy assume-split arm below harvests a genuine failed-assumption
            // core from the SAT solver essentially for free — measured 8201
            // assumptions down to a 2-element core in 0.07s, against this
            // arm's 8001 down to 8001.
            //
            // So when cores are being produced, DECLINE instead of publishing
            // the padded one and pre-empting the arm that would do better.
            // `uc_probe_should_decline` carries the two conditions that make
            // this safe; see its doc comment.
            restore(self, saved_incremental, &saved_assertions);
            return Ok(None);
        }
        restore(self, saved_incremental, &saved_assertions);

        // Certified UNSAT with a deletion-verified core. Clear any SAT model
        // left by a failed drop-test (we report UNSAT of the full problem).
        self.last_model = None;
        self.last_assumption_core = Some(core);
        self.last_unknown_reason = None;
        let result = SolveResult::unsat();
        self.last_result = Some(result.clone());
        Ok(Some(result))
    }

    fn solve_lia_incremental_inner(
        &mut self,
        var_subst: Option<&VariableSubstitution>,
    ) -> Result<SolveResult> {
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();

        // #6853: LIA preprocessing can change the assertion set between
        // check-sats, creating different Tseitin encodings each time.
        // Accumulated global definition clauses from prior check-sats
        // over-constrain the variable space, causing false UNSAT when
        // combined with the current formula's activation clauses.
        //
        // Fix: reset the LIA-specific SAT solver and encoding state so
        // each check-sat starts clean. The LIA pipeline uses dedicated
        // lia_* fields (not the shared fields) to avoid interference
        // with EUF/LRA's persistent state.
        self.incr_theory_state
            .get_or_insert_with(crate::incremental_state::IncrementalTheoryState::new)
            .reset_lia_sat();

        // Standalone QF_LIA lane: run the eager BCP-interleaved arm directly
        // on the session's own IncrementalTheoryState (scope depth is 0).
        if !self.incremental_mode {
            return self.solve_lia_eager_split_loop(var_subst);
        }

        // Fix B1 (lia-hot-loop plan): incremental push/pop sessions also get
        // eager theory propagation by running the same eager split-loop
        // against a TEMPORARY isolated IncrementalTheoryState at scope depth
        // 0, exactly the way solve_lra_standalone_incremental isolates its
        // split-loop state (#4919/#6660). This satisfies the eager arm's
        // "isolated scope depth 0" requirement without touching the macro.
        //
        // Soundness: a check-sat in incremental mode must decide the
        // conjunction of all currently-active assertions, and the caller has
        // already installed exactly that set (preprocessed) in
        // self.ctx.assertions. Nothing persistent is lost: incremental QF_LIA
        // already resets its lia_* SAT/Tseitin state per check-sat (#6853,
        // reset_lia_sat above), so the lazy arm carried no cross-check-sat
        // SAT learning either. The temp state is discarded after the solve
        // and the session state (scope_depth, shared EUF/LRA fields, derived
        // assertion metadata) is restored untouched.
        //
        // Proof-producing sessions stay on the lazy arm: eager-incremental
        // proof artifacts are not yet validated (plan §3.6); CHC BMC/PDR/
        // Houdini traffic does not consume proofs.
        let eager_routing =
            self.lia_incremental_eager_override.unwrap_or(true) && !self.produce_proofs_enabled();
        if eager_routing {
            let saved_state = self.incr_theory_state.take();
            self.incr_theory_state = Some(crate::incremental_state::IncrementalTheoryState::new());
            let result = self.solve_lia_eager_split_loop(var_subst);
            // The macro stored the temp state back into incr_theory_state;
            // discard it and restore the session's persistent state.
            self.incr_theory_state = saved_state;
            return result;
        }

        // Lazy model-enumeration fallback (kill switch / proof sessions).
        solve_incremental_split_loop_pipeline!(self,
            tag: "LIA",
            persistent_sat_field: lia_persistent_sat,
            tseitin_field: lia_tseitin_state,
            encoded_field: lia_encoded_assertions,
            activation_scope_field: lia_assertion_activation_scope,
            create_theory: {
                // #8749: Propagate deadline into LIA so IntSat probe honours --timeout.
                let mut theory = LiaSolver::new(&self.ctx.terms);
                if let Some(dl) = solve_deadline.get() {
                    theory.set_deadline(dl);
                }
                // Executor-scoped propagation-off option (CHC BMC TS lane,
                // sat-side-model-search diagnosis). Applied to the inner
                // LraSolver of every LIA theory instance.
                if self.no_lra_theory_propagation {
                    theory.lra_solver_mut().set_no_theory_propagation(true);
                }
                theory
            },
            extract_models: |theory| {
                use super::solve_harness::TheoryModels;
                let mut lia = theory.extract_model();
                if let (Some(var_subst), Some(model)) = (var_subst, lia.as_mut()) {
                    recover_substituted_lia_values(&self.ctx.terms, var_subst, model);
                }
                TheoryModels { lia, ..TheoryModels::default() }
            },
            max_splits: MAX_SPLITS_LIA,
            pre_theory_import: |theory, lc, hc, ds| {
                theory.import_learned_state(
                    std::mem::take(lc),
                    std::mem::take(hc),
                );
                theory.import_dioph_state(std::mem::take(ds));
            },
            post_theory_export: |theory| {
                let (lc, hc) = theory.take_learned_state();
                let ds = theory.take_dioph_state();
                (lc, hc, ds)
            },
            pre_iter_check: |_s| {
                solve_interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(Ordering::Relaxed))
                || solve_deadline.expired()
                // Fail-closed memory guard (#nia-oom): the branch-and-bound
                // split loop carries the LIA/LRA tableau + learned state ACROSS
                // splits (import_learned_state / import_dioph_state), so a
                // pathological query grows memory without bound over up to
                // MAX_SPLITS iterations. For NIA this is undecidable to rule out
                // a-priori (QF_NIA ⊇ Hilbert's 10th) — we cannot promise
                // termination, but we MUST degrade gracefully rather than
                // OOM-kill the machine. Poll the process memory ceiling (set
                // from --memory or the auto-detected half-RAM default in main)
                // and bail to Unknown before starting the next split, turning a
                // 203 GB machine-kill into Unknown(resource-out).
                || ay_sys::process_memory_exceeded()
            }
        )
    }

    /// The eager BCP-interleaved QF_LIA split-loop (#4919).
    ///
    /// Requires the active `IncrementalTheoryState` to be at scope depth 0
    /// (the eager arm returns Unknown otherwise); callers either run at
    /// session scope depth 0 (standalone lane) or swap in a temporary
    /// isolated state first (incremental lane, Fix B1).
    fn solve_lia_eager_split_loop(
        &mut self,
        var_subst: Option<&VariableSubstitution>,
    ) -> Result<SolveResult> {
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();

        solve_incremental_split_loop_pipeline!(self,
            tag: "LIA",
            persistent_sat_field: lia_persistent_sat,
            tseitin_field: lia_tseitin_state,
            encoded_field: lia_encoded_assertions,
            activation_scope_field: lia_assertion_activation_scope,
            create_theory: {
                // #8749: Propagate deadline into LIA so IntSat probe honours --timeout.
                let mut theory = LiaSolver::new(&self.ctx.terms);
                if let Some(dl) = solve_deadline.get() {
                    theory.set_deadline(dl);
                }
                // Executor-scoped propagation-off option (CHC BMC TS lane,
                // sat-side-model-search diagnosis). Applied to the inner
                // LraSolver of every LIA theory instance.
                if self.no_lra_theory_propagation {
                    theory.lra_solver_mut().set_no_theory_propagation(true);
                }
                theory
            },
            extract_models: |theory| {
                use super::solve_harness::TheoryModels;
                let mut lia = theory.extract_model();
                if let (Some(var_subst), Some(model)) = (var_subst, lia.as_mut()) {
                    recover_substituted_lia_values(&self.ctx.terms, var_subst, model);
                }
                TheoryModels { lia, ..TheoryModels::default() }
            },
            max_splits: MAX_SPLITS_LIA,
            pre_theory_import: |theory, lc, hc, ds| {
                theory.import_learned_state(
                    std::mem::take(lc),
                    std::mem::take(hc),
                );
                theory.import_dioph_state(std::mem::take(ds));
            },
            post_theory_export: |theory| {
                let (lc, hc) = theory.take_learned_state();
                let ds = theory.take_dioph_state();
                (lc, hc, ds)
            },
            eager_extension: true,
            pre_iter_check: |_s| {
                solve_interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(Ordering::Relaxed))
                || solve_deadline.expired()
                // Fail-closed memory guard (#nia-oom): the branch-and-bound
                // split loop carries the LIA/LRA tableau + learned state ACROSS
                // splits (import_learned_state / import_dioph_state), so a
                // pathological query grows memory without bound over up to
                // MAX_SPLITS iterations. For NIA this is undecidable to rule out
                // a-priori (QF_NIA ⊇ Hilbert's 10th) — we cannot promise
                // termination, but we MUST degrade gracefully rather than
                // OOM-kill the machine. Poll the process memory ceiling (set
                // from --memory or the auto-detected half-RAM default in main)
                // and bail to Unknown before starting the next split, turning a
                // 203 GB machine-kill into Unknown(resource-out).
                || ay_sys::process_memory_exceeded()
            },
            // #8727: LIA branch-and-bound/disequality/expression splits are
            // tautological over the integers — `(v ≤ floor) ∨ (v ≥ ceil)`,
            // `(lt) ∨ (gt) ∨ !distinct`, etc. A post-split UNSAT from the
            // propositional layer is therefore a genuine theory UNSAT, not
            // a stale-clause artefact. Opt into accepting it instead of
            // escalating to `Unknown (Incomplete)`. The `_ext_partial > 0`
            // guard still fires first when theory-conflict literals fail
            // to map, preserving soundness for dropped-conflict cases.
            accept_unsat_after_splits: true
        )
    }

    /// Solve using non-linear integer arithmetic (NIA) theory.
    ///
    /// Uses the split-loop pipeline so that NeedSplit from the underlying
    /// LIA branch-and-bound solver is handled correctly. Without splits,
    /// NIA immediately returns Unknown on any NeedSplit (#7920).
    pub(in crate::executor) fn solve_nia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // Note: a symbolic/zero-divisor `(rem a b)` is degraded to `unknown`
        // universally in `route_to_solver` before this point (#nia-symbolic-rem-bypass).
        let original_problem_assertions = self.ctx.assertions.clone();

        // Symbolic mod/div elimination for the NIA path (#nia-modxx-zerodiv).
        //
        // `preprocess_lia_artifacts` only eliminates `(mod a k)` / `(div a k)`
        // with a CONSTANT divisor `k`. A `(mod a b)` with a non-constant divisor
        // (e.g. `(mod x x)`) is left intact, and the LRA layer then flags every
        // atom containing it as UNSUPPORTED and silently DROPS it from the
        // tableau. NIA's tentative-patch path treats LRA's "Sat with unsupported
        // atoms" as feasible and returns SAT on a model that violates those
        // dropped atoms (e.g. `(<= (* y y) (mod x x))` with `y*y=1, (mod x x)=-1`)
        // — a wrong-SAT.
        //
        // Eliminating symbolic mod/div here replaces `(mod x x)` with a single
        // fresh integer `r` constrained by the SMT-LIB division axioms
        // (`x = x*q + r ∧ 0 ≤ r < |x|`, or unconstrained when `x = 0`). Both
        // occurrences resolve to the SAME `r` because the term store hash-conses
        // `(mod x x)` and the elimination is run ONCE over the whole assertion
        // list (shared memo) — so the zero-divisor result stays a single
        // consistent value across all its uses (the congruence the constant-path
        // already enforces). The atoms then become ordinary (non)linear LIA
        // constraints that the tableau actually enforces.
        //
        // SOUNDNESS: the symbolic axiom over-approximates nothing — it is the
        // exact SMT-LIB semantics of `mod`/`div`, with the zero-divisor case left
        // unconstrained (matching z3). When the elimination introduces an
        // unconstrained zero-divisor var, SAT must route through the
        // `sat_validated_by_mod_div_or_branch` bypass because the model evaluator
        // cannot replay `(mod a 0)` (#div0).
        if crate::executor::mod_div_elim::contains_symbolic_int_mod_div(
            &self.ctx.terms,
            &self.ctx.assertions,
        ) {
            let assertions = std::mem::take(&mut self.ctx.assertions);
            let mod_elim = crate::executor::mod_div_elim::eliminate_int_mod_div(
                &mut self.ctx.terms,
                &assertions,
            );
            if mod_elim.introduced_unconstrained_div_mod {
                self.sat_validated_by_mod_div_or_branch = true;
            }
            let mut rewritten = mod_elim.constraints;
            rewritten.extend(mod_elim.rewritten);
            self.ctx.assertions = rewritten;
        }

        let artifacts = self.preprocess_lia_artifacts();
        let introduced_unconstrained_div_mod = artifacts.introduced_unconstrained_div_mod;

        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            original_problem_assertions,
            &artifacts.assertions,
            artifacts.assertion_sources.clone(),
        );

        let saved_style = self.counterexample_style();
        let saved_proof_provenance = self.proof_problem_assertion_provenance.clone();
        let proof_provenance =
            proof_provenance.preserving_authority_from(saved_proof_provenance.as_ref());
        self.set_counterexample_style(crate::CounterexampleStyle::Any);
        self.proof_problem_assertion_provenance = Some(proof_provenance);

        let original_assertions = std::mem::replace(&mut self.ctx.assertions, artifacts.assertions);
        let mut result = self.solve_nia_inner(Some(&artifacts.var_subst));

        self.ctx.assertions = original_assertions;
        self.set_counterexample_style(saved_style);
        if !matches!(result, Ok(ref r) if r.is_unsat()) {
            self.proof_problem_assertion_provenance = saved_proof_provenance;
        }

        if matches!(result, Ok(SolveResult::Sat)) {
            if let Some(model) = self
                .last_model
                .as_mut()
                .and_then(|model| model.lia_model.as_mut())
            {
                recover_substituted_lia_values(&self.ctx.terms, &artifacts.var_subst, model);
                recover_lia_equalities_from_assertions(
                    &self.ctx.terms,
                    &self.ctx.assertions,
                    model,
                );
            }

            if let Some(ref full_model) = self.last_model {
                let lia_values = full_model
                    .lia_model
                    .as_ref()
                    .map(|m| &m.values)
                    .cloned()
                    .unwrap_or_default();
                let bool_overrides = recover_substituted_bool_values(
                    &self.ctx.terms,
                    &artifacts.var_subst,
                    &lia_values,
                );
                if !bool_overrides.is_empty() {
                    if let Some(ref mut full_model) = self.last_model {
                        full_model.bool_overrides.extend(bool_overrides);
                    }
                }
            }

            if self.minimize_counterexamples_enabled() && self.last_assumptions.is_none() {
                self.minimize_model_sat_preserving();
            }
            // #div0: see solve_lia_incremental — bypass full model replay of the
            // under-specified zero-divisor div/mod term (strict gate still runs).
            if introduced_unconstrained_div_mod {
                self.sat_validated_by_mod_div_or_branch = true;
            }
            self.last_model_validated = false;
            result = self.finalize_sat_model_validation();
        }

        result
    }

    fn solve_nia_inner(&mut self, var_subst: Option<&VariableSubstitution>) -> Result<SolveResult> {
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();

        solve_incremental_split_loop_pipeline!(self,
            tag: "NIA",
            persistent_sat_field: persistent_sat,
            create_theory: {
                // #nia-deadline: install the solve deadline on the theory so
                // the NIA refinement loop (and its embedded LIA solver, via
                // the #lia-deadline-forward chain) honours `--timeout`
                // instead of letting a Gomory/tangent cut escalation
                // overshoot the wall budget.
                let mut theory = NiaSolver::new(&self.ctx.terms);
                if let Some(dl) = solve_deadline.get() {
                    theory.set_deadline(dl);
                }
                theory
            },
            extract_models: |theory| {
                use super::solve_harness::TheoryModels;
                let mut lia_model = theory
                    .extract_model()
                    .map(|m| LiaModel { values: m.values });
                if let (Some(var_subst), Some(model)) = (var_subst, lia_model.as_mut()) {
                    recover_substituted_lia_values(&self.ctx.terms, var_subst, model);
                }
                TheoryModels {
                    lia: lia_model,
                    ..TheoryModels::default()
                }
            },
            max_splits: MAX_SPLITS_LIA,
            pre_theory_import: |theory, lc, hc, ds| {
                theory.import_learned_state(
                    std::mem::take(lc),
                    std::mem::take(hc),
                );
                theory.import_dioph_state(std::mem::take(ds));
            },
            post_theory_export: |theory| {
                let (lc, hc) = theory.take_learned_state();
                let ds = theory.take_dioph_state();
                (lc, hc, ds)
            },
            pre_iter_check: |_s| {
                solve_interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(Ordering::Relaxed))
                || solve_deadline.expired()
                // Fail-closed memory guard (#nia-oom): the branch-and-bound
                // split loop carries the LIA/LRA tableau + learned state ACROSS
                // splits (import_learned_state / import_dioph_state), so a
                // pathological query grows memory without bound over up to
                // MAX_SPLITS iterations. For NIA this is undecidable to rule out
                // a-priori (QF_NIA ⊇ Hilbert's 10th) — we cannot promise
                // termination, but we MUST degrade gracefully rather than
                // OOM-kill the machine. Poll the process memory ceiling (set
                // from --memory or the auto-detected half-RAM default in main)
                // and bail to Unknown before starting the next split, turning a
                // 203 GB machine-kill into Unknown(resource-out).
                || ay_sys::process_memory_exceeded()
            }
        )
    }
}
