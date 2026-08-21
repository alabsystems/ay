// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// #qe-prepass: re-solve an `Unknown` quantified query with the deep-QE
    /// pre-pass armed.
    ///
    /// The pre-pass replaces an authored quantifier with a candidate
    /// quantifier-free equivalent. That is a SOLVING-ENGINE choice and never
    /// publication authority: SAT is still re-checked by the mandatory
    /// independent gate against `independent_gate_query_roots()` (the AUTHORED
    /// window, captured before any in-place pass), and an UNSAT reached from a
    /// rewritten premise cannot present a strict proof, because the replacement
    /// is not in the authored `Assume` scope
    /// (`complete_problem_assertions_for_strict_proof` is built from captured
    /// provenance, deliberately not from `ctx.assertions`).
    ///
    /// That is measured, not assumed — and the measurement also fixes WHICH
    /// layer is doing the work. Mutating the eliminator to report the
    /// maximally-WRONG result (every quantified assertion replaced by `false`,
    /// so the rewritten query is trivially refutable) over
    /// `-p ay-dpll --lib -- quantifier::`, 297 tests:
    ///
    /// * No PUBLISHED verdict moved. None of the suite's sixteen directional
    ///   guards ("a valid ∀∃ sentence must never answer unsat", "satisfiable
    ///   existential refuted", …) fired, and the multiset of published verdicts
    ///   among failing tests was identical to the unmutated run.
    /// * The RAW `Executor::check_sat` result did move: two `deferred::` tests
    ///   that call it directly saw `Unsat` where they require `Sat`/`Unknown`.
    ///   That entry point is pre-certification by design, and this is the layer
    ///   the `quantified_proof_translation_incomplete` fence at the pre-pass site
    ///   does NOT reach once elimination leaves the query ground, because the
    ///   quantifier loop's result mapping — the fence's only consumer — no longer
    ///   runs. Mandatory publication certification is what absorbs it.
    ///
    /// So: with a broken elimination this lane costs a wasted solve rather than
    /// an answer, but only because publication is certified. Do not promote a QE
    /// result past that boundary, and do not read the fence as covering the
    /// ground path.
    ///
    /// It runs HERE, on the `Unknown` fallback, rather than unconditionally in
    /// `check_sat_internal_preprocess_and_solve`, and that placement is a
    /// measured requirement, not caution. Adopting the rewrite before every
    /// solve ERASES the authored quantified shape that the exact-semantic UNSAT
    /// lanes (`CheckedExactClosedForall` and siblings) and the CEGQI SAT
    /// authorities match on, so problems those lanes decide today fail closed
    /// instead: measured on `-p ay-dpll --lib -- quantifier::`, an unconditional
    /// pre-pass turned ELEVEN passing tests into `unknown`
    /// (`qe_prepass_ndiv_duality_twin_unsat` — an authored closed `forall` the
    /// precheck refutes exactly — plus nine CEGQI arithmetic tests and
    /// `test_forall_infeasible_linear_eq_still_unsat`). On the `Unknown`
    /// fallback there is by construction no verdict to lose: the retry can only
    /// replace `Unknown` with a verdict that has itself cleared every mandatory
    /// gate, and a retry that stays `Unknown` leaves the original answer.
    ///
    /// Caller contract: `ctx.assertions` must already be restored to the
    /// authored snapshot, which is also passed as `authored` so the retry can
    /// restore it again on every exit path.
    pub(super) fn deep_qe_unknown_retry(
        &mut self,
        result: SolveResult,
        authored: &[TermId],
    ) -> Result<SolveResult> {
        if !matches!(result, SolveResult::Unknown) {
            return Ok(result);
        }
        // One attempt per public solve: the retry re-enters `check_sat_internal`,
        // which reaches this same boundary.
        if self.deep_qe_retry_armed {
            return Ok(result);
        }
        // A caller that asked for a proof ARTIFACT keeps the exact quantified
        // source: the instantiation lanes must be able to derive their ground
        // instances from the authored `forall` with `forall_inst`, and a QE
        // replacement has no such derivation. `cegar_refine_solve` already
        // returns before reaching here in that mode; stating the condition in
        // the lane that depends on it keeps the guarantee local, so moving that
        // early return cannot silently opt proof mode into a rewrite.
        if self.is_producing_proofs() {
            return Ok(result);
        }
        // Nothing for the pre-pass to eliminate, so nothing to gain: never pay
        // a second solve on a ground problem.
        if !authored
            .iter()
            .any(|&a| contains_quantifier(&self.ctx.terms, a))
        {
            return Ok(result);
        }
        // An interrupt/deadline already landed: a second full solve would only
        // burn the caller's remaining budget to reach the same `Unknown`.
        if self.should_abort_theory_loop() {
            return Ok(result);
        }
        // Only re-solve when the pre-pass actually produces a DIFFERENT problem.
        //
        // Without this the lane is a blanket "solve every undecided query
        // twice", which is a different and much more expensive feature: it pays
        // a second full solve on EVERY quantified `Unknown`, including the
        // overwhelming majority the pre-pass refuses outright (its fragment
        // screen rejects UF / arrays / nonlinear before any NNF or DNF work).
        // Probing first makes the lane's cost proportional to its applicability
        // and makes it do what its name says: re-solve a problem that changed.
        //
        // The probe runs on a COPY: the rewrite must not be adopted here.
        // `check_sat_internal` installs `independent_gate_authored_assertions`
        // from whatever `ctx.assertions` holds on entry, so handing it a
        // pre-rewritten vector would point the mandatory SAT gate at the
        // REWRITTEN roots instead of the authored ones. Adoption therefore stays
        // at the in-solve pre-pass site, which runs after that capture. Terms the
        // probe interns are hash-consed and bounded by the pre-pass's own DNF /
        // elimination caps; the in-solve run re-uses them.
        //
        // The probe answers on the AUTHORED vector while the in-solve pre-pass
        // sees the preprocessed one, so the two can disagree. A probe false
        // negative keeps today's `Unknown` (identical to the pre-change
        // behaviour, fail-closed); a false positive costs one extra solve.
        let mut probe = authored.to_vec();
        if !crate::executor::qe_prepass::deep_qe(
            &mut self.ctx.terms,
            &mut probe,
            self.solve_interrupt.as_deref(),
        ) {
            return Ok(result);
        }
        self.prepass_reachability.deep_qe_unknown_retries += 1;
        self.deep_qe_retry_armed = true;
        let retry = self.check_sat_internal();
        self.deep_qe_retry_armed = false;
        self.ctx.assertions = authored.to_vec();
        match retry {
            // A definite verdict has passed the same mandatory certification as
            // any other; adopt it together with the artifacts it published.
            Ok(definite @ (SolveResult::Sat | SolveResult::Unsat(_))) => Ok(definite),
            // The retry failed closed. Its `Unknown` is the published state, so
            // return it rather than the pre-retry value: both are `Unknown`, and
            // `Unknown` has already revoked every artifact either solve emitted.
            Ok(unknown) => Ok(unknown),
            Err(err) => Err(err),
        }
    }

    /// #quantified-trace-arming: re-solve an `Unknown` QUANTIFIED query under
    /// competition shedding with the internal proof trace armed.
    ///
    /// WHY. On a quantified problem the recorded trace is not a user-facing
    /// artifact — it is the publication MECHANISM for an instantiation-driven
    /// refutation. E-matching / CEGQI writers register their exact ground
    /// instances as `forall_inst` derivations, and `disambiguate_cegqi_unsat`
    /// (`quantifier_loop/result_mapping.rs`) publishes `unsat` precisely when
    /// those recorded derivations strict-check against the immutable authored
    /// problem. Competition shedding disables the recorder, so that route is
    /// dead in the competition posture and the SAME refutation that publishes
    /// at `--rigor standard` degrades to `unknown` at `--rigor fast` — a
    /// NON-MONOTONE rigor ladder. Measured on 40 SQ Equality_LinearArith
    /// instances at a 30s budget: `--rigor fast` solved 1, `--rigor standard`
    /// solved 6, and every lost row was confirmed `unsat` by z3 and cvc5.
    ///
    /// WHY ON THE `Unknown` FALLBACK, exactly like `deep_qe_unknown_retry`
    /// above. Arming the recorder for the WHOLE solve is not free and not
    /// verdict-neutral: `produce_proofs_enabled()` flips true, which changes
    /// proof-preserving preprocessing and the classification arms that consult
    /// it. Measured over a 231-instance sweep spanning EVERY non-incremental
    /// quantified logic, arming from the start gained 9 rows and LOST 6 that
    /// the shed path answers today (three of them in well under a second:
    /// `UFNIRA/20240414-funcprobs/problem_U3_sol1`,
    /// `.../problem_U87_sol2`, and an `AUFBVDTLIA` rec-fun row). On the
    /// `Unknown` fallback there is by construction no verdict to lose — the
    /// first pass is byte-identical to the shed baseline, and the retry can
    /// only replace `Unknown` with a verdict that has itself cleared every
    /// mandatory gate.
    ///
    /// SOUNDNESS. This adds a second publication ATTEMPT, not a second
    /// publication policy. The retry re-enters the same `check_sat_internal`
    /// and its verdict passes the same unweakened certification funnel; the B3
    /// `CompetitionRaw` admission lane is untouched. Nothing here can turn an
    /// `unknown` into an uncertified `unsat`.
    ///
    /// Caller contract matches `deep_qe_unknown_retry`: `ctx.assertions` is the
    /// authored snapshot, also passed as `authored` so every exit restores it.
    pub(super) fn quantified_trace_arming_unknown_retry(
        &mut self,
        result: SolveResult,
        authored: &[TermId],
    ) -> Result<SolveResult> {
        if !matches!(result, SolveResult::Unknown) {
            return Ok(result);
        }
        // One attempt per public solve: the retry re-enters `check_sat_internal`,
        // which reaches this same boundary.
        if self.quantified_trace_retry_armed {
            return Ok(result);
        }
        if !crate::quant_unit_authority::quantified_shedding_yield_enabled() {
            return Ok(result);
        }
        // Only a SHED solve has a trace to gain. This conjunct also confines the
        // lane to a competition-mode executor, which every disposable internal
        // probe is not (`qpf_probe_executor` builds a fresh `Executor`), so no
        // nested verification solve can pay for a second pass.
        if !self.competition_shedding_active() {
            return Ok(result);
        }
        // Nothing to record `forall_inst` derivations FROM: never pay a second
        // solve on a ground problem.
        if !authored
            .iter()
            .any(|&a| contains_quantifier(&self.ctx.terms, a))
        {
            return Ok(result);
        }
        // An interrupt/deadline already landed: a second full solve would only
        // burn the caller's remaining budget to reach the same `Unknown`.
        if self.should_abort_theory_loop() {
            return Ok(result);
        }
        self.quantified_trace_retry_armed = true;
        self.arm_quantified_trace_for_retry();
        let retry = self.check_sat_internal();
        self.quantified_trace_retry_armed = false;
        self.disarm_quantified_trace_after_retry();
        self.ctx.assertions = authored.to_vec();
        match retry {
            // A definite verdict has passed the same mandatory certification as
            // any other; adopt it together with the artifacts it published.
            Ok(definite @ (SolveResult::Sat | SolveResult::Unsat(_))) => Ok(definite),
            // The retry failed closed. Its `Unknown` is the published state, so
            // return it rather than the pre-retry value: both are `Unknown`, and
            // `Unknown` has already revoked every artifact either solve emitted.
            Ok(unknown) => Ok(unknown),
            Err(err) => Err(err),
        }
    }
}
