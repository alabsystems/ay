// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::retry_allowance::RetryAllowance;
use super::*;

impl Executor {
    /// The retries of [`Self::cegar_refine_solve`]: what runs when the first
    /// pass and its CEGAR rounds, which spent `spent` units of search work
    /// (`ay_core::resource::thread_work_units`), left `result`.
    ///
    /// A retry that solves the same problem again may spend search work in
    /// proportion to `spent` ([`RetryAllowance`]).
    ///
    /// A refutation whose expansion certificate is already built and
    /// parked waits only for the authored problem obligation the trace-armed
    /// retry installs: that retry re-enters the lane through its memo and
    /// installs the parked candidate through the unchanged strict boundary,
    /// so it goes FIRST, and without a ceiling: its refutation is already
    /// built. The deep-QE retry still runs after it on an `Unknown`. Same
    /// two attempts, same gates, only the order differs.
    pub(super) fn unknown_retries(
        &mut self,
        result: SolveResult,
        authored: &[TermId],
        spent: u64,
    ) -> Result<SolveResult> {
        let allowance = RetryAllowance::after_work_of(spent);
        if self.qlra_expansion_candidate_parked() {
            let result = self.quantified_trace_arming_unknown_retry(
                result,
                authored,
                RetryAllowance::UNBOUNDED,
            )?;
            return self.deep_qe_unknown_retry(result, authored, allowance);
        }
        let result = self.deep_qe_unknown_retry(result, authored, allowance)?;
        // #quantified-trace-arming runs LAST in the `Unknown` cascade: it is the
        // most expensive fallback (a full second solve with the recorder on) and
        // the cheapest ones should get their chance first.
        self.quantified_trace_arming_unknown_retry(result, authored, allowance)
    }

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
    /// restore it again on every exit path. `allowance` bounds the retry only
    /// when its pre-pass rewrites nothing, i.e. when it solves the first
    /// pass's problem again (`deep_qe_prepass_will_rewrite`).
    pub(super) fn deep_qe_unknown_retry(
        &mut self,
        result: SolveResult,
        authored: &[TermId],
        allowance: RetryAllowance,
    ) -> Result<SolveResult> {
        if !matches!(result, SolveResult::Unknown) {
            return Ok(result);
        }
        // One attempt per public solve: the retry re-enters `check_sat_internal`,
        // which reaches this same boundary.
        if self.deep_qe_retry_armed {
            return Ok(result);
        }
        // The QSAT route decides this fragment; eliminating its quantifiers
        // again by DNF-materializing QE is what it replaces.
        if self.qsat_route_applied() {
            return Ok(result);
        }
        // A caller that DEMANDED a checked proof artifact keeps the exact
        // quantified source: the instantiation lanes must be able to derive
        // their ground instances from the authored `forall` with `forall_inst`,
        // and a QE replacement has no such derivation. `cegar_refine_solve`
        // already returns before reaching here in that mode; stating the
        // condition in the lane that depends on it keeps the guarantee local,
        // so moving that early return cannot silently opt proof mode into a
        // rewrite.
        //
        // `checked_certificate_demanded`, NOT `is_producing_proofs` (the same
        // narrowing as the CEGAR loop): the latter is also true for the
        // best-effort sidecar of EVERY default-posture CLI solve, which killed
        // this lane there (LOIS `incremental0`: 68/112 vs 96/112 under
        // `--no-proof`). The retry only replaces an `Unknown`, and its verdict
        // clears the same funnel as under `--no-proof`; a residue refutation
        // has no authored scope and is withheld (pinned by
        // `deep_qe_retry_wrong_elimination_never_publishes_unsat`).
        if self.checked_certificate_demanded() {
            self.prepass_reachability.deep_qe_demand_stand_downs += 1;
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
        let allowance = self.deep_qe_retry_allowance(authored, allowance);
        self.prepass_reachability.deep_qe_unknown_retries += 1;
        match self.retry_within(allowance, |exec| exec.deep_qe_retry_solve(authored)) {
            // A definite verdict has passed the same mandatory certification as
            // any other; adopt it together with the artifacts it published.
            Ok(definite @ (SolveResult::Sat | SolveResult::Unsat(_))) => Ok(definite),
            // The retry failed closed, or ran out of its allowance and left
            // the `Unknown` that stood before it (`retry_within`). Either way
            // the published state is an `Unknown`, which has already revoked
            // every artifact either solve emitted.
            Ok(unknown) => Ok(unknown),
            Err(err) => Err(err),
        }
    }

    /// The allowance of the deep-QE retry: unbounded when its in-solve
    /// pre-pass will rewrite an assertion, so that it solves a different
    /// problem than the pass before it, and `re_solve` otherwise.
    ///
    /// The probe above cannot tell: it runs on the authored vector, while the
    /// in-solve pre-pass runs right after `simplify_vacuous_quantifiers`,
    /// which has already collapsed every quantifier whose body mentions none
    /// of its binders, in the first pass as well. On the authored vector the
    /// eliminators "eliminate" exactly those (a library that declares
    /// `(forall (..) (! true :pattern (..)))` is enough), the probe reports a
    /// change, and the retry then solves the first pass's problem again.
    ///
    /// That second solve is kept: it starts from the terms the first one
    /// left and sometimes refutes what the first left satisfiable. But it is
    /// a re-solve, and gets a re-solve's allowance, when this says no.
    fn deep_qe_retry_allowance(
        &mut self,
        authored: &[TermId],
        re_solve: RetryAllowance,
    ) -> RetryAllowance {
        if self.deep_qe_prepass_will_rewrite(authored) {
            RetryAllowance::UNBOUNDED
        } else {
            re_solve
        }
    }

    /// Whether the in-solve pre-pass will rewrite an assertion of `authored`
    /// once `simplify_vacuous_quantifiers` has run on it.
    fn deep_qe_prepass_will_rewrite(&mut self, authored: &[TermId]) -> bool {
        let mut seen_by_prepass = self.without_vacuous_quantifiers(authored);
        crate::executor::qe_prepass::deep_qe(
            &mut self.ctx.terms,
            &mut seen_by_prepass,
            self.solve_interrupt.as_deref(),
        )
    }

    /// The deep-QE retry's re-solve, armed for exactly one pass.
    ///
    /// Same containment as the trace retry below: a panic inside the re-solve
    /// must not leave the one-shot latch armed (nothing else clears it, so
    /// every later query would skip this lane) or the rewritten assertions
    /// installed. Disarm and restore on both exits, then let the panic continue
    /// to the caller's containment.
    fn deep_qe_retry_solve(&mut self, authored: &[TermId]) -> Result<SolveResult> {
        self.deep_qe_retry_armed = true;
        let retry = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            #[cfg(test)]
            assert!(
                !self.test_panic_in_deep_qe_retry,
                "test hook: panic inside the deep-QE retry"
            );
            self.check_sat_internal()
        }));
        self.deep_qe_retry_armed = false;
        self.ctx.assertions = authored.to_vec();
        match retry {
            Ok(retry) => retry,
            Err(panic) => std::panic::resume_unwind(panic),
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
    /// The armed pass solves the same problem as the shed one, so `allowance`
    /// always bounds it.
    pub(super) fn quantified_trace_arming_unknown_retry(
        &mut self,
        result: SolveResult,
        authored: &[TermId],
        allowance: RetryAllowance,
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
        let retried = self.retry_within(allowance, |exec| {
            exec.quantified_trace_retry_solve(authored)
        });
        match retried {
            // A definite verdict has passed the same mandatory certification as
            // any other; adopt it together with the artifacts it published.
            Ok(definite @ (SolveResult::Sat | SolveResult::Unsat(_))) => Ok(definite),
            // The retry failed closed, or ran out of its allowance and left
            // the `Unknown` that stood before it (`retry_within`). Either way
            // the published state is an `Unknown`, which has already revoked
            // every artifact either solve emitted.
            Ok(unknown) => Ok(unknown),
            Err(err) => Err(err),
        }
    }

    /// The trace-armed retry's re-solve, armed for exactly one pass.
    ///
    /// PANIC-SAFE hand-back. The retry borrows session proof configuration
    /// (recorder enabled, parsed retention, reconstruction budget) that
    /// `(reset)` carries over as host configuration and that no later
    /// `begin_public_solve` restores. A panic inside the retry used to
    /// unwind past the disarm, so the borrowed posture outlived the query
    /// — and, through `HostConfiguration`, the next `(reset)` too. The
    /// disarm and the authored-assertion restore run on BOTH exits; the
    /// panic then continues to the caller's containment unchanged.
    fn quantified_trace_retry_solve(&mut self, authored: &[TermId]) -> Result<SolveResult> {
        self.quantified_trace_retry_armed = true;
        let borrowed = self.arm_quantified_trace_for_retry();
        let retry = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            #[cfg(test)]
            assert!(
                !self.test_panic_in_quantified_trace_retry,
                "test hook: panic inside the quantified trace retry"
            );
            self.check_sat_internal()
        }));
        self.quantified_trace_retry_armed = false;
        self.disarm_quantified_trace_after_retry(borrowed);
        self.ctx.assertions = authored.to_vec();
        match retry {
            Ok(retry) => retry,
            Err(panic) => std::panic::resume_unwind(panic),
        }
    }
}

#[cfg(test)]
#[path = "deep_qe_retry_tests.rs"]
mod deep_qe_retry_tests;
