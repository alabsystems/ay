// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core model validation pipeline.
//!
//! Contains validate_model, validate_model_attempt, finalize_sat_model_validation,
//! and finalize_sat_assumption_validation methods on Executor.
//!
//! Per-term observation logic is in `observation.rs`.

use ay_core::{TermId, VerificationBoundary, VerificationEvidenceKind, VerificationVerdict};

use super::{
    check_definitive_false, dt_axiom_bool, SkeletonVerificationResult, ValidationAttempt,
    ValidationObservation, ValidationSkipKind, ValidationStats, ValidationTarget, TERM_FLAG_ARRAY,
    TERM_FLAG_DATATYPE,
};
use crate::executor::model::{debug_model, Executor};
use crate::executor_types::{ModelValidationError, Result, SolveResult, UnknownReason};
use crate::features::StaticFeatures;

const QFAX_STORE_WALK_LIMIT: usize = 256;
const QFAX_CELL_RECURSION_LIMIT: usize = 32;
const QFAX_CLAUSE_LITERAL_LIMIT: usize = 48;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QfaxCellTerm {
    Value(TermId),
    BaseRead { index: TermId },
}

fn failed_assertion_contains_array(
    terms: &ay_core::term::TermStore,
    failed_assertion: Option<TermId>,
) -> bool {
    failed_assertion
        .is_some_and(|assertion| StaticFeatures::collect(terms, &[assertion]).has_arrays)
}

impl Executor {
    pub(in crate::executor) fn record_model_validation_unknown_diagnostic(
        &mut self,
        detail: impl Into<String>,
    ) {
        let detail = detail.into();
        if ay_core::misc_cli_flags().debug_read_pin {
            eprintln!("[validation-unknown] {detail}");
        }
        // LOUD, UNCONDITIONALLY. Reaching here means AY built a candidate model
        // (or refutation) and its OWN validator would not confirm it. That is a
        // latent wrong answer, not a missing feature.
        //
        // This used to record `Incomplete` and whisper through `tracing::warn!`,
        // which has no subscriber in normal runs. The result: a 2026-07-25
        // corpus scoreboard found 13 real wrong answers (12 UFBV wrong-SATs, one
        // AUFLIA wrong-UNSAT) that this gate had ALREADY caught and reported as
        // a bland `(:reason-unknown incomplete)` — indistinguishable from an
        // unsupported logic, so nobody ever looked.
        //
        // Verdict-neutral by construction: this only records and prints. It
        // cannot turn a correct answer into a wrong one, so making it loud
        // carries no soundness risk — only noise, which is the right trade for
        // a signal this important. `SELF-CHECK-REJECTED` is the greppable token
        // harnesses count.
        self.last_statistics.set_string(
            "unknown.reason",
            UnknownReason::SelfCheckRejected.to_string(),
        );
        // TIER: this is the UNCONFIRMED tier, and saying so is load-bearing.
        //
        // "computed then not certified" is NOT the same as "wrong". Measured on
        // the 2026-07-25 corpus scoreboard: 480 files were decided by AY and
        // returned `unknown` under `--self-check`, and 414 of those 480 AGREE
        // with z3. An alarm that shouts "rejected" on every one of them is ~86%
        // false positives, and an alarm nobody can trust is worse than none.
        //
        // The REFUTED tier — where a checker positively disproved the verdict,
        // which is a near-certain internal bug — already has its own loud,
        // detailed banner with the falsifying assignment
        // (`report_caught_invalid_model`, independent_gate.rs). This line must
        // not be confusable with it.
        //
        // Mode still matters within this tier: under `--self-check` the
        // non-confirmation WITHHELD the verdict, while in default mode the
        // completeness-favoring path may publish it anyway.
        let tier = if self.self_check {
            "UNCONFIRMED/withheld"
        } else {
            "UNCONFIRMED/published"
        };
        // Not while corroborating someone else's verdict. The deferred-trust
        // discharge re-solves the problem in a fresh `Executor` to confirm the
        // OUTER refutation; that probe reaches this same funnel and, when its
        // own proof leans on a trust step, cannot certify itself. Narrating
        // that on the shared transcript reported a failure the user's query
        // did not have -- measured on
        // `(assert (=> p (< x 0))) (assert (> x 0)) (check-sat-assuming (p))`,
        // where the outer certification SUCCEEDS (`all_discharged`) and
        // publishes a certified `unsat`, yet this line still claimed the
        // verdict was unconfirmed. The statistics below stay: they live on the
        // probe's own executor and never reach the user.
        if !crate::executor::unsat_cert::inside_trust_discharge_solve() {
            ay_core::safe_eprintln!(
                "c !! MODEL-UNCONFIRMED [{tier}] (not a refutation — see \
                 [AY SOUNDNESS GATE] for caught invalid models) {detail}"
            );
        }
        self.last_statistics
            .set_string("unknown.phase", "model-validation");
        self.last_statistics
            .set_string("unknown.cost_center", "smt-model-validation");
        self.last_statistics.set_string("unknown.detail", detail);
    }

    /// Verify that every assertion with a SAT variable mapping evaluates to
    /// `true` in the SAT model's boolean skeleton.
    ///
    /// This is a lightweight check that does NOT require theory model evaluation.
    /// It catches Tseitin encoding bugs and SAT-level unsoundness even when
    /// `skip_model_eval` is set (trivially-empty assertions, incremental scope).
    ///
    /// Part of #7912: universal verify_model coverage.
    #[cfg(debug_assertions)]
    fn debug_assert_boolean_skeleton(&self, context: &str) {
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            _ => return, // No model to check
        };
        if model.sat_model.is_empty() && model.term_to_var.is_empty() {
            return; // Trivially SAT (e.g., empty string assertions folded away)
        }
        for (i, &assertion) in self.ctx.assertions.iter().enumerate() {
            if let Some(&var) = model.term_to_var.get(&assertion) {
                let var_idx = var as usize;
                if var_idx < model.sat_model.len() {
                    debug_assert!(
                        model.sat_model[var_idx],
                        "BUG [{context}]: assertion {i} (term {assertion:?}) maps to SAT var {var} \
                         which is FALSE in the SAT model — boolean skeleton violated"
                    );
                }
            }
        }
    }

    /// Verify the SAT boolean skeleton in release mode (#7912).
    ///
    /// For every assertion that has a Tseitin variable mapping (`term_to_var`),
    /// checks that the SAT model assigns it `true`. Returns a summary of
    /// verified/unmapped/violated counts.
    ///
    /// This runs in ALL build modes (debug AND release) and does NOT panic.
    /// It is the release-safe counterpart of `debug_assert_boolean_skeleton`.
    ///
    /// Cost: O(assertions) with hash lookups — negligible compared to solving.
    pub(in crate::executor) fn verify_boolean_skeleton(
        &self,
        context: &str,
    ) -> SkeletonVerificationResult {
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            _ => {
                return SkeletonVerificationResult {
                    total: self.ctx.assertions.len(),
                    unmapped: self.ctx.assertions.len(),
                    ..Default::default()
                };
            }
        };
        if model.sat_model.is_empty() && model.term_to_var.is_empty() {
            // Trivially SAT (e.g., all assertions folded to true before Tseitin).
            return SkeletonVerificationResult {
                total: self.ctx.assertions.len(),
                unmapped: self.ctx.assertions.len(),
                ..Default::default()
            };
        }

        let mut verified = 0usize;
        let mut unmapped = 0usize;
        let mut violations = 0usize;

        for (i, &assertion) in self.ctx.assertions.iter().enumerate() {
            if let Some(&var) = model.term_to_var.get(&assertion) {
                let var_idx = var as usize;
                if var_idx < model.sat_model.len() {
                    if model.sat_model[var_idx] {
                        verified += 1;
                    } else {
                        violations += 1;
                        tracing::error!(
                            context,
                            assertion_index = i,
                            sat_var = var,
                            "boolean skeleton violation: assertion maps to SAT var \
                             which is FALSE in the model"
                        );
                    }
                } else {
                    // Var index out of bounds — treat as unmapped.
                    unmapped += 1;
                }
            } else {
                unmapped += 1;
            }
        }

        let total = self.ctx.assertions.len();
        let result = SkeletonVerificationResult {
            verified,
            unmapped,
            violations,
            total,
        };

        if violations > 0 {
            tracing::error!(
                context,
                verified = result.verified,
                unmapped = result.unmapped,
                violations = result.violations,
                total = result.total,
                "boolean skeleton verification FAILED — SAT model contradicts Tseitin encoding"
            );
        } else {
            tracing::debug!(
                context,
                verified = result.verified,
                unmapped = result.unmapped,
                total = result.total,
                "boolean skeleton verification passed"
            );
        }

        result
    }

    fn apply_assertion_observation(
        stats: &mut ValidationStats,
        observation: ValidationObservation,
    ) -> std::result::Result<(), ModelValidationError> {
        match observation {
            ValidationObservation::Skip(kind) => {
                match kind {
                    ValidationSkipKind::Internal => stats.skipped_internal += 1,
                    ValidationSkipKind::Quantifier => stats.skipped_quantifier += 1,
                    ValidationSkipKind::Datatype => stats.skipped_datatype += 1,
                    ValidationSkipKind::Dtbv => stats.skipped_dtbv += 1,
                    ValidationSkipKind::ArithArrayMix => stats.skipped_arith_array_mix += 1,
                }
                Ok(())
            }
            ValidationObservation::Fallback(_) => {
                stats.sat_fallback_count += 1;
                Ok(())
            }
            ValidationObservation::Verdict { verdict, dt_only } => match verdict {
                VerificationVerdict::Verified { evidence, .. } => {
                    stats.checked += 1;
                    if evidence == VerificationEvidenceKind::DelegatedSolver {
                        stats.delegated_checks += 1;
                    }
                    let _ = dt_only;
                    Ok(())
                }
                VerificationVerdict::Incomplete(failure) => {
                    Err(ModelValidationError::Incomplete(failure))
                }
                VerificationVerdict::Violated(failure) => {
                    Err(ModelValidationError::Violated(failure))
                }
                _ => {
                    unreachable!("unexpected verification verdict variant in assertion validation")
                }
            },
        }
    }

    fn validate_model_attempt(&self) -> ValidationAttempt {
        let debug = debug_model();
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            (Some(SolveResult::Sat), None) => {
                // SAT with no assertions is trivially valid
                if self.ctx.assertions.is_empty() {
                    return ValidationAttempt::success(ValidationStats {
                        total: 0,
                        ..Default::default()
                    });
                }
                if ay_core::misc_cli_flags().f1_diag {
                    eprintln!(
                        "--f1-diag: Sat with last_model=None at validate_model_attempt\n{}",
                        std::backtrace::Backtrace::force_capture()
                    );
                }
                return ValidationAttempt::failure(
                    None,
                    ModelValidationError::violated(
                        VerificationBoundary::SmtGroundAssertion,
                        "No model available",
                    ),
                );
            }
            _ => {
                return ValidationAttempt::failure(
                    None,
                    ModelValidationError::violated(
                        VerificationBoundary::SmtGroundAssertion,
                        "Model validation requires SAT result",
                    ),
                );
            }
        };

        // Memoize `evaluate_term` across this whole immutable-model validation
        // pass (perf-only; #eval-memo). `&self` guarantees the model cannot
        // mutate here, so cached values stay valid until the session drops.
        let _eval_memo = crate::executor::model::EvalMemoSession::new();

        // Flatten top-level conjunctions so each leaf assertion gets its own
        // term flags and SAT-fallback lookup (#5585). The solve pipeline's
        // FlattenAnd preprocessor already splits conjunctions before Tseitin
        // encoding, so the individual conjuncts have SAT variables but the
        // parent conjunction may not. Without flattening here, a conjunction
        // like (and (= (select a i) 1) (>= x 0)) evaluates to Unknown when
        // any child is Unknown, then fails SAT-fallback because the conjunction
        // itself has no term_to_var mapping.
        let flat_assertions = self.flatten_assertion_conjunctions();
        let total = flat_assertions.len();

        // Precompute term classification flags in a single O(T) pass instead
        // of 5 separate recursive tree walks per assertion. On shared DAG terms,
        // the old approach could re-traverse exponentially; this is always O(T).
        let term_flags = self.precompute_term_flags();

        let mut stats = ValidationStats {
            total,
            ..Default::default()
        };
        let has_array_assertions = flat_assertions
            .iter()
            .any(|&assertion| term_flags[assertion.index()] & TERM_FLAG_ARRAY != 0);
        // BV-backed: used in post-loop guards (no_verification_evidence,
        // proportional SAT-fallback) to accept SAT-fallback as valid
        // evidence when eager bit-blasting produced a complete encoding.
        // Per-assertion BV bypass was removed: the observation pipeline
        // already handles BV model fallback correctly, and the old blanket
        // bypass was swallowing genuine Violated/Incomplete errors (#8456).
        let bv_backed = model.bv_model.is_some();

        for (i, &assertion) in flat_assertions.iter().enumerate() {
            let flags_i = term_flags[assertion.index()];
            let observation = self.validate_term_observation(
                model,
                assertion,
                i,
                flags_i,
                has_array_assertions,
                ValidationTarget::GroundAssertion,
            );
            if debug {
                tracing::debug!(
                    assertion_index = i,
                    assertion = %self.format_term(assertion),
                    observation = ?observation,
                    "model validation assertion observation"
                );
                // stderr twin of the tracing line: `AY_DEBUG_MODEL=1` runs of the
                // CLI install no tracing subscriber, so the line above is invisible
                // exactly when a `--self-check` downgrade needs explaining.
                if matches!(
                    observation,
                    ValidationObservation::Skip(_) | ValidationObservation::Fallback(_)
                ) {
                    safe_eprintln!(
                        "[model-validation] non-independent assertion_index={i} obs={observation:?} term={}",
                        self.format_term(assertion)
                    );
                }
            }
            if flags_i & TERM_FLAG_ARRAY != 0
                && matches!(
                    &observation,
                    ValidationObservation::Verdict {
                        verdict: VerificationVerdict::Verified {
                            boundary: VerificationBoundary::SmtTheoryDelegation,
                            ..
                        },
                        ..
                    }
                )
            {
                stats.array_delegated_checks += 1;
            }
            if let Err(error) = Self::apply_assertion_observation(&mut stats, observation) {
                // Witness-extensionality bypass (#dt-array-extensionality-witness):
                // when the datatype-carrying-array fragment is soundly modeled by
                // the search (`dt_array_injectivity_gate_bypass`, set at ENTRY by
                // `dt_array_extensionality_modeled` / the observational-completeness
                // footprint), the model evaluator's inability to INDEPENDENTLY
                // confirm a datatype/datatype-array assertion — there is no
                // `EvalValue` for a datatype value, so `(= X Y)` / `(= v (C ..))`
                // over datatype-element arrays observe as Incomplete — is EXPECTED,
                // not a soundness signal: the emitted extensionality / ROW /
                // selector-tester congruence axioms are part of the solved formula,
                // so the SAT model already satisfies the assertion (the search
                // vouches for it, exactly like a delegated theory check). Treat such
                // an INCOMPLETE observation on a datatype-flagged assertion as a soft
                // datatype skip instead of a hard validation failure, so a genuine
                // SAT is not spuriously degraded to Unknown. A VIOLATED verdict is a
                // definitive counterexample and still fails closed; non-datatype
                // incompleteness (no datatype flag) still fails closed; and when the
                // bypass is NOT set the degrade gate already fired earlier, so this
                // only ever runs on a fragment the search modeled.
                //
                // GATE-VACUITY GUARD (#qf-dt-gate-vacuity, companion of the
                // fast-path in `validate_term_observation`): the bypass
                // predicate is VACUOUSLY true on an array-free problem, and the
                // witness-extensionality argument only vouches for assertions
                // touching the datatype-carrying-ARRAY fragment. Require the
                // ARRAY flag so a pure datatype assertion that observes
                // Incomplete still fails closed instead of being soft-skipped.
                if self.dt_array_injectivity_gate_bypass
                    && matches!(error, ModelValidationError::Incomplete(_))
                    && flags_i & TERM_FLAG_DATATYPE != 0
                    && flags_i & TERM_FLAG_ARRAY != 0
                {
                    stats.skipped_datatype += 1;
                    continue;
                }
                if debug {
                    safe_eprintln!(
                        "[model-validation] failed assertion_index={} term={:?} error={}",
                        i,
                        assertion,
                        error
                    );
                }
                return ValidationAttempt::assertion_failure(Some(stats), error, assertion);
            }
        }

        // Emit skip statistics for sat-debuggability (#4605).
        let skipped_total = stats.skipped_internal
            + stats.skipped_quantifier
            + stats.skipped_datatype
            + stats.skipped_dtbv
            + stats.skipped_arith_array_mix;
        debug_assert!(
            stats.checked + skipped_total + stats.sat_fallback_count <= stats.total,
            "BUG: ValidationStats accounting: checked({}) + skipped({}) + sat_fallback({}) > total({})",
            stats.checked,
            skipped_total,
            stats.sat_fallback_count,
            stats.total,
        );
        if skipped_total > 0 || stats.sat_fallback_count > 0 || debug {
            tracing::debug!(
                checked = stats.checked,
                delegated_checks = stats.delegated_checks,
                array_delegated_checks = stats.array_delegated_checks,
                sat_fallback = stats.sat_fallback_count,
                skipped_internal = stats.skipped_internal,
                skipped_quantifier = stats.skipped_quantifier,
                skipped_datatype = stats.skipped_datatype,
                skipped_dtbv = stats.skipped_dtbv,
                skipped_arith_array_mix = stats.skipped_arith_array_mix,
                total = stats.total,
                "model validation skip counts"
            );
        }
        // (#5488, #5499, #5546, #6273, #4057) Degrade to Unknown when no
        // assertion produced verification evidence at all.
        let euf_backed = model.euf_model.is_some();
        // BV-backed: eager bit-blasting produces a complete SAT encoding of all
        // BV and array terms. SAT-fallback (checking whether the assertion's
        // Tseitin variable is assigned true) IS valid verification evidence for
        // QF_BV/QF_ABV/QF_UFBV/QF_AUFBV — the SAT model is the ground truth
        // for the encoding. Without this, QF_ABV benchmarks with array
        // equalities inside ITE conditions degrade to Unknown because the model
        // evaluator can't evaluate array terms, even though the SAT solver
        // found a satisfying assignment for the complete bit-blasted encoding.
        //
        // #8456: Seq/FP theory models also validate SAT-fallback as evidence.
        // The theory solver's DPLL(T)/CEGAR loop ensures theory consistency;
        // the model evaluator may return Unknown for unconstrained variables
        // but the theory solver has already validated the assignment. Same
        // rationale as euf_backed/bv_backed.
        let seq_backed = model.seq_model.is_some();
        let fp_backed = model.fp_model.is_some();
        // (#7979) Degrade to Unknown when ALL assertions were skipped or
        // SAT-fallback with zero independent verification evidence. However,
        // quantified assertions are NOT counted as suspicious: the solver
        // already verified them via E-matching/CEGQI during solving. Only
        // fire when there are non-quantifier reasons for the skip (dtbv,
        // sat_fallback, arith_array_mix, internal).
        let only_quantifier_skips = stats.skipped_quantifier > 0
            && stats.skipped_dtbv == 0
            && stats.sat_fallback_count == 0
            && stats.skipped_arith_array_mix == 0
            && stats.skipped_internal == 0;
        let no_verification_evidence = stats.checked == 0
            && stats.total > 0
            && !euf_backed
            && !bv_backed
            && !seq_backed
            && !fp_backed
            && !only_quantifier_skips
            && (stats.skipped_dtbv > 0
                || stats.sat_fallback_count > 0
                || stats.skipped_arith_array_mix > 0
                || stats.skipped_internal > 0);
        if no_verification_evidence {
            let msg = format!(
                "all {} assertions were skipped or SAT-fallback \
                 (internal={}, quantifier={}, datatype={}, dtbv={}, \
                 arith_array={}, sat_fallback={})",
                stats.total,
                stats.skipped_internal,
                stats.skipped_quantifier,
                stats.skipped_datatype,
                stats.skipped_dtbv,
                stats.skipped_arith_array_mix,
                stats.sat_fallback_count,
            );
            return ValidationAttempt::failure(
                Some(stats),
                ModelValidationError::incomplete(VerificationBoundary::SmtCircularSatFallback, msg),
            );
        }

        // (#6223) Proportional SAT-fallback guard: even when some assertions
        // independently validated (checked > 0), reject models where >90% of
        // assertions are SAT-fallback. Skip for theory-backed models where the
        // theory solver has validated the assignment (same rationale as
        // no_verification_evidence).
        if stats.total >= 5
            && stats.sat_fallback_count > 0
            && stats.sat_fallback_count * 10 > stats.total * 9
            && !euf_backed
            && !bv_backed
            && !seq_backed
            && !fp_backed
        {
            let msg = format!(
                "{}/{} assertions ({:.0}%) used SAT-fallback \
                 (circular self-validation), only {} independently checked",
                stats.sat_fallback_count,
                stats.total,
                stats.sat_fallback_count as f64 / stats.total as f64 * 100.0,
                stats.checked,
            );
            return ValidationAttempt::failure(
                Some(stats),
                ModelValidationError::incomplete(VerificationBoundary::SmtCircularSatFallback, msg),
            );
        }

        ValidationAttempt::success(stats)
    }

    /// Fail-closed POSITIVE certification of a `sat` verdict against the
    /// assertions the USER authored (#selfcert-authored).
    ///
    /// The `--self-check` SAT gate's ordinary denominator is `ctx.assertions`
    /// *at validation time*. `--self-check` forces proof production on, and in
    /// proof mode the theory routes RETAIN their injected axioms (eager array
    /// ROW/extensionality instances, purification definitions, …) in that
    /// vector so proof premises stay honest. Those axioms mention fresh internal
    /// symbols (`__ay_*`) that carry no model value, so they
    /// observe as `Skip(Internal)` and land in the `incomplete` count — and a
    /// QF_AX model that satisfied all 46 authored assertions was degraded to
    /// `unknown` because 41 *solver-generated* axioms were "unverified". Without
    /// proofs the same model validates 46/46 and is emitted as `sat`.
    ///
    /// This predicate is that missing certification, and it is a POSITIVE one —
    /// not an excuse for the skips. It re-evaluates every AUTHORED assertion,
    /// exactly as the user wrote it, under the emitted model with AY's own model
    /// evaluator, and demands a concrete `Bool(true)` from every single one. It
    /// consults NO SAT-solver literal value and NO theory-solver vouch, so it
    /// cannot launder the circular evidence (`sat_fallback`, `delegated`) the
    /// main pipeline sometimes accepts — the bar here is strictly higher than
    /// the `incomplete == 0` path it stands in for.
    ///
    /// Fails closed: no snapshot (a route that never passed through
    /// `check_sat_internal`), no model, an empty authored window, or any
    /// assertion that does not evaluate to a definite `true` all return `false`,
    /// leaving the caller's downgrade in place. Since it is only consulted when
    /// the gate was about to degrade, it can only ever turn `unknown` back into
    /// the `sat` AY genuinely verified — never the reverse.
    ///
    /// DEFINITIONAL CLOSURE. Proof-mode preprocessing eliminates a defining
    /// equality outright — `substitute_store_flat_equalities` consumes
    /// `(= a_2 (store a_1 i e))` and rewrites `a_2` away — so the eliminated
    /// variable has NO value in the extracted model and the authored assertion
    /// that defines it evaluates to `Unknown`. Rather than accept an unevaluated
    /// assertion (which would be exactly the unchecked `sat` this gate exists to
    /// stop), the check CONSTRUCTS the witness: each such definition is applied
    /// as a substitution to the whole authored window, and the substituted
    /// window is what must evaluate to `true`. That is the standard
    /// model-extension argument — a model of `F[v := t]` extends to a model of
    /// `F ∧ v = t` by interpreting `v` as `t` — so it certifies the ORIGINAL
    /// formula, and the definition itself is not taken on faith: it collapses to
    /// `(= t t)` only because we are *choosing* `v`'s value, and every other
    /// authored assertion mentioning `v` is then checked at that value.
    ///
    /// Only a variable the model leaves genuinely UNVALUED can be defined this
    /// way (never one the solver assigned, which must be checked as-is), the
    /// definition must be acyclic, and a window that still mentions a defined
    /// variable after the fixpoint fails closed.
    ///
    /// The evaluation itself runs with `ctx.assertions` TEMPORARILY set to the
    /// substituted authored window: the array evaluator resolves array leaves
    /// through the surrounding asserted equalities, so it must see the window it
    /// is certifying, not the solver's internal one.
    fn self_check_authored_model_certified(&mut self) -> bool {
        let Some(authored) = self.self_check_authored_assertions.clone() else {
            return false;
        };
        if authored.is_empty() || self.last_model.is_none() {
            return false;
        }
        let Some(window) = self.self_check_authored_definitional_closure(&authored) else {
            return false;
        };
        // `evaluate_term` results are memoized per model state, and this check
        // deliberately changes the assertion context they are computed in, so
        // the memo must not carry values across the swap in either direction.
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, window.clone());
        crate::executor::model::eval_memo_clear();
        let certified = {
            let model = self
                .last_model
                .as_ref()
                .expect("model presence checked above");
            window.iter().all(|&assertion| {
                matches!(
                    self.evaluate_term(model, assertion),
                    crate::executor::model::EvalValue::Bool(true)
                )
            })
        };
        self.ctx.assertions = saved_assertions;
        crate::executor::model::eval_memo_clear();
        if certified {
            tracing::debug!(
                authored = authored.len(),
                "self-check: SAT certified against the authored assertion window"
            );
        }
        certified
    }

    /// Close the authored window under the definitions of variables the emitted
    /// model leaves unvalued (see `self_check_authored_model_certified`).
    ///
    /// Returns the substituted window, or `None` when the closure is not
    /// well-founded — a variable defined twice by syntactically different right
    /// sides is left alone (both equalities are then checked for real), and a
    /// window that still mentions a defined variable after the fixpoint (a
    /// definitional cycle) fails closed.
    fn self_check_authored_definitional_closure(
        &mut self,
        authored: &[TermId],
    ) -> Option<Vec<TermId>> {
        use ay_core::TermData;
        // Quantified windows keep the authored assertions verbatim. `substitute`
        // is not capture-avoiding, and a quantifier-BOUND variable is a
        // `TermData::Var` with no model value — exactly the shape the definition
        // scan looks for — so a `(forall ((x Int)) (= x 5))` would be misread as
        // a definition of a free `x` and pushed through the whole window. Never
        // close over a window that contains a binder.
        if authored
            .iter()
            .any(|&assertion| self.contains_quantifier(assertion))
        {
            return Some(authored.to_vec());
        }
        let model = self.last_model.as_ref()?;
        // A variable is definable here only if the model gives it NO value: a
        // variable the solver assigned must be checked at that value, never
        // redefined to whatever would make the formula true.
        let mut defs: Vec<(TermId, TermId)> = Vec::new();
        let mut rejected: ay_core::kani_compat::DetHashSet<TermId> =
            ay_core::kani_compat::DetHashSet::default();
        for &assertion in authored {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            for (var, body) in [(lhs, rhs), (rhs, lhs)] {
                if !matches!(self.ctx.terms.get(var), TermData::Var(_, _)) {
                    continue;
                }
                if !matches!(
                    self.evaluate_term(model, var),
                    crate::executor::model::EvalValue::Unknown
                ) {
                    continue;
                }
                if Self::term_mentions(&self.ctx.terms, body, var) {
                    continue;
                }
                match defs.iter().find(|(v, _)| *v == var) {
                    Some((_, existing)) if *existing == body => {}
                    Some(_) => {
                        rejected.insert(var);
                    }
                    None => defs.push((var, body)),
                }
            }
        }
        defs.retain(|(var, _)| !rejected.contains(var));
        if defs.is_empty() {
            return Some(authored.to_vec());
        }
        // Chained definitions (`a_2 = store(a_1, ..)`, `a_1 = store(a0, ..)`)
        // need one pass per link; `substitute` is simultaneous and does not
        // recurse into replacements.
        let froms: Vec<TermId> = defs.iter().map(|(v, _)| *v).collect();
        let mut tos: Vec<TermId> = defs.iter().map(|(_, b)| *b).collect();
        for _ in 0..defs.len() {
            let next: Vec<TermId> = tos
                .iter()
                .map(|&body| self.ctx.terms.substitute(body, &froms, &tos))
                .collect();
            if next == tos {
                break;
            }
            tos = next;
        }
        // Fail closed on a definitional cycle: a right-hand side that still
        // mentions a defined variable is not a well-founded witness.
        if tos.iter().any(|&body| {
            froms
                .iter()
                .any(|&var| Self::term_mentions(&self.ctx.terms, body, var))
        }) {
            return None;
        }
        let window: Vec<TermId> = authored
            .iter()
            .map(|&assertion| self.ctx.terms.substitute(assertion, &froms, &tos))
            .collect();
        Some(window)
    }

    fn record_model_validation_stats(&mut self, stats: &ValidationStats) {
        self.last_statistics
            .set_int("model_validation.checked", stats.checked as u64);
        self.last_statistics
            .set_int("model_validation.delegated", stats.delegated_checks as u64);
        self.last_statistics.set_int(
            "model_validation.array_delegated",
            stats.array_delegated_checks as u64,
        );
        self.last_statistics.set_int(
            "model_validation.sat_fallback",
            stats.sat_fallback_count as u64,
        );
        self.last_statistics
            .set_int("model_validation.total", stats.total as u64);
        // Per-kind skip provenance (#selfcert-diag). The `--self-check` SAT gate
        // rejects on `incomplete > 0`, which aggregates every skip kind plus the
        // SAT-fallback count; without these counters a downgrade reports only
        // "N of M unverified" and gives no way to tell an internal-auxiliary
        // skip from a genuine evaluator gap. Observability only.
        self.last_statistics.set_int(
            "model_validation.skipped_internal",
            stats.skipped_internal as u64,
        );
        self.last_statistics.set_int(
            "model_validation.skipped_quantifier",
            stats.skipped_quantifier as u64,
        );
        self.last_statistics.set_int(
            "model_validation.skipped_datatype",
            stats.skipped_datatype as u64,
        );
        self.last_statistics
            .set_int("model_validation.skipped_dtbv", stats.skipped_dtbv as u64);
        self.last_statistics.set_int(
            "model_validation.skipped_arith_array_mix",
            stats.skipped_arith_array_mix as u64,
        );
    }

    /// Validate that the current model satisfies all assertions.
    ///
    /// Returns `Ok(ValidationStats)` if all assertions evaluate to `true`,
    /// or `Err` with details about which assertion failed.
    pub fn validate_model(&self) -> std::result::Result<ValidationStats, ModelValidationError> {
        self.validate_model_attempt().into_result()
    }

    /// Strict pre-gate for SAT model validation.
    ///
    /// Walks every assertion and consults the per-theory `DefinitiveEval`
    /// oracles (see `definitive_eval.rs`). If any oracle declares an
    /// assertion definitively violated — meaning all arguments resolve
    /// to concrete values under the model and the evaluator returns
    /// `Bool(false)` — returns `Some((index, oracle_name))` describing
    /// the violation. Callers treat this as a hard rejection and degrade
    /// SAT to Unknown, BYPASSING the SAT-fallback pipeline entirely.
    ///
    /// This is the global verify_model gate: it closes the `#7460`
    /// SAT-fallback polarity hole that allowed false-SAT results to pass
    /// through the observation pipeline for ground array/string
    /// predicates (#8779, #8729, #8745).
    ///
    /// Returns `None` when no oracle fires, meaning the normal
    /// observation pipeline may proceed.
    pub(in crate::executor) fn verify_model_strict(&self) -> Option<(usize, &'static str, TermId)> {
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            _ => return None,
        };
        // Memoize `evaluate_term` across this immutable-model strict-gate pass
        // (perf-only; #eval-memo). `&self` keeps the model immutable.
        let _eval_memo = crate::executor::model::EvalMemoSession::new();
        // Flatten to per-leaf assertions so oracles see each conjunct
        // individually. The pipeline's FlattenAnd preprocessor already
        // splits top-level `and` before Tseitin, but defensive flattening
        // here keeps the gate sound regardless of the upstream order.
        let flat = self.flatten_assertion_conjunctions();
        for (i, &assertion) in flat.iter().enumerate() {
            if let Some(name) = check_definitive_false(self, model, assertion) {
                return Some((i, name, assertion));
            }
        }
        // (#seq-ite-eq) Cross-conjunct unit-clause contradiction. Some conjuncts
        // each evaluate to Unknown in isolation, yet TOGETHER they force a
        // contradiction once every concretely-`false` disjunct is dropped. The
        // canonical case is a Tseitin-encoded `(= L (ite c t e))` where `L`
        // equals NEITHER branch: it expands to `(or (= L t) (not c))` and
        // `(or c (= L e))`; with `(= L t)` and `(= L e)` both concretely false
        // these reduce to the unit clauses `(not c)` and `c` over the SAME
        // boolean atom `c`, which is unsatisfiable. Detect this soundly (it only
        // ever degrades SAT to Unknown).
        if let Some((idx, atom)) = self.unit_clause_contradiction(model, &flat) {
            return Some((idx, "unit-clause-contradiction", atom));
        }
        // Fail-closed: an asserted ARRAY disequality the model cannot witness
        // (#qf-ax-swap-false-sat) — see `find_unwitnessed_array_disequality`.
        // Unlike the oracles above this is a COMPLETENESS statement (the
        // formula may well be sat), but the shared degrade behavior at every
        // caller (Sat -> Unknown) is exactly right for it.
        if let Some((idx, assertion)) = self.find_unwitnessed_array_disequality() {
            // Completed-cells witness form (#qf-auflia-witness-completion):
            // the witness-completion pass may have just materialized a
            // concrete cell difference the older witness forms don't see.
            let completed_witnessed = (|| {
                let inner = match self.ctx.terms.get(assertion) {
                    ay_core::term::TermData::Not(inner) => *inner,
                    _ => assertion,
                };
                if let ay_core::term::TermData::App(sym, args) = self.ctx.terms.get(inner) {
                    if sym.name() == "=" && args.len() == 2 {
                        return self.completed_chain_cells_differ(args[0], args[1]);
                    }
                }
                false
            })();
            if !completed_witnessed {
                return Some((idx, "arrays-unwitnessed-diseq", assertion));
            }
        }
        // #arrays-read-conflict-fail-closed: extraction DROPPED at least one
        // cell because two committed reads of it disagreed — the completion is
        // internally inconsistent, and every evaluator downstream deliberately
        // treats the poisoned arrays as opaque (lookup -> Unknown, normalize ->
        // None). If an array-bearing ground assertion is then unevaluable,
        // this model carries NO ground evidence for it: the observation
        // pipeline would delegate it back to the very solver that produced the
        // inconsistent completion (rubber-stamp), and the unit-clause /
        // definitive-false oracles above are blind because nothing reduces to
        // a concrete Bool (QF_AX read5 wrong-sat: a read-conflicted candidate
        // on an UNSAT instance shipped as `sat`). Degrade instead. This flows
        // through the shared "arrays" rejection path, so a refinement clause
        // is derived and the search continues — a genuinely-sat instance can
        // still converge to a clean model, and the informed retry may still
        // accept THIS model if the INDEPENDENT gate confirms every assertion.
        // Sound: degrade-only (Sat -> Unknown), never flips a verdict.
        if model
            .array_model
            .as_ref()
            .is_some_and(|am| !am.read_conflicted.is_empty())
        {
            use crate::executor::model::EvalValue;
            // A top-level NEGATED array equality is deliberately excluded: an
            // undecidable `(not (= A B))` is exactly the completeness case the
            // dedicated `arrays-unwitnessed-diseq` oracle above already judges
            // with its witness-completion escapes; re-degrading it here would
            // fail-close genuinely-sat symbolic-index permutations the diseq
            // oracle deliberately tolerates (QF_AUFLIA release_sat_6546).
            let is_array_diseq = |assertion: TermId| {
                let ay_core::term::TermData::Not(inner) = self.ctx.terms.get(assertion) else {
                    return false;
                };
                let ay_core::term::TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                    return false;
                };
                sym.name() == "="
                    && args.len() == 2
                    && matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Array(_))
            };
            for (i, &assertion) in flat.iter().enumerate() {
                if matches!(self.evaluate_term(model, assertion), EvalValue::Unknown)
                    && !is_array_diseq(assertion)
                    && StaticFeatures::collect(&self.ctx.terms, &[assertion]).has_arrays
                {
                    return Some((i, "arrays-read-conflict-uneval", assertion));
                }
            }
        }
        None
    }

    /// Repair array-read pins from asserted equalities before the strict gate
    /// (#qf-auflia-read-pin-repair).
    ///
    /// A top-level asserted `(= x (select A i))` PINS the read `A[i]` to `x`'s
    /// value. Model materialization builds the array interpretation from
    /// store chains and select-cache values whose sources (EUF speculative
    /// class integers, LIA shadow registrations, completion defaults) can
    /// disagree with the value `x` ultimately carries after all completion
    /// passes — the strict gate then rejects the very assertion that DEFINES
    /// the entry, degrading genuine sats (the SMT-COMP storecomm/storeinv
    /// `_pp_` families: ~28 of 120 QF_AUFLIA files at 60s). Aligning the
    /// interpretation entry (and the select term's merged value) with the
    /// asserted pin makes the definition hold by construction.
    ///
    /// Soundness: this runs BEFORE the full validation battery — every oracle,
    /// the unwitnessed-diseq guard, and the independent fail-closed
    /// ay-model-check gate still evaluate the repaired model against every
    /// assertion. The repair only removes SELF-REFERENTIAL rejections; a model
    /// that is wrong anywhere else still degrades exactly as today.
    /// Same-base negated chain-equality decision (#qfax-neg-dual): the
    /// union-find decider's DUAL, for `(not (= chainA chainB))` over ONE
    /// base with repeated write indices and element-var alias writes (the
    /// swap_invalid sf class). Nodes = base cells at the pattern's atoms +
    /// element alias vars; unions = alias definitions resolved under the
    /// pattern (last-write-wins); REJECT a pattern if an asserted element
    /// disequality is unioned; ACCEPT iff some atom's two final chain cells
    /// land in DIFFERENT classes — one fresh value per class is then an
    /// explicit model. Runs ONLY for the assertion the last cycle rejected
    /// (inside the informed retry), so happy paths never pay; every gate
    /// re-validates the install.
    pub(in crate::executor) fn repair_negated_same_base_chain(&mut self) {
        use ay_core::term::TermData;
        let Some(rejected) = self.last_rejected_array_assertion else {
            return;
        };
        if self.last_model.is_none() {
            return;
        }
        if let Some(model) = self.last_model.as_mut() {
            model.revoke_all_quantified_model_seals();
        }
        let dbg = ay_core::misc_cli_flags().debug_read_pin;
        let TermData::Not(inner) = self.ctx.terms.get(rejected) else {
            return;
        };
        let inner = *inner;
        let TermData::App(sym, args) = self.ctx.terms.get(inner) else {
            return;
        };
        if sym.name() != "=" || args.len() != 2 {
            return;
        }
        if !matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Array(_)) {
            return;
        }
        let defs = self.build_array_defs();
        let walk = |mut t: TermId| {
            let mut writes: Vec<(TermId, TermId)> = Vec::new();
            let mut hops = 0usize;
            loop {
                hops += 1;
                if hops > 256 {
                    break;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(s2, a2) if s2.name() == "store" && a2.len() == 3 => {
                        writes.push((a2[1], a2[2]));
                        t = a2[0];
                    }
                    TermData::Var(_, _) => match defs.get(&t) {
                        Some(&d) => t = d,
                        None => break,
                    },
                    _ => break,
                }
            }
            (writes, t)
        };
        let (wa, base_a) = walk(args[0]);
        let (wb, base_b) = walk(args[1]);
        if base_a != base_b || wa.is_empty() || wb.is_empty() {
            return;
        }
        let base = base_a;
        // Index vars.
        let mut idx_vars: Vec<TermId> = Vec::new();
        for &(i, _) in wa.iter().chain(wb.iter()) {
            if matches!(self.ctx.terms.get(i), TermData::Var(_, _)) && !idx_vars.contains(&i) {
                idx_vars.push(i);
            }
        }
        let n = idx_vars.len();
        if n == 0 || n > 9 {
            return;
        }
        // Element alias vars (Var := select(...)) in the defs map, plus any
        // element vars appearing as write values.
        let mut elems: Vec<TermId> = Vec::new();
        for &(_, v) in wa.iter().chain(wb.iter()) {
            if matches!(self.ctx.terms.get(v), TermData::Var(_, _)) && !elems.contains(&v) {
                elems.push(v);
            }
        }
        for (&v, &d) in defs.iter() {
            if matches!(
                self.ctx.terms.get(d),
                TermData::App(s2, a2) if s2.name() == "select" && a2.len() == 2
            ) && !elems.contains(&v)
            {
                elems.push(v);
            }
        }
        elems.sort_unstable_by_key(|t| t.0);
        // Asserted element disequalities AND equalities among `elems`.
        let mut ediseqs: Vec<(usize, usize)> = Vec::new();
        let mut eeqs: Vec<(usize, usize)> = Vec::new();
        for &assertion in &self.ctx.assertions.clone() {
            let (neg, eq_t) = match self.ctx.terms.get(assertion) {
                TermData::Not(i2) => (true, *i2),
                _ => (false, assertion),
            };
            let TermData::App(s2, a2) = self.ctx.terms.get(eq_t) else {
                continue;
            };
            if s2.name() != "=" || a2.len() != 2 {
                continue;
            }
            let (Some(pa), Some(pb)) = (
                elems.iter().position(|&e| e == a2[0]),
                elems.iter().position(|&e| e == a2[1]),
            ) else {
                continue;
            };
            if neg {
                ediseqs.push((pa, pb));
            } else {
                eeqs.push((pa, pb));
            }
        }
        // Pattern enumeration.
        let mut rgs = vec![0usize; n];
        let mut tried = 0usize;
        loop {
            tried += 1;
            if tried > 120_000 {
                break;
            }
            let mut idx_atom: ay_core::kani_compat::DetHashMap<TermId, String> =
                ay_core::kani_compat::DetHashMap::default();
            let mut seen_atoms: Vec<String> = Vec::new();
            for (k, &iv) in idx_vars.iter().enumerate() {
                let a = format!("@ay!wit!nidx!{}", rgs[k]);
                if !seen_atoms.contains(&a) {
                    seen_atoms.push(a.clone());
                }
                idx_atom.insert(iv, a);
            }
            let n_atoms = seen_atoms.len();
            // UF nodes: [0..n_atoms) = base cells; [n_atoms..) = elems.
            let total = n_atoms + elems.len();
            let mut uf: Vec<usize> = (0..total).collect();
            fn find(uf: &mut [usize], mut x: usize) -> usize {
                while uf[x] != x {
                    uf[x] = uf[uf[x]];
                    x = uf[x];
                }
                x
            }
            fn union(uf: &mut [usize], a: usize, b: usize) {
                let (ra, rb) = (find(uf, a), find(uf, b));
                if ra != rb {
                    uf[ra] = rb;
                }
            }
            // Resolve a term (chain-cell or value) to a UF node under the
            // pattern. Returns None on failure.
            // Value resolution: alias var -> its elem node; select over a
            // walked chain -> that chain's cell at the select index's atom.
            struct Ctx2<'a> {
                exec: &'a Executor,
                defs: &'a ay_core::kani_compat::DetHashMap<TermId, TermId>,
                idx_atom: &'a ay_core::kani_compat::DetHashMap<TermId, String>,
                seen_atoms: &'a [String],
                elems: &'a [TermId],
                base: TermId,
                n_atoms: usize,
            }
            fn chain_cell_node(
                c: &Ctx2<'_>,
                chain: TermId,
                at: &str,
                depth: usize,
            ) -> Option<usize> {
                use ay_core::term::TermData;
                if depth > 64 {
                    return None;
                }
                let mut t = chain;
                let mut hops = 0usize;
                loop {
                    hops += 1;
                    if hops > 256 {
                        return None;
                    }
                    match c.exec.ctx.terms.get(t) {
                        TermData::App(s2, a2) if s2.name() == "store" && a2.len() == 3 => {
                            let ia = c.idx_atom.get(&a2[1])?;
                            if ia == at {
                                return value_node(c, a2[2], depth + 1);
                            }
                            t = a2[0];
                        }
                        TermData::Var(_, _) => {
                            if t == c.base {
                                let aid = c.seen_atoms.iter().position(|x| x == at)?;
                                return Some(aid);
                            }
                            match c.defs.get(&t) {
                                Some(&d) => t = d,
                                None => return None,
                            }
                        }
                        _ => return None,
                    }
                }
            }
            fn value_node(c: &Ctx2<'_>, v: TermId, depth: usize) -> Option<usize> {
                use ay_core::term::TermData;
                if depth > 64 {
                    return None;
                }
                match c.exec.ctx.terms.get(v) {
                    TermData::Var(_, _) => {
                        let pe = c.elems.iter().position(|&e| e == v)?;
                        Some(c.n_atoms + pe)
                    }
                    TermData::App(s2, a2) if s2.name() == "select" && a2.len() == 2 => {
                        let at = c.idx_atom.get(&a2[1])?.clone();
                        chain_cell_node(c, a2[0], &at, depth + 1)
                    }
                    _ => None,
                }
            }
            let c = Ctx2 {
                exec: self,
                defs: &defs,
                idx_atom: &idx_atom,
                seen_atoms: &seen_atoms,
                elems: &elems,
                base,
                n_atoms,
            };
            // Unions from alias definitions + asserted element equalities.
            let mut ok = true;
            for &(pa, pb) in &eeqs {
                union(&mut uf, n_atoms + pa, n_atoms + pb);
            }
            for (pe, &e) in elems.iter().enumerate() {
                if let Some(&d) = defs.get(&e) {
                    match value_node(&c, d, 0) {
                        Some(nd) => union(&mut uf, n_atoms + pe, nd),
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
            }
            if ok {
                // Element diseqs must separate.
                for &(pa, pb) in &ediseqs {
                    if find(&mut uf, n_atoms + pa) == find(&mut uf, n_atoms + pb) {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                // Acceptance: some atom where the chains' final cells differ.
                let mut sep = false;
                for a in seen_atoms.clone() {
                    let nl = chain_cell_node(&c, args[0], &a, 0);
                    let nr = chain_cell_node(&c, args[1], &a, 0);
                    if let (Some(x), Some(y)) = (nl, nr) {
                        if find(&mut uf, x) != find(&mut uf, y) {
                            sep = true;
                            break;
                        }
                    } else {
                        sep = false;
                        break;
                    }
                }
                if sep {
                    // Install.
                    let mut elem_vals: Vec<(TermId, String)> = Vec::new();
                    for (pe, &e) in elems.iter().enumerate() {
                        let cls = find(&mut uf, n_atoms + pe);
                        elem_vals.push((e, format!("@ay!wit!dval!{cls}")));
                    }
                    let mut cell_vals: Vec<(String, String)> = Vec::new();
                    for (aid, a) in seen_atoms.iter().enumerate() {
                        let cls = find(&mut uf, aid);
                        cell_vals.push((a.clone(), format!("@ay!wit!dval!{cls}")));
                    }
                    if let Some(model) = self.last_model.as_mut() {
                        if let Some(euf) = model.euf_model.as_mut() {
                            for (&iv, a) in idx_atom.iter() {
                                euf.term_values.insert(iv, a.clone());
                            }
                            for (e, v) in &elem_vals {
                                euf.term_values.insert(*e, v.clone());
                            }
                        }
                        if let Some(am) = model.array_model.as_mut() {
                            let entry = am.array_values.entry(base).or_default();
                            entry.stores.clear();
                            for (k, v) in cell_vals {
                                entry.stores.push((k, v));
                            }
                            entry.default = Some("@ay!wit!dval!default".to_string());
                            let keep: Vec<TermId> = am
                                .array_values
                                .keys()
                                .copied()
                                .filter(|&k| {
                                    k == base
                                        || matches!(self.ctx.terms.get(k), TermData::Var(_, _))
                                })
                                .collect();
                            am.array_values.retain(|k, _| keep.contains(k));
                        }
                    }
                    if dbg {
                        eprintln!("[neg-dual] completion installed (pattern {tried})");
                    }
                    self.last_model_validated = false;
                    self.revoke_cegqi_uf_recompletion_authority();
                    return;
                }
            }
            // next RGS
            let mut k = n as isize - 1;
            loop {
                if k <= 0 {
                    k = -1;
                    break;
                }
                let prefix_max = rgs[..k as usize].iter().copied().max().unwrap_or(0);
                if rgs[k as usize] <= prefix_max {
                    break;
                }
                k -= 1;
            }
            if k < 0 {
                break;
            }
            rgs[k as usize] += 1;
            for v in rgs.iter_mut().skip(k as usize + 1) {
                *v = 0;
            }
        }
        if dbg {
            eprintln!("[neg-dual] no separating pattern ({tried} tried)");
        }
    }

    /// Cross-base chain-equality completion (#qf-ax-storeinv): the storeinv
    /// sat shape asserts a POSITIVE equality between two store chains that
    /// progressively swap cells between two DIFFERENT bases, plus
    /// `(not (= a1 a2))`. Satisfying models need index COLLISIONS (z3
    /// collapses all indices onto 2 atoms) and bases that agree everywhere
    /// except swapped cells. This pass tries candidate index patterns
    /// (all-same, all-distinct, first=last) with base interps aliased
    /// except one differing cell, VERIFIES the chain equality concretely
    /// via a bi-base recursive resolver, and installs the completion only
    /// when the equality holds at every written atom while the bases
    /// differ somewhere. Every downstream gate re-validates fail-closed.
    fn repair_cross_base_chain_equalities(&mut self) {
        use ay_core::term::TermData;
        // OPT-IN (#qf-ax-storeinv, measured incomplete): the bi-base resolver
        // and verified-install machinery are sound, but the completion needs
        // the base-diff cells to sit EXACTLY at atoms overwritten by BOTH
        // chains with EQUAL final written values — and finding such an index
        // pattern is the satisfying search in miniature (z3's model uses a
        // specific 2-value collapse over 10 indices; the three candidate
        // patterns here all fail final-value equality: measured l=xval!0 vs
        // r=xval!1 under all-same — swap parity routes base reads crosswise).
        // Enable for pattern experimentation; the gates re-validate anyway.
        // ALWAYS-ON since the union-find decision + replace-not-merge
        // install (depth-2 repro and storeinv_invalid nf convert sat through
        // the full gate stack; +1 @60s, 0 conflicts). (The former
        // `AY_NO_CROSS_BASE_COMPLETION` kill switch is removed.)
        if self.last_model.is_none() {
            return;
        }
        if let Some(model) = self.last_model.as_mut() {
            model.revoke_all_quantified_model_seals();
        }
        let dbg = ay_core::misc_cli_flags().debug_read_pin;
        // Definition map (#qfax-sf-defchase): sf variants flatten chains
        // through variable definitions (= a_k (store a_j i v)). The walk
        // chases them so a Var that IS a defined chain keeps unfolding;
        // undefined Vars remain bases.
        let mut defs: ay_core::kani_compat::DetHashMap<TermId, TermId> =
            ay_core::kani_compat::DetHashMap::default();
        for &assertion in &self.ctx.assertions {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (a, b) = (args[0], args[1]);
            let a_var = matches!(self.ctx.terms.get(a), TermData::Var(_, _));
            let b_store = matches!(
                self.ctx.terms.get(b),
                TermData::App(s2, a2) if s2.name() == "store" && a2.len() == 3
            );
            let b_var = matches!(self.ctx.terms.get(b), TermData::Var(_, _));
            let a_store = matches!(
                self.ctx.terms.get(a),
                TermData::App(s2, a2) if s2.name() == "store" && a2.len() == 3
            );
            let b_select = matches!(
                self.ctx.terms.get(b),
                TermData::App(s2, a2) if s2.name() == "select" && a2.len() == 2
            );
            let a_select = matches!(
                self.ctx.terms.get(a),
                TermData::App(s2, a2) if s2.name() == "select" && a2.len() == 2
            );
            if a_var && (b_store || b_select) {
                defs.entry(a).or_insert(b);
            } else if b_var && (a_store || a_select) {
                defs.entry(b).or_insert(a);
            }
        }
        let defs = &defs;
        let walk = |terms: &ay_core::TermStore, mut t: TermId| {
            let mut writes: Vec<(TermId, TermId)> = Vec::new();
            let mut hops = 0usize;
            loop {
                hops += 1;
                if hops > 256 {
                    break;
                }
                match terms.get(t) {
                    TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                        writes.push((args[1], args[2]));
                        t = args[0];
                    }
                    TermData::Var(_, _) => {
                        if let Some(&d) = defs.get(&t) {
                            t = d; // chase the definition
                        } else {
                            break;
                        }
                    }
                    _ => break,
                }
            }
            (writes, t)
        };
        // Collect targets: positive array equality over chains with two
        // DIFFERENT Var bases, alongside an asserted base disequality.
        let mut targets: Vec<(TermId, TermId, TermId, TermId, TermId)> = Vec::new();
        let mut base_diseqs: Vec<(TermId, TermId)> = Vec::new();
        for assertion in self.ctx.assertions.clone() {
            match self.ctx.terms.get(assertion) {
                TermData::Not(inner) => {
                    if let TermData::App(sym, args) = self.ctx.terms.get(*inner) {
                        if sym.name() == "="
                            && args.len() == 2
                            && matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Array(_))
                            && matches!(self.ctx.terms.get(args[0]), TermData::Var(_, _))
                            && matches!(self.ctx.terms.get(args[1]), TermData::Var(_, _))
                        {
                            base_diseqs.push((args[0], args[1]));
                        }
                    }
                }
                TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                    if !matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Array(_)) {
                        continue;
                    }
                    let (wl, bl) = walk(&self.ctx.terms, args[0]);
                    let (wr, br) = walk(&self.ctx.terms, args[1]);
                    if bl == br || wl.is_empty() || wr.is_empty() {
                        continue;
                    }
                    if !matches!(self.ctx.terms.get(bl), TermData::Var(_, _))
                        || !matches!(self.ctx.terms.get(br), TermData::Var(_, _))
                    {
                        continue;
                    }
                    targets.push((assertion, args[0], args[1], bl, br));
                }
                _ => {}
            }
        }
        if targets.is_empty() {
            return;
        }
        if dbg {
            eprintln!(
                "[cross-base] targets={} base_diseqs={}",
                targets.len(),
                base_diseqs.len()
            );
        }
        for (_assertion, lhs, rhs, base_l, base_r) in targets {
            // Index variables across both chains, in first-appearance order.
            let (wl, _) = walk(&self.ctx.terms, lhs);
            let (wr, _) = walk(&self.ctx.terms, rhs);
            let mut idx_vars: Vec<TermId> = Vec::new();
            for &(i, _) in wl.iter().chain(wr.iter()) {
                if matches!(self.ctx.terms.get(i), TermData::Var(_, _)) && !idx_vars.contains(&i) {
                    idx_vars.push(i);
                }
            }
            // Select-ONLY index vars (#qfax-sf-selectidx): sf's asymmetric
            // final level reads at indices that never appear as store
            // indices; without them idx_atom is incomplete and cell_ref
            // bails on EVERY pattern (measured: n=8 of 10, bails=4140/4140).
            // Scan write values recursively for select indices.
            {
                let mut stack: Vec<TermId> = wl.iter().chain(wr.iter()).map(|&(_, v)| v).collect();
                let mut steps = 0usize;
                while let Some(t) = stack.pop() {
                    steps += 1;
                    if steps > 4096 {
                        break;
                    }
                    match self.ctx.terms.get(t) {
                        TermData::App(sym, args) if sym.name() == "select" && args.len() == 2 => {
                            if matches!(self.ctx.terms.get(args[1]), TermData::Var(_, _))
                                && !idx_vars.contains(&args[1])
                            {
                                idx_vars.push(args[1]);
                            }
                            stack.push(args[0]);
                            stack.push(args[1]);
                        }
                        TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                            stack.extend(args.iter().copied());
                        }
                        TermData::Var(_, _) => {
                            if let Some(&d) = defs.get(&t) {
                                stack.push(d);
                            }
                        }
                        _ => {}
                    }
                }
            }
            if idx_vars.is_empty() {
                continue;
            }
            // Candidate index patterns: ALL set partitions of the index
            // vars (restricted-growth-string enumeration), capped. z3's
            // satisfying models use specific collapses (e.g. 10 indices onto
            // 2 atoms); the right partition is instance-specific, and with
            // per-pattern verification costing microseconds, exhaustive
            // enumeration up to Bell(10) = 115,975 is affordable for files
            // that are otherwise permanently unknown.
            let n = idx_vars.len();
            const PATTERN_CAP: usize = 200_000;
            let mut patterns: Vec<Vec<usize>> = Vec::new();
            {
                let mut rgs = vec![0usize; n];
                loop {
                    patterns.push(rgs.clone());
                    if patterns.len() >= PATTERN_CAP {
                        break;
                    }
                    // next restricted growth string
                    let mut k = n as isize - 1;
                    loop {
                        if k <= 0 {
                            k = -1;
                            break;
                        }
                        let prefix_max = rgs[..k as usize].iter().copied().max().unwrap_or(0);
                        if rgs[k as usize] <= prefix_max {
                            break;
                        }
                        k -= 1;
                    }
                    if k < 0 {
                        break;
                    }
                    rgs[k as usize] += 1;
                    for v in rgs.iter_mut().skip(k as usize + 1) {
                        *v = 0;
                    }
                }
            }
            let is_int_idx = matches!(self.ctx.terms.sort(idx_vars[0]), ay_core::Sort::Int);
            let mut success = false;
            let mut cnt_bail = 0usize;
            let mut cnt_nosep = 0usize;
            for pattern in patterns {
                // Build trial index valuation (atom strings).
                let mut idx_atom: ay_core::kani_compat::DetHashMap<TermId, String> =
                    ay_core::kani_compat::DetHashMap::default();
                for (k, &iv) in idx_vars.iter().enumerate() {
                    let a = if is_int_idx {
                        format!("{}", 7_000_001 + pattern[k] as i64)
                    } else {
                        format!("@ay!wit!xidx!{}", pattern[k])
                    };
                    idx_atom.insert(iv, a);
                }
                // Trial base interps: base_l gets distinct cells per atom;
                // base_r aliases base_l EXCEPT at the first atom (cell 0),
                // which witnesses (not (= base_l base_r)).
                let mut interp_l: Vec<(String, String)> = Vec::new();
                let mut interp_r: Vec<(String, String)> = Vec::new();
                let mut seen_atoms: Vec<String> = Vec::new();
                for &p in pattern.iter().take(n) {
                    let a = if is_int_idx {
                        format!("{}", 7_000_001 + p as i64)
                    } else {
                        format!("@ay!wit!xidx!{p}")
                    };
                    if !seen_atoms.contains(&a) {
                        seen_atoms.push(a);
                    }
                }
                // Cell universe: (side, atom-id) with side 0 = base_l,
                // 1 = base_r. Union-find over 2 * seen_atoms.len() nodes
                // (#qfax-storeinv-uf): chain equality unions cells; the base
                // disequality needs a separating tracked atom; a verified
                // pattern yields an EXPLICIT model (fresh element per class).
                let n_atoms = seen_atoms.len();
                let mut uf: Vec<usize> = (0..2 * n_atoms).collect();
                fn find(uf: &mut [usize], mut x: usize) -> usize {
                    while uf[x] != x {
                        uf[x] = uf[uf[x]];
                        x = uf[x];
                    }
                    x
                }
                fn union(uf: &mut [usize], a: usize, b: usize) {
                    let (ra, rb) = (find(uf, a), find(uf, b));
                    if ra != rb {
                        uf[ra] = rb;
                    }
                }
                // Resolve a chain cell to a cell-ref: Some((side, atom_id))
                // = a base cell; None = resolution failed (skip pattern).
                #[allow(clippy::too_many_arguments)]
                fn cell_ref(
                    exec: &Executor,
                    defs: &ay_core::kani_compat::DetHashMap<TermId, TermId>,
                    idx_atom: &ay_core::kani_compat::DetHashMap<TermId, String>,
                    base_l: TermId,
                    base_r: TermId,
                    seen_atoms: &[String],
                    arr: TermId,
                    at: &str,
                    depth: usize,
                ) -> Option<(usize, usize)> {
                    use ay_core::term::TermData;
                    if depth > 64 {
                        return None;
                    }
                    if arr == base_l || arr == base_r {
                        let side = usize::from(arr == base_r);
                        let aid = seen_atoms.iter().position(|x| x == at)?;
                        return Some((side, aid));
                    }
                    // Chase variable definitions (sf-flattened chains).
                    if matches!(exec.ctx.terms.get(arr), TermData::Var(_, _)) {
                        if let Some(&d) = defs.get(&arr) {
                            return cell_ref(
                                exec,
                                defs,
                                idx_atom,
                                base_l,
                                base_r,
                                seen_atoms,
                                d,
                                at,
                                depth + 1,
                            );
                        }
                        return None;
                    }
                    let TermData::App(sym, args) = exec.ctx.terms.get(arr) else {
                        return None;
                    };
                    if sym.name() != "store" || args.len() != 3 {
                        return None;
                    }
                    let (b, i, v) = (args[0], args[1], args[2]);
                    let ia = idx_atom.get(&i)?;
                    if ia == at {
                        // Chase element-var aliases (= e_l (select ...)) —
                        // the sf variants write via such aliases (#8785).
                        let mut v = v;
                        let mut hops = 0usize;
                        while hops < 64 {
                            hops += 1;
                            match exec.ctx.terms.get(v) {
                                TermData::Var(_, _) => {
                                    if let Some(&d) = defs.get(&v) {
                                        v = d;
                                    } else {
                                        break;
                                    }
                                }
                                _ => break,
                            }
                        }
                        return match exec.ctx.terms.get(v) {
                            TermData::App(vs, va) if vs.name() == "select" && va.len() == 2 => {
                                let va_at = idx_atom.get(&va[1])?.clone();
                                cell_ref(
                                    exec,
                                    defs,
                                    idx_atom,
                                    base_l,
                                    base_r,
                                    seen_atoms,
                                    va[0],
                                    &va_at,
                                    depth + 1,
                                )
                            }
                            _ => None, // non-select write value: outside fragment
                        };
                    }
                    cell_ref(
                        exec,
                        defs,
                        idx_atom,
                        base_l,
                        base_r,
                        seen_atoms,
                        b,
                        at,
                        depth + 1,
                    )
                }
                // Chain equality at every atom: union the two sides' cells.
                let mut ok = true;
                for a in &seen_atoms {
                    let cl = cell_ref(
                        self,
                        defs,
                        &idx_atom,
                        base_l,
                        base_r,
                        &seen_atoms,
                        lhs,
                        a,
                        0,
                    );
                    let cr = cell_ref(
                        self,
                        defs,
                        &idx_atom,
                        base_l,
                        base_r,
                        &seen_atoms,
                        rhs,
                        a,
                        0,
                    );
                    let (Some((sl, al)), Some((sr, ar))) = (cl, cr) else {
                        ok = false;
                        break;
                    };
                    union(&mut uf, sl * n_atoms + al, sr * n_atoms + ar);
                }
                if !ok {
                    cnt_bail += 1;
                    continue;
                }
                // Base disequality: some tracked atom must separate the bases.
                let mut sep: Option<usize> = None;
                for aid in 0..n_atoms {
                    if find(&mut uf, aid) != find(&mut uf, n_atoms + aid) {
                        sep = Some(aid);
                        break;
                    }
                }
                if sep.is_none() {
                    cnt_nosep += 1;
                    continue; // pattern forces base_l == base_r: no witness
                }
                // Explicit model: one fresh element per union-find class.
                for (aid, a) in seen_atoms.clone().iter().enumerate() {
                    let cl = find(&mut uf, aid);
                    let cr = find(&mut uf, n_atoms + aid);
                    interp_l.push((a.clone(), format!("@ay!wit!xval!{cl}")));
                    interp_r.push((a.clone(), format!("@ay!wit!xval!{cr}")));
                }
                // Install: index valuations + both base interps.
                if let Some(model) = self.last_model.as_mut() {
                    for (&iv, a) in idx_atom.iter() {
                        if is_int_idx {
                            if let Ok(big) = a.parse::<num_bigint::BigInt>() {
                                if let Some(lia) = model.lia_model.as_mut() {
                                    lia.values.insert(iv, big.clone());
                                }
                                if let Some(euf) = model.euf_model.as_mut() {
                                    euf.term_values.insert(iv, a.clone());
                                    euf.int_values.insert(iv, big);
                                }
                            }
                        } else if let Some(euf) = model.euf_model.as_mut() {
                            euf.term_values.insert(iv, a.clone());
                        }
                    }
                    if let Some(am) = model.array_model.as_mut() {
                        for (base, interp) in [(base_l, &interp_l), (base_r, &interp_r)] {
                            let e = am.array_values.entry(base).or_default();
                            // REPLACE the interp wholesale: stale
                            // pre-completion entries at old atoms are cells
                            // the chains read straight from the bases, and
                            // any leftover asymmetry there falsifies the
                            // chain equality at the gate (measured: a stale
                            // ("@Index!2","@Element!1") in one base only).
                            e.stores.clear();
                            for (k, v) in interp.iter() {
                                e.stores.push((k.clone(), v.clone()));
                            }
                            // Untracked cells: both chains read their bases
                            // directly there, so the chain equality forces
                            // a1[y] == a2[y] for every untracked y — the
                            // bases must share ONE default.
                            e.default = Some("@ay!wit!xval!default".to_string());
                        }
                        // Drop STALE alias interps for non-base array terms
                        // (intermediate ?v chains): the independent checker
                        // must recompute every select from the two base
                        // interps, not from solver-era snapshots that
                        // contradict the installed completion (same
                        // discipline as the array reconstruction pass).
                        let keep: Vec<TermId> = am
                            .array_values
                            .keys()
                            .copied()
                            .filter(|&k| {
                                k == base_l
                                    || k == base_r
                                    || matches!(self.ctx.terms.get(k), TermData::Var(_, _))
                            })
                            .collect();
                        am.array_values.retain(|k, _| keep.contains(k));
                    }
                }
                // Element-var aliases (= e_l (select ...)) are asserted
                // definitions the gates re-check: resolve each through the
                // installed interps and write its value, or the alias
                // equality itself falsifies the model (measured on sf).
                {
                    let mut alias_values: Vec<(TermId, String)> = Vec::new();
                    for (&v, &d) in defs.iter() {
                        let TermData::App(ds, da) = self.ctx.terms.get(d) else {
                            continue;
                        };
                        if ds.name() != "select" || da.len() != 2 {
                            continue;
                        }
                        let Some(at) = idx_atom.get(&da[1]).cloned() else {
                            continue;
                        };
                        let Some((side, aid)) = cell_ref(
                            self,
                            defs,
                            &idx_atom,
                            base_l,
                            base_r,
                            &seen_atoms,
                            da[0],
                            &at,
                            0,
                        ) else {
                            continue;
                        };
                        let interp = if side == 0 { &interp_l } else { &interp_r };
                        if let Some((_, val)) = interp.get(aid) {
                            alias_values.push((v, val.clone()));
                        }
                    }
                    if let Some(model) = self.last_model.as_mut() {
                        if let Some(euf) = model.euf_model.as_mut() {
                            for (v, val) in alias_values {
                                euf.term_values.insert(v, val);
                            }
                        }
                    }
                }
                success = true;
                self.last_model_validated = false;
                self.revoke_cegqi_uf_recompletion_authority();
                if dbg {
                    eprintln!("[cross-base] completion installed");
                    // Ground-vs-symbolic diff: evaluate select(chain, iv) for
                    // one index var per atom class and compare with cell_ref.
                    for &iv in idx_vars.iter() {
                        let a = idx_atom.get(&iv).cloned().unwrap_or_default();
                        let sl = self.ctx.terms.mk_select(lhs, iv);
                        let sr = self.ctx.terms.mk_select(rhs, iv);
                        let model = self.last_model.as_ref().unwrap();
                        let gl = self.eval_value_to_model_atom(&self.evaluate_term(model, sl));
                        let gr = self.eval_value_to_model_atom(&self.evaluate_term(model, sr));
                        let rl = cell_ref(
                            self,
                            defs,
                            &idx_atom,
                            base_l,
                            base_r,
                            &seen_atoms,
                            lhs,
                            &a,
                            0,
                        );
                        let rr = cell_ref(
                            self,
                            defs,
                            &idx_atom,
                            base_l,
                            base_r,
                            &seen_atoms,
                            rhs,
                            &a,
                            0,
                        );
                        eprintln!(
                            "[cross-base]   ground@{a}: L={gl:?} R={gr:?} | sym L={rl:?} R={rr:?}"
                        );
                    }
                }
                break;
            }
            if dbg && !success {
                eprintln!(
                    "[cross-base] no pattern verified (n={n} bails={cnt_bail} nosep={cnt_nosep})"
                );
            }
        }
    }

    /// Build the asserted-definition map (#qfax-sf-defchase): Var -> its
    /// defining store/select expression, from top-level equalities. Shared by
    /// the witness completion, the guard witness, and the cross-base pass so
    /// sf-flattened chains unfold everywhere.
    pub(in crate::executor) fn build_array_defs(
        &self,
    ) -> ay_core::kani_compat::DetHashMap<TermId, TermId> {
        use ay_core::term::TermData;
        let mut defs: ay_core::kani_compat::DetHashMap<TermId, TermId> =
            ay_core::kani_compat::DetHashMap::default();
        for &assertion in &self.ctx.assertions {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (a, b) = (args[0], args[1]);
            let is_def_rhs = |t: TermId| {
                matches!(
                    self.ctx.terms.get(t),
                    TermData::App(s2, a2)
                        if (s2.name() == "store" && a2.len() == 3)
                            || (s2.name() == "select" && a2.len() == 2)
                )
            };
            if matches!(self.ctx.terms.get(a), TermData::Var(_, _)) && is_def_rhs(b) {
                defs.entry(a).or_insert(b);
            } else if matches!(self.ctx.terms.get(b), TermData::Var(_, _)) && is_def_rhs(a) {
                defs.entry(b).or_insert(a);
            }
        }
        defs
    }

    /// Recursive cell resolution (#qf-ax-witness-nested): the effective value
    /// of a same-base store chain at a witness index atom. Write values that
    /// are selects over ANY same-base store chain recurse into that chain's
    /// writes (evaluate_term is blind to witness interp entries over
    /// uninterpreted index sorts). Depth-capped defensively.
    pub(in crate::executor) fn witness_cell_rec(
        &self,
        defs: &ay_core::kani_compat::DetHashMap<TermId, TermId>,
        base: TermId,
        interp_lookup: &dyn Fn(&str) -> Option<String>,
        writes: &[(TermId, TermId)],
        at: &str,
        depth: usize,
    ) -> Option<String> {
        use ay_core::term::TermData;
        if depth > 24 {
            return None;
        }
        let model = self.last_model.as_ref()?;
        for &(i, v) in writes {
            let ia = self.eval_value_to_model_atom(&self.evaluate_term(model, i))?;
            if ia == at {
                // Chase element/array aliases (sf-flattened, #qfax-sf-defchase).
                let mut v = v;
                let mut hops = 0usize;
                while hops < 64 {
                    hops += 1;
                    match self.ctx.terms.get(v) {
                        TermData::Var(_, _) => match defs.get(&v) {
                            Some(&d) => v = d,
                            None => break,
                        },
                        _ => break,
                    }
                }
                if let TermData::App(vsym, vargs) = self.ctx.terms.get(v) {
                    if vsym.name() == "select" && vargs.len() == 2 {
                        let mut t = vargs[0];
                        let mut inner: Vec<(TermId, TermId)> = Vec::new();
                        let mut hops2 = 0usize;
                        loop {
                            hops2 += 1;
                            if hops2 > 256 {
                                break;
                            }
                            match self.ctx.terms.get(t) {
                                TermData::App(sym2, args2)
                                    if sym2.name() == "store" && args2.len() == 3 =>
                                {
                                    inner.push((args2[1], args2[2]));
                                    t = args2[0];
                                }
                                TermData::Var(_, _) if t != base => match defs.get(&t) {
                                    Some(&d) => t = d,
                                    None => break,
                                },
                                _ => break,
                            }
                        }
                        if t == base {
                            let i2 = self
                                .eval_value_to_model_atom(&self.evaluate_term(model, vargs[1]))?;
                            return self.witness_cell_rec(
                                defs,
                                base,
                                interp_lookup,
                                &inner,
                                &i2,
                                depth + 1,
                            );
                        }
                    }
                }
                return self.eval_value_to_model_atom(&self.evaluate_term(model, v));
            }
        }
        interp_lookup(at)
    }

    /// Two-base variant of [`Self::witness_cell_rec`]
    /// (#qf-ax-cross-base-guard): resolves chains and select-values rooting
    /// at EITHER base against that base's own interp.
    ///
    /// Like the single-base variant, chases variable-definition aliases from
    /// `defs` (#qfax-sf-defchase) — both on write VALUES (a `Var` defined as a
    /// select over a chain unfolds before the select check) and when walking a
    /// select's array chain back to a base. Each chased definition is an
    /// asserted top-level equality, so unfolding preserves cell semantics
    /// exactly as in [`Self::witness_cell_rec`]. Resolution failure stays
    /// fail-closed (`None` skips the witness).
    #[allow(clippy::too_many_arguments)]
    pub(in crate::executor) fn witness_cell_rec2(
        &self,
        defs: &ay_core::kani_compat::DetHashMap<TermId, TermId>,
        base_a: TermId,
        la: &dyn Fn(&str) -> Option<String>,
        base_b: TermId,
        lb: &dyn Fn(&str) -> Option<String>,
        writes: &[(TermId, TermId)],
        root: TermId,
        at: &str,
        depth: usize,
    ) -> Option<String> {
        use ay_core::term::TermData;
        if depth > 24 {
            return None;
        }
        let model = self.last_model.as_ref()?;
        for &(i, v) in writes {
            let ia = self.eval_value_to_model_atom(&self.evaluate_term(model, i))?;
            if ia == at {
                // Chase element/array aliases (sf-flattened, #qfax-sf-defchase).
                let mut v = v;
                let mut hops = 0usize;
                while hops < 64 {
                    hops += 1;
                    match self.ctx.terms.get(v) {
                        TermData::Var(_, _) => match defs.get(&v) {
                            Some(&d) => v = d,
                            None => break,
                        },
                        _ => break,
                    }
                }
                if let TermData::App(vsym, vargs) = self.ctx.terms.get(v) {
                    if vsym.name() == "select" && vargs.len() == 2 {
                        let mut t = vargs[0];
                        let mut inner: Vec<(TermId, TermId)> = Vec::new();
                        let mut hops2 = 0usize;
                        loop {
                            hops2 += 1;
                            if hops2 > 256 {
                                break;
                            }
                            match self.ctx.terms.get(t) {
                                TermData::App(sym2, args2)
                                    if sym2.name() == "store" && args2.len() == 3 =>
                                {
                                    inner.push((args2[1], args2[2]));
                                    t = args2[0];
                                }
                                TermData::Var(_, _) if t != base_a && t != base_b => {
                                    match defs.get(&t) {
                                        Some(&d) => t = d,
                                        None => break,
                                    }
                                }
                                _ => break,
                            }
                        }
                        if t == base_a || t == base_b {
                            let i2 = self
                                .eval_value_to_model_atom(&self.evaluate_term(model, vargs[1]))?;
                            return self.witness_cell_rec2(
                                defs,
                                base_a,
                                la,
                                base_b,
                                lb,
                                &inner,
                                t,
                                &i2,
                                depth + 1,
                            );
                        }
                    }
                }
                return self.eval_value_to_model_atom(&self.evaluate_term(model, v));
            }
        }
        if root == base_a {
            la(at)
        } else {
            lb(at)
        }
    }

    /// Walk one exact store chain within the QFAX refinement envelope.
    pub(in crate::executor) fn exact_qfax_store_chain(
        &self,
        start: TermId,
    ) -> Option<(Vec<(TermId, TermId)>, TermId)> {
        let mut writes = Vec::new();
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut term = start;
        loop {
            if !seen.insert(term) {
                return None;
            }
            let Some((base, index, value)) = self.exact_cegar_store_parts(term) else {
                return Some((writes, term));
            };
            if writes.len() >= QFAX_STORE_WALK_LIMIT {
                return None;
            }
            writes.push((index, value));
            term = base;
        }
    }

    fn qfax_index_atom(&self, term: TermId) -> Option<String> {
        let model = self.last_model.as_ref()?;
        self.eval_value_to_model_atom(&self.evaluate_term(model, term))
    }

    fn note_qfax_dependency(
        left: TermId,
        right: TermId,
        dependencies: &mut Vec<(TermId, TermId)>,
    ) -> Option<()> {
        if left == right {
            return Some(());
        }
        let pair = if left.0 <= right.0 {
            (left, right)
        } else {
            (right, left)
        };
        if !dependencies.contains(&pair) {
            if dependencies.len() + 1 >= QFAX_CLAUSE_LITERAL_LIMIT {
                return None;
            }
            dependencies.push(pair);
        }
        Some(())
    }

    fn qfax_reduce_cell(
        &self,
        base: TermId,
        writes: &[(TermId, TermId)],
        probe_index: TermId,
        probe_atom: &str,
        dependencies: &mut Vec<(TermId, TermId)>,
        depth: usize,
    ) -> Option<QfaxCellTerm> {
        if depth > QFAX_CELL_RECURSION_LIMIT {
            return None;
        }
        for &(index, value) in writes {
            let index_atom = self.qfax_index_atom(index)?;
            Self::note_qfax_dependency(index, probe_index, dependencies)?;
            if index_atom != probe_atom {
                continue;
            }
            if let Some((array, nested_index)) = self.exact_cegar_select_parts(value) {
                let (nested_writes, nested_base) = self.exact_qfax_store_chain(array)?;
                if nested_base == base {
                    let nested_atom = self.qfax_index_atom(nested_index)?;
                    return self.qfax_reduce_cell(
                        base,
                        &nested_writes,
                        nested_index,
                        &nested_atom,
                        dependencies,
                        depth + 1,
                    );
                }
            }
            return Some(QfaxCellTerm::Value(value));
        }
        Some(QfaxCellTerm::BaseRead { index: probe_index })
    }

    fn qfax_cells_provably_equal(
        &self,
        left: QfaxCellTerm,
        right: QfaxCellTerm,
        dependencies: &mut Vec<(TermId, TermId)>,
    ) -> Option<()> {
        match (left, right) {
            (QfaxCellTerm::Value(left), QfaxCellTerm::Value(right)) => {
                (left == right).then_some(())
            }
            (QfaxCellTerm::BaseRead { index: left }, QfaxCellTerm::BaseRead { index: right }) => {
                if self.ctx.terms.sort(left) != self.ctx.terms.sort(right)
                    || self.qfax_index_atom(left)? != self.qfax_index_atom(right)?
                {
                    return None;
                }
                Self::note_qfax_dependency(left, right, dependencies)
            }
            _ => None,
        }
    }

    fn qfax_blocking_literals(
        &mut self,
        dependencies: Vec<(TermId, TermId)>,
    ) -> Option<Vec<(TermId, bool)>> {
        if dependencies.is_empty() || dependencies.len() >= QFAX_CLAUSE_LITERAL_LIMIT {
            return None;
        }
        let mut literals = Vec::with_capacity(dependencies.len());
        for (left, right) in dependencies {
            if self.ctx.terms.sort(left) != self.ctx.terms.sort(right) {
                return None;
            }
            let left_atom = self.qfax_index_atom(left)?;
            let right_atom = self.qfax_index_atom(right)?;
            let equality = self.ctx.terms.mk_eq(left, right);
            literals.push((equality, left_atom == right_atom));
        }
        Some(literals)
    }

    /// #qfax-cegar: derive a sound blocking clause from an arrays rejection.
    pub(in crate::executor) fn derive_qfax_refinement_clause(&mut self, violated: TermId) {
        use ay_core::term::TermData;
        if self.qfax_refinement_clause.is_some()
            || self.last_model.is_none()
            || self.ctx.terms.entry_stamp(violated).is_none()
        {
            return;
        }
        let equality = match self.ctx.terms.get(violated) {
            TermData::Not(inner) => *inner,
            _ => return,
        };
        let Some((left, right)) = self.exact_cegar_equality_operands(equality) else {
            return;
        };
        if !matches!(self.ctx.terms.sort(left), ay_core::Sort::Array(_)) {
            return;
        }
        let (Some((left_writes, left_base)), Some((right_writes, right_base))) = (
            self.exact_qfax_store_chain(left),
            self.exact_qfax_store_chain(right),
        ) else {
            return;
        };
        if left_base != right_base || (left_writes.is_empty() && right_writes.is_empty()) {
            return;
        }
        let mut probe_atoms = Vec::<(TermId, String)>::new();
        for &(index, _) in left_writes.iter().chain(&right_writes) {
            let Some(atom) = self.qfax_index_atom(index) else {
                return;
            };
            if !probe_atoms.iter().any(|(_, known)| known == &atom) {
                probe_atoms.push((index, atom));
            }
        }
        if probe_atoms.is_empty() {
            return;
        }
        let mut dependencies = Vec::new();
        for (probe_index, probe_atom) in probe_atoms {
            let Some(left_cell) = self.qfax_reduce_cell(
                left_base,
                &left_writes,
                probe_index,
                &probe_atom,
                &mut dependencies,
                0,
            ) else {
                return;
            };
            let Some(right_cell) = self.qfax_reduce_cell(
                left_base,
                &right_writes,
                probe_index,
                &probe_atom,
                &mut dependencies,
                0,
            ) else {
                return;
            };
            if self
                .qfax_cells_provably_equal(left_cell, right_cell, &mut dependencies)
                .is_none()
            {
                return;
            }
        }
        let Some(literals) = self.qfax_blocking_literals(dependencies) else {
            return;
        };
        if ay_core::misc_cli_flags().debug_cegar {
            eprintln!(
                "[qfax-cegar] blocking clause with {} literals",
                literals.len()
            );
        }
        self.qfax_refinement_clause = Some(literals);
    }

    /// Completed-cells witness (#qf-auflia-witness-completion): TRUE when the
    /// two same-base chains' effective cells CONCRETELY differ at some
    /// written index under the current (witness-completed) array interp.
    /// Mirrors the completion's own cell computation, including direct
    /// interp resolution for select-over-base write values (whose generic
    /// evaluation is blind to witness entries over uninterpreted sorts).
    pub(in crate::executor) fn completed_chain_cells_differ(&self, a: TermId, b: TermId) -> bool {
        use ay_core::term::TermData;
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        let walk = |mut t: TermId| {
            let mut writes: Vec<(TermId, TermId)> = Vec::new();
            while let TermData::App(sym, args) = self.ctx.terms.get(t) {
                if sym.name() != "store" || args.len() != 3 {
                    break;
                }
                writes.push((args[1], args[2]));
                t = args[0];
            }
            (writes, t)
        };
        let (wa, base_a) = walk(a);
        let (wb, base_b) = walk(b);
        if wa.is_empty() && wb.is_empty() && base_a == base_b {
            return false;
        }
        // Per-base interp lookup from the model's ACTUAL array values
        // (#qf-ax-cross-base-guard: bases may differ — each side resolves
        // against its own root's interp; a cell difference at any probed
        // atom, including base-vs-base cells at un-overwritten atoms, is a
        // concrete witness).
        let interp_lookup = |base: TermId, at: &str| -> Option<String> {
            let am = model.array_model.as_ref()?;
            let interp = am.array_values.get(&base)?;
            interp
                .stores
                .iter()
                .find(|(k, _)| k == at)
                .map(|(_, v)| v.clone())
                .or_else(|| interp.default.clone())
        };
        let wdefs = self.build_array_defs();
        let la = |at: &str| interp_lookup(base_a, at);
        let lb = |at: &str| interp_lookup(base_b, at);
        let cell_a = |writes: &[(TermId, TermId)], at: &str| -> Option<String> {
            self.witness_cell_rec2(&wdefs, base_a, &la, base_b, &lb, writes, base_a, at, 0)
        };
        let cell_b = |writes: &[(TermId, TermId)], at: &str| -> Option<String> {
            self.witness_cell_rec2(&wdefs, base_a, &la, base_b, &lb, writes, base_b, at, 0)
        };
        let mut atoms: Vec<String> = Vec::new();
        for &(i, _) in wa.iter().chain(wb.iter()) {
            if let Some(atom) = self.eval_value_to_model_atom(&self.evaluate_term(model, i)) {
                if !atoms.contains(&atom) {
                    atoms.push(atom);
                }
            }
        }
        if base_a != base_b {
            if let Some(am) = model.array_model.as_ref() {
                for base in [base_a, base_b] {
                    if let Some(interp) = am.array_values.get(&base) {
                        for (k, _) in &interp.stores {
                            if !atoms.contains(k) {
                                atoms.push(k.clone());
                            }
                        }
                    }
                }
            }
        }
        for atom in &atoms {
            if let (Some(x), Some(y)) = (cell_a(&wa, atom), cell_b(&wb, atom)) {
                if x != y {
                    return true;
                }
            }
        }
        false
    }

    /// Re-run the #A1 LIA model reconciliation passes after a post-validation
    /// repair pass mutated Int leaf values (#A1-repair-resync).
    ///
    /// The AUFLIA extract path establishes substitution equalities
    /// (`recover_substituted_lia_values`), composite Int values
    /// (`recompute_composite_int_values`) and opaque select read congruence
    /// (`reconcile_lia_select_congruence`) BEFORE validation. When
    /// `repair_asserted_array_read_pins` later rewrites leaf values (pin
    /// harmonization, diseq/index shifts), every derived value goes stale:
    /// measured on the A1 gate-over-select tests, `E` kept its pre-repair
    /// value while `(+ B1 (* 4 P))` evaluated to the repaired one, so the
    /// strict arithmetic oracle rejected `(= E (+ B1 (* 4 P)))` and a genuine
    /// `sat` degraded to `unknown`.
    ///
    /// This re-derives the same values from the CURRENT leaves and mirrors
    /// every change into the merged EUF view (and Bool substitution gates
    /// into `bool_overrides`), so all evaluators read one truth. Vars the
    /// repair itself wrote (`extra_protected`) and diseq-constrained vars
    /// keep their repaired values (protected from the RHS recompute).
    /// Sound by construction: every write only re-establishes a definitional
    /// equality under the final assignment, and the full validation battery
    /// still gates acceptance afterwards (fail-closed, #8373 backstop).
    ///
    /// Returns the number of model entries that changed.
    fn reconcile_int_model_after_repair(
        &mut self,
        extra_protected: &ay_core::kani_compat::DetHashSet<TermId>,
    ) -> usize {
        if self.recorded_var_substitutions.is_empty() {
            return 0;
        }
        if self
            .last_model
            .as_ref()
            .is_none_or(|m| m.lia_model.is_none())
        {
            return 0;
        }
        // Doomed-only guard: never touch a model no assertion refutes — the
        // reconciliation exists to rescue models the gates are already going
        // to reject, so a healthy model must pass through byte-identical.
        // (Also the perf guard: candidate trials below re-evaluate the
        // assertion set, which is only worth paying on a doomed model.)
        if !self.some_assertion_definitively_false() {
            return 0;
        }
        let vs = crate::preprocess::VariableSubstitution::from_recorded_map(
            self.recorded_var_substitutions.clone(),
        );
        let mut protected = crate::pipeline_fns::collect_top_level_arith_diseq_vars(
            &self.ctx.terms,
            &self.ctx.assertions,
        );
        protected.extend(extra_protected.iter().copied());
        let mut n_changed = self.repair_root_read_cells(&vs, &protected);
        n_changed += self.resync_lia_derived_values(&vs, &protected);
        n_changed
    }

    /// True iff some original assertion concretely evaluates to `false`
    /// under the current model (the model is DOOMED: full validation will
    /// reject it as-is).
    fn some_assertion_definitively_false(&self) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        let flat = self.flatten_assertion_conjunctions();
        flat.iter().any(|&a| {
            matches!(
                self.evaluate_term(model, a),
                crate::executor::model::EvalValue::Bool(false)
            )
        })
    }

    /// Root read-cell candidate repair (#A1-repair-resync, cross-array).
    ///
    /// Resolve every Int-sorted `select` in the LIA view through definitional
    /// array aliases (`Q -> (store D E F)`) and store chains to its ROOT cell
    /// `(base array, index value)`. The AUFLIA route can leave the SAME root
    /// cell with several DISAGREEING read values: the LIA tableau constrained
    /// one opaque select form, EUF assigned speculative class values to the
    /// congruent alias/pre-substitution forms, and the emitted base interp
    /// carries a completion default (measured on the A1 tests: 0 vs 1 vs 6
    /// for one cell). No local syntactic rule identifies the committed value,
    /// but the CANDIDATE SET is tiny — so try each candidate: write it to
    /// every congruent read and the base interp cell, re-derive the dependent
    /// substituted/composite/Bool values, and keep the first candidate under
    /// which NO original assertion evaluates definitively false. If none
    /// qualifies, the model is restored untouched (degrades exactly as
    /// before — fail-closed).
    ///
    /// Sound by construction: this only RELABELS derived read values in a
    /// model that the full validation battery still gates afterwards; it can
    /// recover a wrongly-degraded `sat` into a gate-verified model but never
    /// manufacture a verdict (#8373 backstop).
    ///
    /// Returns the number of read cells rewritten.
    fn repair_root_read_cells(
        &mut self,
        vs: &crate::preprocess::VariableSubstitution,
        protected: &ay_core::kani_compat::DetHashSet<TermId>,
    ) -> usize {
        use ay_core::term::TermData;
        if let Some(model) = self.last_model.as_mut() {
            model.revoke_all_quantified_model_seals();
        }
        let wdefs = self.build_array_defs();
        // Phase 1 (immutable): group Int reads by resolved root cell.
        let groups: Vec<(
            TermId,
            num_bigint::BigInt,
            Vec<TermId>,
            Vec<num_bigint::BigInt>,
        )> = {
            let Some(model) = self.last_model.as_ref() else {
                return 0;
            };
            let Some(lia) = model.lia_model.as_ref() else {
                return 0;
            };
            let mut groups: ay_core::kani_compat::DetHashMap<
                (TermId, num_bigint::BigInt),
                Vec<(TermId, num_bigint::BigInt)>,
            > = ay_core::kani_compat::DetHashMap::default();
            for (&t, v) in lia.values.iter() {
                let TermData::App(sym, args) = self.ctx.terms.get(t) else {
                    continue;
                };
                if sym.name() != "select" || args.len() != 2 {
                    continue;
                }
                if !matches!(self.ctx.terms.sort(t), ay_core::Sort::Int) {
                    continue;
                }
                let Some(idxv) = crate::executor::theories::lia::eval_lia_int_under_values(
                    &self.ctx.terms,
                    args[1],
                    &lia.values,
                ) else {
                    continue;
                };
                // Resolve to the root base: peel stores whose write index
                // differs from the read index; a write HIT (or any
                // unresolvable form) means the read is covered by a write
                // term, not a base cell — skip it.
                let mut cur = args[0];
                let mut resolved_base = false;
                for _ in 0..64 {
                    match self.ctx.terms.get(cur) {
                        TermData::App(s2, a2) if s2.name() == "store" && a2.len() == 3 => {
                            match crate::executor::theories::lia::eval_lia_int_under_values(
                                &self.ctx.terms,
                                a2[1],
                                &lia.values,
                            ) {
                                Some(wi) if wi != idxv => cur = a2[0],
                                _ => break, // write hit or unknown write index
                            }
                        }
                        TermData::Var(_, _) => match wdefs.get(&cur) {
                            Some(&d) => cur = d,
                            None => {
                                resolved_base = true;
                                break;
                            }
                        },
                        _ => break, // opaque array form
                    }
                }
                if !resolved_base {
                    continue;
                }
                groups.entry((cur, idxv)).or_default().push((t, v.clone()));
            }
            // Deterministic order; keep only DISAGREEING groups, with the
            // base interp's current cell value as an extra candidate.
            let mut out: Vec<(
                TermId,
                num_bigint::BigInt,
                Vec<TermId>,
                Vec<num_bigint::BigInt>,
            )> = Vec::new();
            for ((root, idxv), members) in groups {
                let mut cands: Vec<num_bigint::BigInt> =
                    members.iter().map(|(_, v)| v.clone()).collect();
                if let Some(am) = model.array_model.as_ref() {
                    if let Some(interp) = am.array_values.get(&root) {
                        let key = idxv.to_string();
                        let cell = interp
                            .stores
                            .iter()
                            .find(|(k, _)| *k == key)
                            .map(|(_, v)| v.clone())
                            .or_else(|| interp.default.clone());
                        if let Some(cell) = cell {
                            if let Ok(cv) = cell.parse::<num_bigint::BigInt>() {
                                cands.push(cv);
                            }
                        }
                    }
                }
                cands.sort();
                cands.dedup();
                if cands.len() < 2 {
                    continue; // already congruent
                }
                let terms_only: Vec<TermId> = members.iter().map(|(t, _)| *t).collect();
                out.push((root, idxv, terms_only, cands));
            }
            out.sort_by(|a, b| (a.0 .0, &a.1).cmp(&(b.0 .0, &b.1)));
            out
        };
        if groups.is_empty() {
            return 0;
        }
        let dbg = ay_core::misc_cli_flags().debug_read_pin;
        // Phase 2: candidate trials, bounded.
        let mut trials_left = 24usize;
        let mut cells_fixed = 0usize;
        for (root, idxv, members, cands) in groups {
            if cands.len() > 6 || trials_left == 0 {
                continue; // too ambiguous — leave to the gates (fail-closed)
            }
            let snapshot = self.last_model.clone();
            let mut committed = false;
            for v in &cands {
                if trials_left == 0 {
                    break;
                }
                trials_left -= 1;
                // Apply candidate: all congruent reads + the base interp cell.
                if let Some(model) = self.last_model.as_mut() {
                    if let Some(lia) = model.lia_model.as_mut() {
                        for &t in &members {
                            lia.values.insert(t, v.clone());
                        }
                    }
                    if let Some(euf) = model.euf_model.as_mut() {
                        for &t in &members {
                            euf.int_values.insert(t, v.clone());
                            euf.term_values.insert(t, v.to_string());
                        }
                    }
                    if let Some(am) = model.array_model.as_mut() {
                        let interp = am.array_values.entry(root).or_default();
                        let key = idxv.to_string();
                        match interp.stores.iter_mut().find(|(k, _)| *k == key) {
                            Some((_, cell)) => *cell = v.to_string(),
                            None => interp.stores.push((key, v.to_string())),
                        }
                    }
                }
                // Re-derive dependent values, then accept iff no original
                // assertion is definitively false under the candidate.
                self.resync_lia_derived_values(vs, protected);
                let ok = {
                    let model = self.last_model.as_ref().expect("trial model");
                    let flat = self.flatten_assertion_conjunctions();
                    flat.iter().all(|&a| {
                        !matches!(
                            self.evaluate_term(model, a),
                            crate::executor::model::EvalValue::Bool(false)
                        )
                    })
                };
                if ok {
                    if dbg {
                        eprintln!(
                            "[read-pin-repair] root-cell base=t{} idx={idxv} := {v} \
                             (members={}, candidates={})",
                            root.0,
                            members.len(),
                            cands.len()
                        );
                    }
                    committed = true;
                    cells_fixed += 1;
                    break;
                }
                self.last_model = snapshot.clone();
            }
            if !committed {
                self.last_model = snapshot;
            }
        }
        cells_fixed
    }

    /// Re-derive substituted/composite/congruent LIA values from the CURRENT
    /// Int leaves and mirror every change into the merged EUF view (and Bool
    /// substitution gates into `bool_overrides`) — see
    /// [`Self::reconcile_int_model_after_repair`].
    ///
    /// Returns the number of model entries that changed.
    fn resync_lia_derived_values(
        &mut self,
        vs: &crate::preprocess::VariableSubstitution,
        protected: &ay_core::kani_compat::DetHashSet<TermId>,
    ) -> usize {
        if let Some(model) = self.last_model.as_mut() {
            model.revoke_all_quantified_model_seals();
        }
        // Phase 1: re-derive LIA values from the repaired leaves.
        let changed: Vec<(TermId, num_bigint::BigInt)> = {
            let Some(model) = self.last_model.as_mut() else {
                return 0;
            };
            // Sentinel keys (e.g. the per-model repair marker at
            // `u32::MAX - 7`) live in `term_values` but are not real terms —
            // keep only ids the term store can resolve.
            let n_terms = self.ctx.terms.len() as u32;
            let candidates: Vec<TermId> = model
                .euf_model
                .as_ref()
                .map(|euf| {
                    euf.term_values
                        .keys()
                        .chain(euf.int_values.keys())
                        .copied()
                        .filter(|t| t.0 < n_terms)
                        .collect()
                })
                .unwrap_or_default();
            let euf_view = model.euf_model.as_ref();
            let Some(lia) = model.lia_model.as_mut() else {
                return 0;
            };
            let before = lia.values.clone();
            // Fixpoint over the three passes: `reconcile` can move an opaque
            // select's value AFTER `recover` already derived a substituted
            // var from it (measured on the A1 chain test: `H := eval(select)`
            // ran before the congruence pass pulled the solved-form read
            // value onto that select). Iterate until stable (bounded).
            for _ in 0..4 {
                let before_iter = lia.values.clone();
                crate::executor::theories::lia::recover_substituted_lia_values_protecting(
                    &self.ctx.terms,
                    vs,
                    lia,
                    protected,
                );
                crate::executor::theories::lia::recompute_composite_int_values(
                    &self.ctx.terms,
                    &candidates,
                    lia,
                );
                crate::executor::theories::lia::reconcile_lia_select_congruence(
                    &self.ctx.terms,
                    vs,
                    lia,
                    euf_view,
                );
                if lia.values == before_iter {
                    break;
                }
            }
            lia.values
                .iter()
                .filter(|&(t, v)| before.get(t) != Some(v))
                .map(|(&t, v)| (t, v.clone()))
                .collect()
        };
        // Phase 2: recover Bool substitution gates (`I -> (<= F H)`) under
        // the final Int assignment. Only genuinely-recomputable gates move;
        // vars with a live SAT-model value are unaffected (`bool_overrides`
        // sits below the SAT model in the Var lookup chain).
        let bool_updates: Vec<(TermId, bool)> = {
            let model = self.last_model.as_ref().expect("checked above");
            let lia = model.lia_model.as_ref().expect("checked above");
            crate::executor::theories::lia::recover_substituted_bool_values(
                &self.ctx.terms,
                vs,
                &lia.values,
            )
            .into_iter()
            .filter(|(t, b)| model.bool_overrides.get(t) != Some(b))
            .collect()
        };
        // Phase 3: mirror every change into the merged EUF view so the
        // printer, internal evaluators, strict oracles and the independent
        // gate all read the reconciled values.
        let n_changed = changed.len() + bool_updates.len();
        if n_changed == 0 {
            return 0;
        }
        let dbg = ay_core::misc_cli_flags().debug_read_pin;
        {
            let model = self.last_model.as_mut().expect("checked above");
            if let Some(euf) = model.euf_model.as_mut() {
                for (t, v) in &changed {
                    euf.int_values.insert(*t, v.clone());
                    euf.term_values.insert(*t, v.to_string());
                }
            }
            for (t, v) in &changed {
                if dbg {
                    eprintln!("[read-pin-repair] resync t{}={v}", t.0);
                }
                // Stale completion snapshots would shadow nothing for Int
                // vars (the LIA view wins), but keep the slot coherent for
                // terms whose evaluation falls through to it.
                if model.completed_values.contains_key(t) {
                    model.completed_values.insert(
                        *t,
                        crate::executor::model::EvalValue::Rational(
                            num_rational::BigRational::from(v.clone()),
                        ),
                    );
                }
            }
            for (t, b) in &bool_updates {
                if dbg {
                    eprintln!("[read-pin-repair] resync-bool t{}={b}", t.0);
                }
                model.bool_overrides.insert(*t, *b);
                if model.completed_values.contains_key(t) {
                    model
                        .completed_values
                        .insert(*t, crate::executor::model::EvalValue::Bool(*b));
                }
            }
        }
        if dbg {
            eprintln!("[read-pin-repair] resync changed={n_changed}");
        }
        n_changed
    }

    /// Repair the polarity of a directly asserted Boolean leaf in a candidate
    /// SAT witness before validation.
    ///
    /// Quantifier result restoration can retain a SAT assignment from an inner
    /// ground-instance solve while restoring an original assertion such as
    /// `(assert ext_eq)`.  In that case `term_to_var[ext_eq]` can point at a
    /// stale `false` bit even though the public assertion requires `true`.
    /// Pinning the leaf to its asserted polarity is model construction, not an
    /// acceptance shortcut: every strict/independent/fail-closed gate still
    /// validates the mutated witness, and any consequence made false by the pin
    /// degrades the result to UNKNOWN.
    ///
    /// Only bare Bool variables (and one leading `not`) qualify.  Opposite
    /// asserted polarities are left untouched so a contradictory Boolean
    /// skeleton cannot be hidden by choosing one side.
    pub(in crate::executor) fn repair_asserted_bool_leaf_polarities(&mut self) {
        use ay_core::term::TermData;

        if !matches!(self.last_result, Some(SolveResult::Sat)) || self.last_model.is_none() {
            return;
        }
        if let Some(model) = self.last_model.as_mut() {
            model.revoke_all_quantified_model_seals();
        }

        let mut required: ay_core::kani_compat::DetHashMap<TermId, bool> =
            ay_core::kani_compat::DetHashMap::default();
        let mut pins = Vec::new();
        for assertion in self.flatten_assertion_conjunctions() {
            let (leaf, polarity) = match self.ctx.terms.get(assertion) {
                TermData::Var(_, _)
                    if matches!(self.ctx.terms.sort(assertion), ay_core::Sort::Bool) =>
                {
                    (assertion, true)
                }
                TermData::Not(inner)
                    if matches!(self.ctx.terms.sort(*inner), ay_core::Sort::Bool)
                        && matches!(self.ctx.terms.get(*inner), TermData::Var(_, _)) =>
                {
                    (*inner, false)
                }
                _ => continue,
            };
            if required.get(&leaf).is_some_and(|old| *old != polarity) {
                return;
            }
            required.insert(leaf, polarity);
            pins.push((assertion, leaf, polarity));
        }

        let Some(model) = self.last_model.as_mut() else {
            return;
        };
        let mut changed = false;
        for (assertion, leaf, polarity) in pins {
            if let Some(&var) = model.term_to_var.get(&leaf) {
                if let Some(slot) = model.sat_model.get_mut(var as usize) {
                    if *slot != polarity {
                        *slot = polarity;
                        changed = true;
                    }
                }
            } else if model.bool_overrides.get(&leaf) != Some(&polarity) {
                model.bool_overrides.insert(leaf, polarity);
                changed = true;
            }

            // For `(assert (not b))`, also make the restored assertion's
            // Tseitin bit agree with the repaired leaf.  The semantic evaluator
            // still recomputes `(not b)` and all downstream gates remain
            // mandatory.
            if assertion != leaf {
                if let Some(&var) = model.term_to_var.get(&assertion) {
                    if let Some(slot) = model.sat_model.get_mut(var as usize) {
                        if !*slot {
                            *slot = true;
                            changed = true;
                        }
                    }
                }
            }
        }
        if changed {
            model.revoke_cegqi_uf_recompletion();
            self.cegqi_uf_recompletion_grant = None;
            crate::executor::model::eval_memo_clear();
            self.last_model_validated = false;
        }
    }

    fn repair_asserted_array_read_pins(&mut self) {
        use ay_core::term::TermData;
        if !matches!(self.last_result, Some(SolveResult::Sat)) || self.last_model.is_none() {
            if ay_core::misc_cli_flags().debug_read_pin {
                eprintln!(
                    "[read-pin-repair] bail: result={:?} model={}",
                    self.last_result,
                    self.last_model.is_some()
                );
            }
            return;
        }
        if let Some(model) = self.last_model.as_mut() {
            model.revoke_all_quantified_model_seals();
        }
        // Single-shot PER MODEL (a sentinel in the model itself): re-running
        // after intervening completion passes mixes repair rounds, but a
        // per-executor flag goes stale across the inner/outer solves of
        // rescue routes (observed on QF_AX: an inner probe consumed the shot
        // and the final model never got repaired). The marker travels with
        // the model, so a NEW model always gets exactly one repair.
        const REPAIR_MARKER: TermId = TermId(u32::MAX - 7);
        let stale_marker = {
            let Some(model) = self.last_model.as_ref() else {
                return;
            };
            if model
                .euf_model
                .as_ref()
                .is_some_and(|e| e.term_values.contains_key(&REPAIR_MARKER))
            {
                // Marker present — but the euf_model can be REUSED across
                // inner solves, carrying the marker onto a NEW model whose
                // LIA view was never repaired (measured on storecomm: euf
                // holds stale witness values 3000002/3000010 while the fresh
                // lia view has completion-default 0s; repair skips; the
                // strict arithmetic oracle reads the lia view and rejects).
                // Detect the leak: any var where both views hold values that
                // DISAGREE means the marker belongs to a previous model —
                // clear it and repair this one.
                let views_disagree = model.euf_model.as_ref().is_some_and(|euf| {
                    model.lia_model.as_ref().is_some_and(|lia| {
                        euf.int_values
                            .iter()
                            .any(|(t, ev)| lia.values.get(t).is_some_and(|lv| lv != ev))
                    })
                });
                if !views_disagree {
                    return;
                }
                true
            } else {
                false
            }
        };
        // This primitive is also called by apply_strict_model_gate for a model
        // that may already carry completed validation evidence. The marker is
        // bookkeeping only, so installing or refreshing it must not invalidate
        // semantic evidence. Each actual repair below invalidates the model at
        // its mutation point, or is counted by the common epilogue.
        if self
            .last_model
            .as_ref()
            .and_then(|model| model.euf_model.as_ref())
            .is_none()
        {
            return;
        }
        if stale_marker {
            if let Some(model) = self.last_model.as_mut() {
                if let Some(euf) = model.euf_model.as_mut() {
                    euf.term_values.remove(&REPAIR_MARKER);
                }
            }
        }
        if let Some(model) = self.last_model.as_mut() {
            if let Some(euf) = model.euf_model.as_mut() {
                euf.term_values
                    .insert(REPAIR_MARKER, "repaired".to_string());
            } else {
                return; // no EUF model: nothing the repair could fix anyway
            }
        }
        // Freeze marker for the def-index fast path: the repair rounds below
        // interleave MODEL mutations with thousands of top-level evaluate_term
        // calls (one frame each), so the frame-generation key alone re-runs
        // the O(constraints) def-index snapshot compare once per pin — the
        // dominant remaining cost on the pairwise-expanded `distinct` family.
        // Repair mutates ONLY the model (lia/euf views, sat slots), never
        // `ctx.assertions` / `last_assumptions`; that stated contract is
        // oracle-defended in debug builds (`array_def_candidates` re-compares
        // the full snapshot on every freeze-keyed hit and panics on drift).
        let _assertions_frozen = crate::executor::model::AssertionsFrozen::new();
        self.repair_cross_base_chain_equalities();
        self.repair_negated_same_base_chain();
        // #uflia-witness-complete (1a-ii): asserted range/disequality index for
        // the range-aware shift below. Built LAZILY — only when a collision is
        // actually found — because this primitive runs on every gate pass of
        // every problem and both scans are O(assertion window).
        let mut bound_index: Option<(
            ay_core::kani_compat::DetHashMap<
                TermId,
                crate::executor::model::uflia_witness::AssertedRange,
            >,
            ay_core::kani_compat::DetHashMap<TermId, Vec<TermId>>,
        )> = None;
        let wdefs = self.build_array_defs();
        let mut total_applied = 0usize;
        let mut total_shifted = 0usize;
        // Index vars already shifted once are never shifted again (loop guard).
        let mut shifted_vars: ay_core::kani_compat::DetHashSet<TermId> =
            ay_core::kani_compat::DetHashSet::default();
        // Fresh values start beyond any index magnitude seen this round.
        let mut next_fresh: i64 = 1_000_003;
        for _round in 0..4 {
            // Top-level Int disequality enforcement
            // (#qf-auflia-diseq-shift): storecomm-style store-chain indices
            // appear ONLY in stores (never in select pins), so pin-group
            // separation cannot reach them and completion defaults collide
            // them (measured: strict arithmetic oracle rejects
            // '(not (= i10 i9))' in 2ms). A model violating an asserted
            // var-var Int disequality is already doomed, so shifting one
            // side to a fresh integer can only help; every gate re-checks
            // fail-closed afterwards.
            {
                let mut diseq_shifts: Vec<(TermId, i64)> = Vec::new();
                let int_val = |exec: &Self, t: TermId| -> Option<num_bigint::BigInt> {
                    let model = exec.last_model.as_ref()?;
                    if let Some(lia) = model.lia_model.as_ref() {
                        if let Some(v) = lia.values.get(&t) {
                            return Some(v.clone());
                        }
                    }
                    if let Some(euf) = model.euf_model.as_ref() {
                        if let Some(v) = euf.int_values.get(&t) {
                            return Some(v.clone());
                        }
                    }
                    None
                };
                for assertion in self.ctx.assertions.clone() {
                    let TermData::Not(inner) = self.ctx.terms.get(assertion) else {
                        continue;
                    };
                    let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                        continue;
                    };
                    if sym.name() != "=" || args.len() != 2 {
                        continue;
                    }
                    let (x, y) = (args[0], args[1]);
                    if !matches!(self.ctx.terms.sort(x), ay_core::Sort::Int)
                        || !matches!(self.ctx.terms.sort(y), ay_core::Sort::Int)
                    {
                        continue;
                    }
                    let x_var = matches!(self.ctx.terms.get(x), TermData::Var(_, _));
                    let y_var = matches!(self.ctx.terms.get(y), TermData::Var(_, _));
                    if !x_var && !y_var {
                        continue;
                    }
                    // Absent values complete to the default (0) downstream:
                    // None counts as 0 (measured: store-chain indices appear
                    // only in stores, LIA never rows them, both default 0).
                    let zero = num_bigint::BigInt::from(0);
                    let vx = int_val(self, x).unwrap_or_else(|| zero.clone());
                    let vy = int_val(self, y).unwrap_or_else(|| zero.clone());
                    if vx != vy {
                        continue; // already satisfied
                    }
                    // Violated: shift a free var side.
                    let target = if x_var && !shifted_vars.contains(&x) {
                        x
                    } else if y_var && !shifted_vars.contains(&y) {
                        y
                    } else {
                        continue;
                    };
                    // CENSUS DIAGNOSTIC ONLY (`--model-reject-dump`; default
                    // off is byte-identical — one `var_os` probe, no I/O and no
                    // state change). This shift is the only producer of the
                    // `1_000_003+` sentinel values that later show up in strict
                    // arithmetic-oracle rejections, and the pre-shift COLLIDING
                    // value is what says whether the extracted model dropped a
                    // variable (both sides default) or merged two arithmetic
                    // points. WRITE-ONLY: no verdict path reads it.
                    if ay_core::misc_cli_flags().model_reject_dump {
                        eprintln!(
                            "[diseq-shift] {} := {} (was {}, collided with {} on assertion {})",
                            self.format_term(target),
                            next_fresh,
                            vx,
                            self.format_term(if target == x { y } else { x }),
                            self.format_term(assertion)
                                .chars()
                                .take(80)
                                .collect::<String>()
                        );
                    }
                    // #uflia-witness-complete (1a-ii): the "shifting one side
                    // to a fresh integer can only help" justification above is
                    // FALSE whenever the variable carries ASSERTED BOUNDS —
                    // the sentinel falsifies the very `(< target N)` the same
                    // formula asserts, and the strict arithmetic oracle then
                    // definitively refutes the repaired model. When bounds
                    // exist the shift is REFUSED (or, under
                    // `AY_UFLIA_WITNESS_SHIFT=inrange`, confined to the
                    // interval) and the model is left exactly as the gates
                    // would otherwise have seen it — the collision still
                    // falsifies the asserted disequality, so the candidate is
                    // rejected as before, just not via a fabricated
                    // out-of-bounds value. Env-gated: with the gate off this
                    // returns `Some(next_fresh)` and behaviour is
                    // byte-identical.
                    if bound_index.is_none() {
                        bound_index = Some(
                            if crate::executor::model::uflia_witness::uflia_witness_complete_enabled(
                            ) {
                                (self.asserted_int_ranges(), self.asserted_int_diseq_peers())
                            } else {
                                Default::default()
                            },
                        );
                    }
                    let (bound_ranges, diseq_peers) =
                        bound_index.as_ref().expect("initialized just above");
                    let Some(shift_to) = self.uflia_bounded_diseq_shift_value(
                        self.last_model.as_ref().expect("checked above"),
                        bound_ranges,
                        diseq_peers,
                        target,
                        next_fresh,
                    ) else {
                        shifted_vars.insert(target);
                        continue;
                    };
                    diseq_shifts.push((target, shift_to));
                    next_fresh += 1;
                    shifted_vars.insert(target);
                }
                if !diseq_shifts.is_empty() {
                    let model = self.last_model.as_mut().expect("checked above");
                    for (iv, fresh) in &diseq_shifts {
                        let fresh_big = num_bigint::BigInt::from(*fresh);
                        if let Some(lia) = model.lia_model.as_mut() {
                            lia.values.insert(*iv, fresh_big.clone());
                        }
                        if let Some(euf) = model.euf_model.as_mut() {
                            euf.term_values.insert(*iv, fresh.to_string());
                            euf.int_values.insert(*iv, fresh_big);
                        }
                        total_shifted += 1;
                    }
                    if ay_core::misc_cli_flags().debug_read_pin {
                        eprintln!("[read-pin-repair] diseq_shifts={}", diseq_shifts.len());
                    }
                    // Re-collect pins under the separated values.
                    continue;
                }
            }
            // Phase 1 (immutable): collect (array, idx_term, idx_atom, sel, pin_atom)
            // for every asserted read pin whose evaluation disagrees.
            let mut pins: Vec<(TermId, TermId, String, TermId, String)> = Vec::new();
            let mut pin_vars: Vec<(TermId, usize)> = Vec::new();
            {
                let model = self.last_model.as_ref().expect("checked above");
                for assertion in self.ctx.assertions.clone() {
                    let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                        continue;
                    };
                    if sym.name() != "=" || args.len() != 2 {
                        continue;
                    }
                    for &(x, sel) in &[(args[0], args[1]), (args[1], args[0])] {
                        let TermData::App(ssym, sargs) = self.ctx.terms.get(sel) else {
                            continue;
                        };
                        if ssym.name() != "select" || sargs.len() != 2 {
                            continue;
                        }
                        if !matches!(self.ctx.terms.get(x), TermData::Var(_, _)) {
                            continue;
                        }
                        let v_x = self.evaluate_term(model, x);
                        let v_s = self.evaluate_term(model, sel);
                        let (Some(x_atom), Some(s_atom)) = (
                            self.eval_value_to_model_atom(&v_x),
                            self.eval_value_to_model_atom(&v_s),
                        ) else {
                            continue;
                        };
                        // Keep AGREEING pins too: conflict detection must see
                        // every asserted read of a cell, or repairing one
                        // read silently breaks its previously-agreeing peer.
                        let _pin_agrees = x_atom == s_atom;
                        let idx_val = self.evaluate_term(model, sargs[1]);
                        let Some(idx_atom) = self.eval_value_to_model_atom(&idx_val) else {
                            continue;
                        };
                        pins.push((sargs[0], sargs[1], idx_atom, sel, x_atom));
                        pin_vars.push((x, pins.len() - 1));
                    }
                }
            }
            if pins.is_empty() {
                break;
            }
            // Group by (array, index value); detect conflicting pin values.
            let mut groups: ay_core::kani_compat::DetHashMap<
                (TermId, String),
                Vec<(TermId, TermId, String)>,
            > = ay_core::kani_compat::DetHashMap::default();
            for (arr, idx_term, idx_atom, sel, pin) in &pins {
                groups.entry((*arr, idx_atom.clone())).or_default().push((
                    *idx_term,
                    *sel,
                    pin.clone(),
                ));
            }
            // Index separation (#qf-auflia-index-separation): two asserted
            // reads pinning DIFFERENT values onto the same (array, index
            // value) cell are only reconcilable if their INDEX TERMS get
            // distinct values — the collision is a completion default, not
            // a semantic identity (z3's array model construction separates
            // such indices on demand). Shift one FREE index var per
            // conflicting group to a fresh integer and re-evaluate.
            let mut index_shifts: Vec<(TermId, i64)> = Vec::new();
            for ((_arr, _idx_atom), members) in &groups {
                let mut vals: Vec<&String> = members.iter().map(|(_, _, p)| p).collect();
                vals.sort();
                vals.dedup();
                if vals.len() < 2 {
                    continue;
                }
                // Distinct index VAR terms among the conflicting members.
                let mut idx_vars: Vec<TermId> = members
                    .iter()
                    .map(|(it, _, _)| *it)
                    .filter(|&it| {
                        matches!(self.ctx.terms.get(it), TermData::Var(_, _))
                            && !shifted_vars.contains(&it)
                    })
                    .collect();
                idx_vars.sort_unstable_by_key(|t| t.0);
                idx_vars.dedup();
                if idx_vars.len() < 2 {
                    continue; // same index term or nothing shiftable
                }
                // Shift every distinct index var beyond the first.
                for &iv in &idx_vars[1..] {
                    index_shifts.push((iv, next_fresh));
                    next_fresh += 1;
                    shifted_vars.insert(iv);
                }
            }
            if !index_shifts.is_empty() {
                let model = self.last_model.as_mut().expect("checked above");
                for (iv, fresh) in &index_shifts {
                    let fresh_big = num_bigint::BigInt::from(*fresh);
                    if let Some(lia) = model.lia_model.as_mut() {
                        lia.values.insert(*iv, fresh_big.clone());
                    }
                    if let Some(euf) = model.euf_model.as_mut() {
                        euf.term_values.insert(*iv, fresh.to_string());
                        euf.int_values.insert(*iv, fresh_big);
                    }
                    total_shifted += 1;
                }
                // Re-collect pins next round under the separated indices.
                continue;
            }
            // No shifts possible/needed: apply all non-conflicting pins.
            let mut repairs: Vec<(TermId, String, TermId, String)> = Vec::new();
            for ((arr, idx_atom), members) in groups {
                let mut vals: Vec<&String> = members.iter().map(|(_, _, p)| p).collect();
                vals.sort();
                vals.dedup();
                if vals.len() != 1 {
                    continue; // conflicted and unshiftable — leave to the gate
                }
                for (_, sel, pin) in members {
                    repairs.push((arr, idx_atom.clone(), sel, pin));
                }
            }
            if repairs.is_empty() {
                break;
            }
            // Reconstruction (#qf-auflia-array-reconstruction): route every
            // pin to its SEMANTIC target so all evaluators agree. Peel the
            // pinned read's array through top-level definitional store
            // chains: a write at the pinned index means the pin constrains
            // that WRITE's value term; otherwise the pin lands on the BASE
            // cell. Alias interps are dropped (definitions become the only
            // path, grounding out in total base interps), so the printer,
            // internal evaluators, strict oracles, and the independent gate
            // all read one truth. Conflicting demands on one shared term
            // are skipped (fail-closed: the gates re-check everything).
            let defs: Vec<(TermId, TermId)> = {
                let mut v = Vec::new();
                for assertion in self.ctx.assertions.clone() {
                    let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                        continue;
                    };
                    if sym.name() != "=" || args.len() != 2 {
                        continue;
                    }
                    for &(a, b) in &[(args[0], args[1]), (args[1], args[0])] {
                        if matches!(self.ctx.terms.get(a), TermData::Var(_, _))
                            && matches!(
                                self.ctx.terms.get(b),
                                TermData::App(s2, _) if s2.name() == "store"
                            )
                        {
                            v.push((a, b));
                        }
                    }
                }
                v
            };
            let mut base_entries: Vec<(TermId, String, String)> = Vec::new();
            let mut term_demands: Vec<(TermId, String)> = Vec::new();
            let mut alias_arrays: ay_core::kani_compat::DetHashSet<TermId> =
                ay_core::kani_compat::DetHashSet::default();
            {
                let model = self.last_model.as_ref().expect("checked above");
                for (arr, idx_atom, _sel, pin_atom) in &repairs {
                    let mut cur = *arr;
                    let mut routed = false;
                    // Follow alias definitions / syntactic stores downward.
                    for _depth in 0..16 {
                        let chain = match self.ctx.terms.get(cur) {
                            TermData::App(s2, _) if s2.name() == "store" => cur,
                            TermData::Var(_, _) => {
                                match defs.iter().find(|(a, _)| *a == cur) {
                                    Some(&(_, c)) => {
                                        alias_arrays.insert(cur);
                                        c
                                    }
                                    None => break, // true base variable
                                }
                            }
                            _ => break,
                        };
                        // Walk this store nest; check writes against the pin index.
                        let mut nest = chain;
                        let mut matched = false;
                        while let TermData::App(s2, cargs) = self.ctx.terms.get(nest) {
                            if s2.name() != "store" || cargs.len() != 3 {
                                break;
                            }
                            let wi_val = self.evaluate_term(model, cargs[1]);
                            if self.eval_value_to_model_atom(&wi_val).as_deref()
                                == Some(idx_atom.as_str())
                            {
                                if matches!(self.ctx.terms.get(cargs[2]), TermData::Var(_, _)) {
                                    term_demands.push((cargs[2], pin_atom.clone()));
                                }
                                matched = true;
                                routed = true;
                                break;
                            }
                            nest = cargs[0];
                        }
                        if matched {
                            break;
                        }
                        cur = nest; // continue peeling below the nest
                    }
                    if !routed {
                        base_entries.push((cur, idx_atom.clone(), pin_atom.clone()));
                    }
                }
            }
            // Skip conflicting demands on one shared term.
            {
                let mut seen: ay_core::kani_compat::DetHashMap<TermId, String> =
                    ay_core::kani_compat::DetHashMap::default();
                let mut bad: ay_core::kani_compat::DetHashSet<TermId> =
                    ay_core::kani_compat::DetHashSet::default();
                for (t, v) in &term_demands {
                    match seen.get(t) {
                        None => {
                            seen.insert(*t, v.clone());
                        }
                        Some(prev) if prev != v => {
                            bad.insert(*t);
                        }
                        Some(_) => {}
                    }
                }
                term_demands.retain(|(t, _)| !bad.contains(t));
            }
            let model = self.last_model.as_mut().expect("checked above");
            // Harmonize pinned vars AND write-term demands everywhere.
            let mut writes: Vec<(TermId, String)> = term_demands;
            for (x, pin_idx) in pin_vars {
                writes.push((x, pins[pin_idx].4.clone()));
            }
            for (t, atom) in writes {
                let norm = atom
                    .trim_start_matches("(- ")
                    .trim_end_matches(')')
                    .replace(' ', "");
                if let Ok(mag) = norm.parse::<num_bigint::BigInt>() {
                    let val = if atom.starts_with("(- ") { -mag } else { mag };
                    if let Some(lia) = model.lia_model.as_mut() {
                        lia.values.insert(t, val.clone());
                    }
                    if let Some(euf) = model.euf_model.as_mut() {
                        euf.term_values.insert(t, atom.clone());
                        euf.int_values.insert(t, val);
                    }
                }
            }
            // Base entries + totals; drop alias interps.
            if let Some(am) = model.array_model.as_mut() {
                for (base, idx_atom, pin_atom) in &base_entries {
                    let interp = am.array_values.entry(*base).or_default();
                    match interp.stores.iter_mut().find(|(k, _)| k == idx_atom) {
                        Some((_, v)) => *v = pin_atom.clone(),
                        None => interp.stores.push((idx_atom.clone(), pin_atom.clone())),
                    }
                    if interp.default.is_none() {
                        interp.default = Some("0".to_string());
                    }
                }
                for alias in &alias_arrays {
                    am.array_values.remove(alias);
                }
            }
            // Also refresh the SELECT terms' merged values to the pins — in
            // BOTH model views (#A1-repair-resync): the LIA view is what the
            // substituted-value recovery below evaluates opaque select leaves
            // from, so a euf-only refresh would leave the recovery reading a
            // stale pre-repair value (the exact desync the `views_disagree`
            // marker escape above exists for).
            for (_, _, sel, pin_atom) in &repairs {
                let sel_is_int = matches!(self.ctx.terms.sort(*sel), ay_core::Sort::Int);
                if let Some(euf) = model.euf_model.as_mut() {
                    euf.term_values.insert(*sel, pin_atom.clone());
                    if sel_is_int {
                        if let Ok(v) = pin_atom.parse::<num_bigint::BigInt>() {
                            euf.int_values.insert(*sel, v);
                        }
                    }
                }
                if sel_is_int {
                    if let Ok(v) = pin_atom.parse::<num_bigint::BigInt>() {
                        if let Some(lia) = model.lia_model.as_mut() {
                            lia.values.insert(*sel, v);
                        }
                    }
                }
            }
            total_applied += repairs.len();

            // #A1-repair-resync: the pin/base-entry writes above mutate Int
            // LEAF values without re-running the #A1 reconciliation passes
            // that established the substitution equalities (`E = B1 + 4P`)
            // during model extraction — leaving substituted vars stale and
            // the strict arithmetic oracle rightly rejecting an equality the
            // model itself could satisfy. Re-derive substituted/composite/
            // congruent values from the repaired leaves; if anything moved,
            // take another round so pins and base entries re-key under the
            // FINAL assignment. Fill-and-overwrite is safe: full validation
            // still gates acceptance (fail-closed, #8373 backstop).
            if self.reconcile_int_model_after_repair(&shifted_vars) > 0 {
                continue;
            }

            break;
        }
        // Witness completion for skolemized extensionality reads
        // (#qf-auflia-witness-completion): the sat-side swap_invalid family
        // asserts '(not (= (select A k) (select B k)))' where k is the
        // extensionality Skolem and A,B are store chains over one free base.
        // An all-collide completion makes the reads equal, and symbolic cell
        // comparison stays indefinite because base reads may collide. Build
        // the witness concretely: distinct index values, concrete distinct
        // base cells, find a written index W where the compositions differ,
        // and point k's own model value at W. Every step is re-validated by
        // the full gate battery afterwards (fail-closed).
        {
            use ay_core::term::TermData;
            let walk = |terms: &ay_core::TermStore, mut t: TermId| {
                let mut writes: Vec<(TermId, TermId)> = Vec::new();
                let mut hops = 0usize;
                loop {
                    hops += 1;
                    if hops > 256 {
                        break;
                    }
                    match terms.get(t) {
                        TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                            writes.push((args[1], args[2]));
                            t = args[0];
                        }
                        // #qfax-sf-defchase: unfold sf-flattened chains.
                        TermData::Var(_, _) => match wdefs.get(&t) {
                            Some(&d) => t = d,
                            None => break,
                        },
                        _ => break,
                    }
                }
                (writes, t)
            };
            // Targets: negated equalities between two selects sharing an
            // index term, over same-base chains.
            let mut targets: Vec<(TermId, TermId, TermId, Option<TermId>)> = Vec::new();
            for assertion in self.ctx.assertions.clone() {
                let TermData::Not(inner) = self.ctx.terms.get(assertion) else {
                    continue;
                };
                let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                    continue;
                };
                if sym.name() != "=" || args.len() != 2 {
                    continue;
                }
                let (TermData::App(s1, a1), TermData::App(s2, a2)) =
                    (self.ctx.terms.get(args[0]), self.ctx.terms.get(args[1]))
                else {
                    continue;
                };
                if s1.name() != "select" || s2.name() != "select" || a1[1] != a2[1] {
                    continue;
                }
                targets.push((*inner, a1[0], a2[0], Some(a1[1])));
            }
            // QF_AX '_np_' shape: a direct negated equality between two
            // same-base chains (no skolem read). Steps 1-3 suffice — with
            // distinct indices and concrete distinct base cells the
            // normalized/symbolic comparators return a definite verdict,
            // which IS the witness the guard accepts.
            for assertion in self.ctx.assertions.clone() {
                let TermData::Not(inner) = self.ctx.terms.get(assertion) else {
                    continue;
                };
                let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                    continue;
                };
                if sym.name() == "="
                    && args.len() == 2
                    && matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Array(_))
                {
                    targets.push((*inner, args[0], args[1], None));
                }
            }
            let mut fresh_idx: i64 = 3_000_001;
            let mut fresh_val: i64 = 5_000_001;
            if ay_core::misc_cli_flags().debug_read_pin {
                eprintln!("[witness-dbg] targets={}", targets.len());
            }
            for (eq_term, chain_a, chain_b, k_term) in targets {
                // Skip when the model already witnesses the difference —
                // EXCEPT for the assertion the last validation cycle
                // rejected (#qfax-rejected-target): there the evaluator's
                // verdict is exactly what the oracle already refuted.
                // (History: removing the skip clobbered good witnesses; a
                // resolver-based skip regressed storecomm throughput 11
                // files; this targeted bypass costs nothing on happy paths.)
                let force = self.last_rejected_array_assertion.is_some_and(|r| {
                    r == eq_term
                        || matches!(
                            self.ctx.terms.get(r),
                            TermData::Not(i) if *i == eq_term
                        )
                });
                if ay_core::misc_cli_flags().debug_read_pin {
                    eprintln!(
                        "[witness-dbg] target eq={} force={} stored={:?}",
                        eq_term.0,
                        force,
                        self.last_rejected_array_assertion.map(|t| t.0)
                    );
                }
                if !force {
                    if let Some(model) = self.last_model.as_ref() {
                        if matches!(
                            self.evaluate_term(model, eq_term),
                            crate::executor::model::EvalValue::Bool(false)
                        ) {
                            continue;
                        }
                    }
                }
                let (wa, base_a) = walk(&self.ctx.terms, chain_a);
                let (wb, base_b) = walk(&self.ctx.terms, chain_b);
                if base_a != base_b || (wa.is_empty() && wb.is_empty()) {
                    continue;
                }
                let base = base_a;
                // (1) Distinct values for the chains' index VARIABLES —
                // with a bounded retry loop over targeted COLLISIONS: some
                // invalid variants' compositions differ ONLY when a specific
                // index pair collides (the missing-guard shape), the dual of
                // the distinct completion.
                let mut idx_vars: Vec<TermId> = wa
                    .iter()
                    .chain(wb.iter())
                    .map(|&(i, _)| i)
                    .filter(|&i| matches!(self.ctx.terms.get(i), TermData::Var(_, _)))
                    .collect();
                idx_vars.sort_unstable_by_key(|t| t.0);
                idx_vars.dedup();
                let mut pairs: Vec<(TermId, TermId)> = Vec::new();
                for (ai, &x) in idx_vars.iter().enumerate() {
                    for &y in idx_vars.iter().skip(ai + 1) {
                        pairs.push((x, y));
                    }
                }
                let max_attempts = 1 + pairs.len().min(20);
                // The bounded search mutates a trial assignment in place. If
                // no separating cell exists, the attempt establishes nothing
                // and must leave the predecessor model byte-for-byte intact.
                let trial_predecessor = self.last_model.clone();
                let mut witness: Option<String> = None;
                for attempt in 0..max_attempts {
                    // Assign fresh distinct values to every index var.
                    if let Some(model) = self.last_model.as_mut() {
                        for &iv in &idx_vars {
                            if matches!(self.ctx.terms.sort(iv), ay_core::Sort::Int) {
                                let v = num_bigint::BigInt::from(fresh_idx);
                                fresh_idx += 1;
                                if let Some(lia) = model.lia_model.as_mut() {
                                    lia.values.insert(iv, v.clone());
                                }
                                if let Some(euf) = model.euf_model.as_mut() {
                                    euf.term_values.insert(iv, v.to_string());
                                    euf.int_values.insert(iv, v);
                                }
                            } else {
                                let atom = format!("@ay!wit!idx!{fresh_idx}");
                                fresh_idx += 1;
                                if let Some(euf) = model.euf_model.as_mut() {
                                    euf.term_values.insert(iv, atom);
                                }
                            }
                        }
                        // Attempt > 0: collide one pair (second := first).
                        if attempt > 0 {
                            let (x, y) = pairs[attempt - 1];
                            let xv_str = model
                                .euf_model
                                .as_ref()
                                .and_then(|e| e.term_values.get(&x).cloned());
                            if let Some(xs) = xv_str {
                                if let Some(euf) = model.euf_model.as_mut() {
                                    euf.term_values.insert(y, xs.clone());
                                }
                                if matches!(self.ctx.terms.sort(y), ay_core::Sort::Int) {
                                    if let Ok(iv) = xs.parse::<num_bigint::BigInt>() {
                                        if let Some(lia) = model.lia_model.as_mut() {
                                            lia.values.insert(y, iv.clone());
                                        }
                                        if let Some(euf) = model.euf_model.as_mut() {
                                            euf.int_values.insert(y, iv);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // (2) Concrete DISTINCT base cells at every written index.
                    let mut written_atoms: Vec<String> = Vec::new();
                    {
                        let model = self.last_model.as_ref().expect("model checked");
                        for &(i, _) in wa.iter().chain(wb.iter()) {
                            let iv = self.evaluate_term(model, i);
                            if let Some(atom) = self.eval_value_to_model_atom(&iv) {
                                if !written_atoms.contains(&atom) {
                                    written_atoms.push(atom);
                                }
                            }
                        }
                    }
                    if let Some(model) = self.last_model.as_mut() {
                        if let Some(am) = model.array_model.as_mut() {
                            let interp = am.array_values.entry(base).or_default();
                            if interp.default.is_none() {
                                interp.default = Some("0".to_string());
                            }
                            let elem_is_int = matches!(
                                self.ctx.terms.sort(base),
                                ay_core::Sort::Array(a) if matches!(a.element_sort, ay_core::Sort::Int)
                            );
                            for atom in &written_atoms {
                                if !interp.stores.iter().any(|(k, _)| k == atom) {
                                    let val = if elem_is_int {
                                        fresh_val.to_string()
                                    } else {
                                        format!("@ay!wit!val!{fresh_val}")
                                    };
                                    interp.stores.push((atom.clone(), val));
                                    fresh_val += 1;
                                }
                            }
                        }
                    }
                    // (3) Effective cell per chain at each written index.
                    let interp_lookup = |exec: &Self, at: &str| -> Option<String> {
                        let model = exec.last_model.as_ref()?;
                        let am = model.array_model.as_ref()?;
                        let interp = am.array_values.get(&base)?;
                        interp
                            .stores
                            .iter()
                            .find(|(k, _)| k == at)
                            .map(|(_, v)| v.clone())
                            .or_else(|| interp.default.clone())
                    };
                    let cell =
                        |exec: &Self, writes: &[(TermId, TermId)], at: &str| -> Option<String> {
                            let lookup = |at2: &str| -> Option<String> { interp_lookup(exec, at2) };
                            exec.witness_cell_rec(&wdefs, base, &lookup, writes, at, 0)
                        };
                    // (4) A written index where the compositions differ.
                    for atom in &written_atoms {
                        let ca = cell(self, &wa, atom);
                        let cb = cell(self, &wb, atom);
                        if ay_core::misc_cli_flags().debug_read_pin {
                            eprintln!("[witness-dbg]   cell@{atom}: a={ca:?} b={cb:?}");
                        }
                        if let (Some(x), Some(y)) = (ca, cb) {
                            if x != y {
                                witness = Some(atom.clone());
                                break;
                            }
                        }
                    }
                    if witness.is_some() {
                        break;
                    }
                    if ay_core::misc_cli_flags().debug_read_pin && attempt == 0 {
                        eprintln!(
                            "[witness-dbg] eq={} idx_vars={} written={} no-diff-yet",
                            eq_term.0,
                            idx_vars.len(),
                            written_atoms.len()
                        );
                    }
                }
                let Some(w_atom) = witness else {
                    self.last_model = trial_predecessor;
                    crate::executor::model::eval_memo_clear();
                    continue;
                };
                // Drop STALE derived-chain interps (#qfax-sf-stale-chain-interp).
                // The install above re-keys the BASE interpretation and the
                // index valuation, but the extraction-era entries for the
                // DERIVED chain arrays (sf-named vars like a_318..a_337 and
                // anonymous store terms) still describe the REJECTED
                // pre-repair candidate — on the storecomm sf shape both
                // chains carried one identical snapshot interp, and
                // `normalize_array_to_stores` PREFERS a model entry over the
                // definitional chase, so the strict arrays oracle kept
                // "refuting" the repaired diseq from the stale snapshots
                // (permanent fail-close of 2 genuine sats). Same discipline
                // as the cross-base pass's stale-alias drop: every consumer
                // recomputes the chains from the base + definitions. Sound:
                // removing entries only makes evaluation MORE partial
                // (fail-closed), and the full gate battery still decides
                // acceptance of the final model.
                {
                    let mut stale: Vec<TermId> = Vec::new();
                    for &chain in &[chain_a, chain_b] {
                        let mut t = chain;
                        let mut hops = 0usize;
                        while t != base && hops < 256 {
                            hops += 1;
                            stale.push(t);
                            match self.ctx.terms.get(t) {
                                TermData::App(sym, args)
                                    if sym.name() == "store" && args.len() == 3 =>
                                {
                                    t = args[0];
                                }
                                TermData::Var(_, _) => match wdefs.get(&t) {
                                    Some(&d) => t = d,
                                    None => break,
                                },
                                _ => break,
                            }
                        }
                    }
                    if let Some(model) = self.last_model.as_mut() {
                        if let Some(am) = model.array_model.as_mut() {
                            for t in stale {
                                am.array_values.remove(&t);
                            }
                        }
                    }
                }
                // (5) Point k's own model value at the witness index (skolem
                //     targets only; direct chain equalities need no pointer —
                //     the comparators now see the concrete difference). The
                //     application's value is authoritative (#qf-auflia-sk).
                let Some(k_term) = k_term else {
                    total_shifted += 1;
                    continue;
                };
                let norm = w_atom
                    .trim_start_matches("(- ")
                    .trim_end_matches(')')
                    .replace(' ', "");
                if let Ok(mag) = norm.parse::<num_bigint::BigInt>() {
                    let wv = if w_atom.starts_with("(- ") { -mag } else { mag };
                    if let Some(model) = self.last_model.as_mut() {
                        if let Some(lia) = model.lia_model.as_mut() {
                            lia.values.insert(k_term, wv.clone());
                        }
                        if let Some(euf) = model.euf_model.as_mut() {
                            euf.term_values.insert(k_term, w_atom.clone());
                            euf.int_values.insert(k_term, wv);
                        }
                    }
                    total_shifted += 1;
                } else if let Some(model) = self.last_model.as_mut() {
                    // Uninterpreted witness index: element atom value.
                    if let Some(euf) = model.euf_model.as_mut() {
                        euf.term_values.insert(k_term, w_atom.clone());
                    }
                    total_shifted += 1;
                }
            }
        }

        // Alias reconciliation (#qfax-alias-reconcile): every asserted
        // definition (= v (select arr i)) must HOLD under the possibly
        // repaired/completed array interps — the gates re-check them, and a
        // stale alias value falsifies an otherwise-correct model (measured:
        // '(= e_152 (select a1 i3))' rejecting swap_invalid sf after witness
        // completion). Resolve each alias through the FINAL interps (chasing
        // defs) and update its value; gates re-validate everything after.
        if total_applied > 0 || total_shifted > 0 {
            let mut updates: Vec<(TermId, String)> = Vec::new();
            if let Some((model, am)) = self
                .last_model
                .as_ref()
                .and_then(|model| model.array_model.as_ref().map(|arrays| (model, arrays)))
            {
                for (&v, &d) in wdefs.iter() {
                    let TermData::App(ds, da) = self.ctx.terms.get(d) else {
                        continue;
                    };
                    if ds.name() != "select" || da.len() != 2 {
                        continue;
                    }
                    // Chase the select's array to a base with an interp.
                    let mut arr = da[0];
                    let mut hops = 0usize;
                    let mut writes: Vec<(TermId, TermId)> = Vec::new();
                    loop {
                        hops += 1;
                        if hops > 256 {
                            break;
                        }
                        match self.ctx.terms.get(arr) {
                            TermData::App(s2, a2) if s2.name() == "store" && a2.len() == 3 => {
                                writes.push((a2[1], a2[2]));
                                arr = a2[0];
                            }
                            TermData::Var(_, _) if !am.array_values.contains_key(&arr) => {
                                match wdefs.get(&arr) {
                                    Some(&dd) => arr = dd,
                                    None => break,
                                }
                            }
                            _ => break,
                        }
                    }
                    let Some(interp) = am.array_values.get(&arr) else {
                        continue;
                    };
                    let Some(at) = self.eval_value_to_model_atom(&self.evaluate_term(model, da[1]))
                    else {
                        continue;
                    };
                    // Effective cell: innermost-out write match, else interp.
                    let mut val: Option<String> = None;
                    for &(wi, wv) in &writes {
                        let Some(wa) =
                            self.eval_value_to_model_atom(&self.evaluate_term(model, wi))
                        else {
                            continue;
                        };
                        if wa == at {
                            val = self.eval_value_to_model_atom(&self.evaluate_term(model, wv));
                            break;
                        }
                    }
                    let val = val.or_else(|| {
                        interp
                            .stores
                            .iter()
                            .find(|(k, _)| *k == at)
                            .map(|(_, x)| x.clone())
                            .or_else(|| interp.default.clone())
                    });
                    if let Some(val) = val {
                        updates.push((v, val));
                    }
                }
            }
            if !updates.is_empty() {
                if let Some(model) = self.last_model.as_mut() {
                    if let Some(euf) = model.euf_model.as_mut() {
                        for (v, val) in updates {
                            euf.term_values.insert(v, val);
                        }
                    }
                }
            }
        }

        // #A1-repair-resync, final pass: a model can arrive here ALREADY
        // desynced (stale substituted vars / incongruent root reads from the
        // extraction+completion pipeline) with nothing for the pin loop to
        // apply — measured on the A1 multiple-gates test, where the strict
        // arithmetic oracle rejected `(= x (+ base (* 8 i)))` although no pin
        // or shift ever ran. The reconciliation is internally guarded to
        // doomed models only (some assertion concretely false) and restores
        // itself on failed candidate trials, so this is a no-op on every
        // healthy model.
        let resynced = self.reconcile_int_model_after_repair(&shifted_vars);
        if total_applied > 0 || total_shifted > 0 || resynced > 0 {
            self.last_model_validated = false;
            self.revoke_cegqi_uf_recompletion_authority();
        }
        if ay_core::misc_cli_flags().debug_read_pin
            && (total_applied > 0 || total_shifted > 0 || resynced > 0)
        {
            eprintln!(
                "[read-pin-repair] applied={total_applied} index_shifts={total_shifted} \
                 final_resync={resynced}"
            );
        }
    }

    /// Sound cross-conjunct refutation: detect a pair of asserted conjuncts that
    /// reduce — under the current SAT model, after dropping every disjunct that
    /// evaluates to a concrete `Bool(false)` — to two UNIT clauses over the same
    /// boolean atom with OPPOSITE polarity (`atom` and `(not atom)`). Such a pair
    /// is unsatisfiable regardless of the atom's (model-undetermined) value, so
    /// the SAT model is unsound and must be degraded to Unknown.
    ///
    /// This is deliberately conservative: it only concludes a contradiction when
    /// each side simplifies to a SINGLE residual literal, so it can never reject
    /// a genuinely satisfiable model. Returns `Some((conjunct_index, atom_term))`
    /// on a definitive contradiction, else `None`.
    fn unit_clause_contradiction(
        &self,
        model: &crate::executor::model::Model,
        flat: &[TermId],
    ) -> Option<(usize, TermId)> {
        use crate::executor::model::EvalValue;
        use ay_core::kani_compat::DetHashMap as HashMap;
        // atom term -> (required polarity, conjunct index that forced it).
        let mut forced: HashMap<TermId, (bool, usize)> = HashMap::default();
        for (i, &conjunct) in flat.iter().enumerate() {
            // Only conjuncts we cannot otherwise decide are interesting.
            if !matches!(self.evaluate_term(model, conjunct), EvalValue::Unknown) {
                continue;
            }
            let Some((atom, polarity)) = self.reduce_to_unit_literal(model, conjunct) else {
                continue;
            };
            if let Some(&(prev_pol, _)) = forced.get(&atom) {
                if prev_pol != polarity {
                    return Some((i, atom));
                }
            } else {
                forced.insert(atom, (polarity, i));
            }
        }
        None
    }

    /// Self-check only: detect a SAT model that assigns a finite enum datatype
    /// sort MORE distinct inhabitants than it has constructors (a phantom
    /// infinite-domain model). The EUF model records, per uninterpreted/enum
    /// sort, the distinct element representatives it materialized; if that count
    /// exceeds the sort's constructor count `k`, the model violates the sort's
    /// exact finite cardinality and is unsound. Returns `(sort, distinct_used, k)`
    /// on violation. Degrade-only + `--self-check`-gated, so it can never turn a
    /// genuine SAT into a wrong answer.
    fn self_check_enum_cardinality_violation(&self) -> Option<(String, usize, usize)> {
        let euf = self.last_model.as_ref()?.euf_model.as_ref()?;
        for (sort_name, elements) in euf.sort_elements.iter() {
            if let Some(k) = self
                .enum_datatype_constructor_count(&ay_core::Sort::Uninterpreted(sort_name.clone()))
            {
                if elements.len() > k {
                    return Some((sort_name.clone(), elements.len(), k));
                }
            }
        }
        None
    }

    /// Reduce an asserted (top-level) Boolean conjunct to a single residual
    /// literal `(atom, polarity)` under `model`, dropping every `or`-disjunct
    /// that evaluates to a concrete `Bool(false)`. Returns `None` unless EXACTLY
    /// one residual literal remains and that literal is a Boolean atom (an
    /// `App`/`Var`, optionally under a single `not`) which itself evaluates to
    /// `Unknown` (i.e. the model genuinely does not pin it).
    ///
    /// `polarity == true` means the conjunct requires `atom` to be true;
    /// `false` means it requires `atom` to be false.
    fn reduce_to_unit_literal(
        &self,
        model: &crate::executor::model::Model,
        conjunct: TermId,
    ) -> Option<(TermId, bool)> {
        use crate::executor::model::EvalValue;
        use ay_core::term::TermData;
        use ay_core::Sort;
        // Collect the disjuncts of an `or` (or the singleton term itself).
        let disjuncts: Vec<TermId> = match self.ctx.terms.get(conjunct) {
            TermData::App(sym, args) if sym.name() == "or" => args.clone(),
            _ => vec![conjunct],
        };
        let mut residual: Option<TermId> = None;
        for d in disjuncts {
            match self.evaluate_term(model, d) {
                // A concretely-false disjunct is dropped — BUT the raw
                // `evaluate_term` is UNRELIABLE for a datatype (dis)equality (it
                // reads decoupled EUF element identity the eager DT route does
                // not maintain), so dropping a spuriously-false datatype disjunct
                // would fabricate a unit-clause contradiction. Only drop a
                // datatype-related disjunct when the datatype+Boolean AXIOMS
                // CONFIRM it false; otherwise keep it as an undecided residual
                // (sound — never fabricates a contradiction). (#g4-dt-consistency)
                EvalValue::Bool(false) => {
                    if self.contains_datatype_term(d)
                        && !matches!(dt_axiom_bool(self, d, 4000), Some(false))
                    {
                        if residual.is_some() {
                            return None;
                        }
                        residual = Some(d);
                    }
                }
                // A concretely-true disjunct satisfies the whole clause: it is
                // NOT a unit constraint, so this conjunct forces nothing.
                EvalValue::Bool(true) => return None,
                // An undecided disjunct is a residual literal. More than one
                // residual => not a unit clause, bail out.
                _ => {
                    if residual.is_some() {
                        return None;
                    }
                    residual = Some(d);
                }
            }
        }
        let lit = residual?;
        // Strip a single negation to recover the underlying atom + polarity.
        let (atom, polarity) = match self.ctx.terms.get(lit) {
            TermData::Not(inner) => (*inner, false),
            _ => (lit, true),
        };
        // The atom must be a genuinely-undetermined Boolean atom. Requiring it to
        // evaluate to Unknown (not a concrete Bool) guarantees we only compare
        // truly model-free atoms across conjuncts, so two opposite-polarity unit
        // clauses over the SAME atom are a real contradiction.
        if !matches!(self.ctx.terms.sort(atom), Sort::Bool) {
            return None;
        }
        if !matches!(self.evaluate_term(model, atom), EvalValue::Unknown) {
            return None;
        }
        Some((atom, polarity))
    }

    /// Whether a narrowly identified strict-oracle *coverage* gap may defer to
    /// stronger, independently checked SAT authority.
    ///
    /// Exact oracle spellings are intentional. `datatype` may enter this lane
    /// only when the current candidate has a nonempty W6 datatype-array
    /// inventory that reauthenticates from stamps, carriers, exact field values,
    /// and the current authored term census. Raw `dt_ground` rows are never
    /// authority, so scalar-only construction and stale/tampered W6 evidence
    /// remain fail-closed. The separate model view must then compositionally
    /// evaluate every exact authored assertion to `Bool(true)` with no residual,
    /// tautology, unsupported-atom, or skipped-assertion escape. Every other
    /// oracle and every `ModelViolates` / `CannotConfirm` result remains
    /// fail-closed.
    fn strict_coverage_gap_has_full_independent_authority(&self, oracle: &str) -> bool {
        let reauthenticated_w6 = (oracle == "datatype")
            .then(|| {
                self.last_model
                    .as_ref()
                    .and_then(|model| self.authenticated_datatype_array_field_classes(model))
            })
            .flatten();
        let in_scope = oracle == "arrays-read-conflict-uneval"
            || reauthenticated_w6
                .as_ref()
                .is_some_and(|classes| !classes.is_empty());
        if !in_scope {
            return false;
        }
        let verdict = self.confirm_sat_with_fully_evaluated_independent_gate();
        matches!(verdict, ay_model_check::GateVerdict::ConfirmedSat)
    }

    /// Run the strict oracle and apply every scoped independent-authority
    /// exception in one place, so all SAT-validation funnels have identical
    /// fail-closed policy.
    fn verify_model_strict_with_scoped_authority(&self) -> Option<(usize, &'static str, TermId)> {
        match self.verify_model_strict() {
            Some((_, oracle, _))
                if self.strict_coverage_gap_has_full_independent_authority(oracle) =>
            {
                None
            }
            Some((_, oracle, _))
                if oracle == "datatype-field"
                    && self.problem_has_datatype_carrying_array()
                    && matches!(
                        self.confirm_sat_with_independent_gate(),
                        ay_model_check::GateVerdict::ConfirmedSat
                    ) =>
            {
                None
            }
            other => other,
        }
    }

    /// Run the global strict definitive-false gate on the current SAT result and
    /// degrade it to `Unknown` if any [`DefinitiveEval`] oracle proves the
    /// produced model makes an asserted leaf concretely false.
    ///
    /// Idempotent and safe to call on any result: it no-ops unless `result` is
    /// `Sat`, and `verify_model_strict` only fires on a definitive violation
    /// (never on a genuine SAT model). This must run even when the model was
    /// already validated in-loop (`last_model_validated == true`), because that
    /// in-loop validation can accept a model via theory SAT-fallback that the
    /// strict oracles then prove unsound (e.g. the ite-defines-a-UF-app
    /// false-SAT, P1) — soundness over completeness, regardless of path.
    pub(in crate::executor) fn apply_strict_model_gate(
        &mut self,
        result: SolveResult,
    ) -> SolveResult {
        if result != SolveResult::Sat {
            return result;
        }
        self.repair_asserted_bool_leaf_polarities();
        self.complete_opaque_array_defaults_gate_verified();
        // #uflia-witness-complete (1a-i): fill absent / out-of-range
        // asserted-bound Int leaves BEFORE the read-pin repair measures any
        // collision, so the range-blind diseq shift is never even reached for
        // them. Env-gated; default off is a no-op returning 0.
        self.uflia_fill_bounded_int_leaves();
        self.repair_asserted_array_read_pins();
        // #uflia-witness-complete (1b), mirroring the finalize site: an
        // IN-LOOP-validated model reaches the funnel through THIS entry, so
        // the free-UF-point completion must run here too or the class is never
        // seen (measured: the whole mathsat Hash 1b sub-class arrives with
        // `last_model_validated == true`). The completion clears that evidence
        // itself, so `emit_sat_verdict` re-runs the FULL unchanged validation
        // pipeline over the completed witness — no gate is bypassed and no
        // certificate can be minted from stale evidence. Env-gated; default
        // off is a no-op.
        self.uflia_complete_free_uf_chain_witness();
        // Central strict-coverage policy (also on the finalize entries): the
        // existing `datatype-field` array gap and the total-construction
        // `datatype` gap may defer only to their scoped independent authority.
        // The latter requires the fully-evaluated gate; see the centralized
        // helper for the exact fail-closed contract.
        let mut strict = self.verify_model_strict_with_scoped_authority();
        if let Some((_, oracle, assertion)) = strict {
            if oracle.starts_with("arrays") {
                self.derive_qfax_refinement_clause(assertion);
                self.last_rejected_array_assertion = Some(assertion);
                // #qfax-rejected-target retry: this cycle's repair ran before
                // the rejection named its assertion. Clear the per-model
                // marker, re-run repair once (the bypass now forces completion
                // for the named target), and re-verify. Single retry, arrays
                // only.
                //
                // This entry is used for a model that was validated in-loop.
                // Repair MUTATES that witness, so its validation evidence is
                // stale even if the strict oracle becomes silent. Clear the
                // evidence before mutation; emit_sat_verdict will run the full
                // pipeline again before any certificate can be minted.
                if !self.qfax_retry_done {
                    self.last_model_validated = false;
                    self.qfax_retry_done = true;
                    if let Some(model) = self.last_model.as_mut() {
                        if let Some(euf) = model.euf_model.as_mut() {
                            euf.term_values.remove(&TermId(u32::MAX - 7));
                        }
                    }
                    self.repair_asserted_array_read_pins();
                    strict = self.verify_model_strict_with_scoped_authority();
                    self.qfax_retry_done = false;
                    if strict.is_none() {
                        self.last_rejected_array_assertion = None;
                    }
                }
            }
        }
        if let Some((idx, oracle, assertion)) = strict {
            self.note_exact_ite_uf_definition_model_rejection(oracle);
            self.last_statistics.model_validation_failures += 1;
            self.last_statistics
                .set_int("model_validation.strict.assertion_index", idx as u64);
            self.last_statistics
                .set_string("model_validation.strict.oracle", oracle);
            self.last_statistics
                .set_string("model_validation.strict.term", self.format_term(assertion));
            // LOUD, always-visible alarm + falsifying assignment (stderr +
            // trace): the strict definitive-false oracle caught a model that
            // falsifies an assertion. Emitted while `last_model` is still live.
            let term = self.format_term(assertion);
            // CENSUS DIAGNOSTIC ONLY (`--model-reject-dump`): name the
            // rejecting SITE and oracle. Three different code paths print the
            // same soundness banner; a census that cannot tell them apart
            // cannot attribute a rejection. WRITE-ONLY.
            if ay_core::misc_cli_flags().model_reject_dump {
                eprintln!("[reject-site] apply_strict_model_gate oracle={oracle} idx={idx}");
            }
            self.report_caught_invalid_model(assertion, &term);
            tracing::warn!(
                assertion_index = idx,
                oracle,
                "apply_strict_model_gate: definitive violation — degrading SAT to Unknown"
            );
            // #abv-subst-model-retry: a strict-oracle refutation of a model
            // built by the substitution-carrying eager BV lane arms the single
            // preprocessing-free re-solve in `check_sat_guarded` (same defect
            // class as the in-loop BV validator / independent-gate hooks).
            if self.bv_subst_lane {
                self.bv_subst_model_rejected = true;
            }
            self.last_model = None;
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.last_result = Some(SolveResult::Unknown);
            self.record_model_validation_unknown_diagnostic(format!(
                "strict model-validation oracle {oracle} rejected assertion {idx}"
            ));
            return SolveResult::Unknown;
        }
        result
    }

    /// Read-only strict check for an affine quantified-certificate model.
    ///
    /// The ordinary strict entry may repair its candidate before deciding.
    /// Certificate publication instead runs only this raw read-only oracle on
    /// the producer's exact theorem model. A model that needs repair therefore
    /// fails closed rather than silently changing the witness after its
    /// quantified theorem was proved.
    pub(in crate::executor) fn exact_certificate_model_passes_strict_read_only(&self) -> bool {
        self.verify_model_strict().is_none()
    }

    /// Find a top-level asserted array disequality — `(not (= A B))` over
    /// Array-sorted operands, or an Array-sorted `(distinct ...)` pair — for
    /// which the current model provides NO definitive difference witness:
    /// `compare_array_models_normalized` cannot separate them AND
    /// `compare_same_base_store_chains` cannot separate them. See
    /// `apply_strict_model_gate` for why this fails closed.
    ///
    /// SCOPE: only arrays over an UNINTERPRETED index sort (the QF_AX
    /// `(Array Index Element)` shape, where the swap/storeinv false-SAT
    /// epidemic lives). Int/BV/Bool-indexed arrays are excluded: their models
    /// carry arithmetic/bit-level valuations whose reconstruction gaps (e.g.
    /// an unconstrained index variable evaluating Unknown) routinely leave a
    /// GENUINELY-witnessable disequality formally "unwitnessed" — degrading
    /// those would trade real QF_ALIA/QF_AUFLIA sat throughput for no
    /// soundness gain (their validation has concrete evaluation paths).
    fn find_unwitnessed_array_disequality(&self) -> Option<(usize, TermId)> {
        use ay_core::term::TermData;
        use ay_core::Sort;
        // The fail-closed guard is UNCONDITIONAL: the former
        // `AY_UNWITNESSED_DISEQ_GUARD=0` research kill switch is removed —
        // no environment variable may turn off a soundness guard.
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            _ => return None,
        };
        let uninterpreted_indexed = |t: TermId| -> bool {
            matches!(
                self.ctx.terms.sort(t),
                Sort::Array(a) if matches!(a.index_sort, Sort::Uninterpreted(_))
            )
        };
        let flat = self.flatten_assertion_conjunctions();
        for (i, &assertion) in flat.iter().enumerate() {
            // Collect the array pairs this assertion claims distinct.
            let mut pairs: Vec<(TermId, TermId)> = Vec::new();
            match self.ctx.terms.get(assertion) {
                TermData::Not(inner) => {
                    if let TermData::App(sym, args) = self.ctx.terms.get(*inner) {
                        if sym.name() == "=" && args.len() == 2 && uninterpreted_indexed(args[0]) {
                            pairs.push((args[0], args[1]));
                        }
                    }
                }
                TermData::App(sym, args)
                    if sym.name() == "distinct"
                        && args.len() >= 2
                        && uninterpreted_indexed(args[0]) =>
                {
                    for x in 0..args.len() {
                        for y in (x + 1)..args.len() {
                            pairs.push((args[x], args[y]));
                        }
                    }
                }
                _ => {}
            }
            for (a, b) in pairs {
                let normalized = self.compare_array_models_normalized(model, a, b);
                if ay_core::misc_cli_flags().debug_unwitnessed {
                    let sb = self.compare_same_base_store_chains(model, a, b);
                    let ap =
                        super::definitive_eval::ArrayOracle::concrete_select_pairs(self, model, a);
                    let bp =
                        super::definitive_eval::ArrayOracle::concrete_select_pairs(self, model, b);
                    let am = model
                        .array_model
                        .as_ref()
                        .map(|m| m.array_values.contains_key(&a));
                    let bm = model
                        .array_model
                        .as_ref()
                        .map(|m| m.array_values.contains_key(&b));
                    eprintln!(
                        "[unwitnessed-dbg] a={a:?} b={b:?} normalized={normalized:?} same_base={sb:?} a_pairs={} b_pairs={} a_interp={am:?} b_interp={bm:?}",
                        ap.len(),
                        bp.len()
                    );
                }
                if normalized == Some(false) {
                    continue; // witnessed: reconstructed interpretations differ
                }
                let same_base = self.compare_same_base_store_chains(model, a, b);
                if same_base == Some(false) {
                    continue; // witnessed: same-base chains differ at a written index
                }
                // Select-level witness: the formula itself reads both arrays,
                // and at some model-equal index the two reads carry distinct
                // concrete model values (the storecomm shape: element aliases
                // `e_k = select(a, i_k)` with asserted element disequalities).
                // That IS an extensional difference witness.
                if self.select_pairs_witness_difference(model, a, b) {
                    continue;
                }
                // Only judge models that actually SAY something about these
                // arrays. Nested probe executors (alternation/overapprox
                // re-entries) validate PARTIAL models with no array
                // information at all — degrading those turns sound inner
                // probes into unknowns (observed on storecomm_invalid: the
                // main context is witnessed, a fresh-term-store probe is
                // not). A model with zero array evidence falls through to
                // the enforced independent model-check gate, which proves
                // violations on the completed model instead.
                let has_info = |t: TermId| -> bool {
                    model
                        .array_model
                        .as_ref()
                        .is_some_and(|m| m.array_values.contains_key(&t))
                };
                if !has_info(a) && !has_info(b) {
                    continue;
                }
                // `Some(true)` (provably EQUAL) is a definitive violation the
                // ArrayOracle in verify_model_strict already rejects before
                // this runs; treat any remainder here as unwitnessed.
                return Some((i, assertion));
            }
        }
        None
    }

    /// True when the model pins select values on BOTH arrays at a shared
    /// concrete index with DIFFERING element values — a sound extensional
    /// difference witness (used by `find_unwitnessed_array_disequality`).
    /// Sound: both values are model-forced reads of the two arrays at the
    /// same index, so the arrays differ under this model at that index.
    fn select_pairs_witness_difference(
        &self,
        model: &crate::executor::model::Model,
        a: TermId,
        b: TermId,
    ) -> bool {
        use super::definitive_eval::ArrayOracle;
        use crate::executor::model::EvalValue;
        let a_pairs = ArrayOracle::concrete_select_pairs(self, model, a);
        if a_pairs.is_empty() {
            return false;
        }
        let b_pairs = ArrayOracle::concrete_select_pairs(self, model, b);
        for (ai, av) in &a_pairs {
            if matches!(ai, EvalValue::Unknown) || matches!(av, EvalValue::Unknown) {
                continue;
            }
            for (bi, bv) in &b_pairs {
                if matches!(Self::eval_values_equal_exact(ai, bi), Some(true))
                    && !matches!(bv, EvalValue::Unknown)
                    && matches!(Self::eval_values_equal_exact(av, bv), Some(false))
                {
                    return true;
                }
            }
        }
        false
    }

    /// True when some `(seq.unit e)` in the assertions has a BitVec-sorted
    /// element `e` that is an INTERPRETED BV application (bvadd/bvxor/bvnot/...
    /// or a BV structural op). Such elements are opaque to the BV-less combined
    /// seq solver, so a SAT it returns over them cannot be model-validated
    /// (#seq-bv-WS). Bare BV variables/constants do NOT count.
    fn seq_has_interpreted_bv_element(&self) -> bool {
        use ay_core::term::TermData;
        fn is_bv_op(name: &str) -> bool {
            name.starts_with("bv")
                || matches!(
                    name,
                    "concat"
                        | "extract"
                        | "zero_extend"
                        | "sign_extend"
                        | "rotate_left"
                        | "rotate_right"
                        | "repeat"
                )
        }
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == "seq.unit" && args.len() == 1 {
                        let e = args[0];
                        if matches!(self.ctx.terms.sort(e), ay_core::Sort::BitVec(_)) {
                            if let TermData::App(esym, eargs) = self.ctx.terms.get(e) {
                                if !eargs.is_empty() && is_bv_op(esym.name()) {
                                    return true;
                                }
                            }
                        }
                    }
                    for &a in args {
                        stack.push(a);
                    }
                }
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, th, el) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*el);
                }
                _ => {}
            }
        }
        false
    }

    /// True when an assertion is a seq equality `(= v R)` (either side) where `v`
    /// is a seq VARIABLE and `R` contains a `(seq.extract S I N)` whose source `S`
    /// transitively mentions `v` — a self-referential extract definition
    /// (`s1 = (seq.extract ([-1].[2].s1) 0 5)`). Its length is a `min(N, len(S))`
    /// fixpoint the combined seq solver leaves unresolved, so a returned SAT model
    /// does not validate the definition. Descends top-level `and` only.
    fn has_self_referential_seq_extract(&self) -> bool {
        use ay_core::term::{Symbol, TermData};
        // Does `root` contain `target` as a subterm?
        fn contains(this: &Executor, root: TermId, target: TermId) -> bool {
            let mut stack = vec![root];
            let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
            while let Some(n) = stack.pop() {
                if n == target {
                    return true;
                }
                if !seen.insert(n) {
                    continue;
                }
                match this.ctx.terms.get(n) {
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(i) => stack.push(*i),
                    TermData::Ite(c, a, b) => {
                        stack.push(*c);
                        stack.push(*a);
                        stack.push(*b);
                    }
                    _ => {}
                }
            }
            false
        }
        // Does `t` contain a `(seq.extract S ..)` whose source `S` mentions `v`?
        fn extract_source_mentions(this: &Executor, t: TermId, v: TermId) -> bool {
            let mut stack = vec![t];
            let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
            while let Some(n) = stack.pop() {
                if !seen.insert(n) {
                    continue;
                }
                if let TermData::App(Symbol::Named(name), args) = this.ctx.terms.get(n) {
                    if name == "seq.extract" && args.len() == 3 && contains(this, args[0], v) {
                        return true;
                    }
                    for &a in args {
                        stack.push(a);
                    }
                }
            }
            false
        }
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t).clone() else {
                continue;
            };
            if name == "and" {
                stack.extend(args);
                continue;
            }
            if name == "=" && args.len() == 2 && self.ctx.terms.sort(args[0]).is_seq() {
                for (vside, rside) in [(args[0], args[1]), (args[1], args[0])] {
                    if matches!(self.ctx.terms.get(vside), TermData::Var(..))
                        && extract_source_mentions(self, rside, vside)
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// True when some top-level string-CONTENT assertion (a String-sorted
    /// `=`/`distinct`, or a str.contains/prefixof/suffixof/</<=/in_re predicate)
    /// contains a String-sorted array `select` subterm that the model cannot
    /// resolve (`EvalValue::Unknown`). The string theory never sees array-sourced
    /// string content, so such a SAT model is not independently validatable
    /// (#mixed-combo-WS). Pure Int-context `(= (str.len (select ..)) k)` is NOT a
    /// string-content atom and is excluded, so length-only SAT stays decided.
    fn has_array_sourced_string_content_unknown(
        &self,
        model: &crate::executor::model::Model,
    ) -> bool {
        use crate::executor::model::EvalValue;
        use ay_core::term::TermData;
        let is_string_content_atom = |t: TermId| -> bool {
            let inner = match self.ctx.terms.get(t) {
                TermData::Not(i) => *i,
                _ => t,
            };
            let TermData::App(sym, args) = self.ctx.terms.get(inner) else {
                return false;
            };
            match sym.name() {
                "=" | "distinct" if args.len() >= 2 => {
                    matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::String)
                }
                "str.contains" | "str.prefixof" | "str.suffixof" | "str.<" | "str.<="
                | "str.in_re" | "str.in.re" => true,
                _ => false,
            }
        };
        for &assertion in &self.ctx.assertions {
            // Flatten only top-level `(and ...)`.
            let atoms: Vec<TermId> = match self.ctx.terms.get(assertion) {
                TermData::App(sym, args) if sym.name() == "and" => args.clone(),
                _ => vec![assertion],
            };
            for atom in atoms {
                if !is_string_content_atom(atom) {
                    continue;
                }
                let mut stack = vec![atom];
                let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
                while let Some(t) = stack.pop() {
                    if !seen.insert(t) {
                        continue;
                    }
                    match self.ctx.terms.get(t) {
                        TermData::App(sym, sargs) => {
                            if sym.name() == "select"
                                && matches!(self.ctx.terms.sort(t), ay_core::Sort::String)
                                && matches!(self.evaluate_term(model, t), EvalValue::Unknown)
                            {
                                return true;
                            }
                            for &x in sargs {
                                stack.push(x);
                            }
                        }
                        TermData::Not(i) => stack.push(*i),
                        TermData::Ite(c, th, el) => {
                            stack.push(*c);
                            stack.push(*th);
                            stack.push(*el);
                        }
                        _ => {}
                    }
                }
            }
        }
        false
    }

    /// Finalize SAT model validation: validate the model and handle
    /// graceful degradation for assertions that cannot be fully checked.
    ///
    /// `Incomplete` errors degrade SAT to `Unknown`. `Violated` errors
    /// propagate as hard `ExecutorError::ModelValidation` failures.
    /// Detect a SAT model that assigns a finite enum (all-nullary datatype) sort
    /// MORE distinct inhabitants than it has constructors — a phantom
    /// infinite-domain model that violates the sort's exact finite cardinality.
    ///
    /// The EUF model records, per sort, the distinct element representatives it
    /// materialized; if that count exceeds the sort's constructor count `k`, the
    /// model is unsound. Returns `(sort, distinct_used, k)` on violation, else
    /// `None`. Degrade-only by construction (callers turn `sat` into `unknown`),
    /// so it can never turn a genuine SAT into a wrong answer.
    pub(in crate::executor) fn enum_cardinality_violation(&self) -> Option<(String, usize, usize)> {
        let euf = self.last_model.as_ref()?.euf_model.as_ref()?;
        for (sort_name, elements) in euf.sort_elements.iter() {
            if let Some(k) = self
                .enum_datatype_constructor_count(&ay_core::Sort::Uninterpreted(sort_name.clone()))
            {
                if elements.len() > k {
                    return Some((sort_name.clone(), elements.len(), k));
                }
            }
        }
        None
    }

    pub(in crate::executor) fn finalize_sat_model_validation(&mut self) -> Result<SolveResult> {
        // Skips accrued BEFORE this finalization (nested/deferred probe solves,
        // or a previous check-sat in the same incremental session) say nothing
        // about the model being finalized here — see the mixed Seq+datatype
        // gate below, which must only react to a skip taken for THIS model.
        let skips_before_finalize = self.last_statistics.model_validation_skips;
        // Model completion: make the model total over the original free
        // variables (recover `VariableSubstitution`-eliminated variables
        // from their defining RHS, default truly-unconstrained ones) BEFORE
        // any validation gate evaluates. Completion is fill-only — it never
        // overwrites solver-assigned values — and the full validation below
        // still decides acceptance, so it cannot introduce a wrong SAT. See
        // model/completion.rs.
        //
        // ROOTS MUST MATCH THE GATE (#dt-assumption-completion-roots). The
        // verdict this finalizer publishes is "sat under the CURRENT
        // assumptions", and `independent_gate_query_roots` checks exactly
        // `ctx.assertions ∪ last_assumptions`. Completing over the assertions
        // ALONE left the model total on a strictly SMALLER set than the one it
        // is then judged against, and an assumption-only atom is invisible to
        // every completion phase — including the datatype construction, whose
        // union-find is what turns a committed `=` into ONE class value.
        //
        // Measured shape (the deductive-checks `eval_objective_exact` control): the
        // body binding `(= result (eval_terms_saturating t a))` is carried as
        // an ASSUMPTION while the disequality between the two Result-valued UF
        // applications is a top-level assertion. Rooted on the assertions only,
        // `result` and `(eval_terms_saturating t a)` never merged, so
        // construction gave them two DIFFERENT well-founded values — and the
        // independent gate, which DOES read the assumption, then caught the
        // published model falsifying it and fired the soundness banner. The
        // model was genuinely wrong, not merely unconfirmable; the missing
        // equality was the cause.
        //
        // Sound: an assumption is enforced true for this `check_sat_assuming`
        // exactly as a top-level assertion is (completion.rs already documents
        // and relies on that for its `extra_roots`), `last_assumptions` is
        // cleared per solve by `prepare_check_sat_internal_state` so it can
        // never be stale, and completion stays candidate-only — every gate
        // re-checks the result, so a wrong completion still degrades to
        // `unknown` rather than shipping a wrong `sat`.
        let assumption_roots = self.last_assumptions.clone().unwrap_or_default();
        self.complete_model_for_validation(&assumption_roots);
        self.materialize_symbolic_array_defaults();
        self.repair_asserted_bool_leaf_polarities();

        // String GAP completion (gate-verified, retracting). The strings solver
        // validates HERE (in-loop) and downgrades a genuine SAT to Unknown when
        // a `(str.len x) = N`-pinned string variable — or a substr/concat
        // reduction skolem bridged to it — is left unassigned, BEFORE the outer
        // `emit_sat_verdict` constrained-gap sweep would run. Complete those
        // String-sorted gaps through the SAME snapshot-and-retract pass here so
        // the fix reaches the string path. Any completion the strict +
        // independent gate refutes is fully RETRACTED, so this can only turn a
        // today-Unknown string model into a validated SAT — never a wrong SAT
        // and never a sat→unknown regression (#str-gap).
        self.complete_string_gaps_gate_verified();
        self.complete_opaque_array_defaults_gate_verified();

        // Enum model repair (#enum-model-repair): map surplus EUF elements of
        // a finite all-nullary (enum) datatype sort onto constructor slots
        // consistent with the model's committed (dis)equalities, BEFORE the
        // cardinality gate below counts them. The eager DT route leaves
        // unconstrained selector-application classes unmerged, so extraction
        // mints more elements than the sort has inhabitants and the gate
        // (rightly) degrades a genuine SAT to Unknown. Candidate-only: the
        // gate still re-counts and the full validation below still decides
        // acceptance, so a bad repair degrades exactly as before (never a
        // wrong SAT). See `repair_enum_model_overpopulation`.
        self.repair_enum_model_overpopulation();

        // Finite-enum CARDINALITY gate (DEFAULT mode, degrade-only).
        //
        // An all-nullary (enum) datatype sort has EXACTLY `k` inhabitants — its
        // `k` constructor constants. The EUF model materializes one fresh element
        // representative per distinct equivalence class of that sort; it only
        // splits two terms into different representatives when they are FORCED
        // distinct (no genuine-SAT problem ever needs more reps than `k` — the
        // congruence model collapses everything that may collapse). Therefore a
        // produced model whose `sort_elements[sort].len() > k` assigns MORE
        // pairwise-distinct inhabitants than the sort can hold: a finite-domain
        // pigeonhole violation. Such a "model" is not a real model, so the SAT
        // verdict is unsound and we degrade it to a sound `unknown`.
        //
        // SOUNDNESS: this is strictly degrade-only — it can only turn `sat` into
        // `unknown`, never into `unsat` and never into a wrong `sat`. The worst
        // case (an over-fragmented EUF model on a genuinely-SAT problem) yields a
        // sound `unknown`, which is always acceptable (soundness over
        // completeness). It never claims UNSAT, so it cannot manufacture a
        // wrong-unsat. The exact-cardinality fact (`k` = constructor count of an
        // all-nullary datatype) is checked by `enum_datatype_constructor_count`,
        // which returns `Some(k)` ONLY for all-nullary datatypes (any field makes
        // the domain unbounded → `None`, untouched).
        if let Some((sort, used, k)) = self.enum_cardinality_violation() {
            if ay_core::misc_cli_flags().phase_trace {
                eprintln!("c phase-trace model-gate enum-cardinality used={used} k={k}");
            }
            self.last_statistics.model_validation_failures += 1;
            tracing::warn!(
                sort = %sort,
                distinct_used = used,
                inhabitants = k,
                "SAT model over-populates a finite enum sort, degrading to Unknown"
            );
            self.last_model = None;
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.last_result = Some(SolveResult::Unknown);
            self.record_model_validation_unknown_diagnostic(format!(
                "model assigns finite enum sort {sort} {used} distinct values \
                 but it has only {k} inhabitants (finite-domain pigeonhole)"
            ));
            return Ok(SolveResult::Unknown);
        }

        // #8779/#8729/#8745: Global strict gate runs BEFORE any defer/skip
        // short-circuit. If any per-theory DefinitiveEval oracle declares an
        // assertion definitively violated (structurally ground arguments,
        // evaluator returns Bool(false) with polarity accounted for), the
        // model is unsound and we MUST degrade SAT to Unknown regardless of
        // downstream fallbacks.
        // #uflia-witness-complete (1a-i): see `apply_strict_model_gate`.
        self.uflia_fill_bounded_int_leaves();
        self.repair_asserted_array_read_pins();
        // #uflia-witness-complete (1b): UNDER-COMPLETED UF TABLE. A falsified
        // UF-chain equality whose chain argument lands on a function point the
        // formula constrains NOWHERE ELSE is a model-EXTRACTION gap, not a bad
        // search point — the table simply did not pick the colliding value.
        // Complete it here, as a model-completion step, so the strict oracle
        // below and every downstream gate (independent, authoritative,
        // postcondition) re-check the COMPLETED witness with NO gate weakened.
        // Env-gated (`--uflia-witness-complete=1`); default off is a no-op.
        // A completion the gates refute degrades to `unknown` exactly as the
        // uncompleted model does today — never a wrong `sat`.
        self.uflia_complete_free_uf_chain_witness();
        // Central strict-coverage policy: both the existing `datatype-field`
        // array gap and the total-construction `datatype` gap are handled by
        // the same scoped helper as the other SAT funnels. All non-confirming
        // independent verdicts remain strict failures.
        let strict_verdict = self.verify_model_strict_with_scoped_authority();
        // #qfax-rejected-target retry: this cycle's repair ran before
        // the rejection named its assertion. Clear the per-model marker,
        // re-run repair once (the bypass now forces completion for the
        // named target), and re-verify. Single retry, arrays only.
        //
        // On retry SUCCESS the repaired model may only short-circuit to `Sat`
        // when the INDEPENDENT, fail-closed gate re-checks EVERY assertion
        // true (`ConfirmedSat`) — the same arbiter the #g4-dt-defer sites
        // use — and that confirmation is what justifies setting
        // `last_model_validated`. A bare strict definitive-false sweep is NOT
        // full model validation: the former unconditional early return here
        // emitted a public SAT with `last_model_validated == false` (#7912
        // postcondition violation, caught by the ay-chc ghost-pair fence test
        // in debug builds). When the gate cannot confirm, the verdict is
        // cleared and control FALLS THROUGH to the rest of the validation
        // pipeline, which alone decides acceptance — so the retry only ever
        // widens the candidate set, never the unvalidated-SAT set.
        let strict_verdict = match strict_verdict {
            Some((_, oracle, assertion))
                if oracle.starts_with("arrays") && !self.qfax_retry_done =>
            {
                self.derive_qfax_refinement_clause(assertion);
                self.last_rejected_array_assertion = Some(assertion);
                self.qfax_retry_done = true;
                if let Some(model) = self.last_model.as_mut() {
                    if let Some(euf) = model.euf_model.as_mut() {
                        euf.term_values.remove(&TermId(u32::MAX - 7));
                    }
                }
                self.repair_asserted_array_read_pins();
                let reverdict = self.verify_model_strict_with_scoped_authority();
                self.qfax_retry_done = false;
                if reverdict.is_none() {
                    self.last_rejected_array_assertion = None;
                    if matches!(
                        self.confirm_sat_with_independent_gate(),
                        ay_model_check::GateVerdict::ConfirmedSat
                    ) {
                        self.last_model_validated = true;
                        return Ok(SolveResult::Sat);
                    }
                }
                reverdict
            }
            other => other,
        };
        if let Some((idx, oracle, assertion)) = strict_verdict {
            self.note_exact_ite_uf_definition_model_rejection(oracle);
            if oracle.starts_with("arrays") {
                self.derive_qfax_refinement_clause(assertion);
                self.last_rejected_array_assertion = Some(assertion);
            }
            self.last_statistics.model_validation_failures += 1;
            self.last_statistics
                .set_int("model_validation.strict.assertion_index", idx as u64);
            self.last_statistics
                .set_string("model_validation.strict.oracle", oracle);
            self.last_statistics
                .set_string("model_validation.strict.term", self.format_term(assertion));
            if ay_core::misc_cli_flags().phase_trace {
                let t = self.format_term(assertion);
                let t = if t.len() > 400 { &t[..400] } else { &t[..] };
                eprintln!(
                    "c phase-trace model-gate definitive-false-oracle idx={idx} oracle={oracle} term={t}"
                );
            }
            // CENSUS DIAGNOSTIC ONLY (`--model-reject-dump`; default off is
            // byte-identical — a single `var_os` probe and no I/O). Unlike
            // `apply_strict_model_gate`, this DEFERRED-validation rejection site
            // is silent: it records the violated assertion in the statistics but
            // never prints the concrete values the extracted model gave that
            // assertion's leaves. A model-rejection census therefore cannot tell
            // an out-of-range extracted value from a genuinely-bad search point.
            // Reuse the existing loud-alarm formatter (falsifying assignment
            // included) so both strict sites report the same evidence shape.
            // WRITE-ONLY: nothing in any verdict path reads this, and the
            // degrade below is unchanged.
            if ay_core::misc_cli_flags().model_reject_dump {
                let dump_term = self.format_term(assertion);
                self.report_caught_invalid_model(assertion, &dump_term);
            }
            // Futile-deepening backstop (#dt-array-degrade-backstop, extended):
            // a datatype-field oracle rejection on a datatype-carrying-array
            // problem is the same uncovered hazard family as the dt-array
            // degrade gate below (e.g. a datatype-valued `select` whose field
            // lane the eager-BV encoding cannot represent — observed on a BMC
            // instance as `(= (Ctor f1..) (select a #x0))` false-evaluating).
            // The DT iterative-deepening loop only materializes DT selector
            // frontiers; it does not add array-select field congruence, so
            // re-solving at deeper frontiers re-derives the SAME rejected model
            // shape at 2x the CNF until the memory cap kills the run (measured:
            // round 2 doubled 30M->59M clauses and hit memout). Mark the
            // existing depth-invariant flag so the deepening loop returns this
            // sound Unknown immediately. Strictly a perf backstop: the verdict
            // (Unknown) is unchanged, only the futile retries are skipped.
            if oracle == "datatype-field" && self.problem_has_datatype_carrying_array() {
                self.last_degrade_was_datatype_array = true;
            }
            tracing::warn!(
                assertion_index = idx,
                oracle = oracle,
                "SAT degraded to Unknown: definitive-false oracle rejected model \
                 (strict gate, #8779/#8729/#8745)"
            );
            // CEGAR (#dt-array-cegar / #array-select-congruence-gate): on an
            // array problem, a strict-oracle rejection can BE the derived-equal-
            // index select-congruence violation (two reads of one array identity
            // class at a model-equal index pinned to incompatible values) — the
            // upgraded arrays oracle now proves the violated assertion false
            // before the dedicated congruence gates below ever run. Before
            // dropping the model, distill the violated congruence tautology so
            // `cegar_refine_solve` can install it and re-solve to a definite
            // verdict (e.g. the derived-index disequality becomes provably
            // unsat). Identical guards/dedup as the gates below; when nothing
            // distills, this degrade is byte-for-byte unchanged. SOUND: the
            // lemma is an array-theory tautology, so installing it is
            // verdict-preserving.
            if self.problem_has_array()
                && self.cegar_rounds_remaining > 0
                && self.cegar_pending_lemma.is_none()
            {
                if let Some(model) = self.last_model.take() {
                    // The census distills the "two reads DIFFER at a model-equal
                    // index" polarity. When a read-pin repair already UNIFIED the
                    // reads (so the oracle instead proved the asserted
                    // DISEQUALITY false), the violated tautology is the same
                    // select-congruence lemma — build it from the rejected
                    // assertion's own `(not (= (select ..) (select ..)))` /
                    // `(= (select ..) (select ..))` read pair.
                    let lemma = self.census_congruence_cegar_lemma(&model).or_else(|| {
                        use ay_core::term::TermData;
                        let eq = match self.ctx.terms.get(assertion) {
                            TermData::Not(inner) => *inner,
                            _ => assertion,
                        };
                        self.strict_oracle_select_congruence_lemma(&model, eq)
                    });
                    if let Some(lemma) = lemma {
                        if !self.cegar_emitted_lemmas.contains(&lemma) {
                            if ay_core::misc_cli_flags().phase_trace {
                                eprintln!("c phase-trace cegar-lemma-distilled kind=strict-oracle");
                            }
                            self.cegar_pending_lemma = Some(lemma);
                        }
                    }
                    self.last_model = Some(model);
                }
            }
            // #abv-subst-model-retry: see `apply_strict_model_gate`.
            if self.bv_subst_lane {
                self.bv_subst_model_rejected = true;
            }
            // #uflia-cong-repair-arm: a strict-oracle refutation of a
            // UFLIA-lane model is the same evidence class as the independent
            // gate's function-graph refutation — cross-theory model merging
            // moved an arithmetic value to satisfy UF congruence (coincident
            // argument collision) and falsified a ground assertion. The
            // non-persistent eager arm has no in-loop blocking retry, so
            // without arming here the solve dies as a final Unknown without
            // ever trying the congruence-repair re-solve (mathsat Hash
            // hash_sat_04_13: `(< x2 5)` false under the merged model in both
            // arms). Scoped to the UFLIA lane like the gate site; the verdict
            // here still degrades, the retry-once latch bounds the cost, and
            // the armed re-solve routes back through this same strict gate
            // plus the independent/authoritative funnel — recover-only.
            if self.uflia_congruence_lane {
                self.uflia_congruence_gate_rejected = true;
                // #uflia-model-repair EVIDENCE CAPTURE (env-gated): this
                // strict rejection also fires IN-ATTEMPT (in-loop validation
                // inside the split-loop arms), where the outer pre-emission
                // snapshot in `check_sat_guarded` never sees the candidate —
                // the `last_model = None` below erases it. Preserve the
                // refuted candidate (latest rejection wins) so the §3.2
                // targeted repair re-solve can name the colliding value
                // assignment. Verdict flow is byte-identical: pure clone
                // before the existing erase.
                if crate::executor::uflia_model_repair::uflia_model_repair_enabled() {
                    if let Some(model) = self.last_model.clone() {
                        crate::executor::uflia_model_repair::push_repair_candidate(
                            &mut self.uflia_repair_candidates,
                            model,
                        );
                    }
                }
            }
            self.last_model = None;
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.last_result = Some(SolveResult::Unknown);
            self.record_model_validation_unknown_diagnostic(format!(
                "strict model-validation oracle {oracle} rejected assertion {idx}"
            ));
            return Ok(SolveResult::Unknown);
        }

        // Datatype-through-array soundness gate (DEFAULT mode, degrade-only).
        //
        // The combined DT + Array/BV route bit-blasts datatype values stored in
        // arrays WITHOUT constructor injectivity through array equality. It can
        // therefore return a spurious SAT for e.g.
        //   (= (store a i (Ctor x)) (store b i (Ctor (x+1))))
        // which is UNSAT — the two arrays must differ at index i because
        // `Ctor x != Ctor (x+1)` — yet the (incomplete) bit-blasted model
        // satisfies the equality.
        //
        // The store-value constructor-injectivity bridge
        // (`dt_store_value_injectivity_axioms`, #dt-array-store-value-injectivity)
        // now emits that entailment as a valid Array+DT axiom for the store-pair
        // fragment, so decidable instances reach a genuine `unsat` and the gate
        // never sees their SAT. `dt_array_injectivity_gate_bypass` records whether
        // the bridge PROVABLY modeled every datatype-carrying-array hazard in the
        // problem; when it did, a returned SAT model already satisfies the emitted
        // injectivity/disjointness implications and is sound, so the degrade is
        // skipped (restoring completeness for genuinely-SAT instances such as
        // `store(a,i,C x) = store(b,i,C x)`). Otherwise (uncovered hazard:
        // datatype-valued select, const-array/map of a datatype array, datatype-
        // indexed arrays, quantified fragment, ...) degrade the SAT to a sound
        // `unknown`. SOUNDNESS: strictly degrade-only for the uncovered case — it
        // can only turn `sat` into `unknown`, never into `unsat` and never into a
        // wrong `sat`. UNSAT verdicts are unaffected (this gate runs on the SAT
        // path only).
        if self.problem_has_datatype_carrying_array() && !self.dt_array_injectivity_gate_bypass {
            // PHASE 1 CENSUS (#dt-array-model-census): the model-based certification
            // boundary. The conservative degrade below fails-closes EVERY datatype-
            // carrying-array SAT the search could not prove; the census instead
            // RECONSTRUCTS the candidate model's datatype-array fragment and, when it
            // is provably consistent + fully decidable (select-congruence keyed by
            // evaluated index, model array-identity, distinct witnessed), CERTIFIES
            // the SAT — a positive concrete witness, sound by construction (it can
            // only turn this degrade into a validated SAT, never a false SAT). The
            // strict per-assertion oracle already ran above, so this closes the
            // remaining datatype-array obligations.
            if let Some(model) = self.last_model.take() {
                let _t_census = std::time::Instant::now();
                let certified = self.datatype_array_census_certifies(&model);
                if ay_core::misc_cli_flags().phase_trace {
                    eprintln!(
                        "c phase-trace TIMING dt-array-census {:.1}s certified={certified}",
                        _t_census.elapsed().as_secs_f64()
                    );
                }
                if certified {
                    if ay_core::misc_cli_flags().phase_trace {
                        eprintln!("c phase-trace model-gate dt-array-census-certified");
                    }
                    self.last_model = Some(model);
                    self.last_model_validated = true;
                    return Ok(SolveResult::Sat);
                }
                // Not census-certified: restore the model so the independent
                // ground-evaluation gate below can still inspect and confirm it.
                self.last_model = Some(model);
            }
            // Before the SYNTACTIC degrade, defer to the INDEPENDENT, fail-closed
            // ground-evaluation gate (guarded above): it re-checks EVERY assertion
            // against the model with a solver-independent evaluator, resolving each
            // datatype-carrying array through its asserted store-chain definition.
            // That ground evaluation DIRECTLY decides the exact
            // constructor-injectivity-through-array hazard this syntactic gate
            // guards — it computes `(= (store a i (C x)) (store b i (C (x+1))))`
            // FALSE (the stored constructors differ) and REFUTES such a model —
            // while CONFIRMING a genuinely-SAT datatype-array model the syntactic
            // footprint check cannot certify (variable-index `Vec::push` chains,
            // datatype-valued selects at concrete model indices). Only a full
            // `ConfirmedSat` skips the degrade; `ModelViolates` / `CannotConfirm`
            // fall through and STILL degrade (fail-closed). SOUND: a `Sat` survives
            // here only when an independent evaluator has ground-verified every
            // assertion, so no wrong `Sat` — and the later gate re-confirms it.
            // (#dt-array-defer-to-independent-gate)
            if !matches!(
                self.confirm_sat_with_independent_gate(),
                ay_model_check::GateVerdict::ConfirmedSat
            ) {
                // CEGAR (#dt-array-cegar): neither the census nor the independent
                // gate certified this model. Before dropping it, distill the array
                // select-congruence lemma the model VIOLATED so the deepening loop
                // can install it and re-solve. Sound: the lemma is a theory
                // tautology (verdict-preserving); the loop is budgeted, so failing
                // to converge degrades to `unknown`.
                if self.cegar_rounds_remaining > 0 && self.cegar_pending_lemma.is_none() {
                    if let Some(model) = self.last_model.take() {
                        if let Some(lemma) = self.census_congruence_cegar_lemma(&model) {
                            if !self.cegar_emitted_lemmas.contains(&lemma) {
                                if ay_core::misc_cli_flags().phase_trace {
                                    eprintln!("c phase-trace cegar-lemma-distilled kind=dt-array");
                                }
                                self.cegar_pending_lemma = Some(lemma);
                            }
                        }
                        self.last_model = Some(model);
                    }
                }
                // Perf backstop (#dt-array-degrade-backstop): record that THIS Unknown
                // came from the depth-invariant datatype-array degrade gate, so the DT
                // iterative-deepening loop can return it immediately instead of
                // re-solving at deeper frontiers (both gate inputs are depth-invariant).
                if ay_core::misc_cli_flags().phase_trace {
                    eprintln!("c phase-trace model-gate datatype-array-degrade");
                }
                self.last_degrade_was_datatype_array = true;
                self.last_statistics.model_validation_failures += 1;
                self.last_statistics
                    .set_int("model_validation.datatype_array_degrade", 1);
                tracing::warn!(
                    "SAT over a datatype-carrying array is not soundly decidable \
                     (constructor injectivity through array equality is unmodeled); \
                     degrading to Unknown"
                );
                self.last_model = None;
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.last_result = Some(SolveResult::Unknown);
                self.record_model_validation_unknown_diagnostic(
                    "SAT over a datatype-carrying array degraded to Unknown \
                     (datatype<->array constructor injectivity unmodeled)"
                        .to_string(),
                );
                return Ok(SolveResult::Unknown);
            }
            // Independent gate CONFIRMED the SAT: skip the syntactic degrade and
            // fall through to the remaining gates (#dt-array-defer-to-independent-gate).
        }

        // General SELECT-CONGRUENCE model gate (#array-select-congruence-gate).
        // The eager array encoding does not enforce select-congruence at
        // DERIVED-equal indices for every element sort — a plain
        // `(declare-sort E)` / scalar-element array can be returned SAT on a
        // model where two reads of one array at a model-equal (but syntactically
        // distinct) index disagree. That is a real theory violation, so degrade
        // it to a sound `unknown`. Runs on the SAT path only, for any array
        // problem the datatype-array gate above did not already resolve, and
        // trips ONLY on a PROVEN incompatibility — a genuine SAT model is
        // select-congruent on its read cells and passes untouched, so
        // completeness is preserved. Degrade-only: never turns a verdict into
        // `unsat` or a wrong `sat`.
        if self.problem_has_array() {
            if let Some(model) = self.last_model.take() {
                if self.array_select_congruence_violated(&model) {
                    if ay_core::misc_cli_flags().phase_trace {
                        eprintln!("c phase-trace model-gate array-select-congruence-degrade");
                    }
                    // CEGAR (#array-select-congruence-gate): distill the violated
                    // congruence lemma before dropping the model. For the UNSAT
                    // uninterpreted-element cases this drives a subsequent round to
                    // a genuine `unsat` instead of a degraded `unknown`.
                    if self.cegar_rounds_remaining > 0 && self.cegar_pending_lemma.is_none() {
                        if let Some(lemma) = self.census_congruence_cegar_lemma(&model) {
                            if !self.cegar_emitted_lemmas.contains(&lemma) {
                                if ay_core::misc_cli_flags().phase_trace {
                                    eprintln!("c phase-trace cegar-lemma-distilled kind=array");
                                }
                                self.cegar_pending_lemma = Some(lemma);
                            }
                        }
                    }
                    self.last_statistics.model_validation_failures += 1;
                    self.last_statistics
                        .set_int("model_validation.array_select_congruence_degrade", 1);
                    tracing::warn!(
                        "SAT model violates array select-congruence at a \
                         derived-equal index (eager encoding gap); degrading to \
                         Unknown"
                    );
                    self.last_model = None;
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    self.last_result = Some(SolveResult::Unknown);
                    self.record_model_validation_unknown_diagnostic(
                        "SAT degraded to Unknown (array select-congruence \
                         violated at a derived-equal index)"
                            .to_string(),
                    );
                    return Ok(SolveResult::Unknown);
                }
                // Not a violation — restore the model and continue validation.
                self.last_model = Some(model);
            }
        }

        // Self-check global finite-enum cardinality gate. Per-assertion model
        // evaluation cannot observe a model that assigns a finite enum datatype
        // sort MORE distinct inhabitants than it has constructors (a phantom
        // infinite-domain model — e.g. an UF whose range materializes 4 fresh
        // representatives over a 2-constructor enum, which is a finite-model
        // pigeonhole UNSAT). Degrade such a SAT to a sound `unknown` under
        // `--self-check`. This is gated and degrade-only, so it can never turn a
        // genuine SAT into a wrong answer. (#self-check-enum-cardinality)
        if self.self_check {
            if let Some((sort, used, k)) = self.self_check_enum_cardinality_violation() {
                self.last_statistics.model_validation_failures += 1;
                tracing::warn!(
                    sort = %sort,
                    distinct_used = used,
                    inhabitants = k,
                    "self-check: SAT model over-populates a finite enum sort, degrading to Unknown"
                );
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.last_result = Some(SolveResult::Unknown);
                self.record_model_validation_unknown_diagnostic(format!(
                    "self-check: model assigns finite enum sort {sort} {used} distinct \
                     values but it has only {k} inhabitants"
                ));
                return Ok(SolveResult::Unknown);
            }
        }

        // When quantifier E-matching is active, the assertion set contains ground
        // instances instead of the original quantified formulas. Validating now would
        // produce false violations because the model may not satisfy synthetic ground
        // instances that were only added to guide the SAT solver. Validation is deferred
        // to check_sat_internal after the original assertions are restored (#2862).
        //
        // SOUNDNESS AUDIT (#7912, Gap B, #8456):
        // - defer_model_validation: set ONLY in solve_current_assertions_with_quantifier_support()
        //   when qr.original_assertions.is_some() (quantifier E-matching rewrote assertions).
        //   Validation occurs later in map_quantifier_result() after originals are restored.
        // - skip_model_eval suppresses full evaluation for scoped inner solves
        //   (incremental_scope.rs and internal verification probes). Those
        //   scopes restore it before returning to the public emission funnel.
        //   Two BV+LIA fallback routes also use it for a provisional SAT after
        //   model validation failed; therefore the flag is NEVER public
        //   validation evidence. emit_sat_verdict rejects any non-trivial SAT
        //   unless last_model_validated is true. Seq, FP, and String theories
        //   run full model validation (#8456). Trivially-SAT paths (all
        //   assertions fold to true) set last_model_validated=true instead.
        //   Both flags are cleared at check_sat/check_sat_assuming entry.
        // Strict verify_model gate (#7912 / #8779 / #8729): reject any
        // SAT result where a theory oracle declares an assertion
        // definitively violated under the produced model. This check
        // runs BEFORE skip_model_eval / defer_model_validation short-
        // circuits because those flags only suppress the full
        // observation pipeline — they must NOT allow a known-wrong
        // model to escape as SAT. Soundness over completeness.
        self.repair_asserted_array_read_pins();
        // Third strict-gate site in finalize: use the same centralized,
        // fail-closed coverage policy as both earlier funnels and their retries.
        let strict3 = self.verify_model_strict_with_scoped_authority();
        // #qfax-rejected-target retry (site 2): same contract as the first
        // strict-gate site above — a successful repair+re-verify may only
        // short-circuit to `Sat` on an independent-gate `ConfirmedSat` (which
        // justifies `last_model_validated`); otherwise it clears the verdict
        // and continues to the full validation pipeline. It must NOT
        // unconditionally early-return `Sat` (#7912 postcondition).
        let strict3 = match strict3 {
            Some((_, oracle, assertion))
                if oracle.starts_with("arrays") && !self.qfax_retry_done =>
            {
                self.derive_qfax_refinement_clause(assertion);
                self.last_rejected_array_assertion = Some(assertion);
                self.qfax_retry_done = true;
                if let Some(model) = self.last_model.as_mut() {
                    if let Some(euf) = model.euf_model.as_mut() {
                        euf.term_values.remove(&TermId(u32::MAX - 7));
                    }
                }
                self.repair_asserted_array_read_pins();
                let reverdict = self.verify_model_strict_with_scoped_authority();
                self.qfax_retry_done = false;
                if reverdict.is_none() {
                    self.last_rejected_array_assertion = None;
                    if matches!(
                        self.confirm_sat_with_independent_gate(),
                        ay_model_check::GateVerdict::ConfirmedSat
                    ) {
                        self.last_model_validated = true;
                        return Ok(SolveResult::Sat);
                    }
                }
                reverdict
            }
            other => other,
        };
        if let Some((idx, oracle, assertion)) = strict3 {
            self.note_exact_ite_uf_definition_model_rejection(oracle);
            if oracle.starts_with("arrays") {
                self.derive_qfax_refinement_clause(assertion);
                self.last_rejected_array_assertion = Some(assertion);
            }
            self.last_statistics.model_validation_failures += 1;
            self.last_statistics
                .set_int("model_validation.strict.assertion_index", idx as u64);
            self.last_statistics
                .set_string("model_validation.strict.oracle", oracle);
            self.last_statistics
                .set_string("model_validation.strict.term", self.format_term(assertion));
            tracing::warn!(
                assertion_index = idx,
                oracle,
                "verify_model_strict: definitive violation — degrading SAT to Unknown"
            );
            // #abv-subst-model-retry: see `apply_strict_model_gate`.
            if self.bv_subst_lane {
                self.bv_subst_model_rejected = true;
            }
            self.last_model = None;
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.last_result = Some(SolveResult::Unknown);
            self.record_model_validation_unknown_diagnostic(format!(
                "strict model-validation oracle {oracle} rejected assertion {idx}"
            ));
            return Ok(SolveResult::Unknown);
        }

        let assertion_features = StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
        let has_seq_terms = assertion_features.has_seq;
        let has_native_seq_ops = assertion_features.has_seq_ops;
        let mixed_seq_datatype = has_seq_terms && self.assertions_contain_datatype_terms();
        // (#seq-bv-WS) Seq<BitVec> whose unit elements are INTERPRETED BV
        // expressions (bvxor/bvadd/...) is not decidable by the BV-less combined
        // seq solver: it treats those ops as uninterpreted, so a returned SAT
        // model has no bv_model and cannot be independently validated (e.g.
        // `(= (seq.unit (bvxor x #x8)) (seq.unit (bvadd #xe x)))` is UNSAT over
        // all values but was reported SAT). Fail closed to Unknown. Bare BV
        // variables/constants as elements are fine (the EUF model is genuine) and
        // are NOT degraded.
        if has_seq_terms
            && self
                .last_model
                .as_ref()
                .map_or(true, |m| m.bv_model.is_none())
            && self.seq_has_interpreted_bv_element()
        {
            self.last_statistics.model_validation_failures += 1;
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.last_result = Some(SolveResult::Unknown);
            self.record_model_validation_unknown_diagnostic(
                "Seq<BitVec> with interpreted BV element expressions cannot be independently model-validated",
            );
            return Ok(SolveResult::Unknown);
        }
        if self.sat_validated_by_mod_div_or_branch && has_native_seq_ops {
            self.last_statistics.model_validation_failures += 1;
            tracing::debug!("Seq SAT from mod/div shortcut, degrading to Unknown");
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.last_result = Some(SolveResult::Unknown);
            self.record_model_validation_unknown_diagnostic(
                "Seq SAT from mod/div shortcut cannot be independently model-validated",
            );
            return Ok(SolveResult::Unknown);
        }
        // (#bug18) A SELF-REFERENTIAL seq.extract definition `(= v (seq.extract S
        // I N))` whose source `S` transitively mentions `v` (e.g.
        // `s1 = (seq.extract ([-1].[2].s1) 0 5)`) pins `len(v)` through a
        // `min(N, len(S))` fixpoint the combined seq solver does not resolve, so a
        // returned SAT model (typically the empty default for `v`) does not
        // satisfy the definition. AY already returns Unknown for the definition in
        // isolation; fail closed to Unknown here so the extra ground assertions
        // cannot manufacture a spurious SAT around the unvalidated definition.
        if has_seq_terms && self.has_self_referential_seq_extract() {
            self.last_statistics.model_validation_failures += 1;
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.last_result = Some(SolveResult::Unknown);
            self.record_model_validation_unknown_diagnostic(
                "self-referential seq.extract definition cannot be independently model-validated",
            );
            return Ok(SolveResult::Unknown);
        }

        if self.sat_validated_by_mod_div_or_branch {
            // #div0-soundness: The mod/div bypass exists ONLY because the model
            // evaluator returns Unknown on an under-specified zero-divisor
            // `(mod a 0)`/`(div a 0)` term, whose value is unspecified per
            // SMT-LIB. It must NOT accept a model that DEFINITIVELY violates the
            // (eliminated) constraints — in particular the SMT-LIB division
            // axioms emitted for each mod/div, or any surrounding linear/
            // nonlinear assertion. The eliminated assertion set (`self.ctx.assertions`
            // here) carries those axioms (`x = x*q + r ∧ 0 ≤ r < |x|`, etc.); a
            // model whose `q`/`r` violate the axiom — or whose div/mod value
            // (carried as a fresh var) makes a downstream assertion false — makes
            // the corresponding assertion evaluate to a definitive `Bool(false)`.
            //
            // Genuinely-zero-divisor sub-terms are unconstrained, so any
            // assertion that depends on one evaluates to `Unknown` (never
            // `Bool(false)`) and is correctly left unvalidated here; only an
            // assertion the evaluator CAN decide to be false is rejected. This
            // closes the wrong-SAT where the solver returned `(div y z)=1` for
            // `y=0,z=-1` (axiom-violating) and used the bogus value to satisfy a
            // surrounding constraint, while keeping every genuine zero-divisor
            // SAT decided.
            let definitive_false = self.last_model.as_ref().and_then(|model| {
                self.ctx.assertions.iter().copied().find(|&assertion| {
                    matches!(
                        self.evaluate_term(model, assertion),
                        crate::executor::model::EvalValue::Bool(false)
                    )
                })
            });
            if let Some(assertion) = definitive_false {
                self.last_statistics.model_validation_failures += 1;
                tracing::warn!(
                    assertion = %self.format_term(assertion),
                    "mod/div bypass SAT degraded to Unknown: assertion evaluates definitively false under model"
                );
                self.last_model = None;
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.last_result = Some(SolveResult::Unknown);
                self.record_model_validation_unknown_diagnostic(
                    "mod/div bypass rejected: an eliminated assertion is definitively false under the model",
                );
                return Ok(SolveResult::Unknown);
            }
            // Fail-closed self-check: the mod/div OR-branch accepts SAT from a
            // syntactically stronger branch without fully replaying the original
            // (symbolic-division-bearing) assertions, so AY has not certified
            // this model itself. Degrade to a sound `unknown` under --self-check.
            if self.self_check {
                self.last_statistics.model_validation_failures += 1;
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.last_result = Some(SolveResult::Unknown);
                self.record_model_validation_unknown_diagnostic(
                    "self-check: SAT via symbolic mod/div OR branch is not independently certified",
                );
                return Ok(SolveResult::Unknown);
            }
            self.last_statistics.model_validation_skips += 1;
            self.last_model_validated = true;
            tracing::debug!(
                "finalize_sat_model_validation accepted SAT from stronger symbolic mod/div OR branch"
            );
            return Ok(SolveResult::Sat);
        }

        if self.defer_model_validation || self.skip_model_eval {
            // #8165: Track model validation skips.
            self.last_statistics.model_validation_skips += 1;
            // Log which validation skip path is active for debuggability.
            tracing::debug!(
                defer_model_validation = self.defer_model_validation,
                skip_model_eval = self.skip_model_eval,
                "finalize_sat_model_validation skipped (validation deferred or model eval unsupported)"
            );
            // #7912: Even when full model evaluation is skipped (trivially-empty
            // assertions, incremental inner solves), verify the SAT boolean skeleton
            // in ALL build modes. Every assertion with a term_to_var mapping must be
            // true in the SAT model. This catches Tseitin encoding bugs and SAT-level
            // unsoundness without requiring theory model eval.
            if self.skip_model_eval {
                let skeleton =
                    self.verify_boolean_skeleton("finalize_sat_model_validation/skip_model_eval");
                if skeleton.violations > 0 {
                    // Boolean skeleton violated — the SAT model contradicts the
                    // Tseitin encoding. This is a real soundness bug; degrade to
                    // Unknown rather than returning a provably-wrong SAT.
                    tracing::warn!(
                        violations = skeleton.violations,
                        verified = skeleton.verified,
                        unmapped = skeleton.unmapped,
                        total = skeleton.total,
                        "skip_model_eval SAT degraded to Unknown: boolean skeleton violated"
                    );
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    self.last_result = Some(SolveResult::Unknown);
                    self.record_model_validation_unknown_diagnostic(format!(
                        "boolean skeleton violated during skipped model evaluation: violations={}",
                        skeleton.violations
                    ));
                    return Ok(SolveResult::Unknown);
                }
                // Skeleton passed — log unverified theory-level assertions.
                if skeleton.unmapped > 0 {
                    tracing::debug!(
                        verified = skeleton.verified,
                        unmapped = skeleton.unmapped,
                        total = skeleton.total,
                        "skip_model_eval: boolean skeleton OK, {} assertions unverifiable \
                         at SAT level (theory model eval unavailable)",
                        skeleton.unmapped,
                    );
                }
                // Also keep the debug_assert for backwards compatibility.
                #[cfg(debug_assertions)]
                self.debug_assert_boolean_skeleton(
                    "finalize_sat_model_validation/skip_model_eval/debug",
                );
            }
            return Ok(SolveResult::Sat);
        }

        // Materialize concrete witness strings for under-constrained string
        // variables BEFORE model validation (#str-witness). A string variable
        // pinned only by its `str.len` LIA proxy (or by prefix/suffix/char-at
        // constraints) otherwise prints as the default "" — a value whose
        // length violates the proxy. `materialize_string_witnesses` builds a
        // concrete witness of the required length with all forced positions
        // pinned, then strictly re-validates it by full substitution. If a
        // consistent witness cannot be constructed, it returns false and we
        // fail closed: degrade SAT to Unknown rather than print an invalid
        // model. Soundness: the materialized model is re-checked below by the
        // normal validation pipeline AND by the internal strict substitution
        // check, so no `sat` can print a model that violates the assertions.
        if !self.materialize_string_witnesses() {
            self.last_statistics.model_validation_failures += 1;
            tracing::warn!(
                "SAT degraded to Unknown: could not materialize a valid string witness \
                 (under-constrained string variable, #str-witness)"
            );
            self.last_model = None;
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.last_result = Some(SolveResult::Unknown);
            self.record_model_validation_unknown_diagnostic(
                "could not materialize a valid string witness for an under-constrained variable",
            );
            return Ok(SolveResult::Unknown);
        }

        // Materialize a self-consistent array interpretation for finite-set
        // carriers (#set-model-witness). A set `s : (Set T)` is modelled on
        // `(Array T Bool)`; membership atoms `(set.member e s)` elaborate to
        // SAT-assigned `(select s e)` literals that the Set+LIA solver does not
        // reconstruct into an `ArrayInterpretation`. Without this, get-model
        // prints the bare default const-array (the EMPTY set) while
        // `(get-value ((select s e)))` reports the SAT-assigned `true` — the two
        // disagree and the printed model violates `(set.member e s)`.
        // `materialize_set_witnesses` records store entries `e -> true/false`
        // matching exactly the per-atom values get-value returns, so the printed
        // store chain and get-value stay in lockstep. It only augments the
        // printed interpretation (never the SAT/UNSAT verdict), and the model is
        // re-validated by the normal pipeline below.
        //
        // The same pass also makes the carrier exhibit the CARDINALITY the model
        // assigns to its `set.card` term (#set-card-model-witness): a free set
        // constrained only by `(= 1 (set.card s))` probes no membership at all,
        // so it used to print the empty set while `(get-value ((set.card s)))`
        // answered 1. When no valid witness can be built (an uninterpreted
        // element sort with no enumerable universe, a cardinality larger than
        // the domain, contradictory pinned cells) it returns false and we fail
        // closed: `unknown` is sound, a `sat` whose model falsifies its own
        // assertion is not.
        if !self.materialize_set_witnesses() {
            self.last_statistics.model_validation_failures += 1;
            tracing::warn!(
                "SAT degraded to Unknown: could not materialize a finite-set carrier of the \
                 required cardinality (#set-card-model-witness)"
            );
            self.last_model = None;
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.last_result = Some(SolveResult::Unknown);
            self.record_model_validation_unknown_diagnostic(
                "could not materialize a finite-set witness of the required cardinality",
            );
            return Ok(SolveResult::Unknown);
        }

        // (#mixed-combo-WS) String content sourced from an Array `select` is opaque
        // to the string theory; AY's array-string model defaults the select to ""
        // with an inconsistent length, so a string-CONTENT assertion over it (e.g.
        // `(= (select a i) (str.++ (select a i) "z"))`) is wrongly SAT. When a
        // string-content assertion contains a String-sorted `select` that the model
        // cannot resolve (EvalValue::Unknown), the SAT model is not independently
        // validatable -> fail closed to Unknown. Pure `(= (str.len (select a i)) k)`
        // Int-context assertions are NOT string-content and stay SAT. No test uses
        // `(Array _ String)`, so this cannot regress the suite.
        let mixed_string_array_unknown = matches!(self.last_result, Some(SolveResult::Sat))
            && self
                .last_model
                .as_ref()
                .is_some_and(|m| self.has_array_sourced_string_content_unknown(m));
        if mixed_string_array_unknown {
            self.last_statistics.model_validation_failures += 1;
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.last_result = Some(SolveResult::Unknown);
            self.record_model_validation_unknown_diagnostic(
                "string content sourced from an array select cannot be independently model-validated (mixed string-over-array)",
            );
            return Ok(SolveResult::Unknown);
        }

        let attempt = self.validate_model_attempt();
        // Preserve exact failure provenance before consuming the attempt. The
        // independent-array handoff below is deliberately available only when
        // the assertion that defeated the canonical evaluator itself contains
        // an array; an unrelated array elsewhere in the query is not enough.
        let failed_assertion_has_array =
            failed_assertion_contains_array(&self.ctx.terms, attempt.failed_assertion);
        // Same provenance discipline for the datatype handoff below
        // (#dt-completion-gate-handoff): only the assertion that actually
        // defeated the canonical evaluator authorizes deferring to the
        // independent gate, not an unrelated datatype elsewhere in the query.
        let failed_assertion_has_datatype = attempt
            .failed_assertion
            .is_some_and(|assertion| self.contains_datatype_term(assertion));
        self.last_validation_stats = match attempt.error.as_ref() {
            None | Some(ModelValidationError::Incomplete(_)) => attempt.stats.clone(),
            Some(ModelValidationError::Violated(_)) => None,
        };
        if let Some(stats) = self.last_validation_stats.clone() {
            self.record_model_validation_stats(&stats);
        }
        match attempt.into_result() {
            Ok(stats) => {
                tracing::debug!(
                    checked = stats.checked,
                    sat_fallback = stats.sat_fallback_count,
                    skipped_internal = stats.skipped_internal,
                    skipped_quantifier = stats.skipped_quantifier,
                    skipped_datatype = stats.skipped_datatype,
                    skipped_dtbv = stats.skipped_dtbv,
                    skipped_arith_array_mix = stats.skipped_arith_array_mix,
                    total = stats.total,
                    "finalized SAT model validation"
                );
                let (_, _, incomplete) = stats.verification_evidence_counts();
                // Fail-closed self-check (`--self-check`): only emit `sat` when
                // AY independently confirmed every assertion under the model
                // (or a theory solver vouched for it). Any assertion that was
                // skipped or only accepted via a SAT-agrees fallback means AY
                // could NOT verify the model itself, so we degrade to a sound
                // `unknown` rather than emit an unchecked `sat`. This is what
                // turns "AY says sat but can't prove it" into a self-certified
                // answer — the wrong-SAT bugs surface here as `incomplete > 0`.
                // Rescue path (#selfcert-authored): before degrading, demand a
                // POSITIVE certificate — every assertion the USER authored
                // evaluates to `true` under the emitted model. See
                // `self_check_authored_model_certified`.
                let authored_certified =
                    self.self_check && incomplete > 0 && self.self_check_authored_model_certified();
                if authored_certified {
                    self.last_statistics
                        .set_int("self_check.authored_certified", 1);
                }
                if self.self_check && incomplete > 0 && !authored_certified {
                    self.last_statistics.model_validation_failures += 1;
                    tracing::warn!(
                        incomplete,
                        checked = stats.checked,
                        total = stats.total,
                        "self-check: SAT not independently certified, degrading to Unknown"
                    );
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    self.last_result = Some(SolveResult::Unknown);
                    self.record_model_validation_unknown_diagnostic(format!(
                        "self-check: model could not be independently certified \
                         ({incomplete} of {} assertion(s) unverified)",
                        stats.total
                    ));
                    return Ok(SolveResult::Unknown);
                }
                // (#mixed-seq-dt-skip-scope) The skip counter is CUMULATIVE
                // across nested probe solves and prior check-sats; a stale skip
                // from an unrelated pass degraded a model this pass had
                // certified INDEPENDENTLY and in FULL (incomplete == 0). Scope
                // it: only a skip taken for THIS finalization is evidence that
                // THIS model went unchecked. (The skip paths above all return
                // early, so this is precisely the intended reading.)
                let skipped_this_pass =
                    self.last_statistics.model_validation_skips > skips_before_finalize;
                if mixed_seq_datatype && (incomplete > 0 || skipped_this_pass) {
                    self.last_statistics.model_validation_failures += 1;
                    tracing::debug!(
                        incomplete,
                        validation_skips = self.last_statistics.model_validation_skips,
                        "mixed Seq+datatype SAT validation incomplete, degrading to Unknown"
                    );
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    self.last_result = Some(SolveResult::Unknown);
                    self.record_model_validation_unknown_diagnostic(format!(
                        "mixed Seq+datatype SAT validation incomplete: incomplete={incomplete}, validation_skips={}",
                        self.last_statistics.model_validation_skips
                    ));
                    return Ok(SolveResult::Unknown);
                }
                self.last_model_validated = true;
                Ok(SolveResult::Sat)
            }
            Err(e @ ModelValidationError::Incomplete(_)) => {
                // The canonical evaluator is intentionally incomplete for some
                // extensional array models: a pair of otherwise-free arrays
                // constrained only by `(= a b)` has no finite store/default
                // reconstruction and therefore evaluates to `Unknown`. That is
                // not a refutation. Give the independent, fail-closed model gate
                // authority to close only this array-bearing ground-assertion
                // gap. `ConfirmedSat` means it independently re-evaluated every
                // assertion as true; `ModelViolates` and `CannotConfirm` still
                // take the existing sound Unknown path below.
                let array_ground_gap = e.failure().boundary
                    == VerificationBoundary::SmtGroundAssertion
                    && failed_assertion_has_array;
                // (#dt-completion-gate-handoff) The z3-audit DT fail-close layer
                // (779d8f9e, observation.rs) degrades a compound Boolean whose
                // embedded datatype-reconstruction (dis)equality it cannot
                // independently confirm under the DT+BV bit-blast: the masked
                // three-valued eval returns `None` when the verdict necessarily
                // rests on an uncertified EUF-identity truth value. That layer
                // predates the mv-printer-package e-graph value assignment
                // (merge 547590f8): on models whose DT values are
                // COMPLETION-CONSTRUCTED from the DT lane's exported e-graph,
                // the canonical evaluator cannot re-ground the selector chains,
                // so the masked eval stays `None` even though the witness is
                // fully concrete — 166 Barrett QF_DT sats fail-closed to
                // unknown (bisected to 547590f8; both parents answered sat, the
                // branch line via model_check_gate.result=confirmed-sat).
                // Give the INDEPENDENT, fail-closed gate the same authority the
                // array handoff above already has: it re-evaluates EVERY
                // assertion against the exact emitted witness with finite-tree
                // datatype semantics — constructor congruence and acyclicity
                // hold BY CONSTRUCTION over `ModelValue::Datatype` trees, so a
                // cyclic commitment (the false-SAT class 779d8f9e fail-closes)
                // can never be confirmed: no finite trees satisfy it, and the
                // gate answers ModelViolates/CannotConfirm, which still degrade
                // below. This is genuine independent confirmation, not a
                // weakening of the fail-close oracle.
                let dt_ground_gap = e.failure().boundary
                    == VerificationBoundary::SmtGroundAssertion
                    && failed_assertion_has_datatype;
                if (array_ground_gap || dt_ground_gap)
                    && matches!(
                        self.confirm_sat_with_independent_gate(),
                        ay_model_check::GateVerdict::ConfirmedSat
                    )
                {
                    let total = self.flatten_assertion_conjunctions().len();
                    let stats = ValidationStats {
                        checked: total,
                        total,
                        ..Default::default()
                    };
                    self.record_model_validation_stats(&stats);
                    self.last_validation_stats = Some(stats);
                    if array_ground_gap {
                        self.last_statistics
                            .set_int("model_validation.independent_array_handoff", 1);
                    }
                    if dt_ground_gap {
                        self.last_statistics
                            .set_int("model_validation.independent_dt_handoff", 1);
                    }
                    self.last_model_validated = true;
                    tracing::debug!(
                        "canonical model validation was incomplete on an array/datatype \
                         ground assertion; independent gate confirmed every assertion"
                    );
                    return Ok(SolveResult::Sat);
                }
                // (#dt-egraph-validation-retry) This finalization may be
                // running inside `solve_and_store_model_full`, where the DT
                // lane's e-graph export is deliberately stashed aside — the
                // gate above then cannot read the single-source per-class
                // values and answers CannotConfirm even for a witness the
                // emit-time gate would confirm. Ask the storing caller to
                // attach the export and re-run finalization once. Sound: the
                // retry can only end in the SAME fail-closed arms; it merely
                // lets the independent gate see the values the printer emits.
                if dt_ground_gap {
                    self.dt_validation_wants_egraph = true;
                }
                // #8165: Track model validation failures.
                self.last_statistics.model_validation_failures += 1;
                tracing::debug!(error = %e, "model validation incomplete, degrading to Unknown");
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.last_result = Some(SolveResult::Unknown);
                self.record_model_validation_unknown_diagnostic(format!(
                    "model validation incomplete: {:?}: {}",
                    e.failure().boundary,
                    e.failure().detail
                ));
                Ok(SolveResult::Unknown)
            }
            Err(e @ ModelValidationError::Violated(_)) => {
                // #g4-dt-defer (general validator): on a datatype-carrying-array
                // problem, the observation pipeline can evaluate a
                // read-over-equality / McCarthy-congruence assertion false because
                // ay's array-model RECONSTRUCTION is internally inconsistent (a
                // ROW2 gap: two arrays asserted equal whose reconstructed reads
                // disagree) — NOT because the query is unsatisfiable. The
                // INDEPENDENT, fail-closed gate resolves such assertions through
                // its extensionality-merge (equal arrays share one reconstructed
                // value) + model-independent tautology normalizer and re-checks
                // EVERY assertion; a `ConfirmedSat` there is a proof a consistent
                // model exists (z3-cross-checked). Defer to it — keep the SAT only
                // on ConfirmedSat; `ModelViolates` / `CannotConfirm` still degrade
                // below (fail-closed). Scoped to datatype-carrying-array problems.
                if self.problem_has_datatype_carrying_array()
                    && matches!(
                        self.confirm_sat_with_independent_gate(),
                        ay_model_check::GateVerdict::ConfirmedSat
                    )
                {
                    self.last_model_validated = true;
                    return Ok(SolveResult::Sat);
                }
                // #8373: Degrade Violated to Unknown instead of hard error.
                //
                // When the theory solver says SAT but the model violates an
                // original assertion, this indicates theory incompleteness
                // (e.g., ITE terms with pure Boolean conditions that the
                // LRA theory over-approximates as fresh variables). Returning
                // Unknown is always sound and lets the solver continue or
                // report "unknown" instead of crashing with an error.
                //
                // The hard error was a development diagnostic that leaked
                // into production. In a sound solver, a failed model
                // validation should produce Unknown, not an error.
                self.last_statistics.model_validation_failures += 1;
                tracing::warn!(error = %e, "model validation violated, degrading to Unknown (#8373)");
                self.last_model = None;
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.last_result = Some(SolveResult::Unknown);
                self.record_model_validation_unknown_diagnostic(format!(
                    "model validation violated: {:?}: {}",
                    e.failure().boundary,
                    e.failure().detail
                ));
                Ok(SolveResult::Unknown)
            }
        }
    }

    /// Finalize SAT validation for assumption-based checks.
    ///
    /// Both `Incomplete` and `Violated` errors degrade SAT to `Unknown`. A
    /// `Violated` assumption against a fill-completed model is a completion
    /// artifact (e.g. an assumption like `len == 3` that is false on a
    /// 0-defaulted completion model), not a soundness signal, so it must not
    /// surface as a hard `ExecutorError::ModelValidation` (which `check.rs`
    /// maps to `Unknown(InternalError)`). This mirrors the plain
    /// `finalize_sat_model_validation` path, which already degrades the
    /// analogous `Violated` completion-artifact case to `Unknown(Incomplete)`
    /// (#8373).
    pub(in crate::executor) fn finalize_sat_assumption_validation(
        &mut self,
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        // Same fill-only model completion as finalize_sat_model_validation
        // so assumption evaluation sees a total model (see completion.rs).
        self.complete_model_for_validation(assumptions);
        match self.validate_sat_assumptions(assumptions) {
            Ok(()) => Ok(SolveResult::Sat),
            Err(e @ ModelValidationError::Incomplete(_)) => {
                tracing::debug!(error = %e, "assumption validation incomplete, degrading to Unknown");
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.last_result = Some(SolveResult::Unknown);
                Ok(SolveResult::Unknown)
            }
            Err(e @ ModelValidationError::Violated(_)) => {
                // Degrade Violated to Unknown instead of a hard error, matching
                // the plain validation path (#8373). A Violated assumption on a
                // fill-completed model reflects completion-model incompleteness
                // (e.g. an assumption that is false only because an unconstrained
                // term was defaulted), not unsoundness. Returning Unknown is
                // always sound: it never turns a genuine SAT or UNSAT answer
                // into the opposite, it only removes a spurious InternalError.
                self.last_statistics.model_validation_failures += 1;
                tracing::warn!(error = %e, "assumption validation violated, degrading to Unknown");
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.last_result = Some(SolveResult::Unknown);
                self.record_model_validation_unknown_diagnostic(format!(
                    "assumption validation violated: {:?}: {}",
                    e.failure().boundary,
                    e.failure().detail
                ));
                Ok(SolveResult::Unknown)
            }
        }
    }
}

#[cfg(test)]
mod scoped_authority_tests;

#[cfg(test)]
mod failed_assertion_provenance_tests {
    use super::*;
    use ay_core::{Sort, Symbol};

    #[test]
    fn asserted_bool_leaf_repair_pins_restored_positive_polarity() {
        let mut executor = Executor::new();
        let asserted = executor.ctx.terms.mk_var("restored", Sort::Bool);
        executor.ctx.assertions.push(asserted);
        executor.last_result = Some(SolveResult::Sat);
        executor.last_model_validated = true;
        let mut model = crate::executor::model::Model::empty();
        model.sat_model = vec![false];
        model.term_to_var.insert(asserted, 0);
        executor.last_model = Some(model);

        executor.repair_asserted_bool_leaf_polarities();

        let model = executor.last_model.as_ref().expect("candidate model");
        assert_eq!(
            executor.evaluate_term(model, asserted),
            crate::executor::model::EvalValue::Bool(true)
        );
        assert!(
            !executor.last_model_validated,
            "mutating the witness must invalidate prior validation evidence"
        );
    }

    #[test]
    fn asserted_bool_leaf_repair_does_not_mask_opposite_polarities() {
        let mut executor = Executor::new();
        let asserted = executor.ctx.terms.mk_var("contradictory", Sort::Bool);
        let negated = executor.ctx.terms.mk_not(asserted);
        executor.ctx.assertions.extend([asserted, negated]);
        executor.last_result = Some(SolveResult::Sat);
        executor.last_model_validated = true;
        let mut model = crate::executor::model::Model::empty();
        model.sat_model = vec![false, true];
        model.term_to_var.insert(asserted, 0);
        model.term_to_var.insert(negated, 1);
        executor.last_model = Some(model);

        executor.repair_asserted_bool_leaf_polarities();

        let model = executor.last_model.as_ref().expect("candidate model");
        assert_eq!(
            executor.evaluate_term(model, asserted),
            crate::executor::model::EvalValue::Bool(false)
        );
        assert!(
            executor.last_model_validated,
            "a conflicting requirement must not mutate the candidate"
        );
    }

    #[test]
    fn independent_array_handoff_uses_failed_leaf_not_unrelated_array() {
        let mut terms = ay_core::term::TermStore::new();
        let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let zero = terms.mk_int(0.into());
        let array_read = terms.mk_select(array, zero);
        let unrelated_array_assertion = terms.mk_eq(array_read, zero);
        let x = terms.mk_var("x", Sort::Int);
        let scalar_failed_assertion = terms.mk_app(Symbol::named("P"), vec![x], Sort::Bool);

        assert!(
            StaticFeatures::collect(
                &terms,
                &[unrelated_array_assertion, scalar_failed_assertion]
            )
            .has_arrays,
            "the overall problem must contain an array for this regression"
        );
        assert!(failed_assertion_contains_array(
            &terms,
            Some(unrelated_array_assertion)
        ));
        assert!(
            !failed_assertion_contains_array(&terms, Some(scalar_failed_assertion)),
            "an unrelated array must not authorize handoff of a scalar failure"
        );
        assert!(!failed_assertion_contains_array(&terms, None));
    }
}
