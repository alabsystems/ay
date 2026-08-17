// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unified result acceptance pipeline for portfolio engine results.
//!
//!
//! Both `solve_parallel` and `solve_sequential` run the same 5-step
//! soundness guard before accepting an engine result. This module
//! contains that logic in a single place so soundness fixes land once.

use super::*;

/// Drop guard that logs total accept_or_reject duration under
/// --chc-accept-profile regardless of which early-return path fires.
struct AcceptProfileSpan {
    enabled: bool,
    start: ay_core::time::Instant,
    engine: String,
}

impl Drop for AcceptProfileSpan {
    fn drop(&mut self) {
        if self.enabled {
            safe_eprintln!(
                "[ACCEPT-PROF] accept_or_reject end engine={} dt={:.3}s",
                self.engine,
                self.start.elapsed().as_secs_f64()
            );
        }
    }
}

fn scopeguard_accept_profile(
    enabled: bool,
    start: ay_core::time::Instant,
    engine: &str,
) -> AcceptProfileSpan {
    AcceptProfileSpan {
        enabled,
        start,
        engine: engine.to_string(),
    }
}

/// Result acceptance decision for a single engine result.
#[derive(Debug)]
pub(crate) enum AcceptDecision {
    /// Accept this result — return to caller.
    Accept(PortfolioResult),
    /// Reject this result — try next engine.
    Reject,
}

impl PortfolioSolver {
    /// Unified soundness guard pipeline for engine results.
    ///
    /// Called by both `solve_parallel` and `solve_sequential` after
    /// `convert_engine_result`. Contains ALL acceptance/rejection logic
    /// in one place so soundness fixes land once.
    ///
    /// Five-step pipeline:
    /// 1. BV-abstracted Unsafe confirmation
    /// 2. BMC witness-less multi-predicate rejection (#6800)
    /// 3. Skeleton Unsafe rejection (no witness, empty assignments)
    /// 4. Always-on Unsafe validation (#8585, was opt-in via config.validate)
    /// 5. Mandatory Safe full validation (#6787, #6824)
    pub(crate) fn accept_or_reject(
        &self,
        mut result: PortfolioResult,
        mut needs_validation: bool,
        engine_name: &str,
        engine_idx: usize,
    ) -> AcceptDecision {
        let profile = crate::transform::accept_profile_enabled();
        let t_accept = ay_core::time::Instant::now();
        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] accept_or_reject start engine={} idx={} kind={}",
                engine_name,
                engine_idx,
                match &result {
                    PortfolioResult::Safe(_) => "Safe",
                    PortfolioResult::Unsafe(_) => "Unsafe",
                    _ => "other",
                }
            );
        }
        let _accept_span = scopeguard_accept_profile(profile, t_accept, engine_name);
        // Step 1: BV-abstracted Unsafe confirmation
        if self.bv_abstracted {
            if let PortfolioResult::Unsafe(cex) = &result {
                let Some(confirmed) =
                    self.confirm_bv_abstracted_unsafe(cex, engine_idx, engine_name)
                else {
                    return AcceptDecision::Reject;
                };
                result = confirmed;
                needs_validation = false;
            }
        }

        // Step 2 (#6800): Reject witness-less BMC Unsafe on multi-predicate
        // problems. BMC produces a flat list of per-level assignments with
        // predicate=0 for every step, which cannot justify a multi-predicate
        // Unsafe. Uses engine_problem() (not original_problem) because
        // preprocessing may reduce predicates.
        if engine_name == "BMC" {
            if let PortfolioResult::Unsafe(cex) = &result {
                let engine_pred_count = self.engine_problem().predicates().len();
                if cex.witness.is_none() && engine_pred_count > 1 {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Engine {} (BMC) witness-less Unsafe suppressed on multi-predicate problem ({} predicates)",
                            engine_idx, engine_pred_count
                        );
                    }
                    return AcceptDecision::Reject;
                }
            }
        }

        // Early bail if cancelled before expensive validation steps (#8630).
        if self.cancellation_token.is_cancelled() {
            return AcceptDecision::Reject;
        }

        // Step 3: Reject skeleton Unsafe results (no witness, empty
        // assignments) unconditionally. Engines like PDKIND produce skeleton
        // counterexamples that cannot be independently verified without
        // validation (#2273, #5010).
        //
        // On success the result carries the back-translated counterexample
        // that actually passed original-clause replay (FM2b — mirror of Fix
        // B1 for Safe models), and step 4 is skipped to avoid re-translating
        // an already-translated counterexample.
        if let PortfolioResult::Unsafe(cex) = &result {
            if cex.witness.is_none() && cex.steps.iter().all(|s| s.assignments.is_empty()) {
                match self.validate_unsafe_translating(cex) {
                    Ok(translated_cex) => {
                        // Skeleton verified — accept the translated witness.
                        result = PortfolioResult::Unsafe(translated_cex);
                        needs_validation = false;
                    }
                    Err(reason) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Portfolio: Engine {} ({}) skeleton Unsafe rejected: {}",
                                engine_idx,
                                engine_name,
                                reason
                            );
                        }
                        return AcceptDecision::Reject;
                    }
                }
            }
        }

        // Step 4: Always validate Unsafe results before accepting (#429, #5213, #8585).
        // Safe results handled by mandatory full validation below (#6824).
        //
        // SOUNDNESS FIX #8585: Unsafe validation is now always-on. Previously gated
        // on `config.validate` (default: false), meaning wrong Unsafe results
        // silently escaped. The config.validate gate has been removed.
        //
        // On success the result carries the back-translated counterexample
        // that passed original-clause replay (FM2b): the adaptive layer's
        // final verified-result validation runs with an identity translator
        // (`enable_preprocessing: false`), so an engine-space counterexample
        // would replay transform-space metadata against the original problem
        // and be demoted to Unknown.
        if needs_validation {
            if let PortfolioResult::Unsafe(cex) = &result {
                match self.validate_unsafe_translating(cex) {
                    Ok(translated_cex) => {
                        // Validation passed — accept the translated witness.
                        result = PortfolioResult::Unsafe(translated_cex);
                    }
                    Err(reason) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Portfolio: Engine {} ({}) Unsafe result failed validation: {}, continuing",
                                engine_idx, engine_name, reason
                            );
                        }
                        return AcceptDecision::Reject;
                    }
                }
            }
        }

        // Step 4.20: Empty-model acyclic BMC Safe admission.
        //
        // `BMC_ACYCLIC_EXHAUSTIVE` means BMC exhausted its configured DAG bound
        // and returned Safe without an invariant model. This is complete for a
        // Bool/Int-only acyclic predicate DAG. #9227 showed the same shape is
        // not proof-grade for richer theories, so BV, Array, Real, and Datatype
        // state still fails closed.
        if engine_name == "BMC_ACYCLIC_EXHAUSTIVE"
            && matches!(&result, PortfolioResult::Safe(model) if model.is_empty())
        {
            let theory_proof_grade = !self.problem.has_array_sorts()
                && !self.problem.has_bv_sorts()
                && !self.problem.has_real_sorts()
                && !self.problem.has_datatype_sorts();

            if theory_proof_grade && self.transform_memory.is_identity_grade() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Engine {} accepted Bool/Int acyclic exhaustive BMC Safe proof",
                        engine_idx
                    );
                }
                return AcceptDecision::Accept(result);
            }

            if theory_proof_grade {
                // MUST-FIX B (rank-6 review, narrow Safe bypass): the
                // exhaustiveness argument covers the TRANSFORMED problem only.
                // With a non-identity transform stack, the empty model carries
                // no evidence about the ORIGINAL clauses, so do NOT early
                // return. Fall through to Step 5, which back-translates the
                // model and validates it against the original problem; an
                // empty model that back-translation cannot complete is
                // rejected there (fail closed).
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Engine {} acyclic exhaustive BMC empty-model Safe on \
                         non-identity transform stack; deferring to original validation \
                         (Step 5)",
                        engine_idx
                    );
                }
            } else {
                tracing::warn!(
                    engine_idx,
                    "rejecting acyclic exhaustive BMC empty-model Safe over non-Bool/Int state: no proof-grade invariant/replay evidence (#9227)"
                );
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Engine {} returned acyclic exhaustive BMC empty-model Safe over non-Bool/Int state; \
                         rejecting — no proof-grade invariant/replay evidence (#9227)",
                        engine_idx
                    );
                }
                return AcceptDecision::Reject;
            }
        }

        // Step 4.25: BMC empty-model Safe rejection (#8585).
        //
        // SOUNDNESS FIX #8585: BMC empty-model Safe results are always rejected.
        // BMC acyclic exhaustion without an invariant model is an unverifiable
        // proof. The correct response is Unknown. Previously this was accepted
        // unless strict_proofs was set; now strict_proofs behavior is the default.
        if engine_name == "BMC"
            && matches!(&result, PortfolioResult::Safe(model) if model.is_empty())
        {
            tracing::warn!(
                engine_idx,
                "rejecting BMC empty-model Safe: no invariant model for verification (#8585)"
            );
            if self.config.verbose {
                safe_eprintln!(
                    "Portfolio: Engine {} (BMC) returned empty-model Safe from acyclic exhaustion; \
                     rejecting — unverifiable without invariant model (#8585)",
                    engine_idx
                );
            }
            return AcceptDecision::Reject;
        }

        // Step 4.5 (#6787): Fast query-only pre-check for Safe results.
        // Catches tautological false-Safe where the invariant is literally the
        // negated query (#6789). This is a syntactic check that avoids the
        // expensive full validation when the model is obviously wrong.
        //
        // EXCEPTION (#1306): An invariant that equals exact `not(query)` is
        // ambiguous — it might be a genuine inductive invariant that happens
        // to match the negation of the query constraint. Query-only validation
        // cannot distinguish this case. Instead of hard-rejecting, defer to
        // Step 5 (full per-rule validation) which can check inductiveness.
        // Shared back-translation for Steps 4.5 and 5: the synthesized
        // interpretations for eliminated predicates are built ONCE and the
        // same translated model feeds both the query-only pre-check and
        // mandatory full validation. On graph-collapse stacks
        // (16-eliminated-predicate HOLA shapes) each translation costs the
        // full QE/synthesis pipeline, and translating twice doubled the
        // acceptance latency. Translation failure fails closed (Reject).
        let translated_for_validation = if let PortfolioResult::Safe(ref model) = result {
            match self.back_translate_safe_model(model) {
                Ok(translated) => Some(translated),
                Err(reason) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Engine {} ({}) Safe result failed back-translation: {}, rejecting",
                            engine_idx, engine_name, reason
                        );
                    }
                    return AcceptDecision::Reject;
                }
            }
        } else {
            None
        };

        if let Some(ref translated) = translated_for_validation {
            match self.validate_safe_query_only_pre_translated(translated) {
                SafePrecheckResult::Valid => {}
                SafePrecheckResult::ExactNegatedQuery(reason) => {
                    // Ambiguous: defer to Step 5 full validation (#1306)
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Engine {} ({}) Safe result is exact ¬query ({}); \
                             deferring to full validation (#1306)",
                            engine_idx,
                            engine_name,
                            reason
                        );
                    }
                }
                SafePrecheckResult::Invalid(reason) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Engine {} ({}) Safe result failed query-only validation: {}, continuing",
                            engine_idx, engine_name, reason
                        );
                    }
                    return AcceptDecision::Reject;
                }
            }
        }

        // Step 5 (#6787, #6824, #8585): Full validation for ALL Safe results.
        //
        // Query-only (step 4.5) checks that the invariant blocks bad states.
        // Full validation re-checks inductiveness w.r.t. transition clauses
        // in a fresh SMT context.
        //
        // #8585: Full validation is now mandatory for ALL engines, including
        // multi-predicate PDR/CEGAR. The trust-proof fallback that previously
        // accepted multi-pred PDR results despite validation failure has been
        // removed. If the result cannot be independently verified, it becomes
        // Unknown rather than a possibly-wrong Safe.
        //
        // #9227: `individually_inductive` is useful evidence, but it is not a
        // sound replacement for final validation against the original clauses.
        // Query-only validation only checks that the candidate blocks bad
        // states; it does not re-check initiation or transitions.
        if let Some(translated) = translated_for_validation {
            match self.validate_safe_with_mode_pre_translated(translated, ValidationBudget::PerRule)
            {
                Ok(translated_model) => {
                    // Fix B1 (stop discarding verified Safe results): the
                    // artifact that passed verification on the ORIGINAL
                    // problem is the back-translated model, which includes
                    // interpretations synthesized for predicates eliminated by
                    // preprocessing (e.g. ClauseInliner). Returning the
                    // engine-space model instead made the adaptive layer's
                    // final interpretation gate demote the verified Safe to
                    // Unknown (O0_sendmail-class regressions). Carry the
                    // verified model forward.
                    result = PortfolioResult::Safe(translated_model);
                }
                Err(reason) => {
                    // #8585: Full validation is mandatory for ALL engines. If the
                    // invariant model cannot be independently verified in a fresh
                    // context, reject the result. The trust-proof fallback for
                    // multi-predicate PDR/CEGAR has been removed.
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Engine {} ({}) Safe result failed mandatory full validation: {}, rejecting (#8585)",
                            engine_idx, engine_name,
                            reason
                        );
                    }
                    return AcceptDecision::Reject;
                }
            }
        }

        AcceptDecision::Accept(result)
    }
}
