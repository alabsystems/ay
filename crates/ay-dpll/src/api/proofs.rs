// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consumer-facing proof export API for UNSAT results.
//!
//! Provides [`UnsatProofArtifact`] as a consumer-facing proof artifact that
//! downstream consumers (downstream proof consumers) can use without linking
//! against executor internals, plus a native strict proof verdict and consumer
//! acceptance helpers. Use [`SerializableProofBundle`] for a self-contained,
//! offline-recheckable certificate; rendered Alethe may be an honest diagnostic
//! skeleton containing `hole`.

use ay_core::{AletheRule, ProofStep};
use ay_proof::{
    check_proof_collecting_trust_with_typed_context, check_proof_partial, check_proof_with_quality,
    AlethePrintError, DatatypeMemberSignature, PartialProofCheck, ProofCheckError, ProofQuality,
};
use num_rational::BigRational;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use crate::array_proof_check::{
    check_array_clause, check_array_clause_with_controls, ArrayStepVerdict,
};
use crate::bv_proof_check::{
    check_bv_assertions_unsat, check_bv_assertions_unsat_with_controls, check_bv_clause,
    check_bv_clause_with_controls, BvStepVerdict,
};

mod artifact_types;
pub use artifact_types::{FarkasCertificate, ProofAcceptanceMode};

mod exact_query;
pub use exact_query::ExactSmtlibQueryBinding;

mod bv_lia_source_replay;
use bv_lia_source_replay::discharge_source_bv_lia;

mod bv_int_bridge_schema;
use bv_int_bridge_schema::discharge_bv_int_bridge_schema;

/// Bail-point probe for [`discharge_trust_clause`], on the existing
/// `--probe-cert-reject` channel.
///
/// The per-clause discharge is a funnel of seven lanes that all return the same
/// `None`, so a rejection reports which clause failed but never which lane
/// declined it, nor whether a lane declined on evidence or on a budget — the
/// distinction this whole investigation turns on. The two nested-solve lanes
/// therefore also report the wall budget they ACTUALLY spent, which is what
/// showed their 1000 ms cutoff is never the operative bound (measured 2 ms and
/// 4 ms; they decline on the depth-0 re-entrancy guard). Lazily formatted; an
/// unset flag costs one field read.
fn probe_discharge(message: impl FnOnce() -> String) {
    if ay_core::misc_cli_flags().probe_cert_reject {
        eprintln!("--probe-cert-reject: discharge_trust_clause {}", message());
    }
}

/// Caller-owned resource envelope for the fresh executors used while
/// discharging one deferred-trust clause.
///
/// The ordinary proof-export API has no active solve transaction. Its legacy
/// specialized BV/array checks therefore remain unbounded, while its generic
/// replay/probe lanes retain their existing local one-second cap. The mandatory
/// UNSAT publication funnel supplies its live interrupt, absolute deadline, RSS
/// ceiling, and per-executor term-store ceiling so a corroborating solve cannot
/// silently escape the outer query's controls.
#[derive(Clone, Debug, Default)]
pub(crate) struct TrustClauseDischargeControls {
    pub(crate) interrupt: Option<Arc<AtomicBool>>,
    pub(crate) deadline: Option<ay_core::time::Instant>,
    pub(crate) memory_limit: Option<usize>,
    pub(crate) term_memory_limit: Option<usize>,
}

impl TrustClauseDischargeControls {
    fn exact_term_memory_exceeded(&self, terms: &ay_core::TermStore) -> bool {
        self.term_memory_limit
            .is_some_and(|limit| terms.true_memory_bytes() > limit)
    }

    fn stop_requested(&self, terms: &ay_core::TermStore) -> bool {
        self.interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
            || self
                .deadline
                .is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
            || crate::memory::memory_exceeded(self.memory_limit)
            || ay_sys::process_memory_exceeded()
            || ay_core::TermStore::global_memory_exceeded()
            || self
                .term_memory_limit
                .is_some_and(|limit| terms.instance_memory_exceeded(limit))
    }

    pub(crate) fn nested_deadline(&self) -> ay_core::time::Instant {
        let local = ay_core::time::Instant::now() + Duration::from_secs(1);
        self.deadline.map_or(local, |outer| outer.min(local))
    }

    fn accept_if_live(&self, terms: &ay_core::TermStore) -> Option<()> {
        (!self.stop_requested(terms) && !self.exact_term_memory_exceeded(terms)).then_some(())
    }

    pub(crate) fn live_until(
        &self,
        terms: &ay_core::TermStore,
        deadline: ay_core::time::Instant,
    ) -> bool {
        ay_core::time::Instant::now() < deadline && !self.stop_requested(terms)
    }

    pub(crate) fn accept_until(
        &self,
        terms: &ay_core::TermStore,
        deadline: ay_core::time::Instant,
    ) -> bool {
        self.live_until(terms, deadline) && !self.exact_term_memory_exceeded(terms)
    }

    pub(crate) fn term_store_clone_fits(
        &self,
        terms: &ay_core::TermStore,
        deadline: ay_core::time::Instant,
    ) -> bool {
        self.accept_until(terms, deadline)
            && crate::memory::probe_clone_fits(terms.true_memory_bytes(), self.memory_limit)
    }

    fn install_on(&self, executor: &mut crate::Executor, deadline: ay_core::time::Instant) -> bool {
        executor.set_memory_limit(self.memory_limit);
        executor.set_term_memory_limit(self.term_memory_limit);
        executor.set_solve_controls(self.interrupt.clone(), Some(deadline));
        self.accept_until(&executor.ctx.terms, deadline)
    }

    /// Install this publication envelope on a fresh native proof-checking
    /// solver before translation allocates into its private term store.
    pub(crate) fn start_native_solver(
        &self,
        solver: &mut super::Solver,
        deadline: ay_core::time::Instant,
    ) -> bool {
        solver.set_memory_limit(self.memory_limit);
        solver.set_term_memory_limit(self.term_memory_limit);
        self.native_solver_accepts(solver, deadline)
    }

    /// Poll both the caller controls and the fresh solver's own term store.
    pub(crate) fn native_solver_live(
        &self,
        solver: &super::Solver,
        deadline: ay_core::time::Instant,
    ) -> bool {
        self.live_until(solver.terms(), deadline)
    }

    fn native_solver_accepts(
        &self,
        solver: &super::Solver,
        deadline: ay_core::time::Instant,
    ) -> bool {
        self.accept_until(solver.terms(), deadline)
    }

    /// Run a fresh native internal query under the already-elapsing deadline.
    /// `None` means the envelope fired before or after the checked result.
    pub(crate) fn check_native_solver_until(
        &self,
        solver: &mut super::Solver,
        deadline: ay_core::time::Instant,
    ) -> Option<super::VerifiedSolveResult> {
        if !self.native_solver_accepts(solver, deadline) {
            return None;
        }
        let remaining = deadline.checked_duration_since(ay_core::time::Instant::now())?;
        solver.set_timeout(Some(remaining));
        let result = if let Some(interrupt) = self.interrupt.clone() {
            solver.check_sat_interruptible_internal_query(move || interrupt.load(Ordering::Relaxed))
        } else {
            solver.check_sat_internal_query()
        };
        self.native_solver_accepts(solver, deadline)
            .then_some(result)
    }
}

/// Exported strict-verification verdict for an UNSAT proof artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum StrictProofVerdict {
    /// AY's native proof-IR validation succeeded with the returned metrics.
    ///
    /// This verdict does not claim that an external checker accepted the
    /// rendered [`UnsatProofArtifact::alethe`] text. An internally supported
    /// inference can render there as an honest `hole` when the pinned Alethe
    /// calculus has no corresponding rule.
    Verified(ProofQuality),
    /// Strict proof validation rejected the artifact with a stable explanation.
    Rejected(String),
}

/// Error returned when an UNSAT proof artifact is not acceptable at a
/// consumer boundary.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ProofAcceptanceError {
    /// Strict proof validation failed.
    #[error("strict proof verification failed: {reason}")]
    StrictRejected {
        /// Stable rejection detail from the strict checker.
        reason: String,
    },
    /// Strict validation succeeded, but the proof is outside the restricted rule subset.
    #[error("proof is not in the restricted-rule-subset strict subset")]
    NotRestrictedRuleSubset,
}

/// A consumer-facing UNSAT proof artifact for downstream consumers.
///
/// Contains rendered Alethe proof text, diagnostic quality metrics, a native
/// strict proof verdict, and a restricted-rule-subset flag for consumers that need a
/// stricter acceptance boundary than the raw solver result.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
#[must_use]
pub struct UnsatProofArtifact {
    /// Diagnostic native-IR quality metrics: trust/hole/resolution/theory counts.
    ///
    /// This is a diagnostic summary. It does **not** imply full semantic
    /// verification — theory lemmas and generic rules are accepted as axioms.
    /// Use [`strict_verdict`](Self::strict_verdict) for the native strict verdict.
    /// These counts describe the native IR, so `hole_count` can be zero even
    /// when the rendered Alethe text contains a disclosed compatibility hole.
    pub quality: ProofQuality,
    /// Rendered Alethe proof text (SMT-LIB compatible).
    ///
    /// This may be an honestly holey diagnostic skeleton when AY's native
    /// strict checker supports an inference that the pinned external Alethe
    /// calculus does not. [`Self::strict_verdict`] reports validation of the
    /// native proof IR; it is not a claim that Carcara returned `valid` for
    /// this text. [`Self::restricted_rule_subset`] stays false for such artifacts.
    pub alethe: String,
    /// Exact SMT-LIB problem bytes authored for [`Self::alethe`].
    ///
    /// External-checker consumers must use this transport instead of
    /// reconstructing a problem from their own normalized formula. `None`
    /// means the current problem theory cannot yet be serialized without
    /// losing semantic identity; it does not weaken the independent native
    /// [`Self::strict_verdict`].
    pub alethe_problem_smt2: Option<String>,
    /// Partial check result from the internal checker.
    pub partial_check: Option<PartialProofCheck>,
    /// Consumer-visible verdict from AY's native strict proof checker.
    pub strict_verdict: StrictProofVerdict,
    /// Whether every proof step uses only rules in the restricted-rule-subset subset
    /// **and** the proof passes strict semantic validation.
    ///
    /// True only when:
    /// 1. [`strict_verdict`](Self::strict_verdict) is [`StrictProofVerdict::Verified`]
    /// 2. Every `Step` rule is in the restricted rule whitelist
    /// 3. Every `TheoryLemma` kind is in the restricted-rule-subset subset (EUF only)
    pub restricted_rule_subset: bool,
    /// Serialized LRAT certificate for the SAT backbone proof, when available.
    ///
    /// This is exported only when the stored clause trace is complete enough
    /// to replay into a standalone LRAT certificate.
    pub lrat_certificate: Option<Vec<u8>>,
    /// Structured Farkas certificates extracted from arithmetic theory lemmas.
    pub farkas_certificates: Vec<FarkasCertificate>,
}

/// Internal evaluation of all three proof quality signals.
///
/// Computed once per artifact export, preventing redundant proof walks.
struct ProofArtifactEvaluation {
    /// Non-strict diagnostic quality (theory lemmas treated as axioms).
    diagnostic_quality: ProofQuality,
    /// Partial check result from the internal checker.
    partial_check: PartialProofCheck,
    /// Result of `check_proof_strict` — `Ok` when every step is semantically
    /// verified, `Err` when any step fails strict validation.
    strict_quality: Result<ProofQuality, ProofCheckError>,
}

/// Convert the strict checker result into the stable consumer-facing verdict.
///
/// Production goes through [`strict_verdict_with_deferred_trust`]; this plain
/// conversion is exercised directly by the artifact-boundary tests.
#[cfg(test)]
pub(super) fn strict_verdict_from_result(
    strict_quality: Result<ProofQuality, ProofCheckError>,
) -> StrictProofVerdict {
    match strict_quality {
        Ok(quality) => StrictProofVerdict::Verified(quality),
        Err(error) => StrictProofVerdict::Rejected(error.to_string()),
    }
}

/// Compute the strict verdict, but rescue a proof whose ONLY strict failure is a
/// `trust` step demoted from genuine bit-vector / array theory reasoning.
///
/// Rationale: `ay` correctly decides many BV/array clauses UNSAT, then exports
/// the learned theory clause as an Alethe `trust` step (the Alethe BV/array
/// proof-rule set is incomplete). The plain strict checker rejects every `trust`
/// step by rule name, so a genuinely-discharged BV tautology is demoted to
/// `Unknown`. This routine consolidates the two existing-but-unwired soundness
/// paths:
///
/// 1. [`check_proof_collecting_trust_with_context`] runs the FULL strict
///    structural check
///    (every non-trust rule at the strict boundary) but DEFERS each `trust`
///    step, returning its conclusion clause. If any non-trust step fails strict
///    validation, this errors and we stay [`StrictProofVerdict::Rejected`].
/// 2. Each deferred trust clause is then INDEPENDENTLY re-discharged by the
///    fail-closed semantic checkers ([`check_bv_clause`] / [`check_array_clause`]
///    in `ay-dpll`), which assert `¬clause` into a fresh solver and require
///    UNSAT. A clause is accepted ONLY when an independent solve confirms it is a
///    genuine theory tautology ([`BvStepVerdict::Valid`] /
///    [`ArrayStepVerdict::Valid`]). `Unchecked` / `Invalid` (or a forged or
///    non-tautological clause) keeps the verdict Rejected.
///
/// Acceptance here stays at the SmtBacked / strict-checked tier: `ay`'s checker
/// is the trusted base. It does NOT claim kernel-`Certified`.
fn strict_verdict_with_deferred_trust(
    strict_quality: Result<ProofQuality, ProofCheckError>,
    diagnostic_quality: &ProofQuality,
    proof: &ay_core::Proof,
    terms: &ay_core::TermStore,
    assertions: &[ay_core::TermId],
    resolve_ctx: &ay_frontend::Context,
) -> StrictProofVerdict {
    // Fast path: the plain strict checker already accepted.
    let plain_err = match strict_quality {
        Ok(quality) => return StrictProofVerdict::Verified(quality),
        Err(error) => error,
    };

    // Only trust-step rejections are candidates for the deferred-trust rescue.
    // Any other strict failure is a real structural rejection — stay Rejected.
    if !matches!(
        plain_err,
        ProofCheckError::TrustStep { .. } | ProofCheckError::StrictProofModeTrust { .. }
    ) {
        return StrictProofVerdict::Rejected(plain_err.to_string());
    }

    // FRESH-RE-SOLVE FORGED-UNSAT GUARD (dominant, fail-closed). We are here only
    // because the proof leaned on a trust-fallback step (the plain strict checker
    // rejected it as `TrustStep`/`StrictProofModeTrust`). Before honoring ANY of the
    // deferred-trust accept paths below (`all_standalone` per-clause discharge OR the
    // whole-problem `executor_reconfirms_unsat` fallback), independently re-decide the
    // original problem assertions in a FRESH `Executor`. If that clean re-solve returns
    // a DEFINITIVE SAT, the UNSAT verdict is FORGED — a satisfiable problem can never be
    // genuinely UNSAT — so reject the proof and let the consumer downgrade to Unknown.
    // This dominates `all_standalone`, closing the residual hole where every collected
    // trust clause looks like a standalone theory tautology yet the overall UNSAT is
    // forged (term-less Tseitin aux var in the split path; theory-conflict Farkas gap).
    // SOUND: downgrade-only and gated on a DEFINITIVE SAT, so a genuine UNSAT (re-solves
    // to UNSAT or Unknown, never SAT) is never disturbed and no false verdict is created.
    if executor_redecides_definitive_sat(resolve_ctx) {
        return StrictProofVerdict::Rejected(
            "forged UNSAT: a fresh Executor independently re-decides the problem \
             assertions as DEFINITIVE SAT, so the trust-fallback UNSAT proof is not \
             reproducible and is downgraded fail-closed"
                .to_string(),
        );
    }

    // Re-run strict validation, this time deferring (collecting) trust clauses.
    // A non-trust strict error here means the proof is genuinely unsound → stay
    // Rejected with that error.
    let datatype_declarations: Vec<(String, Vec<String>)> = resolve_ctx
        .datatype_iter()
        .map(|(name, constructors)| (name.to_string(), constructors.to_vec()))
        .collect();
    let constructor_selectors: Vec<(String, Vec<String>)> = resolve_ctx
        .ctor_selectors_iter()
        .map(|(constructor, selectors)| (constructor.clone(), selectors.clone()))
        .collect();
    let Some(datatype_member_signatures) = exact_datatype_member_signatures(resolve_ctx) else {
        return StrictProofVerdict::Rejected(
            "datatype registries lack an exact sticky member signature".to_string(),
        );
    };
    let collected = match check_proof_collecting_trust_with_typed_context(
        proof,
        terms,
        (!datatype_declarations.is_empty()).then_some(datatype_declarations.as_slice()),
        (!constructor_selectors.is_empty()).then_some(constructor_selectors.as_slice()),
        datatype_member_signatures.as_slice(),
        Some(assertions),
    ) {
        Ok(collected) => collected,
        Err(error) => return StrictProofVerdict::Rejected(error.to_string()),
    };

    // Defensive: if nothing was collected the plain checker should have accepted.
    if collected.is_empty() {
        return StrictProofVerdict::Rejected(plain_err.to_string());
    }

    // Independently discharge the collected trust clauses. PREFERRED (strongest):
    // every clause is a genuine standalone theory tautology — a non-empty clause
    // whose negation is UNSAT, or the terminal EMPTY trust clause re-solved against
    // the whole problem. When EVERY collected clause discharges standalone, the
    // proof's trust steps are each independently certified.
    let all_standalone = collected
        .iter()
        .all(|(_, clause)| discharge_trust_clause(terms, clause, assertions).is_some());
    if all_standalone {
        return StrictProofVerdict::Verified(diagnostic_quality.clone());
    }

    // FALLBACK (still sound): some collected trust clause is CONTEXT-DEPENDENT —
    // valid only given the other assertions, so it is not a standalone tautology.
    // This is the norm for LIA `Generic` lemmas (e.g. an ite-arithmetic lemma whose
    // proof is not Farkas-pure) and the terminal trust step. The independent
    // certificate for such a proof is the SAME one the empty-terminal-clause path
    // uses: re-decide the ORIGINAL problem assertions and confirm they are jointly
    // UNSAT in a fresh solver (now LIA-capable via `pick_logic`). This certifies
    // the CONCLUSION (the property holds) without trusting the proof's structure;
    // a forged UNSAT for a satisfiable problem re-solves to SAT → Rejected, so it
    // can never produce a false-PROVE.
    //
    // PRIMARY re-solve: a FRESH `Executor` over a CLONE of the original
    // `TermStore`, asserting the ORIGINAL TermIds. Repeating the search verdict
    // is not evidence by itself: the fresh result is accepted only when its own
    // proof passes the plain strict checker, with no deferred-trust rescue. This
    // prevents the same unsound engine path from corroborating itself.
    if executor_reconfirms_unsat(resolve_ctx) {
        return StrictProofVerdict::Verified(diagnostic_quality.clone());
    }
    match check_bv_assertions_unsat(terms, assertions) {
        BvStepVerdict::Valid => StrictProofVerdict::Verified(diagnostic_quality.clone()),
        BvStepVerdict::Invalid { .. } | BvStepVerdict::Unchecked { .. } => {
            StrictProofVerdict::Rejected(
                "deferred-trust discharge failed: a collected trust clause is not a \
                 standalone theory tautology AND the problem assertions could not be \
                 independently re-solved as UNSAT"
                    .to_string(),
            )
        }
    }
}

fn exact_datatype_member_signatures(
    context: &ay_frontend::Context,
) -> Option<Vec<DatatypeMemberSignature>> {
    let mut signatures = Vec::new();
    for (_, constructors) in context.datatype_iter() {
        for constructor in constructors {
            let fields = context.constructor_selectors(constructor)?;
            let tester = format!("is-{constructor}");
            for identity in std::iter::once(constructor.as_str())
                .chain(std::iter::once(tester.as_str()))
                .chain(fields.iter().map(String::as_str))
            {
                let info = context.exact_datatype_member_info(identity)?;
                signatures.push(DatatypeMemberSignature {
                    identity: identity.to_string(),
                    argument_sorts: info.arg_sorts.clone(),
                    result_sort: info.sort.clone(),
                    nullary_term: info.term,
                });
            }
        }
    }
    Some(signatures)
}

/// Independent whole-problem UNSAT re-confirmation through the COMPLETE `Executor`
/// path. `check_bv_assertions_unsat` re-translates the assertions through the thin
/// BV/LIA `Translator` into a fresh `Solver`; that re-built term structure defeats
/// `solve_lia` on deep nested-ite obligations even though the original (parser-built)
/// terms decide. This instead builds a FRESH `Executor`, sets its `TermStore` to a
/// CLONE of the original `terms`, asserts the ORIGINAL `assertions` TermIds, and runs
/// the full `check_sat` (logic detection → `solve_lia` with arithmetic-ite lifting).
/// Returns `true` only when the fresh solve both reports UNSAT and supplies a
/// proof accepted by the plain strict checker. Fresh search state alone is not
/// independence: without the second condition, the same wrong-UNSAT path could
/// simply repeat and certify itself.
fn executor_reconfirms_unsat(resolve_ctx: &ay_frontend::Context) -> bool {
    if resolve_ctx.assertions.is_empty() {
        return false;
    }
    // Fresh `Executor` over a CLONE of the full solving context (terms, assertions,
    // logic, options incl. `:produce-proofs`) — the same setup the main solve used,
    // so the complete `check_sat` path re-decides. Executor::new()'s own SAT/theory
    // state is fresh; `check_sat` re-encodes the assertions from scratch.
    let mut exec = crate::Executor::new();
    exec.ctx = resolve_ctx.clone();
    executor_reports_plain_strict_unsat(&mut exec)
}

/// Re-solve one fresh executor obligation and accept UNSAT only with a plain
/// strict proof over its exact authored roots.
///
/// This deliberately does not call the deferred-trust rescue: a trust-bearing
/// proof may be the object currently being discharged, so allowing another
/// same-engine re-solve to use the same rescue would be circular.
fn executor_reports_plain_strict_unsat(exec: &mut crate::Executor) -> bool {
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    if !matches!(exec.check_sat(), Ok(result) if result.is_unsat()) {
        return false;
    }
    let Some(proof) = exec.last_proof() else {
        return false;
    };
    exec.check_proof_strict_with_datatypes(proof).is_ok()
}

/// Fresh-re-solve forged-UNSAT guard: the DUAL of [`executor_reconfirms_unsat`].
///
/// Builds a FRESH [`crate::Executor`] over a CLONE of the original solving context
/// and re-decides the problem assertions from scratch. Returns `true` ONLY when that
/// independent solve returns a **definitive SAT** (a model exists) — i.e. the original
/// UNSAT verdict is FORGED. A re-solve that returns `Unknown` (incomplete / timeout)
/// returns `false`: we only downgrade on a positive, definitive contradiction of the
/// UNSAT claim, never on a non-result. This is what makes the guard SOUND and
/// downgrade-only — it can turn a forged `Verified` into `Rejected`, but a genuine
/// UNSAT (which re-solves to UNSAT or Unknown, never SAT) is never disturbed, so the
/// guard can never manufacture a false verdict.
///
/// Used as the DOMINANT gate in [`strict_verdict_with_deferred_trust`]: any proof that
/// relied on a trust-fallback is only honored once we have confirmed the problem is not
/// independently, definitively satisfiable. This catches the residual forged-UNSAT
/// cases (e.g. a term-less Tseitin aux var in the split path, or a theory-conflict
/// Farkas-recording gap) whose per-clause trust steps may each look like standalone
/// theory tautologies (`all_standalone == true`) yet whose overall UNSAT is forged for
/// a satisfiable problem.
pub(crate) fn executor_redecides_definitive_sat(resolve_ctx: &ay_frontend::Context) -> bool {
    if resolve_ctx.assertions.is_empty() {
        // An empty assertion set is trivially SAT, but there is nothing to forge:
        // never treat it as a forged-UNSAT signal.
        return false;
    }
    let mut exec = crate::Executor::new();
    exec.ctx = resolve_ctx.clone();
    matches!(exec.check_sat(), Ok(result) if result.is_sat())
}

/// Independently discharge a deferred trust step, accepting only a checked
/// non-empty theory tautology or a fresh strict refutation of the exact
/// authored assertions for a terminal empty clause. All unsupported,
/// satisfiable, unknown, malformed, or resource-limited cases fail closed.
pub(crate) fn discharge_trust_clause(
    terms: &ay_core::TermStore,
    clause: &[ay_core::TermId],
    assertions: &[ay_core::TermId],
) -> Option<()> {
    let controls = TrustClauseDischargeControls::default();
    discharge_trust_clause_impl(terms, clause, assertions, &controls, None)
}

/// [`discharge_trust_clause`] under an already-elapsing publication resource
/// envelope. Any fired/exceeded control declines the clause (fail-closed).
pub(crate) fn discharge_trust_clause_with_controls(
    terms: &ay_core::TermStore,
    clause: &[ay_core::TermId],
    assertions: &[ay_core::TermId],
    controls: &TrustClauseDischargeControls,
) -> Option<()> {
    discharge_trust_clause_impl(terms, clause, assertions, controls, Some(controls))
}

/// Shared discharge funnel. `specialized_controls == None` preserves the
/// ordinary proof-export API's legacy unbounded BV/array solvers; mandatory
/// publication passes the active envelope through those private solvers too.
fn discharge_trust_clause_impl(
    terms: &ay_core::TermStore,
    clause: &[ay_core::TermId],
    assertions: &[ay_core::TermId],
    controls: &TrustClauseDischargeControls,
    specialized_controls: Option<&TrustClauseDischargeControls>,
) -> Option<()> {
    if controls.stop_requested(terms) {
        return None;
    }
    // Terminal empty trust clause → re-discharge the original problem assertions.
    if clause.is_empty() {
        let verdict = specialized_controls.map_or_else(
            || check_bv_assertions_unsat(terms, assertions),
            |controls| check_bv_assertions_unsat_with_controls(terms, assertions, controls),
        );
        return match verdict {
            BvStepVerdict::Valid => {
                probe_discharge(|| "ACCEPT empty-clause bv-assertions-unsat".to_string());
                controls.accept_if_live(terms)
            }
            // SAT/Unknown/unmodellable: the UNSAT claim is not independently
            // reproducible. Never accept (fail closed).
            BvStepVerdict::Invalid { .. } | BvStepVerdict::Unchecked { .. } => {
                probe_discharge(|| "DECLINE empty-clause bv-assertions-unsat".to_string());
                None
            }
        };
    }

    let bv_verdict = specialized_controls.map_or_else(
        || check_bv_clause(terms, clause),
        |controls| check_bv_clause_with_controls(terms, clause, controls),
    );
    match bv_verdict {
        BvStepVerdict::Valid => {
            probe_discharge(|| "ACCEPT check_bv_clause".to_string());
            return controls.accept_if_live(terms);
        }
        // Invalid: ¬clause is SAT → NOT a BV tautology. Never accept.
        BvStepVerdict::Invalid { .. } => {
            probe_discharge(|| "DECLINE check_bv_clause=Invalid".to_string());
            return None;
        }
        // Unchecked: the BV checker could not model it; try the array checker.
        BvStepVerdict::Unchecked { .. } => {}
    }
    if controls.stop_requested(terms) {
        return None;
    }
    let array_verdict = specialized_controls.map_or_else(
        || check_array_clause(terms, clause),
        |controls| check_array_clause_with_controls(terms, clause, controls),
    );
    match array_verdict {
        ArrayStepVerdict::Valid => {
            probe_discharge(|| "ACCEPT check_array_clause".to_string());
            return controls.accept_if_live(terms);
        }
        // Invalid: an independent solve refuted it. Never accept.
        ArrayStepVerdict::Invalid { .. } => {
            probe_discharge(|| "DECLINE check_array_clause=Invalid".to_string());
            return None;
        }
        // Neither specialised checker can MODEL this clause — that is a
        // coverage limit of those checkers, not evidence about the clause.
        ArrayStepVerdict::Skipped | ArrayStepVerdict::Unchecked { .. } => {}
    }
    if controls.stop_requested(terms) {
        return None;
    }

    if discharge_source_bv_lia(terms, clause, assertions, controls) {
        probe_discharge(|| "ACCEPT discharge_source_bv_lia".to_string());
        return controls.accept_if_live(terms);
    }
    if controls.stop_requested(terms) {
        return None;
    }

    // CLOSED-FORM BV<->Int BRIDGE SCHEMAS (#unsat-cert-bridge-schema).
    //
    // An ADDITIONAL non-solving authenticator, not a relaxation of anything
    // above: it structurally re-derives the two bridge lemma schemas the
    // BV/LIA bridge feeds the arithmetic solver (the `bvadd`/`bvsub` modular
    // residue disjunction, and the `bvult`/`bvule` unsigned order fact) from
    // widths and constants READ OUT OF THE TERM STORE AND CHECKED. Anything it
    // does not recognise declines and the lanes below still run.
    //
    // WHY IT IS NEEDED. `discharge_source_bv_lia` authenticates these only by
    // ENUMERATING the finite assignment space, so it declines at every width
    // above 8 ("finite assignment space exceeds 65536" / "a free 64-bit BV
    // variable exceeds finite enumeration"). Every remaining route is a nested
    // solve, and a nested solve cannot discharge its own trust steps (the
    // depth-0 guard in `discharge_trust_steps_for_certification`), so the whole
    // family fell through to the wall-clock-budgeted whole-problem re-solve —
    // publishing a correct UNSAT as `unsat` or `unknown` depending on machine
    // load. Measured on the deductive-checks `i = i + 1usize` loop-counter obligation:
    // stage (3) accepted 0 times, stage (4) 28, and the depth guard rejected
    // 36. See `bv_int_bridge_schema` for the derivations and the narrowness
    // pins.
    if discharge_bv_int_bridge_schema(terms, clause, assertions) {
        probe_discharge(|| "ACCEPT discharge_bv_int_bridge_schema".to_string());
        return controls.accept_if_live(terms);
    }
    if controls.stop_requested(terms) {
        return None;
    }
    let arena_deadline = controls.nested_deadline();
    if !controls.term_store_clone_fits(terms, arena_deadline) {
        return None;
    }
    let mut arena = terms.clone();
    if controls.stop_requested(&arena) {
        return None;
    }
    let mut negated = Vec::new();
    if negated.try_reserve_exact(clause.len()).is_err() {
        return None;
    }
    for &term in clause {
        if controls.stop_requested(&arena) {
            return None;
        }
        negated.push(arena.mk_not(term));
    }
    if controls.stop_requested(&arena) {
        return None;
    }

    // ENTAILMENT DISCHARGE (#unsat-cert-entailment).
    //
    // Try the context-aware obligation BEFORE the context-free generic probe.
    // Most emitted trust clauses are consequences of the authored problem, not
    // standalone tautologies. In particular, incremental LIA refutations used
    // to spend the generic probe's full one-second budget at every depth before
    // this stronger check succeeded in milliseconds. Since `P ∧ ¬C` UNSAT also
    // holds for every standalone tautology C, this ordering changes no
    // acceptance condition; the smaller context-free probe remains below as a
    // fallback when the larger problem is harder for the solver.
    //
    // The test asks whether the PROBLEM entails `C`: assert `P ∧ ¬C` in a fresh
    // executor and require UNSAT.
    //
    // SOUNDNESS. Suppose every deferred clause passes this test and the rest of
    // the proof passes strict validation. If `P` were satisfiable, then
    // `P ∧ ¬C` unsat gives `P ⊨ C` for each such `C`, so every clause the proof
    // leans on is a logical consequence of `P`; the strictly-checked remainder
    // then derives the empty clause from `P`, contradicting satisfiability.
    // So `P` is unsat and the published verdict is correct.
    //
    // The degenerate case is harmless: if `P` is itself unsat then it entails
    // every C, but that is exactly the verdict being certified. `Unsat` is the
    // only accepting outcome; Sat, Unknown, and timeout all decline.
    if !assertions.is_empty() {
        let deadline = controls.nested_deadline();
        let mut entail = ay_frontend::Context::new();
        entail.terms = arena;
        entail.assertions = assertions.to_vec();
        entail.assertions.extend_from_slice(&negated);
        let mut exec = crate::Executor::new();
        exec.ctx = entail;
        if !controls.install_on(&mut exec, deadline) {
            return None;
        }
        let started = std::time::Instant::now();
        let accepted = executor_reports_plain_strict_unsat(&mut exec);
        let elapsed = started.elapsed();
        probe_discharge(|| {
            format!(
                "{} entailment-lane (1000ms wall budget) elapsed={}ms unknown.reason={:?}",
                if accepted { "ACCEPT" } else { "DECLINE" },
                elapsed.as_millis(),
                exec.statistics().get_string("unknown.reason"),
            )
        });
        if accepted && controls.accept_until(&exec.ctx.terms, deadline) {
            return Some(());
        }
        if ay_core::time::Instant::now() >= deadline || controls.stop_requested(&exec.ctx.terms) {
            return None;
        }
        arena = std::mem::take(&mut exec.ctx.terms);
    }

    if controls.stop_requested(&arena) {
        return None;
    }

    // THEORY-AGNOSTIC STANDALONE FALLBACK (#unsat-cert-general-discharge).
    //
    // `check_bv_clause` / `check_array_clause` are specialised: they model the
    // clause in one theory and decline everything else. Most trust steps in
    // quantified problems are neither — they are LIA / quantifier-instantiation
    // lemmas — so both decline, the clause goes undischarged, and a correct
    // refutation is thrown away. Measured: 48 of the 49 verdict failures in
    // `group_quantifiers` are exactly this, `expected unsat, got unknown`, with
    // messages like "closed false universal", "evil broadcast" and the
    // per-element `seq` invariants.
    //
    // The generic test is the definition of the obligation itself: a clause `C`
    // is a tautology iff `¬C` is unsatisfiable. Assert `¬C` into a FRESH
    // executor and require UNSAT. This subsumes what the specialised checkers do
    // and extends it to every theory the solver can decide, without assuming
    // anything about which one the clause belongs to.
    //
    // SOUND and fail-closed. A repeated raw `Unsat` is not accepting evidence;
    // the nested solve must also produce a plain-strict proof of `not C`'s
    // inconsistency. `Sat`, `Unknown`, timeout, missing proof, or any trust/hole
    // in that proof all decline.
    let mut probe = ay_frontend::Context::new();
    probe.terms = arena;
    probe.assertions = negated;
    let deadline = controls.nested_deadline();
    let mut exec = crate::Executor::new();
    exec.ctx = probe;
    if !controls.install_on(&mut exec, deadline) {
        return None;
    }
    let started = std::time::Instant::now();
    let accepted = executor_reports_plain_strict_unsat(&mut exec);
    let elapsed = started.elapsed();
    probe_discharge(|| {
        format!(
            "{} standalone-lane (1000ms wall budget) elapsed={}ms unknown.reason={:?}",
            if accepted { "ACCEPT" } else { "DECLINE" },
            elapsed.as_millis(),
            exec.statistics().get_string("unknown.reason"),
        )
    });
    (accepted && controls.accept_until(&exec.ctx.terms, deadline)).then_some(())
}

/// Evaluate the proof through all three validation levels in a single pass.
fn evaluate_proof_artifact_boundary(
    proof: &ay_core::Proof,
    terms: &ay_core::TermStore,
    strict_quality: Result<ProofQuality, ProofCheckError>,
) -> Option<ProofArtifactEvaluation> {
    let diagnostic_quality = check_proof_with_quality(proof, terms).ok()?;
    let (partial_check, _partial_err) = check_proof_partial(proof, terms);
    Some(ProofArtifactEvaluation {
        diagnostic_quality,
        partial_check,
        strict_quality,
    })
}

/// Hard-coded whitelist of Alethe rules that a downstream checker can reconstruct as
/// kernel proof terms. Derived from trust-free QF_BOOL and simple QF_UF
/// proof evidence.
fn is_restricted_rule_subset_rule(rule: &AletheRule) -> bool {
    matches!(
        rule,
        // Propositional tautology rules (Tseitin clausification)
        AletheRule::True
            | AletheRule::False
            | AletheRule::NotTrue
            | AletheRule::NotFalse
            | AletheRule::And
            | AletheRule::AndPos(_)
            | AletheRule::AndNeg
            | AletheRule::NotAnd
            | AletheRule::Or
            | AletheRule::OrPos(_)
            | AletheRule::OrNeg
            | AletheRule::NotOr
            | AletheRule::Implies
            | AletheRule::ImpliesPos
            | AletheRule::ImpliesNeg1
            | AletheRule::ImpliesNeg2
            | AletheRule::NotImplies1
            | AletheRule::NotImplies2
            | AletheRule::Equiv
            | AletheRule::EquivPos1
            | AletheRule::EquivPos2
            | AletheRule::EquivNeg1
            | AletheRule::EquivNeg2
            | AletheRule::NotEquiv1
            | AletheRule::NotEquiv2
            | AletheRule::Ite
            | AletheRule::ItePos1
            | AletheRule::ItePos2
            | AletheRule::IteNeg1
            | AletheRule::IteNeg2
            | AletheRule::NotIte1
            | AletheRule::NotIte2
            | AletheRule::XorPos1
            | AletheRule::XorPos2
            | AletheRule::XorNeg1
            | AletheRule::XorNeg2
            // Resolution and structural
            | AletheRule::Resolution
            | AletheRule::ThResolution
            | AletheRule::Contraction
            | AletheRule::Drup
            // EUF equality rules
            | AletheRule::Refl
            | AletheRule::Symm
            | AletheRule::Trans
            | AletheRule::Cong
            | AletheRule::EqReflexive
            | AletheRule::EqTransitive
            | AletheRule::EqCongruent
            | AletheRule::EqCongruentPred
            // Simplification (boolean only for now)
            | AletheRule::AllSimplify
            | AletheRule::BoolSimplify
    )
}

/// Check whether all proof steps use only restricted-rule-subset rules.
///
/// Returns `true` only when:
/// 1. `trust_count == 0` and `hole_count == 0`
/// 2. Every `Step` rule is in the restricted rule whitelist
/// 3. Every `TheoryLemma` kind is in the restricted-rule-subset subset (EUF only)
fn check_restricted_rule_subset(quality: &ProofQuality, proof: &ay_core::Proof) -> bool {
    use ay_core::TheoryLemmaKind;

    if quality.trust_count > 0 || quality.hole_count > 0 {
        return false;
    }

    for step in &proof.steps {
        match step {
            ProofStep::Step { rule, .. }
                if !is_restricted_rule_subset_rule(rule) => {
                    return false;
                }
            ProofStep::TheoryLemma { kind, .. }
                // Only EUF theory lemmas are in the restricted-rule-subset first slice.
                // Arithmetic (LraFarkas, LiaGeneric) and other theories are out
                // of scope even when they don't export as `trust`.
                if !matches!(
                    kind,
                    TheoryLemmaKind::EufTransitive
                        | TheoryLemmaKind::EufCongruent
                        | TheoryLemmaKind::EufCongruentPred
                ) => {
                    return false;
                }
            // Assume, Resolution, Anchor are always OK.
            _ => {}
        }
    }
    true
}

fn extract_farkas_certificates(proof: &ay_core::Proof) -> Vec<FarkasCertificate> {
    proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(proof_step_index, step)| {
            let ProofStep::TheoryLemma {
                farkas: Some(annotation),
                ..
            } = step
            else {
                return None;
            };
            Some(FarkasCertificate {
                proof_step_index: u32::try_from(proof_step_index).ok()?,
                coefficients: annotation
                    .coefficients
                    .iter()
                    .map(|coefficient| {
                        BigRational::new(
                            (*coefficient.numer()).into(),
                            (*coefficient.denom()).into(),
                        )
                    })
                    .collect(),
            })
        })
        .collect()
}

impl UnsatProofArtifact {
    /// Accept this proof artifact at a consumer-facing boundary.
    ///
    /// `Strict` requires the strict checker to have accepted the proof.
    /// `RestrictedRuleSubset` additionally requires the proof to remain inside the current
    /// restricted-rule-subset strict subset.
    #[must_use = "consumer boundaries must check whether an UNSAT proof artifact is acceptable"]
    pub fn accept_for_consumer(
        &self,
        mode: ProofAcceptanceMode,
    ) -> Result<(), ProofAcceptanceError> {
        match (&self.strict_verdict, mode) {
            (StrictProofVerdict::Verified(_), ProofAcceptanceMode::Strict) => Ok(()),
            (StrictProofVerdict::Verified(_), ProofAcceptanceMode::RestrictedRuleSubset)
                if self.restricted_rule_subset =>
            {
                Ok(())
            }
            (StrictProofVerdict::Verified(_), ProofAcceptanceMode::RestrictedRuleSubset) => {
                Err(ProofAcceptanceError::NotRestrictedRuleSubset)
            }
            (StrictProofVerdict::Rejected(reason), _) => {
                Err(ProofAcceptanceError::StrictRejected {
                    reason: reason.clone(),
                })
            }
        }
    }
}

impl super::Solver {
    /// Export the last UNSAT proof as rendered Alethe diagnostic text with
    /// native quality metrics, a native strict verdict, and a clean
    /// compatibility flag.
    ///
    /// `strict_verdict` preserves AY's native `check_proof_strict` result; it
    /// is not an external-checker verdict for the rendered Alethe text.
    /// `restricted_rule_subset` is `true` only when the strict verdict is verified
    /// **and** every rule is in the restricted rule whitelist. The `quality` field
    /// remains the non-strict diagnostic summary.
    ///
    /// Returns `None` if:
    /// - The last result was not UNSAT
    /// - Proof output was not requested for that solve
    /// - No proof was generated
    /// - A query-sealed proof has no current authenticated Alethe surface
    /// - Bounded Alethe rendering fails or exhausts its work budget
    #[must_use]
    pub fn export_last_unsat_artifact(&self) -> Option<UnsatProofArtifact> {
        let proof = self.executor.last_proof()?;
        let finite_enum = self.executor.last_proof_has_finite_enum_sidecar();
        let strict_quality = self.executor.check_proof_strict_with_datatypes(proof);
        let ordinary_surface = self
            .executor
            .try_export_last_proof_alethe_for_problem_scope()?;
        let alethe_problem_smt2 = self.executor.try_export_last_proof_alethe_problem_smt2();
        let alethe = match ordinary_surface {
            Ok(alethe) => alethe,
            Err(AlethePrintError::UnsupportedArrayExtensionality { id })
                if strict_quality.is_ok() =>
            {
                self.executor
                    .try_export_extensionality_artifact_surface(id)?
                    .ok()?
            }
            Err(_) => return None,
        };
        let terms = self.executor.terms();
        let evaluation = evaluate_proof_artifact_boundary(proof, terms, strict_quality)?;

        let restricted_rule_subset_ok =
            check_restricted_rule_subset(&evaluation.diagnostic_quality, proof);
        // Strict verdict with the deferred-trust rescue: a proof whose only
        // strict failure is a `trust` step demoted from genuine BV/array theory
        // reasoning is accepted IFF every such clause is independently
        // re-discharged as a theory tautology (¬clause UNSAT). All other strict
        // failures stay Rejected. Stays at the strict-checked (SmtBacked) tier.
        let strict_verdict = if finite_enum {
            match &evaluation.strict_quality {
                Ok(quality) => StrictProofVerdict::Verified(quality.clone()),
                Err(error) => StrictProofVerdict::Rejected(error.to_string()),
            }
        } else {
            let problem_assertions = self.executor.problem_assertions_for_strict_proof();
            let mut resolve_ctx = self.executor.context().clone();
            resolve_ctx.assertions = problem_assertions;
            let assertions = resolve_ctx.assertions.as_slice();
            // Deferred-trust validation can run fresh solvers. Those are
            // semantic checks of this already-produced proof, not new caller
            // decisions, so they must preserve the sealed CNF byte-for-byte.
            let _export_suppression = crate::Executor::suppress_bv_cnf_export_for_internal_checks();
            strict_verdict_with_deferred_trust(
                evaluation.strict_quality,
                &evaluation.diagnostic_quality,
                proof,
                terms,
                assertions,
                &resolve_ctx,
            )
        };
        let restricted_rule_subset =
            matches!(&strict_verdict, StrictProofVerdict::Verified(_)) && restricted_rule_subset_ok;
        let farkas_certificates = extract_farkas_certificates(proof);

        Some(UnsatProofArtifact {
            alethe,
            alethe_problem_smt2,
            quality: evaluation.diagnostic_quality,
            partial_check: Some(evaluation.partial_check),
            strict_verdict,
            restricted_rule_subset,
            lrat_certificate: self.executor.last_lrat_certificate().map(<[u8]>::to_vec),
            farkas_certificates,
        })
    }

    /// Export the last UNSAT proof as a portable, serializable bundle that can
    /// be re-checked OFFLINE by [`ay_proof::re_check_bundle_strict`] — with no
    /// solver run and without trusting this solver. The bundle carries the proof
    /// steps, a checker-only term snapshot (so every embedded `TermId` resolves),
    /// and its proof-authorized obligation term ids (so the strict checker can
    /// constrain the proof's `assume` axioms to the claimed obligation). Those
    /// ids may form an authenticated UNSAT-core subset of the full query.
    ///
    /// Offline re-checking establishes the bundle's internal soundness; it does
    /// not authenticate that the producer supplied the intended external
    /// problem. A consumer must independently verify that every obligation
    /// assertion is a member of the intended query, compare the embedded
    /// datatype tables, and independently obtain and compare the complete
    /// free-symbol declaration context required by the
    /// [`SerializableProofBundle`] binding contract.
    ///
    /// Unlike [`export_last_unsat_artifact`](Self::export_last_unsat_artifact),
    /// this native bundle does not require an authenticated Alethe surface. A
    /// surface-less sealed finite-enum proof can therefore export a bundle even
    /// when textual Alethe export declines. It still returns `None` when the
    /// last result was not UNSAT, proof output was not requested, no proof was
    /// generated, or the bounded bundle snapshot/current-query checks fail.
    #[must_use]
    pub fn export_last_unsat_bundle(&self) -> Option<ay_proof::SerializableProofBundle> {
        let proof = self.executor.last_proof()?;
        let terms = self.executor.terms();
        let finite_enum = self.executor.last_proof_has_finite_enum_sidecar();
        if finite_enum && !self.executor.last_proof_is_checked_finite_enum() {
            return None;
        }
        let (datatype_declarations, constructor_selectors, datatype_member_signatures) =
            if finite_enum {
                if !self
                    .executor
                    .checked_finite_enum_bundle_export_is_bounded(proof)
                {
                    return None;
                }
                self.executor
                    .checked_finite_enum_export_declarations(proof)?
            } else {
                (
                    self.executor.datatype_decls_for_strict_proof(),
                    self.executor.ctor_selector_decls_for_strict_proof(),
                    self.executor
                        .datatype_member_signatures_for_strict_proof()?,
                )
            };
        let assertions = self.executor.problem_assertions_for_strict_proof();
        Some(
            ay_proof::SerializableProofBundle::from_proof_with_typed_context(
                proof,
                terms,
                assertions,
                datatype_declarations,
                constructor_selectors,
                datatype_member_signatures,
            ),
        )
    }

    /// Render a term to a canonical, store-INDEPENDENT S-expression string
    /// (variables by name; see [`ay_proof::render_term_canonical`]).
    ///
    /// This is a no-solve structural comparison aid: a consumer can render a
    /// term it built in THIS solver and compare it against a term embedded in a
    /// [`SerializableProofBundle`] produced by another solver, without sharing
    /// term ids. Canonical text does not include the complete declaration
    /// environment, so it is not sufficient to authenticate an external
    /// obligation by itself; consumers must compare the embedded datatype
    /// tables and independently obtain and compare the complete free-symbol
    /// declaration context required by the bundle binding contract.
    #[must_use]
    pub fn render_term_canonical(&self, term: super::Term) -> String {
        let term = self.require_term("render_term_canonical", term);
        ay_proof::render_term_canonical(self.executor.terms(), term)
    }

    /// Export the last UNSAT proof as rendered Alethe text.
    ///
    /// Returns `None` if the last result was not UNSAT, proof output was not requested for
    /// that solve, no current authenticated surface is available, or rendering fails.
    #[must_use]
    pub fn export_last_proof_alethe(&self) -> Option<String> {
        self.executor
            .try_export_last_proof_alethe_for_problem_scope()?
            .ok()
    }

    /// Get diagnostic (non-strict) quality metrics for the last UNSAT proof.
    ///
    /// This returns the same non-strict summary as `UnsatProofArtifact::quality`.
    /// For the strict verdict, use [`last_strict_proof_quality`](Self::last_strict_proof_quality).
    ///
    /// Returns `None` if the last result was not UNSAT or proof output was not requested.
    #[must_use]
    pub fn last_proof_quality(&self) -> Option<ProofQuality> {
        let proof = self.executor.last_proof()?;
        let terms = self.executor.terms();
        check_proof_with_quality(proof, terms).ok()
    }

    /// Get strict proof validation result for the last UNSAT proof.
    ///
    /// Returns:
    /// - `None` — no UNSAT proof available
    /// - `Some(Ok(quality))` — strict validation succeeded
    /// - `Some(Err(error))` — strict validation rejected the proof
    ///
    /// This is the authoritative *native* proof validation result. Unlike
    /// [`last_proof_quality`](Self::last_proof_quality), the strict checker
    /// rejects theory lemmas without semantic validators and unvalidated
    /// generic Alethe rules. A semantically revalidated `Generic` arithmetic
    /// lemma can therefore return `Ok` while its diagnostic quality still has
    /// `trust_count > 0` and its Alethe rendering honestly contains `hole`.
    /// The conservative strict-proofs publication policy refuses this known
    /// diagnostic class without changing native validation.
    #[must_use]
    pub fn last_strict_proof_quality(&self) -> Option<Result<ProofQuality, ProofCheckError>> {
        let proof = self.executor.last_proof()?;
        Some(self.executor.check_proof_strict_with_datatypes(proof))
    }

    /// Get partial check result for the last UNSAT proof.
    ///
    /// Returns `None` if the last result was not UNSAT or proof output was not requested.
    #[must_use]
    pub fn last_partial_proof_check(&self) -> Option<PartialProofCheck> {
        let proof = self.executor.last_proof()?;
        let terms = self.executor.terms();
        let (partial, _err) = check_proof_partial(proof, terms);
        Some(partial)
    }
}

#[cfg(test)]
mod trust_clause_resource_control_tests {
    use super::*;

    #[test]
    fn nested_executor_inherits_live_publication_controls() {
        let interrupt = Arc::new(AtomicBool::new(false));
        let outer_deadline = ay_core::time::Instant::now() + Duration::from_secs(1);
        let controls = TrustClauseDischargeControls {
            interrupt: Some(Arc::clone(&interrupt)),
            deadline: Some(outer_deadline),
            memory_limit: Some(usize::MAX),
            term_memory_limit: Some(usize::MAX),
        };
        let effective_deadline = controls.nested_deadline();
        assert_eq!(effective_deadline, outer_deadline);

        let mut executor = crate::Executor::new();
        assert!(controls.install_on(&mut executor, effective_deadline));
        assert_eq!(executor.current_solve_deadline(), Some(outer_deadline));
        assert_eq!(executor.memory_limit(), Some(usize::MAX));
        assert_eq!(executor.term_memory_limit(), Some(usize::MAX));

        interrupt.store(true, Ordering::Relaxed);
        assert!(executor.solve_interrupt_is_set());
    }

    #[test]
    fn controlled_discharge_rejects_expired_or_exhausted_envelopes() {
        let mut terms = ay_core::TermStore::new();
        let tautology = terms.true_term();
        let proposition = terms.mk_var("controlled_assertion_p", ay_core::Sort::Bool);
        let not_proposition = terms.mk_not_raw(proposition);
        let expired = ay_core::time::Instant::now()
            .checked_sub(Duration::from_millis(1))
            .expect("one millisecond must fit before the current instant");
        let expired_controls = TrustClauseDischargeControls {
            deadline: Some(expired),
            ..TrustClauseDischargeControls::default()
        };
        assert!(
            discharge_trust_clause_with_controls(&terms, &[tautology], &[], &expired_controls,)
                .is_none()
        );

        let exhausted_controls = TrustClauseDischargeControls {
            term_memory_limit: Some(0),
            ..TrustClauseDischargeControls::default()
        };
        assert!(discharge_trust_clause_with_controls(
            &terms,
            &[tautology],
            &[],
            &exhausted_controls,
        )
        .is_none());

        let live_child_controls = TrustClauseDischargeControls {
            term_memory_limit: Some(usize::MAX),
            ..TrustClauseDischargeControls::default()
        };
        assert_eq!(
            check_bv_clause_with_controls(&terms, &[tautology], &live_child_controls),
            BvStepVerdict::Valid
        );
        assert_eq!(
            check_array_clause_with_controls(&terms, &[tautology], &live_child_controls),
            ArrayStepVerdict::Valid
        );
        assert_eq!(
            check_bv_assertions_unsat_with_controls(
                &terms,
                &[proposition, not_proposition],
                &live_child_controls,
            ),
            BvStepVerdict::Valid
        );

        // Directly exercise each fresh specialized Solver under a ceiling far
        // below its non-empty baseline store. This isolates child propagation
        // from the later structural replay lanes in the full discharge funnel.
        let child_exhausted_controls = TrustClauseDischargeControls {
            term_memory_limit: Some(1),
            ..TrustClauseDischargeControls::default()
        };
        let BvStepVerdict::Unchecked { reason } =
            check_bv_clause_with_controls(&terms, &[tautology], &child_exhausted_controls)
        else {
            panic!("tiny child term limit must decline the BV checker");
        };
        assert!(reason.contains("resource envelope"));
        let ArrayStepVerdict::Unchecked { reason } =
            check_array_clause_with_controls(&terms, &[tautology], &child_exhausted_controls)
        else {
            panic!("tiny child term limit must decline the array checker");
        };
        assert!(reason.contains("resource envelope"));
        let BvStepVerdict::Unchecked { reason } = check_bv_assertions_unsat_with_controls(
            &terms,
            &[proposition, not_proposition],
            &child_exhausted_controls,
        ) else {
            panic!("tiny child term limit must decline the BV assertion checker");
        };
        assert!(reason.contains("resource envelope"));
    }

    #[test]
    fn clone_preflight_uses_an_exact_term_store_census() {
        let mut terms = ay_core::TermStore::new();
        let baseline = terms.true_memory_bytes();
        assert!(!terms.instance_memory_exceeded(baseline));
        for index in 0..512 {
            let _ = terms.mk_var(
                format!("clone_preflight_exact_census_{index}"),
                ay_core::Sort::Bool,
            );
            if terms.true_memory_bytes() > baseline {
                break;
            }
        }
        let growth = terms.true_memory_bytes().saturating_sub(baseline);
        assert!(growth > 0, "fixture must grow the source term store");
        assert!(
            growth < 64 * 1024,
            "fixture must remain inside the hot-path cache window"
        );
        assert!(
            !terms.instance_memory_exceeded(baseline),
            "cached hot-path census must still be stale for this regression"
        );

        let controls = TrustClauseDischargeControls {
            term_memory_limit: Some(baseline),
            ..TrustClauseDischargeControls::default()
        };
        assert!(!controls.term_store_clone_fits(
            &terms,
            ay_core::time::Instant::now() + Duration::from_secs(1),
        ));
    }
}

#[cfg(test)]
#[path = "proofs/deferred_trust_source_replay_tests.rs"]
mod deferred_trust_source_replay_tests;
