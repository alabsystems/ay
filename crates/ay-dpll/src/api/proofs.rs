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
pub use ay_proof::{AletheDialect, CarcaraSurface, CleanOnlySpelling};
use num_rational::BigRational;

use crate::array_proof_check::{check_array_clause_with_controls, ArrayStepVerdict};
use crate::bv_proof_check::{
    check_bv_assertions_unsat_with_controls, check_bv_clause_with_controls, BvStepVerdict,
};

mod artifact_types;
pub use artifact_types::{FarkasCertificate, ProofAcceptanceMode};

mod certification_effort;
pub(crate) use certification_effort::{
    certify_node, CertificationEffort, EffortShare, EnvelopeStop,
    CLOSED_SENTENCE_REFUTATION_ROUND_TRIPS,
};

mod discharge_controls;
#[cfg(test)]
pub(crate) use discharge_controls::arm_one_poll_memory_stop_for_testing;
pub(crate) use discharge_controls::TrustClauseDischargeControls;

#[cfg(test)]
mod consumer_subset_tests;

mod exact_query;
pub use exact_query::ExactSmtlibQueryBinding;

mod native_query;
pub(in crate::api) use native_query::NativeQueryObservation;
pub use native_query::{
    NativeDiagnosticSolve, NativeQueryBinding, NativeQueryDiagnosticDocument,
    NativeQueryProofEnvelope,
};

mod external_support;
pub use external_support::{ExternalProofAssumption, ExternalProofSupport};

#[cfg(test)]
pub(crate) fn native_support_test_executor(solver: &super::Solver) -> &crate::Executor {
    &solver.executor
}

#[cfg(test)]
pub(crate) fn native_support_test_executor_mut(solver: &mut super::Solver) -> &mut crate::Executor {
    &mut solver.executor
}

mod bv_lia_source_replay;
use bv_lia_source_replay::discharge_source_bv_lia;

mod bv_int_bridge_schema;
use bv_int_bridge_schema::discharge_bv_int_bridge_schema;

/// Bail-point probe for [`discharge_trust_clause_with_controls`], on the
/// existing `--probe-cert-reject` channel.
///
/// The per-clause discharge is a funnel of seven lanes that all return the same
/// `None`, so a rejection reports which clause failed but never which lane
/// declined it, nor whether a lane declined on evidence or on its count — the
/// distinction this whole investigation turns on. The two nested-solve lanes
/// therefore also report the conflict grant they drew from the certification
/// pool and the conflicts they spent (P4a.1: the count that replaced their
/// one-second wall). Lazily formatted; an unset flag costs one field read.
fn probe_discharge(message: impl FnOnce() -> String) {
    if ay_core::misc_cli_flags().probe_cert_reject {
        eprintln!("--probe-cert-reject: discharge_trust_clause {}", message());
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
    /// Strict validation was STOPPED before it could decide: the deferred-trust
    /// discharge (or the strict walk itself) was ended by a stop, never by
    /// evidence about the proof. The same proof may verify on a retry with
    /// more memory, or without the interrupt. A consumer must treat it as "no
    /// verdict", never as a rejection, and never as verified.
    Stopped(StrictVerdictStop),
}

/// What stopped a [`StrictProofVerdict::Stopped`] verdict.
///
/// There is no timeout: the export path installs no clock of its own, and
/// every fresh solve it runs is bounded by the solved query's own `:rlimit`
/// (P4a.1). That certification count's refusal is a [`StrictProofVerdict::Rejected`]
/// whose text says "certification effort exhausted". An independently installed
/// original caller boundary (including its work count) can instead stop a walk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum StrictVerdictStop {
    /// The solver's interrupt was raised (or, defensively, a wall-clock stop
    /// fired inside a fresh solve; the export path installs none), or an
    /// original caller boundary withdrew permission to continue.
    Interrupted,
    /// A memory ceiling stopped it. `term_store` when it was the term-store
    /// ceiling, a count of term-store bytes, rather than a process or lane
    /// memory reading.
    MemoryLimit {
        /// Whether the term-store ceiling (a count) stopped it.
        term_store: bool,
    },
}

impl StrictVerdictStop {
    /// The export's name for an envelope stop.
    pub(crate) fn of_envelope(stop: EnvelopeStop) -> Self {
        match stop {
            EnvelopeStop::Interrupt
            | EnvelopeStop::Backstop
            | EnvelopeStop::Caller
            | EnvelopeStop::WorkLimit => Self::Interrupted,
            EnvelopeStop::ProcessMemory | EnvelopeStop::LaneShare => {
                Self::MemoryLimit { term_store: false }
            }
            EnvelopeStop::TermMemory => Self::MemoryLimit { term_store: true },
        }
    }
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
    /// Strict validation was stopped before it decided
    /// ([`StrictProofVerdict::Stopped`]): no verdict, not a rejection.
    #[error("strict proof verification was stopped before it decided: {stop:?}")]
    StrictStopped {
        /// What stopped it.
        stop: StrictVerdictStop,
    },
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
    /// losing semantic identity, or that the caller asked for the artifact
    /// without it because it already holds the problem
    /// ([`super::Solver::export_last_unsat_artifact_without_problem_transport`])
    /// AND the document is printed in that problem's own spelling. A document
    /// the canonical-spelling rescue produced is checkable only against the
    /// canonical problem, so it always carries it, whatever the caller asked
    /// for. An authenticated native support projection likewise always carries
    /// its paired problem, as disclosed by [`Self::external_support`]. Neither
    /// changes the independent native [`Self::strict_verdict`].
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
    /// 4. Every other step is `Assume`, `Resolution`, or `Anchor`; native-only
    ///    certificate variants such as `NraSos` are outside this subset
    pub restricted_rule_subset: bool,
    /// Serialized LRAT certificate for the SAT backbone proof, when available.
    ///
    /// This is exported only when the stored clause trace is complete enough
    /// to replay into a standalone LRAT certificate.
    pub lrat_certificate: Option<Vec<u8>>,
    /// Structured Farkas certificates extracted from arithmetic theory lemmas.
    pub farkas_certificates: Vec<FarkasCertificate>,
    /// Whether pinned Carcara can check [`Self::alethe`] as rendered — the
    /// external-recheck surface verdict (owner decision D7, 2026-09-22).
    ///
    /// `Supported` means the document can be handed to Carcara as-is.
    /// `Unsupported { reason }` means it cannot — a `Seq`, `FloatingPoint` or
    /// `Char` sort, or a symbol that needs the AY/Z3 escape extension — and
    /// names the first offender. `CleanDialect { spelling }` means pinned
    /// Carcara parses it but refuses a step spelled for Clean's vendored
    /// Carcara (the default [`ay_proof::AletheDialect::Clean`]; see
    /// [`super::Solver::set_alethe_dialect`]); before 2026-09-30 such a
    /// document said `Supported`. `WithoutLetExpansion` means the document
    /// eliminates a `let` of [`Self::alethe_problem_smt2`] with `:rule let`,
    /// which pinned Carcara checks only in AY's canonical invocation
    /// `carcara check -- PROOF PROBLEM`, never under `--expand-let-bindings`;
    /// before 2026-09-30 it said `Supported`. The verdict is independent of
    /// [`Self::strict_verdict`]: an `Unsupported` artifact is exactly as
    /// strict-checked as a `Supported` one. A consumer that CLAIMS an external
    /// Carcara check must refuse an `Unsupported` artifact with `reason`,
    /// fail-closed; a consumer that claims none takes the artifact at the
    /// strict-checker class and never promotes it past it. The type is
    /// `#[non_exhaustive]`: treat a variant you do not know as unsupported.
    pub carcara_surface: CarcaraSurface,
    /// A native support export's full-query binding and exact emitted inputs.
    /// Only the live checked support workflow can populate this description.
    pub(crate) external_support: Option<ExternalProofSupport>,
}

/// Whether an exported artifact carries its own problem transport.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProblemTransport {
    /// Render `alethe_problem_smt2` from the proof's problem scope.
    Rendered,
    /// The caller holds the problem; leave `alethe_problem_smt2` as `None`.
    Omitted,
}

impl ProblemTransport {
    fn render(self, render: impl FnOnce() -> Option<String>) -> Option<String> {
        match self {
            Self::Rendered => render(),
            Self::Omitted => None,
        }
    }
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
///
/// Every fresh solve below (the guard, each clause's lanes, the whole-problem
/// fallback) runs on a share of `controls`' certification count, never on a
/// clock (P4a.1).
fn strict_verdict_with_deferred_trust(
    strict_quality: Result<ProofQuality, ProofCheckError>,
    diagnostic_quality: &ProofQuality,
    proof: &ay_core::Proof,
    terms: &ay_core::TermStore,
    assertions: &[ay_core::TermId],
    resolve_ctx: &ay_frontend::Context,
    controls: &TrustClauseDischargeControls,
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
    if executor_redecides_definitive_sat(resolve_ctx, controls) {
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
    let all_standalone = collected.iter().all(|(_, clause)| {
        discharge_trust_clause_with_controls(terms, clause, assertions, controls).is_some()
    });
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
    if executor_reconfirms_unsat(resolve_ctx, controls) {
        return StrictProofVerdict::Verified(diagnostic_quality.clone());
    }
    match check_bv_assertions_unsat_with_controls(
        terms,
        assertions,
        controls,
        EffortShare::Reconfirm,
    ) {
        BvStepVerdict::Valid => StrictProofVerdict::Verified(diagnostic_quality.clone()),
        BvStepVerdict::Invalid { .. } | BvStepVerdict::Unchecked { .. } => {
            let mut reason = "deferred-trust discharge failed: a collected trust clause is not \
                              a standalone theory tautology AND the problem assertions could \
                              not be independently re-solved as UNSAT"
                .to_string();
            if let Some(exhausted) = controls.effort.exhaustion() {
                reason.push_str("; ");
                reason.push_str(&exhausted);
            }
            StrictProofVerdict::Rejected(reason)
        }
    }
}

/// The verdict the export publishes once its discharge has returned: a stop
/// any lane latched is the verdict, whatever the lanes said, and a rejection
/// that a lane-local clock contributed to is that stop too. A stop only ever
/// ends lanes, so it is never published as [`StrictProofVerdict::Rejected`].
fn stopped_verdict(
    verdict: StrictProofVerdict,
    controls: &TrustClauseDischargeControls,
) -> StrictProofVerdict {
    let stop = match verdict {
        StrictProofVerdict::Rejected(_) => controls.decline_stop(),
        _ => controls.observed_stop(),
    };
    stop.map_or(verdict, |stop| {
        StrictProofVerdict::Stopped(StrictVerdictStop::of_envelope(stop))
    })
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
///
/// It runs on step (4)'s share of the certification count, the whole
/// allowance: the same bound the executor path's step (4) has, now inside the
/// outer `:rlimit` instead of unbounded.
fn executor_reconfirms_unsat(
    resolve_ctx: &ay_frontend::Context,
    controls: &TrustClauseDischargeControls,
) -> bool {
    if resolve_ctx.assertions.is_empty() {
        return false;
    }
    // Fresh `Executor` over a CLONE of the full solving context (terms, assertions,
    // logic, options incl. `:produce-proofs`) — the same setup the main solve used,
    // so the complete `check_sat` path re-decides. Executor::new()'s own SAT/theory
    // state is fresh; `check_sat` re-encodes the assertions from scratch.
    let mut exec = checking_executor();
    exec.ctx = resolve_ctx.clone();
    if controls
        .install_on(&mut exec, EffortShare::Reconfirm)
        .is_none()
    {
        return false;
    }
    let accepted = executor_reports_plain_strict_unsat(&mut exec);
    controls.settle_nested(&exec, EffortShare::Reconfirm);
    accepted && controls.accept_fits(&exec.ctx.terms)
}

/// A fresh executor for a solve whose verdict is used to CHECK another one.
///
/// Evidence policy P1 (2026-10-02): such a solve never runs a
/// satisfiability-preserving strengthening (`executor/strengthening.rs`),
/// which would let it re-derive the very fact it is checking.
fn checking_executor() -> crate::Executor {
    let mut exec = crate::Executor::new();
    exec.force_strengthenings_off();
    exec
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
///
/// It runs on the guard's share of the certification count (an eighth of the
/// allowance) and its grant of split-loop round trips, as the executor path's
/// guard does: it is downgrade-only, so a smaller share costs at most a
/// downgrade.
fn executor_redecides_definitive_sat(
    resolve_ctx: &ay_frontend::Context,
    controls: &TrustClauseDischargeControls,
) -> bool {
    if resolve_ctx.assertions.is_empty() {
        // An empty assertion set is trivially SAT, but there is nothing to forge:
        // never treat it as a forged-UNSAT signal.
        return false;
    }
    let mut exec = checking_executor();
    exec.ctx = resolve_ctx.clone();
    // A derived query: the guard reads the verdict and nothing else, so the
    // deletion minimizer's subset re-solves are pure waste here (see
    // `Executor::new_derived_query_executor`; core tracking itself stays on
    // because the named-core redirect is the faster engine on some shapes).
    exec.core_shrinking_suppressed = true;
    if controls.install_on(&mut exec, EffortShare::Guard).is_none() {
        return false;
    }
    let decided_sat = matches!(
        controls.in_round_trip_grant(EffortShare::Guard, || exec.check_sat()),
        Ok(result) if result.is_sat()
    );
    controls.settle_nested(&exec, EffortShare::Guard);
    decided_sat
}

/// Independently discharge a deferred trust step under the default envelope
/// (the ground allowance, no backstop): the test entry point.
#[cfg(test)]
pub(crate) fn discharge_trust_clause(
    terms: &ay_core::TermStore,
    clause: &[ay_core::TermId],
    assertions: &[ay_core::TermId],
) -> Option<()> {
    let controls = TrustClauseDischargeControls::default();
    discharge_trust_clause_with_controls(terms, clause, assertions, &controls)
}

/// Independently discharge a deferred trust step, accepting only a checked
/// non-empty theory tautology or a fresh strict refutation of the exact
/// authored assertions for a terminal empty clause. All unsupported,
/// satisfiable, unknown, malformed, or count-exhausted cases fail closed; a
/// stop declines too and stays latched on `controls`, which is how the
/// caller tells the two apart.
///
/// Every nested solve draws from `controls`' certification pool, in proof
/// order, and nothing here reads a clock.
pub(crate) fn discharge_trust_clause_with_controls(
    terms: &ay_core::TermStore,
    clause: &[ay_core::TermId],
    assertions: &[ay_core::TermId],
    controls: &TrustClauseDischargeControls,
) -> Option<()> {
    if controls.stop_requested(terms) {
        return None;
    }
    // Terminal empty trust clause → re-discharge the original problem assertions.
    if clause.is_empty() {
        let verdict =
            check_bv_assertions_unsat_with_controls(terms, assertions, controls, EffortShare::Pool);
        return match verdict {
            BvStepVerdict::Valid => {
                probe_discharge(|| "ACCEPT empty-clause bv-assertions-unsat".to_string());
                controls.accept_fits(terms).then_some(())
            }
            // SAT/Unknown/unmodellable: the UNSAT claim is not independently
            // reproducible. Never accept (fail closed).
            BvStepVerdict::Invalid { .. } | BvStepVerdict::Unchecked { .. } => {
                probe_discharge(|| "DECLINE empty-clause bv-assertions-unsat".to_string());
                None
            }
        };
    }
    discharge_trust_clause_impl(terms, clause, assertions, controls)
}

/// The non-empty clause's funnel.
fn discharge_trust_clause_impl(
    terms: &ay_core::TermStore,
    clause: &[ay_core::TermId],
    assertions: &[ay_core::TermId],
    controls: &TrustClauseDischargeControls,
) -> Option<()> {
    match check_bv_clause_with_controls(terms, clause, controls) {
        BvStepVerdict::Valid => {
            probe_discharge(|| "ACCEPT check_bv_clause".to_string());
            return controls.accept_fits(terms).then_some(());
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
    match check_array_clause_with_controls(terms, clause, controls) {
        ArrayStepVerdict::Valid => {
            probe_discharge(|| "ACCEPT check_array_clause".to_string());
            return controls.accept_fits(terms).then_some(());
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
        return controls.accept_fits(terms).then_some(());
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
    // family fell through to the whole-problem re-solve, which was then
    // wall-clock-budgeted — publishing a correct UNSAT as `unsat` or `unknown`
    // depending on machine load. Measured on the deductive-checks `i = i + 1usize` loop-counter obligation:
    // stage (3) accepted 0 times, stage (4) 28, and the depth guard rejected
    // 36. See `bv_int_bridge_schema` for the derivations and the narrowness
    // pins.
    if discharge_bv_int_bridge_schema(terms, clause, assertions) {
        probe_discharge(|| "ACCEPT discharge_bv_int_bridge_schema".to_string());
        return controls.accept_fits(terms).then_some(());
    }
    if !controls.clone_fits(terms) {
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
    // to spend the generic probe's whole budget (then a one-second wall) at
    // every depth before this stronger check succeeded in milliseconds. Since `P ∧ ¬C` UNSAT also
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
    // only accepting outcome; Sat, Unknown, a spent grant and a stop all
    // decline.
    if !assertions.is_empty() {
        let mut entail = ay_frontend::Context::new();
        entail.terms = arena;
        entail.assertions = assertions.to_vec();
        entail.assertions.extend_from_slice(&negated);
        let mut exec = checking_executor();
        exec.ctx = entail;
        let accepted = run_pool_lane(controls, &mut exec, "entailment-lane")?;
        if accepted && controls.accept_fits(&exec.ctx.terms) {
            return Some(());
        }
        if controls.stop_requested(&exec.ctx.terms) {
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
    // inconsistency. `Sat`, `Unknown`, a spent grant, a stop, missing proof, or
    // any trust/hole in that proof all decline.
    let mut probe = ay_frontend::Context::new();
    probe.terms = arena;
    probe.assertions = negated;
    let mut exec = checking_executor();
    exec.ctx = probe;
    let accepted = run_pool_lane(controls, &mut exec, "standalone-lane")?;
    (accepted && controls.accept_fits(&exec.ctx.terms)).then_some(())
}

/// One nested-solve lane of the per-clause discharge on a draw from the
/// certification pool and the lane's grant of split-loop round trips: arm
/// `exec`, re-solve it, debit what it spent, latch its stop. `None`: nothing
/// ran (the pool is spent or a stop fired first); otherwise whether the
/// re-solve was a plain-strict `unsat`.
fn run_pool_lane(
    controls: &TrustClauseDischargeControls,
    exec: &mut crate::Executor,
    lane: &str,
) -> Option<bool> {
    let Some(grant) = controls.install_on(exec, EffortShare::Pool) else {
        probe_discharge(|| {
            format!(
                "DECLINE {lane}: {}",
                controls
                    .effort
                    .exhaustion()
                    .unwrap_or_else(|| format!("stopped ({:?})", controls.observed_stop()))
            )
        });
        return None;
    };
    let accepted = controls.in_round_trip_grant(EffortShare::Pool, || {
        executor_reports_plain_strict_unsat(exec)
    });
    controls.settle_nested(exec, EffortShare::Pool);
    probe_discharge(|| {
        format!(
            "{} {lane} grant={grant} conflicts={} pool_spent={} unknown.reason={:?}",
            if accepted { "ACCEPT" } else { "DECLINE" },
            exec.statistics().conflicts,
            controls.effort.spent(),
            exec.statistics().get_string("unknown.reason"),
        )
    });
    Some(accepted)
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
/// 4. Other variants must be explicitly supported structural steps
fn check_restricted_rule_subset(quality: &ProofQuality, proof: &ay_core::Proof) -> bool {
    use ay_core::TheoryLemmaKind;

    if quality.trust_count > 0 || quality.hole_count > 0 {
        return false;
    }

    proof.steps.iter().all(|step| match step {
        ProofStep::Assume(_) | ProofStep::Resolution { .. } | ProofStep::Anchor { .. } => true,
        ProofStep::Step { rule, .. } => is_restricted_rule_subset_rule(rule),
        // Native validity does not imply support in the consumer's rule subset.
        ProofStep::TheoryLemma { kind, .. } => matches!(
            kind,
            TheoryLemmaKind::EufTransitive
                | TheoryLemmaKind::EufCongruent
                | TheoryLemmaKind::EufCongruentPred
        ),
        // In particular, NraSos is independently checked (and lowers to checked
        // Alethe) but is no subset rule. Future native variants need admission.
        _ => false,
    })
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
    /// Describe an authenticated supported-premise transport, when one was
    /// required. Such an artifact always carries its paired SMT-LIB problem.
    #[must_use]
    pub fn external_support(&self) -> Option<&ExternalProofSupport> {
        self.external_support.as_ref()
    }

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
            (StrictProofVerdict::Stopped(stop), _) => {
                Err(ProofAcceptanceError::StrictStopped { stop: *stop })
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
    /// The document renders what the strict checker accepted for EVERY sort
    /// (owner decision D7, 2026-09-22). A `Seq`, `FloatingPoint` or `Char`
    /// sort, or a symbol spelled with the AY/Z3 escape extension, is not a
    /// reason for `None`: the artifact is published and
    /// [`UnsatProofArtifact::carcara_surface`] discloses that pinned Carcara
    /// cannot parse it, so only a consumer claiming an external check refuses
    /// it. Before D7 such proofs vanished here and reached every consumer as
    /// "UNSAT but no strict-checked proof artifact was produced".
    ///
    /// Returns `None` if:
    /// - The last result was not UNSAT
    /// - Proof output was not requested for that solve
    /// - No proof was generated
    /// - A query-sealed proof has no current authenticated Alethe surface
    /// - Bounded Alethe rendering fails or exhausts its work budget
    /// - Rendering fails only for the AUTHORED assertion spelling, and the
    ///   canonical-spelling re-render that rescues that case would publish a
    ///   `Rejected` strict verdict.
    ///
    /// What the canonical-spelling rescue widens is the DECISION to publish,
    /// and only in one direction: it turns a `None` into an artifact whose
    /// strict verdict this boundary would have accepted anyway had the
    /// spelling been printable. It never turns a refused render into a refused
    /// verdict on the record.
    ///
    /// It does not restore the authored spelling, and a rescued artifact is
    /// not the document the authored spelling would have produced. Both halves
    /// — `alethe` and `alethe_problem_smt2` — are re-rendered in the CANONICAL
    /// spelling `check_proof_strict` validated, so they agree with each other
    /// throughout; a consumer that diffs either against the submitted source
    /// text will see the canonical form, not its own.
    #[must_use]
    pub fn export_last_unsat_artifact(&self) -> Option<UnsatProofArtifact> {
        self.export_last_unsat_artifact_with(ProblemTransport::Rendered)
    }

    /// [`Self::export_last_unsat_artifact`] for a caller that already holds
    /// the problem: `alethe_problem_smt2` is not rendered and is `None` —
    /// unless the document had to be re-printed in the canonical spelling,
    /// which the caller's transcript does not match; then the canonical
    /// problem it does match is rendered. An authenticated native support
    /// projection also always carries its paired problem: the caller's full
    /// query is not the projected checker input.
    ///
    /// A push/pop session asserts every fact once and checks many queries
    /// against its live stack. Rendering the whole live stack again for every
    /// UNSAT would make the artifact stream cost the SUM of the rows' cones —
    /// the quadratic term a session exists to remove. The caller identifies
    /// the problem instead by its own transcript of the live assertions (and,
    /// in `ay-bindings`' `ExecutionSession`, by the chain digest of that live
    /// stack). Every other field, including the native strict verdict against
    /// the live problem scope, is exactly what the rendering export returns.
    #[must_use]
    pub fn export_last_unsat_artifact_without_problem_transport(
        &self,
    ) -> Option<UnsatProofArtifact> {
        self.export_last_unsat_artifact_with(ProblemTransport::Omitted)
    }

    fn export_last_unsat_artifact_with(
        &self,
        transport: ProblemTransport,
    ) -> Option<UnsatProofArtifact> {
        let proof = self.executor.last_proof()?;
        let finite_enum = self.executor.last_proof_has_finite_enum_sidecar();
        let strict_quality = self.executor.check_proof_strict_with_datatypes(proof);
        let support = strict_quality.as_ref().ok().and_then(|_| {
            self.executor
                .checked_external_proof_support_for_current_proof()
        });
        // A datatype presentation retains the full authenticated scope. Its
        // standard tester spellings belong to one paired render; ordinary
        // omitted-problem exports keep their historical source presentation.
        let datatype_pair = if transport == ProblemTransport::Rendered && strict_quality.is_ok() {
            self.executor.try_export_last_unsat_datatype_pair()
        } else {
            None
        };
        // D7: a support seal supplies one checked proof/problem/surface pair.
        // Other exports read the SAME proof and override table used by their
        // render, so the disclosure describes their own bytes — the canonical
        // document after a rescue, the authored one otherwise. A document that kept a
        // spelling only Clean's vendored Carcara accepts is `CleanDialect`,
        // as the CLI's certificate line says `clean-dialect` for it, and one
        // that eliminated a problem `let` with `:rule let` is
        // `WithoutLetExpansion` (`without-let-expansion`).
        let (alethe, alethe_problem_smt2, canonical_rescue, carcara_surface) =
            if let Some(support) = support.as_ref() {
                (
                    support.proof_text().to_owned(),
                    Some(support.problem_text().to_owned()),
                    false,
                    support.surface().clone(),
                )
            } else if let Some((proof, problem, surface)) = datatype_pair {
                (proof, Some(problem), false, surface)
            } else {
                let (alethe, problem, canonical_rescue, dialect) =
                    self.render_artifact_surface(transport, strict_quality.is_ok())?;
                let surface = self
                    .executor
                    .carcara_surface_for_last_export(canonical_rescue)?
                    .with_dialect_report(&dialect);
                (alethe, problem, canonical_rescue, surface)
            };
        let terms = self.executor.terms();
        let evaluation = evaluate_proof_artifact_boundary(proof, terms, strict_quality)?;

        let restricted_rule_subset_ok =
            check_restricted_rule_subset(&evaluation.diagnostic_quality, proof);
        let ProofArtifactEvaluation {
            diagnostic_quality,
            partial_check,
            strict_quality,
        } = evaluation;
        let strict_verdict =
            self.artifact_strict_verdict(finite_enum, strict_quality, &diagnostic_quality, proof);
        // The canonical-spelling rescue above exists to keep a CHECKED
        // refutation from being withdrawn over an unprintable authored
        // spelling. It is not a second chance for a refutation the strict
        // checker refused: before that rescue this boundary returned `None`
        // for every print error, so publishing a `Rejected` artifact here
        // would be new behaviour that the rescue never claimed, and a
        // consumer that only inspects `alethe` would read a document it was
        // previously never handed. Re-withdraw it, exactly as before.
        if canonical_rescue && !matches!(&strict_verdict, StrictProofVerdict::Verified(_)) {
            return None;
        }
        let restricted_rule_subset =
            matches!(&strict_verdict, StrictProofVerdict::Verified(_)) && restricted_rule_subset_ok;
        let farkas_certificates = extract_farkas_certificates(proof);

        Some(UnsatProofArtifact {
            alethe,
            alethe_problem_smt2,
            quality: diagnostic_quality,
            partial_check: Some(partial_check),
            strict_verdict,
            restricted_rule_subset,
            lrat_certificate: self.executor.last_lrat_certificate().map(<[u8]>::to_vec),
            farkas_certificates,
            carcara_surface,
            external_support: support.as_ref().map(|support| support.disclosure().clone()),
        })
    }

    /// The Alethe document of the last UNSAT proof, its problem transport
    /// (per `transport`), whether the canonical-spelling rescue produced it,
    /// and the dialect report of exactly the published render.
    fn render_artifact_surface(
        &self,
        transport: ProblemTransport,
        strict_ok: bool,
    ) -> Option<(String, Option<String>, bool, ay_proof::AletheDialectReport)> {
        // Each render is captured on its own, so the dialect report describes
        // exactly the document published, never a refused first attempt.
        let (ordinary_surface, ordinary_dialect) = ay_proof::capture_alethe_dialect_report(|| {
            self.executor
                .try_export_last_proof_alethe_for_problem_scope()
        });
        Some(match ordinary_surface? {
            Ok(alethe) => (
                alethe,
                transport.render(|| self.executor.try_export_last_proof_alethe_problem_smt2()),
                false,
                ordinary_dialect,
            ),
            Err(AlethePrintError::UnsupportedArrayExtensionality { id }) if strict_ok => {
                let (surface, dialect) = ay_proof::capture_alethe_dialect_report(|| {
                    self.executor.try_export_extensionality_artifact_surface(id)
                });
                (
                    surface?.ok()?,
                    transport.render(|| self.executor.try_export_last_proof_alethe_problem_smt2()),
                    false,
                    dialect,
                )
            }
            // The printer refused ONE SPELLING, not the refutation. Authored
            // source syntax is a presentation channel, and it can be one the
            // printer has no bridge for: an authored `(bvadd #x08 #x08)` and the
            // canonical `#b00010000` in congruent positions of one `cong` step, or an
            // `(assert (and A B (or C (and false D))))` whose canonical term
            // flattens to `(and A B C)` and leaves the proof's `and_pos` steps
            // with no printable projection off the authored grouping. Either
            // way the document is refused although `check_proof_strict`
            // accepted the derivation, and withdrawing the artifact there
            // reports a checked UNSAT as `Unknown` at every strict consumer.
            //
            // WHICH spellings lack a bridge is not a fixed set — it shrinks as
            // bridges are added, and neither this arm nor the gate below
            // depends on the membership of that set. What they depend on is
            // that the set is non-empty and fail-closed, which is a property of
            // the printer's posture, not of any one fixture.
            //
            // This boundary owns the PAIRED problem transport, so it can
            // re-render both halves in the canonical spelling the strict
            // checker validated and disclose a document that agrees with the
            // problem shipped beside it. `(get-proof)` and file-backed proof
            // output keep the loud refusal, because the problem file they are
            // checked against is not AY's to re-render.
            //
            // Nothing is lowered. The canonical retry goes through the same
            // fail-closed printer, so an override-independent refusal — a
            // missing Farkas certificate, an unrepresentable Skolem step, a
            // non-problem `assume` — still yields `None` here. MEASURED, that
            // happens two ways and the `?` / `.ok()?` below treat them alike:
            // the same error is raised again, OR the canonical exporter
            // DECLINES the proof outright (`None`) because it has no canonical
            // spelling to fall back to — a sealed finite-enum proof, whose
            // surface overrides are its authority rather than a presentation
            // preference, is the case that exists today.
            //
            // The arm is deliberately BROAD, and the retry — not the error
            // type — is what separates an authored-spelling refusal from an
            // override-independent one. `AlethePrintError` carries no
            // provenance field, and every variant the authored channel can
            // raise (`InvalidSurfaceStep`, `InvalidCongruenceStep`,
            // `InvalidArrayStep`, `AmbiguousSymbolSort`,
            // `UndeclarableProofSymbols`, `ResugaredWitnessPrintedRaw`) is
            // also raised for causes that have nothing to do with it, so no
            // variant list draws the line. Withholding the overrides and
            // re-printing does: a refusal the spelling caused disappears, a
            // refusal the derivation caused survives. `Some(Ok(_))` from the
            // canonical exporter is the only outcome that means rescued.
            //
            // What the retry does NOT decide is the VERDICT, so `canonical_rescue`
            // carries the fact of the rescue to the gate below: this arm must
            // only ever turn a `None` into a strictly ACCEPTED artifact. What
            // it then publishes is the CANONICAL document and the canonical
            // problem transport, whatever `transport` asked for: a caller's
            // own problem is the AUTHORED one, which the canonical `assume`s
            // do not match (measured: 25 of 79 session rows were Carcara-valid
            // only against the canonical problem the session export dropped).
            Err(_) => {
                let (surface, dialect) = ay_proof::capture_alethe_dialect_report(|| {
                    self.executor
                        .try_export_last_proof_alethe_for_problem_scope_canonical()
                });
                (
                    surface?.ok()?,
                    self.executor
                        .try_export_last_proof_alethe_problem_smt2_canonical(),
                    true,
                    dialect,
                )
            }
        })
    }

    /// Strict verdict with the deferred-trust rescue: a proof whose only
    /// strict failure is a `trust` step demoted from genuine BV/array theory
    /// reasoning is accepted IFF every such clause is independently
    /// re-discharged as a theory tautology (¬clause UNSAT). All other strict
    /// failures stay Rejected. Stays at the strict-checked (SmtBacked) tier.
    fn artifact_strict_verdict(
        &self,
        finite_enum: bool,
        strict_quality: Result<ProofQuality, ProofCheckError>,
        diagnostic_quality: &ProofQuality,
        proof: &ay_core::Proof,
    ) -> StrictProofVerdict {
        // A walk the strict checker's envelope CANCELLED reached no verdict:
        // publish the stop it recorded, never a rejection.
        if matches!(strict_quality, Err(ProofCheckError::Cancelled)) {
            let stop = self.executor.certification_stop().map_or(
                StrictVerdictStop::Interrupted,
                StrictVerdictStop::of_envelope,
            );
            return StrictProofVerdict::Stopped(stop);
        }
        if finite_enum {
            return match strict_quality {
                Ok(quality) => StrictProofVerdict::Verified(quality),
                Err(error) => StrictProofVerdict::Rejected(error.to_string()),
            };
        }
        // The plain strict checker accepted: `strict_verdict_with_deferred_trust`
        // returns this verdict before reading the context, so do not pay for
        // cloning the whole frontend context (every term of the session) on
        // the path every accepted artifact takes.
        let error = match strict_quality {
            Ok(quality) => return StrictProofVerdict::Verified(quality),
            Err(error) => error,
        };
        let terms = self.executor.terms();
        let problem_assertions = self.executor.problem_assertions_for_strict_proof();
        let mut resolve_ctx = self.executor.context().clone();
        resolve_ctx.assertions = problem_assertions;
        let assertions = resolve_ctx.assertions.as_slice();
        // Deferred-trust validation can run fresh solvers. Those are
        // semantic checks of this already-produced proof, not new caller
        // decisions, so they must preserve the sealed CNF byte-for-byte.
        let _export_suppression = crate::Executor::suppress_bv_cnf_export_for_internal_checks();
        let controls = self.artifact_discharge_controls();
        let verdict = strict_verdict_with_deferred_trust(
            Err(error),
            diagnostic_quality,
            proof,
            terms,
            assertions,
            &resolve_ctx,
            &controls,
        );
        stopped_verdict(verdict, &controls)
    }

    /// The envelope of the export's deferred-trust discharge: the solved
    /// query's own `:rlimit` as its count, this solver's interrupt and memory
    /// ceilings, and NO backstop. No solve is active here, so no clock is left
    /// to stop it: every fresh solve it runs is bounded by the count alone.
    fn artifact_discharge_controls(&self) -> TrustClauseDischargeControls {
        let tighter = |left: Option<usize>, right: Option<usize>| match (left, right) {
            (Some(left), Some(right)) => Some(left.min(right)),
            (limit, None) | (None, limit) => limit,
        };
        TrustClauseDischargeControls::new(
            Some(self.interrupt.clone()),
            None,
            tighter(self.executor.memory_limit(), self.memory_limit),
            tighter(self.executor.term_memory_limit(), self.term_memory_limit),
            CertificationEffort::for_query(&self.executor),
        )
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
        if self.executor.has_strict_native_nra_sos_bundle_state() {
            // A stale SOS seal is terminal, just like the BV/LIA seal below.
            // Generic rebuilding must not renew expired exact-query evidence.
            return self
                .executor
                .strict_native_nra_sos_bundle_for_proof(proof)
                .cloned();
        }
        if self.executor.has_strict_native_bv_lia_bundle_state() {
            // Presence selects the exact sealed W7 exporter. A stale state is
            // terminal: falling through would let the generic builder mint a
            // fresh bundle after the authenticated term snapshot changed.
            return self
                .executor
                .strict_native_bv_lia_bundle_for_proof(proof)
                .cloned();
        }
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
    ///
    /// # Panics
    ///
    /// Panics when `term` is not a live handle of this solver. Use
    /// [`Self::try_render_term_canonical`] for a fallible version.
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
#[path = "proofs/discharge_controls_tests.rs"]
mod discharge_controls_tests;

#[cfg(test)]
#[path = "proofs/stopped_verdict_tests.rs"]
mod stopped_verdict_tests;

#[cfg(test)]
#[path = "proofs/deferred_trust_source_replay_tests.rs"]
mod deferred_trust_source_replay_tests;

#[cfg(feature = "z3-compat-internals")]
#[path = "proofs/dag_snapshot.rs"]
mod dag_snapshot;
#[cfg(test)]
#[path = "proofs/round_trip_grant_tests.rs"]
mod round_trip_grant_tests;
#[cfg(feature = "z3-compat-internals")]
pub use dag_snapshot::{
    NativeProofApplication, NativeProofDag, NativeProofInputBinding, NativeProofTrackingCache,
};

#[cfg(feature = "z3-compat-internals")]
#[path = "proofs/clause_trail.rs"]
mod clause_trail;
#[cfg(feature = "z3-compat-internals")]
pub use clause_trail::{NativeClauseEvent, NativeClauseOrigin, NativeClauseTrail};
