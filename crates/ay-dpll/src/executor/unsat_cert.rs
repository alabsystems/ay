// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mandatory UNSAT certification at the public verdict boundary.
//!
//! Inner solver lanes return a provisional [`SolveResult::Unsat`].  A public
//! caller may observe that verdict only after the finished proof has passed the
//! strict checker against the exact authored assertion/assumption query epoch.

use std::cell::Cell;

use ay_core::TermId;

use super::Executor;
use crate::executor_types::{SolveResult, UnknownOrigin};

thread_local! {
    /// Re-entrancy depth for the deferred-trust discharge.
    ///
    /// The discharge runs nested solves, and those solves reach this same
    /// publication funnel. Admitting the rescue only at depth 0 bounds the
    /// recursion; nested certifications use plain strict checking, which
    /// terminates. See [`Executor::discharge_trust_steps_for_certification`].
    static TRUST_DISCHARGE_DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// Print a certification-rejection diagnostic when `AY_PROBE_CERT_REJECT` is set.
///
/// Downstream embedders (deductive-checks) surface only the opaque
/// `(incomplete self-check-rejected)` reason code, so the gate that actually
/// refused a refutation -- and, for a strict-checker refusal, the Alethe rule
/// and step it names -- is otherwise unobservable outside this crate. The
/// message is computed lazily so an unset variable costs one `var_os` probe.
fn probe_cert_reject(message: impl FnOnce() -> String) {
    if std::env::var_os("AY_PROBE_CERT_REJECT").is_some() {
        eprintln!("AY_PROBE_CERT_REJECT: {}", message());
    }
}

/// True while a nested deferred-trust discharge solve is in flight.
///
/// Those solves run in a FRESH `Executor` purely to corroborate the outer
/// verdict, and they reach the same publication funnel. Their per-verdict
/// diagnostics describe an INTERNAL probe, not the user's query, and the
/// transcript is a shared stream -- so a probe that fails its own
/// certification must not narrate that on the user's stderr while the OUTER
/// certification goes on to succeed.
pub(crate) fn inside_trust_discharge_solve() -> bool {
    TRUST_DISCHARGE_DEPTH.with(|depth| depth.get()) > 0
}

/// One-shot capability proving that a provisional UNSAT verdict passed strict
/// proof validation for its exact public query epoch.
///
/// The tuple field is private to this module.  Consequently, code outside this
/// module can move the capability to the public result boundary but cannot mint
/// one.  The epoch is retained in the token so stale tokens are distinguishable
/// while debugging even though the token is consumed immediately.
#[derive(Debug)]
pub(crate) struct UnsatCertificate(u64);

/// Exact authenticated inputs for one public decision query.
///
/// The initial pre-elaboration assertion snapshot may be replaced once by the
/// frontend's materialized SMT-LIB 2.7 schematic instances before assumptions
/// are bound. It is immutable after that pre-solve rebind.
#[derive(Debug, Clone)]
pub(super) struct UnsatQueryEpoch {
    id: u64,
    assertions: Vec<TermId>,
    assumptions: Option<Vec<TermId>>,
    /// The solver-declared EXTENSION of this query's obligation.
    ///
    /// Empty for every ordinary query, and writable only through
    /// [`Executor::declare_pareto_front_exhaustion_extension`], which REBUILDS
    /// its terms from the executor's own objectives and emitted points rather
    /// than accepting a caller-supplied slice. That restriction is the whole
    /// safety argument: no caller can widen the obligation, so this cannot
    /// become a general escape hatch.
    ///
    /// #pareto-terminal-obligation — a Pareto `(check-sat)` after N emitted
    /// points does not ask "is the authored formula unsatisfiable"; it asks
    /// "is there a feasible point no emitted point dominates-or-equals". The
    /// refutation the seed probe produces is of `authored AND blocking`, and
    /// that is exactly the claim `unsat` makes there (Z3 behaves the same).
    /// Certifying it against `authored` ALONE rejects a correct refutation.
    ///
    /// This certifies the refutation only. It deliberately does NOT cover the
    /// separate enumeration-completeness claim that the emitted set IS the
    /// whole front — that rests on the lex-push construction and its debug
    /// assertions, exactly as before.
    declared_extension: Vec<TermId>,
}

/// Typed failure from the mandatory UNSAT publication gate.
#[derive(Debug, thiserror::Error)]
pub(crate) enum UnsatCertificationError {
    /// No public-query epoch was established for this provisional result.
    #[error("no public UNSAT query epoch is active")]
    MissingEpoch,
    /// The public wrapper did not bind the assumptions before solving.
    #[error("the public UNSAT query epoch has no bound assumption set")]
    UnboundAssumptions,
    /// A wrapper attempted to certify a different assumption set.
    #[error("the UNSAT publication assumptions do not match the bound query epoch")]
    AssumptionEpochMismatch,
    /// Proof-source provenance is absent or belongs to another assertion epoch.
    #[error("the UNSAT proof provenance is not bound to the authored assertion epoch")]
    AssertionEpochMismatch,
    /// An internal assumption used by a redirect was not authored by this query.
    #[error("the UNSAT proof contains an assumption outside the authored query epoch")]
    ForeignInternalAssumption,
    /// No refutation artifact was produced.
    #[error("the provisional UNSAT verdict has no proof")]
    MissingProof,
    /// The strict proof checker rejected the refutation.
    #[error("strict UNSAT proof validation failed: {reason}")]
    StrictProofRejected { reason: String },
}

impl Executor {
    /// Whether an assumption leaf belongs to the authenticated public query.
    ///
    /// Named-core solving may assumption-track an equivalence-exact rewrite of
    /// an authored named assertion. `named_assert_rewrites` is populated only
    /// by per-assertion equivalence-preserving passes and maps the rewritten
    /// term back to its authored root, so accepting that root relationship does
    /// not widen the query. Solver-generated assumptions without such a root
    /// remain foreign.
    fn query_authorizes_assumption(
        &self,
        term: TermId,
        authored_assertions: &[TermId],
        public_assumptions: &[TermId],
    ) -> bool {
        authored_assertions.contains(&term)
            || public_assumptions.contains(&term)
            || self
                .named_assert_rewrites
                .get(&term)
                .is_some_and(|root| authored_assertions.contains(root))
    }

    /// Canonically reject a definite verdict that lacks its one-shot
    /// publication capability.
    ///
    /// This is shared by strict UNSAT certification and the final native API
    /// wrapper boundary. It publishes the registered verdict-certification
    /// origin immediately, revoking every model/proof/core/optimum artifact so
    /// the executor state and returned wrapper cannot disagree.
    pub(crate) fn reject_uncertified_verdict_for_publication(
        &mut self,
        diagnostic: String,
    ) -> SolveResult {
        self.publish_unknown_from_origin(UnknownOrigin::VerdictCertification);
        self.record_model_validation_unknown_diagnostic(diagnostic);
        SolveResult::Unknown
    }

    /// Start a new immutable public-query epoch.
    ///
    /// Called only after the preceding query artifacts have been invalidated.
    /// [`Self::rebind_unsat_query_epoch_assertions`] may replace this initial
    /// snapshot once command elaboration has materialized authenticated
    /// schematic instances, but no solver-owned transformation may intervene.
    pub(super) fn begin_unsat_query_epoch(&mut self, assertions: &[TermId]) {
        self.next_unsat_query_epoch = self.next_unsat_query_epoch.wrapping_add(1);
        // Zero is reserved as the visibly-uninitialized value in diagnostics.
        if self.next_unsat_query_epoch == 0 {
            self.next_unsat_query_epoch = 1;
        }
        self.unsat_query_epoch = Some(UnsatQueryEpoch {
            id: self.next_unsat_query_epoch,
            assertions: assertions.to_vec(),
            assumptions: None,
            declared_extension: Vec::new(),
        });
        self.last_unsat_certificate = None;
    }

    /// Replace the pre-elaboration assertion snapshot with the exact roots
    /// produced by the frontend for this same public query.
    ///
    /// SMT-LIB 2.7 schematic assertions are authenticated authored inputs, but
    /// their concrete instances do not exist until command elaboration. This
    /// rebind is permitted only before assumptions have been attached and
    /// before solving starts. Any lifecycle violation drops the epoch so a
    /// later provisional UNSAT fails closed instead of borrowing authority.
    pub(super) fn rebind_unsat_query_epoch_assertions(&mut self, assertions: &[TermId]) -> bool {
        let can_rebind = self
            .unsat_query_epoch
            .as_ref()
            .is_some_and(|epoch| epoch.assumptions.is_none());
        if !can_rebind {
            self.unsat_query_epoch = None;
            self.last_unsat_certificate = None;
            return false;
        }
        if let Some(epoch) = self.unsat_query_epoch.as_mut() {
            epoch.assertions.clear();
            epoch.assertions.extend_from_slice(assertions);
            self.last_unsat_certificate = None;
            true
        } else {
            self.last_unsat_certificate = None;
            false
        }
    }

    /// Bind the exact caller-supplied assumptions before entering a solve.
    ///
    /// Rebinding is accepted only when it is byte-for-byte identical. This lets
    /// narrow wrapper layers be idempotent without permitting an internal retry
    /// to change the authority of an already-started public query.
    pub(crate) fn bind_unsat_query_assumptions(&mut self, assumptions: &[TermId]) {
        let Some(epoch) = self.unsat_query_epoch.as_mut() else {
            return;
        };
        match &epoch.assumptions {
            Some(bound) if bound != assumptions => {
                // Preserve the first binding. Certification will reject the
                // wrapper's later, mismatching assumption slice.
            }
            Some(_) => {}
            None => epoch.assumptions = Some(assumptions.to_vec()),
        }
    }

    /// The solver-declared obligation extension for the active query, if any.
    /// Empty for every query but a Pareto terminal (#pareto-terminal-obligation).
    pub(crate) fn declared_obligation_extension(&self) -> Vec<TermId> {
        self.unsat_query_epoch
            .as_ref()
            .map(|epoch| epoch.declared_extension.clone())
            .unwrap_or_default()
    }

    /// Declare that THIS query's obligation is `authored AND blocking`, where
    /// the blocking conjuncts are rebuilt here from the executor's own
    /// objectives and the points Pareto enumeration has already emitted.
    ///
    /// #pareto-terminal-obligation. Called only from the Pareto terminal arm,
    /// which is publishing "the front is exhausted" — a refutation of
    /// `authored AND blocking`, not of `authored`.
    ///
    /// The blocking terms are RECONSTRUCTED rather than passed in. A setter
    /// that accepted a caller-supplied `&[TermId]` would let any caller widen
    /// the certified obligation to anything at all, including `false`; because
    /// this one derives its terms from `emitted`, the worst a buggy enumeration
    /// can do is certify a refutation of a DIFFERENT (still authored-plus-
    /// blocking) query — it can never certify a refutation of the empty
    /// obligation.
    pub(crate) fn declare_pareto_front_exhaustion_extension(&mut self, blocking: &[TermId]) {
        // Ownership check: every term must be one this executor just built for
        // its own emitted points. Rebuilding is done by the caller through
        // `mk_not_dominated_or_equal_by`, which reads `ctx.objectives()`; the
        // assertion here keeps the coupling explicit if that ever changes.
        debug_assert!(
            !self.ctx.objectives().is_empty(),
            "pareto obligation extension declared without objectives"
        );
        if let Some(epoch) = self.unsat_query_epoch.as_mut() {
            epoch.declared_extension = blocking.to_vec();
        }
    }

    /// Strictly certify a provisional public UNSAT result and mint its token.
    fn mint_unsat_certificate(
        &self,
        assumptions: &[TermId],
    ) -> Result<UnsatCertificate, UnsatCertificationError> {
        let epoch = self
            .unsat_query_epoch
            .as_ref()
            .ok_or(UnsatCertificationError::MissingEpoch)?;
        let bound = epoch
            .assumptions
            .as_deref()
            .ok_or(UnsatCertificationError::UnboundAssumptions)?;
        if bound != assumptions {
            return Err(UnsatCertificationError::AssumptionEpochMismatch);
        }

        // The public-query lifecycle installs this provenance from the exact
        // authored/materialized assertion snapshot before any preprocessing or
        // theory axiom can alter the working stack. Requiring exact vector
        // equality prevents a proof from borrowing authority from an older or
        // solver-generated assertion set.
        let Some(provenance) = self.proof_problem_assertion_provenance.as_ref() else {
            probe_cert_reject(|| "assertion epoch: no proof provenance is installed".to_string());
            return Err(UnsatCertificationError::AssertionEpochMismatch);
        };
        if provenance.original_problem_assertions != epoch.assertions {
            probe_cert_reject(|| {
                let render = |ids: &[TermId]| -> String {
                    ids.iter()
                        .enumerate()
                        .map(|(i, t)| {
                            let rendered = ay_proof::format_term_alethe(&self.ctx.terms, *t);
                            format!("    [{i}] {rendered}")
                        })
                        .collect::<Vec<_>>()
                        .join("\n")
                };
                format!(
                    "assertion epoch mismatch\n  provenance.original_problem_assertions \
                     ({}):\n{}\n  epoch.assertions ({}):\n{}",
                    provenance.original_problem_assertions.len(),
                    render(&provenance.original_problem_assertions),
                    epoch.assertions.len(),
                    render(&epoch.assertions),
                )
            });
            return Err(UnsatCertificationError::AssertionEpochMismatch);
        }

        // Named-core redirects temporarily move authored assertions into the
        // executor's assumption slot. Such terms remain legitimate only when
        // they occur in the frozen base or in the caller's exact assumption
        // slice. No solver-generated term may expand the proof's authority.
        if self
            .last_assumptions
            .iter()
            .flatten()
            .any(|&term| !self.query_authorizes_assumption(term, &epoch.assertions, assumptions))
        {
            return Err(UnsatCertificationError::ForeignInternalAssumption);
        }
        // The declared extension travels in its own slot and must never also
        // arrive through `last_assumptions`, which the check above keeps
        // strict. Overlap would mean a solver-generated term had reached the
        // assumption channel, and that is exactly the tripwire to preserve.
        debug_assert!(
            self.last_assumptions
                .iter()
                .flatten()
                .all(|term| { !epoch.declared_extension.contains(term) }),
            "BUG: the Pareto obligation extension leaked into last_assumptions"
        );

        let proof = self
            .last_proof
            .as_ref()
            .ok_or(UnsatCertificationError::MissingProof)?;
        match self.check_proof_strict_with_datatypes(proof) {
            Ok(_) => {}
            // A trust-kind rejection is the ONLY one eligible for independent
            // re-discharge; every other strict failure is a real structural
            // rejection and stays one.
            //
            // `TheoryLemmaKind::Generic` belongs here even though the checker
            // reports it as `UnsupportedTheoryLemmaKind` rather than `TrustStep`:
            // `Generic` IS the trust kind — `TheoryLemmaKind::Generic.alethe_rule()`
            // is literally `"trust"` — so the two errors describe the same
            // situation through different variants. Omitting it meant the rescue
            // never fired on the shape AY actually emits most often: measured on
            // the UFBV `fixpoint` corpus, every one of the 74 discarded
            // refutations reports "step t1 uses unsupported theory lemma kind
            // Generic in strict mode", so the whole discharge path was dead code
            // for them.
            //
            // Eligibility is only a gate on WHICH rejections get re-examined; the
            // discharge itself is unchanged, so every accepted clause still has to
            // survive the forged-UNSAT guard, full strict validation of every
            // non-trust step, and an independent solve. The collecting checker
            // already defers this kind — its contract states it defers "explicit
            // trust steps (and trust-kind generic theory lemmas)" — so nothing
            // downstream needed changing.
            //
            // `HoleStep` joins them for the same reason, one defect later. AY
            // treats `Hole` as a member of the trust family everywhere it
            // matters — `proof_euf_lemma.rs` and `proof.rs` match
            // `Trust | Hole` in a single pattern, `terminal_trust.rs` counts
            // holes as reachable trust, and `arrays_to_lia.rs` DOWNGRADES a real
            // step to `Hole` while keeping its clause, so a hole carries an
            // obligation rather than marking an absence. Only this gate and the
            // checker's collector disagreed, which made the rescue dead code for
            // every hole-bearing refutation: a census of nine `ay-dpll` buckets
            // at the commit before this one put "uses unsupported hole rule"
            // joint-top of what remained, at 7 occurrences.
            Err(
                error @ (ay_proof::ProofCheckError::TrustStep { .. }
                | ay_proof::ProofCheckError::StrictProofModeTrust { .. }
                | ay_proof::ProofCheckError::HoleStep { .. }),
            ) => {
                self.discharge_trust_steps_for_certification(&error)?;
            }
            Err(
                error @ ay_proof::ProofCheckError::UnsupportedTheoryLemmaKind {
                    kind: ay_core::TheoryLemmaKind::Generic,
                    ..
                },
            ) => {
                self.discharge_trust_steps_for_certification(&error)?;
            }
            Err(error) => {
                return Err(UnsatCertificationError::StrictProofRejected {
                    reason: error.to_string(),
                });
            }
        }

        Ok(UnsatCertificate(epoch.id))
    }

    /// Independently re-discharge a refutation the plain strict checker rejected
    /// only because it leans on `trust` steps (#unsat-cert-trust-discharge).
    ///
    /// AY decides many BV/array clauses UNSAT and then exports the learned theory
    /// clause as an Alethe `trust` step, because the Alethe BV/array rule set is
    /// incomplete. The plain strict checker rejects every `trust` step BY RULE
    /// NAME, so a genuinely-discharged tautology was demoted to `unknown`. That is
    /// a CHECKER-COVERAGE gap, not a solver one: the answer is computed, correct,
    /// and z3-confirmable — it is simply discarded at the publication funnel.
    ///
    /// This does not weaken the gate; it replaces "reject by name" with "verify".
    /// Acceptance requires ALL of:
    ///
    /// 1. **Not forged.** A FRESH `Executor` re-decides the authored assertions.
    ///    A definitive `sat` means the UNSAT is forged, so reject. This dominates
    ///    the per-clause check, closing the residual case where every trust clause
    ///    looks like a standalone tautology yet the overall refutation is bogus.
    ///    Sound and downgrade-only: it fires on a positive contradiction, never on
    ///    an `unknown`, so a genuine UNSAT is never disturbed.
    /// 2. **Every non-trust step still passes the full strict boundary** — the
    ///    collecting checker defers ONLY `trust`, and errors on anything else.
    /// 3. **Every deferred trust clause is independently confirmed a theory
    ///    tautology**, by asserting its negation into a fresh solver and requiring
    ///    UNSAT (terminal empty clause: re-solve the whole problem). Any
    ///    `Unchecked`/`Invalid`/unmodellable outcome keeps the rejection.
    ///
    /// So the trusted base is unchanged: a clause is admitted only when an
    /// INDEPENDENT solve confirms it, never because of what the step is called.
    ///
    /// RECURSION. Steps 1 and 3 run nested solves, and those solves reach this
    /// same publication funnel, so an unguarded implementation could recurse
    /// without bound. `TRUST_DISCHARGE_DEPTH` admits the rescue only at depth 0;
    /// nested certifications fall back to plain strict, which terminates. Failing
    /// closed on the nested path costs completeness, never soundness.
    /// Time-bounded twin of `api::proofs::executor_redecides_definitive_sat`.
    ///
    /// Returns `true` ONLY on a definitive `sat` inside the budget. A timeout,
    /// an `unknown`, or an `unsat` all return `false`, so the guard stays
    /// downgrade-only: it can reject a forged refutation but can never accept
    /// one, and a genuine UNSAT is never disturbed by the budget expiring.
    /// Independently re-decide the authored assertions and require UNSAT.
    ///
    /// The certificate for a CONTEXT-DEPENDENT trust clause: rather than proving
    /// the clause is a tautology (it is not), reproduce the CONCLUSION in a fresh
    /// executor that shares none of the original solve's state and does not see
    /// its proof. `Unsat` is the only accepting outcome — `sat`, `unknown` and a
    /// budget expiry all decline — so a forged refutation of a satisfiable
    /// problem can never be accepted here.
    fn reconfirms_unsat_within(&self, problem: &[TermId], budget_ms: u64) -> bool {
        if problem.is_empty() {
            // An empty conjunction is satisfiable; there is nothing to confirm.
            return false;
        }
        let mut exec = crate::Executor::new();
        exec.ctx = self.ctx.clone();
        // Re-decide the AUTHORED problem, NOT `self.ctx.assertions` — the same
        // set steps (1) and (2) use, which `proof_export_scope_assertions`
        // builds to INCLUDE the query's `check-sat-assuming` assumptions.
        //
        // `ctx.assertions` holds the base alone. For `check-sat-assuming A` the
        // published claim is `base AND A |= false`, so re-solving the base by
        // itself asks a strictly STRONGER question: for
        // `(assert (=> p (< x 0))) (assert (> x 0)) (check-sat-assuming (p))`
        // the base is plainly satisfiable with `p` false, so this declined and a
        // CORRECT `unsat` was published UNCONFIRMED. Sound but over-conservative
        // — `base |= false` implies `base AND A |= false`, never the reverse.
        exec.ctx.assertions = problem.to_vec();
        exec.set_deadline(Some(
            ay_core::time::Instant::now() + std::time::Duration::from_millis(budget_ms),
        ));
        matches!(exec.check_sat(), Ok(result) if result.is_unsat())
    }

    /// The MINIMAL authored obligation for the step-(4) corroborating re-solve.
    ///
    /// `problem_assertions_for_strict_proof` is a deliberate SUPERSET, and that
    /// is right for the freshness and authority tests in steps (1)-(3), where
    /// extra terms only make the test stricter. It is the wrong input to a
    /// RE-SOLVE. It folds in `last_proof_rebuild_originals`, which carries
    /// ALPHA-RENAMED copies of the background `forall` axioms; renamed binders
    /// are not hash-cons-equal, so the nested solve carries every quantified
    /// axiom TWICE and pays for instantiating both.
    ///
    /// Measured on the `ext_eq_7956` fixture: 26 assertions, 203_520 decisions,
    /// 5.85s versus 16 assertions, 110_953 decisions, 2.90s — the same `Unsat`,
    /// half the work. That margin is the whole defect. The nominal
    /// `WHOLE_PROBLEM_RESOLVE_BUDGET_MS` is not the operative wall:
    /// `install_quantifier_deadline_backstop` extends the deadline by
    /// `remaining * (QUANTIFIED_BACKSTOP_FACTOR - 1)`, so the real wall is 4x
    /// the budget, and a 5.85s re-solve sat at 1.37x margin against it. Any CPU
    /// contention past ~1.4x flipped a correct `unsat` to `unknown`. Halving the
    /// work takes the margin to 2.7x; measured 6/6 correct at a load average of
    /// 18, where the superset scored 0/6.
    ///
    /// SUBSET-ONLY, and that is the entire soundness argument. If the minimal
    /// scope is not contained in `problem` this returns `problem` unchanged, so
    /// the re-solve can only ever be asked a question at least as strong as
    /// today's. Note what the guard does NOT buy: `problem` already unions the
    /// assumptions and the rebuild originals, so a solver-derived term that also
    /// appears in `problem` passes it. It buys MONOTONICITY, not provenance.
    ///
    /// The assumptions union is required, not tidiness: for
    /// `check-sat-assuming A` the published claim is `base AND A |= false`, and
    /// re-solving the base alone asks a strictly stronger question that
    /// previously threw away correct refutations (see the note in
    /// [`Self::reconfirms_unsat_within`]).
    ///
    /// COUPLING, load-bearing and previously undocumented: branch (1) below is
    /// dead on every real query. `check_sat.rs` saves and restores
    /// `self_check_authored_assertions` around the solve, so it is `None` at
    /// certification time by design and only the `ctx.assertions` fallback runs.
    /// That fallback is authored-only SOLELY because `check_sat.rs` restores
    /// `scope_tracked_assertions` into `ctx.assertions` on exit. If that restore
    /// ever stops happening, this scope silently becomes the post-preprocessing
    /// window and the `debug_assert!` below is what should catch it.
    fn authored_corroboration_scope(&self, problem: &[TermId]) -> Vec<TermId> {
        let mut scope = self
            .self_check_authored_assertions
            .clone()
            .unwrap_or_else(|| self.ctx.assertions.clone());
        if let Some(assumptions) = self.last_assumptions.as_ref() {
            for &assumption in assumptions {
                if !scope.contains(&assumption) {
                    scope.push(assumption);
                }
            }
        }
        for extension in self.declared_obligation_extension() {
            if !scope.contains(&extension) {
                scope.push(extension);
            }
        }
        debug_assert!(
            scope.iter().all(|t| problem.contains(t)),
            "the corroboration scope must stay a subset of the strict-proof \
             problem; a term outside it would mean the re-solve is answering a \
             question the publication never claimed"
        );
        if !scope.iter().all(|t| problem.contains(t)) {
            return problem.to_vec();
        }
        scope
    }

    fn redecides_definitive_sat_within(&self, authored: &[TermId], budget_ms: u64) -> bool {
        if authored.is_empty() {
            return false;
        }
        let mut exec = crate::Executor::new();
        exec.ctx = self.ctx.clone();
        // Re-decide the AUTHORED assertions, NOT `self.ctx.assertions`.
        //
        // By certification time the working set has been through the solve
        // pipeline: `flatten_and_strip_quantifiers` has removed the quantifiers,
        // CE lemmas have been pushed, preprocessing has run. That formula is
        // strictly WEAKER than the user's problem, so it is routinely satisfiable
        // even when the authored problem is not — whereupon this guard reports
        // "definitive SAT", concludes the refutation is forged, and destroys a
        // CORRECT `unsat`.
        //
        // Measured: 13 of the `ay-dpll --lib` failures were this guard rejecting
        // valid refutations with "forged UNSAT: a fresh Executor independently
        // re-decides the authored assertions as DEFINITIVE SAT". The message
        // said "authored"; the code passed the working set.
        //
        // The guard remains downgrade-only either way, so this was a
        // completeness bug rather than a soundness one — but silently discarding
        // sound answers is precisely the failure mode this funnel exists to
        // prevent.
        exec.ctx.assertions = authored.to_vec();
        exec.set_deadline(Some(
            ay_core::time::Instant::now() + std::time::Duration::from_millis(budget_ms),
        ));
        matches!(exec.check_sat(), Ok(result) if result.is_sat())
    }

    fn discharge_trust_steps_for_certification(
        &self,
        plain_error: &ay_proof::ProofCheckError,
    ) -> Result<(), UnsatCertificationError> {
        let reject = |reason: String| UnsatCertificationError::StrictProofRejected { reason };

        // Depth 0 only. Raising this limit was TRIED AND MEASURED: 64 of the
        // `ay-dpll --lib` certification rejections report "discharge not attempted"
        // from this branch, which looks like the guard starving the rescue of its
        // own evidence — a nested solve that leans on a trust step cannot discharge
        // it, publishes `unknown`, and so the outer `reconfirms_unsat_within` sees
        // a non-`unsat` and declines. Allowing two levels instead of one moved the
        // failure count by exactly ZERO (115 -> 115, 483.3s -> 483.5s), so those
        // nested downgrades are not what blocks the outer rescue. The limit stays
        // at depth 0: no measured benefit is worth extra recursion surface in a
        // mandatory soundness gate.
        if TRUST_DISCHARGE_DEPTH.with(|depth| depth.get()) > 0 {
            return Err(reject(format!(
                "{plain_error}; deferred-trust discharge not attempted: already \
                 inside a nested discharge solve"
            )));
        }

        struct DepthGuard;
        impl Drop for DepthGuard {
            fn drop(&mut self) {
                TRUST_DISCHARGE_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
            }
        }
        TRUST_DISCHARGE_DEPTH.with(|depth| depth.set(depth.get() + 1));
        let _guard = DepthGuard;

        // (1) Forged-UNSAT guard, dominant — but BUDGETED.
        //
        // The API-layer guard re-solves with no deadline, which is fine there
        // because it runs once per public call. Here it runs on the rejection
        // path of every proof that leaned on a trust step, so an unbounded solve
        // would add unbounded latency to verdicts that are being DOWNGRADED
        // anyway. Measured before this budget: `group_quantifiers` went 2.7s ->
        // 20.1s. The guard is downgrade-only, so cutting it short can only cost
        // the downgrade it would have forced, never soundness — and the
        // per-clause discharge in (3) still has to pass.
        const FORGED_GUARD_BUDGET_MS: u64 = 250;
        // The whole-problem re-solve runs at most once per certification and only
        // after per-clause discharge has already failed, so it can afford more
        // than the forged guard — but it is still bounded, because this path is
        // reached on verdicts that are being downgraded anyway.
        // MEASURED NULL — do not raise this hoping to rescue the residual
        // "a collected trust clause is not a standalone theory tautology AND the
        // authored assertions could not be independently re-solved as UNSAT"
        // rejections. A census at this commit counted 8 of them, and raising the
        // budget 30x (2000 -> 60000) cleared exactly ONE:
        //
        //   group_auflia 28 -> 27, group_bv 5 -> 5, group_arrays 7 -> 7,
        //   group_lia 7 -> 7, group_theory_misc 4 -> 4
        //
        // while `group_lia`'s wall clock went 7.1s -> 30.0s. Those eight are
        // STRUCTURAL, not budget-bound. And a longer fixed budget inside a
        // MANDATORY gate is actively harmful: it is the reason bucket counts move
        // with machine load at all, since this re-solve is an ACCEPTING step, so
        // a slow machine silently downgrades correct refutations.
        // AND THE DEEPER PROBLEM: a wall-clock budget inside a MANDATORY gate
        // makes the published VERDICT NONDETERMINISTIC. Measured on
        // `auflia_verification_consumer_ext_eq_7956::test_quantifier_consumer_singleton_prefix_array_ext_eq_proves_first_element`,
        // six release runs of the identical binary on the identical input:
        //
        //     unknown unknown unknown unsat unsat unsat
        //
        // AY computes the correct `unsat` every time; whether it PUBLISHES it
        // depends on whether this re-solve finishes inside 2000ms. The same
        // query answers differently run to run, which is a worse property than
        // the incompleteness it is trading against — a caller cannot tell a
        // capability limit from a busy machine.
        //
        // (In debug the same test fails 6/6, so the nondeterminism is
        // release-only; do not conclude from a debug run that it is stable.)
        //
        // MEASURED NULL #2 — swapping the wall clock for a DETERMINISTIC decision
        // budget does not fix it either, and costs 2-4x wall time. Tried:
        // `set_decision_limit(2_000_000)` as the operative bound with the wall
        // clock widened to a 30s hang-backstop, following the
        // `DEFAULT_GROUND_DECISION_ALLOWANCE` precedent. Result on the flaky
        // test: still 5 of 6 runs `unknown`, and each run 20-35s instead of 9s.
        //
        // CORRECTED — the "why" first recorded here was wrong, and the wrong
        // diagnosis is worth more than the null. It said the re-solve "genuinely
        // does not converge". It converges, deterministically: `Unsat`, 365
        // conflicts, 203_520 decisions, 5.79-6.01s, the SAME decision count on
        // every run and in every arm. Null #2 failed for a mundane reason —
        // 2_000_000 decisions is ~10x more than the re-solve ever needs, so that
        // bound was simply never reached and the wall clock still decided.
        //
        // Nor is 2000ms the operative wall. `install_quantifier_deadline_backstop`
        // extends the deadline by `remaining * (QUANTIFIED_BACKSTOP_FACTOR - 1)`,
        // so the real bound here is 4x this constant = 8000ms, and a 5.85s
        // re-solve sat at just 1.37x margin. That margin — not chance, and not
        // non-convergence — is the entire nondeterminism: contention slowing the
        // box past ~1.4x flips a correct `unsat` to `unknown`. Sweeping the
        // budget across 2000 / 10000 / 60000 / 300000 / none gives the identical
        // 203_520 decisions, which is why every "raise the number" experiment
        // came back null.
        //
        // WHAT ACTUALLY FIXED IT: halving the WORK instead of widening the bound
        // — see `authored_corroboration_scope`, which stops feeding the re-solve
        // two alpha-renamed copies of every quantified axiom. 110_953 decisions,
        // 2.90s, margin 2.7x, and 6/6 correct at a load average of 18 where the
        // superset scored 0/6.
        //
        // STILL OPEN, and deliberately not papered over: the authored-16 re-solve
        // needs 110_953 decisions where the identical COLD solve of the same
        // query needs 19. E-matching is identical in both (2 rounds, 13
        // instances), so it is downstream of instantiation; a fresh `Context`
        // reproduces the numbers exactly, ruling out inherited state. Unexplained.
        // This change buys margin, it does not close that gap.
        const WHOLE_PROBLEM_RESOLVE_BUDGET_MS: u64 = 2000;
        // The guard must re-decide the AUTHORED problem, so its assertions have
        // to be resolved before it runs — see the note on
        // `redecides_definitive_sat_within` for why using the working set here
        // silently destroys correct refutations.
        let decls = self.datatype_decls_for_strict_proof();
        let selectors = self.ctor_selector_decls_for_strict_proof();
        let problem = self.problem_assertions_for_strict_proof();
        if self.redecides_definitive_sat_within(&problem, FORGED_GUARD_BUDGET_MS) {
            return Err(reject(
                "forged UNSAT: a fresh Executor independently re-decides the \
                 authored assertions as DEFINITIVE SAT, so the trust-fallback \
                 refutation is not reproducible"
                    .to_string(),
            ));
        }

        // (2) Full strict validation, deferring only `trust`.
        let proof = self
            .last_proof
            .as_ref()
            .ok_or(UnsatCertificationError::MissingProof)?;
        let collected = ay_proof::check_proof_collecting_trust_with_context(
            proof,
            &self.ctx.terms,
            (!decls.is_empty()).then_some(decls.as_slice()),
            (!selectors.is_empty()).then_some(selectors.as_slice()),
            Some(problem.as_slice()),
        )
        .map_err(|error| {
            reject(format!(
                "deferred-trust discharge rejected a NON-trust step: {error}"
            ))
        })?;

        // Defensive: nothing deferred means the plain checker should have passed,
        // so honour its original rejection rather than inventing an acceptance.
        if collected.is_empty() {
            return Err(reject(format!(
                "{plain_error}; deferred-trust discharge declined: the collecting \
                 checker deferred no clause, so the plain rejection stands"
            )));
        }

        // (3) Independently discharge every deferred clause.
        let all_discharged = collected.iter().all(|(_, clause)| {
            crate::api::proofs::discharge_trust_clause(&self.ctx.terms, clause, &problem).is_some()
        });
        if all_discharged {
            return Ok(());
        }

        // (4) CONTEXT-DEPENDENT FALLBACK.
        //
        // A collected clause can be valid only GIVEN the other assertions rather
        // than standalone — the norm for LIA `Generic` lemmas (an ite-arithmetic
        // lemma whose proof is not Farkas-pure) and for the terminal trust step.
        // Such a clause is not a tautology, so (3) correctly declines it, but the
        // CONCLUSION can still be certified independently: re-decide the ORIGINAL
        // authored assertions in a fresh executor and require UNSAT.
        //
        // This certifies the property without trusting the proof's structure. It
        // cannot produce a false verdict: a forged UNSAT of a satisfiable problem
        // re-solves to `sat` (or `unknown`) and is rejected, and `unsat` is the
        // only accepting outcome. It is the same certificate the terminal
        // empty-clause path already uses, applied to the whole query.
        // Re-solve the MINIMAL authored obligation, not the strict-proof
        // superset — the superset carries every quantified axiom twice and
        // doubled the cost of this step. See `authored_corroboration_scope`.
        let corroboration_scope = self.authored_corroboration_scope(&problem);
        if self.reconfirms_unsat_within(&corroboration_scope, WHOLE_PROBLEM_RESOLVE_BUDGET_MS) {
            return Ok(());
        }

        Err(reject(format!(
            "{plain_error}; deferred-trust discharge failed: a collected trust \
             clause is not a standalone theory tautology AND the authored \
             assertions could not be independently re-solved as UNSAT"
        )))
    }

    /// The single public UNSAT publication funnel.
    ///
    /// Non-UNSAT results pass through after revoking stale UNSAT authority. A
    /// provisional UNSAT is retained only when strict validation mints a token;
    /// every failure revokes all query artifacts and becomes `Unknown`.
    pub(crate) fn certify_unsat_for_publication(
        &mut self,
        proposed: SolveResult,
        assumptions: &[TermId],
    ) -> SolveResult {
        self.last_unsat_certificate = None;
        if !proposed.is_unsat() {
            if !self.is_producing_proofs() {
                self.proof_tracker.disable();
            }
            return self.finalize_unknown_publication(proposed);
        }

        let published = match self.mint_unsat_certificate(assumptions) {
            Ok(certificate) => {
                self.last_unsat_certificate = Some(certificate);
                proposed
            }
            Err(error) => {
                tracing::warn!(%error, "rejecting uncertified public UNSAT verdict");
                probe_cert_reject(|| error.to_string());
                self.reject_uncertified_verdict_for_publication(format!(
                    "computed UNSAT rejected by mandatory strict certification: {error}"
                ))
            }
        };
        if !self.is_producing_proofs() {
            self.proof_tracker.disable();
        }
        published
    }

    /// Consume the one-shot capability for the immediately preceding verdict.
    pub(crate) fn take_unsat_certificate(&mut self) -> Option<UnsatCertificate> {
        self.last_unsat_certificate.take().map(|certificate| {
            // Read the private payload before consumption so dead-field lints
            // cannot tempt a future refactor to replace this with a unit marker.
            let _certified_epoch = certificate.0;
            certificate
        })
    }
}

#[cfg(test)]
mod tests {
    use ay_core::Proof;

    use super::*;
    use crate::executor_types::UnknownReason;

    #[test]
    fn missing_proof_fails_closed_and_mints_no_token() {
        let mut executor = Executor::new();
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);

        let result = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(result.is_unknown());
        assert!(executor.take_unsat_certificate().is_none());
        assert_eq!(
            executor.unknown_reason(),
            Some(UnknownReason::SelfCheckRejected)
        );
    }

    #[test]
    fn invalid_empty_proof_fails_closed() {
        let mut executor = Executor::new();
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        executor.last_proof = Some(Proof::new());

        let result = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(result.is_unknown());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn changed_assumption_slice_cannot_reuse_epoch() {
        let mut executor = Executor::new();
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let unexpected = executor.ctx.terms.true_term();

        let result = executor.certify_unsat_for_publication(SolveResult::unsat(), &[unexpected]);
        assert!(result.is_unknown());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn only_authenticated_named_rewrites_extend_assumption_authority() {
        let mut executor = Executor::new();
        let authored = executor.ctx.terms.mk_var("authored", ay_core::Sort::Bool);
        let rewritten = executor.ctx.terms.mk_var("rewritten", ay_core::Sort::Bool);
        let generated = executor.ctx.terms.mk_var("generated", ay_core::Sort::Bool);

        executor.named_assert_rewrites.insert(rewritten, authored);

        assert!(executor.query_authorizes_assumption(rewritten, &[authored], &[]));
        assert!(!executor.query_authorizes_assumption(generated, &[authored], &[]));
    }
}
