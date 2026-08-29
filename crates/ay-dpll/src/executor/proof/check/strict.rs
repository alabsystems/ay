// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict proof validation and authored-premise context.

use super::*;

use super::strict_check_progress::check_with_executor_progress_reporting_work;

impl Executor {
    /// Strict proof check that also validates datatype constructor-distinctness lemmas (#8419).
    /// `DatatypeDistinct` steps (promoted from `Generic` at proof finalization
    /// by `promote_datatype_distinct_lemmas`) cannot be validated from the
    /// `TermStore` alone — runtime datatype terms carry `Sort::Uninterpreted`.
    /// This supplies the `declare-datatype` registry so the strict checker can
    /// semantically validate them against the actual constructor declarations
    /// instead of failing closed.
    ///
    /// It also supplies the complete authored premise scope. Strict mode uses
    /// that scope both to reject foreign `Assume` steps and to validate
    /// `ArrayExtensionality`: that clause is sound only for a witness the solver
    /// minted fresh, and "fresh" is a statement ABOUT the problem, so the
    /// checker verifies it against the problem's own symbols rather than
    /// trusting a name or a solver flag.
    pub(crate) fn check_proof_strict_with_datatypes(
        &self,
        proof: &Proof,
    ) -> Result<ProofQuality, ProofCheckError> {
        self.check_proof_strict_with_datatypes_reporting_work(proof)
            .0
    }

    /// As [`Self::check_proof_strict_with_datatypes`], additionally reporting
    /// the aggregate metered WORK the walk consumed — the deterministic,
    /// machine-independent cost figure (see
    /// `check_with_executor_progress_reporting_work`). The finite-enum
    /// capability route reports 0: it is separately bounded by its own
    /// capability budget and never enters the aggregate meter.
    pub(in crate::executor) fn check_proof_strict_with_datatypes_reporting_work(
        &self,
        proof: &Proof,
    ) -> (Result<ProofQuality, ProofCheckError>, usize) {
        // M0(a) attribution counters (the development design notes):
        // every strict-check entry through this wrapper is counted, including
        // the finite-enum route below and the mint-time re-check in
        // `unsat_cert.rs`. Counting only — zero behavior change.
        self.strict_check_invocations
            .set(self.strict_check_invocations.get() + 1);
        self.strict_check_steps_validated
            .set(self.strict_check_steps_validated.get() + proof.steps.len() as u64);
        if let Some(capability) = self.checked_finite_enum_capability_for_proof(proof) {
            let assumptions: Vec<TermId> = capability.assumptions().collect();
            return (
                self.check_bounded_finite_enum_proof(
                    proof,
                    &assumptions,
                    &capability.datatype_decls,
                    &capability.selector_decls,
                    &capability.member_signatures,
                ),
                0,
            );
        }
        let decls = self.datatype_decls_for_strict_proof();
        let selectors = self.ctor_selector_decls_for_strict_proof();
        let member_signatures = match self.datatype_member_signatures_for_strict_proof() {
            Some(member_signatures) => member_signatures,
            None => {
                return (
                    Err(ProofCheckError::InvalidDatatypeSignatureContext {
                        reason: "executor datatype registries lack an exact sticky member \
                                 signature"
                            .to_string(),
                    }),
                    0,
                )
            }
        };
        // A non-matching candidate must never inherit a narrow scope merely
        // because the current stored proof has a finite-enum capability.
        let problem = self.complete_problem_assertions_for_strict_proof();
        // #strict-walk-memo — the pipeline re-asks this exact question about
        // an unchanged document many times per solve (measured: two 30-walk
        // fans per `sal/bakery` solve, one 66-walk fan on
        // `DTP/DTP_k2_n35_c245_s4`; see `check/strict_memo.rs`). Replay the
        // stored verdict only when EVERY input the checker read — literal
        // document, term-store snapshot stamp, the checker-visible term-store
        // metadata generation, both datatype registries, the member
        // signatures and the authored scope — is proven unchanged;
        // any doubt is a miss and a real walk. The capability route above
        // never consults the memo, and runs before it on every call, so a
        // proof that acquires a finite-enum capability can never be answered
        // with a stored general-route verdict.
        let key = StrictWalkKey {
            datatype_decls: decls.as_slice(),
            selector_decls: selectors.as_slice(),
            member_signatures: member_signatures.as_slice(),
            problem: problem.as_slice(),
        };
        if let Some((outcome, work)) = self.strict_walk_memo_lookup(proof, &key) {
            self.strict_check_memo_hits
                .set(self.strict_check_memo_hits.get() + 1);
            return (outcome, work);
        }
        let (outcome, work) = check_with_executor_progress_reporting_work(
            self,
            proof,
            (!decls.is_empty()).then_some(decls.as_slice()),
            (!selectors.is_empty()).then_some(selectors.as_slice()),
            member_signatures.as_slice(),
            Some(problem.as_slice()),
        );
        self.strict_walk_memo_store(proof, &key, &outcome, work);
        (outcome, work)
    }

    /// Strictly validate a proof's derivation while deliberately postponing
    /// authored-premise authorization.
    ///
    /// Proof-surgery passes use this as an atomic revert gate while they replace
    /// one derived lemma inside a larger proof. At that point the proof can still
    /// contain preprocessing assumptions which a later rewrite will derive from
    /// authored roots or demote to an explicit trust step. Treating those
    /// unrelated leaves as an authorization failure here would revert a valid
    /// local replacement and preserve its trust lemma.
    ///
    /// Every current `Assume` is supplied as an allowed premise solely for this
    /// structural check. This does not weaken the final boundary:
    /// [`Self::check_proof_strict_with_datatypes`] and the exported bundle still
    /// validate the finished proof against the independently captured authored
    /// scope. Including all assumes is also conservative for array witness
    /// freshness: it can only reject a witness that occurs in a premise.
    pub(crate) fn check_proof_strict_derivation_with_datatypes(
        &self,
        proof: &Proof,
    ) -> Result<ProofQuality, ProofCheckError> {
        let decls = self.datatype_decls_for_strict_proof();
        let selectors = self.ctor_selector_decls_for_strict_proof();
        let member_signatures = self
            .datatype_member_signatures_for_strict_proof()
            .ok_or_else(|| ProofCheckError::InvalidDatatypeSignatureContext {
                reason: "executor datatype registries lack an exact sticky member signature"
                    .to_string(),
            })?;
        let assumptions: Vec<TermId> = proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Assume(term) => Some(*term),
                _ => None,
            })
            .collect();
        check_with_executor_progress(
            self,
            proof,
            (!decls.is_empty()).then_some(decls.as_slice()),
            (!selectors.is_empty()).then_some(selectors.as_slice()),
            member_signatures.as_slice(),
            Some(assumptions.as_slice()),
        )
    }

    /// The complete authored premise scope for strict proof checking.
    ///
    /// Deliberately NOT `ctx.assertions`: at proof time that stack also carries
    /// the solver's own injected extensionality axioms, which mention every
    /// witness and would make all of them look non-fresh. The authored window
    /// (captured before in-place preprocessing) is preferred when present; the
    /// parsed-prefix and provenance-tracked problem assertions are unioned in.
    /// `check-sat-assuming` literals and structurally authenticated source terms
    /// rebuilt during proof repair are included because they can legitimately
    /// appear as `Assume` leaves. Solver-generated constraints are excluded.
    /// A SUPERSET is always safe here — extra terms can only make the freshness
    /// test stricter, never more permissive.
    pub(in crate::executor) fn complete_problem_assertions_for_strict_proof(&self) -> Vec<TermId> {
        let mut problem = self.proof_export_scope_assertions();
        // Membership through a set, not `Vec::contains` (#strict-proof-dedup).
        // Both loops below dedup against `problem`, which on the DT families is
        // thousands of assertions long, so the linear scan made this O(n^2) —
        // and mandatory certification runs it on EVERY public UNSAT. Order is
        // preserved exactly: the set only answers "already present".
        let mut seen: ay_core::kani_compat::DetHashSet<TermId> = problem.iter().copied().collect();
        if let Some(authored) = self.self_check_authored_assertions.as_ref() {
            for &assertion in authored {
                if seen.insert(assertion) {
                    problem.push(assertion);
                }
            }
        }
        // #pareto-terminal-obligation — a Pareto terminal `(check-sat)` refutes
        // `authored AND blocking`, so the blocking conjuncts are part of the
        // question being decided rather than facts borrowed from nowhere. The
        // slot is empty for every other query and is writable only by
        // `declare_pareto_front_exhaustion_extension`, which rebuilds its terms
        // from the executor's own objectives.
        for extension in self.declared_obligation_extension() {
            if seen.insert(extension) {
                problem.push(extension);
            }
        }
        problem
    }

    /// Premise scope for APIs that export the exact stored proof.
    ///
    /// Only the canonical, current finite-enum proof receives its selected
    /// direct-root scope. Every other proof path retains the complete authored
    /// scope assembled above.
    pub(crate) fn problem_assertions_for_strict_proof(&self) -> Vec<TermId> {
        self.last_proof
            .as_ref()
            .and_then(|proof| self.finite_enum_scope_for_proof(proof))
            .unwrap_or_else(|| self.complete_problem_assertions_for_strict_proof())
    }

    /// Constructor→selector registry for strict proof validation:
    /// `(constructor_name, [selector_name in field order])` from the elaboration
    /// context. Like the distinctness registry, the field positions cannot be
    /// recovered from the `TermStore` (datatype terms carry `Sort::Uninterpreted`),
    /// so they are supplied here for `DatatypeSelectorProject` validation.
    pub(crate) fn ctor_selector_decls_for_strict_proof(&self) -> Vec<(String, Vec<String>)> {
        self.ctx
            .ctor_selectors_iter()
            .map(|(ctor, selectors)| (ctor.clone(), selectors.clone()))
            .collect()
    }

    /// Complete exact core signatures for every sticky datatype constructor,
    /// selector, and tester in the declaration registries used by strict proof
    /// checking. Returns `None` on any registry/signature mismatch so callers
    /// fail closed rather than silently dropping typed authority.
    pub(crate) fn datatype_member_signatures_for_strict_proof(
        &self,
    ) -> Option<Vec<ay_proof::DatatypeMemberSignature>> {
        let mut signatures = Vec::new();
        for (_, constructors) in self.ctx.datatype_iter() {
            for constructor in constructors {
                let fields = self.ctx.constructor_selectors(constructor)?;
                let tester = format!("is-{constructor}");
                for identity in std::iter::once(constructor.as_str())
                    .chain(std::iter::once(tester.as_str()))
                    .chain(fields.iter().map(String::as_str))
                {
                    let info = self.ctx.exact_datatype_member_info(identity)?;
                    signatures.push(ay_proof::DatatypeMemberSignature {
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

    /// Validate proof and collect quality metrics.
    ///
    /// In debug builds, runs the full proof checker (rejects invalid proofs via
    /// warning). In all builds, collects [`ProofQuality`] step-type counts for
    /// diagnostic reporting via `(get-info :all-statistics)`.
    pub(in crate::executor::proof) fn validate_and_measure_proof(
        &self,
        proof: &Proof,
    ) -> Option<ProofQuality> {
        let has_hole = proof.steps.iter().any(|s| {
            matches!(
                s,
                ProofStep::Step {
                    rule: AletheRule::Hole,
                    ..
                }
            )
        });
        if has_hole {
            return None;
        }

        // Use strict checker when enabled (#4420).
        let result = if self.strict_proofs_enabled() {
            self.check_proof_strict_with_datatypes(proof)
        } else {
            ay_proof::check_proof_with_quality(proof, &self.ctx.terms)
        };

        match result {
            Ok(quality) => {
                tracing::debug!(
                    %quality,
                    complete = quality.is_complete(),
                    "UNSAT proof quality"
                );
                if !quality.is_complete() {
                    tracing::warn!(
                        trust = quality.trust_count,
                        hole = quality.hole_count,
                        total = quality.total_steps,
                        "UNSAT proof has unverified fallback steps"
                    );
                }
                Some(quality)
            }
            Err(e) => {
                tracing::warn!(
                    error = %e,
                    steps = proof.len(),
                    "internal proof checker rejected UNSAT proof"
                );
                None
            }
        }
    }

    pub(crate) fn proof_derives_empty_clause(proof: &Proof) -> bool {
        proof.steps.iter().any(|step| match step {
            // An `array_ext_diff_intro` is a clause-free DEFINITION; its empty
            // `clause` field is not a derivation of `(cl)`.
            ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                ..
            } => false,
            ProofStep::Step { clause, .. } | ProofStep::Resolution { clause, .. } => {
                clause.is_empty()
            }
            _ => false,
        })
    }

    /// Check that the proof derives empty clause AND the resolution chain is
    /// valid (each ThResolution step's conclusion matches its premises).
    ///
    /// #diagnostic-envelope — this used to be an ASSOCIATED function taking a
    /// bare `&TermStore`, which is exactly why it had no envelope: with no
    /// executor in hand there was nothing to poll. It is the hottest of the
    /// unmetered walks, because `build_unsat_assembly` calls it on EVERY
    /// reconstructed proof to decide whether the resolution chain needs
    /// rebuilding — MEASURED at 126,548 steps / 393,087,456 clause literals on
    /// deductive-checks's `datatype_ne_refutation` obligation, walked with the caller's
    /// 30 s deadline already expired. Taking `&self` lets the same envelope the
    /// mandatory strict gate uses apply here.
    ///
    /// A refused/cancelled walk answers `false`, which is the answer this
    /// predicate already gives for "the checker did not accept it": the caller
    /// declines to self-certify. That cannot make a verdict more accepting.
    ///
    /// Callers that want to REPAIR the chain must not use this predicate — see
    /// [`Executor::empty_clause_derivation_status`] and the note on
    /// [`EmptyClauseDerivation`] for why.
    pub(in crate::executor::proof) fn proof_derives_valid_empty_clause(
        &self,
        proof: &Proof,
    ) -> bool {
        matches!(
            self.empty_clause_derivation_status(proof),
            EmptyClauseDerivation::Valid
        )
    }

    /// As [`Executor::proof_derives_valid_empty_clause`], but distinguishing
    /// "the chain is broken" from "I was stopped before I could tell".
    ///
    /// #diagnostic-envelope AMENDMENT. Metering this walk introduced a second
    /// way for it to answer "not valid", and the two answers call for opposite
    /// responses. `unsat_proof_self_certified` is right to treat both as
    /// failure — it is deciding whether to CLAIM something, and a claim it
    /// could not check must not be made. `build_unsat_assembly` is not: it
    /// treats "not valid" as "the rewrite invalidated the chain, rebuild it",
    /// and that inference holds only for a chain the checker actually
    /// inspected and rejected.
    ///
    /// MEASURED on deductive-checks's `datatype_ne_refutation::t_dbl_one_eq`: with the
    /// two collapsed, the rebuild ladder fired 12 times per solve, every single
    /// one with `err = Cancelled`, one of them on a 199,149-step proof — an
    /// unmetered ten-strategy re-derivation plus a coarsely-polled Farkas
    /// repair, entered *because* the caller had asked the solve to stop. That
    /// is the very behaviour the envelope exists to remove, re-entered through
    /// the response to the envelope firing.
    #[cfg(feature = "proof-checker")]
    pub(in crate::executor::proof) fn empty_clause_derivation_status(
        &self,
        proof: &Proof,
    ) -> EmptyClauseDerivation {
        if !Self::proof_derives_empty_clause(proof) {
            // Structural, and decided without walking anything: there is no
            // empty clause to derive. A genuine defect.
            return EmptyClauseDerivation::Invalid;
        }
        // Run the partial checker. If it finds no errors, the chain is valid.
        let outcome = check_partial_with_executor_progress(self, proof, WantQuality::No);
        classify_empty_clause_walk(outcome.error.as_ref(), outcome.envelope_refused())
    }

    #[cfg(not(feature = "proof-checker"))]
    pub(in crate::executor::proof) fn empty_clause_derivation_status(
        &self,
        proof: &Proof,
    ) -> EmptyClauseDerivation {
        if Self::proof_derives_empty_clause(proof) {
            EmptyClauseDerivation::Valid
        } else {
            EmptyClauseDerivation::Invalid
        }
    }
}
