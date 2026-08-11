// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory-attributed UNSAT core extraction.
//!
//! Walks the proof DAG to collect theory lemma attributions and maps them
//! back to the named assertions in the UNSAT core.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use ay_core::ProofStep;
use ay_core::TermId;

use crate::api::types::annotated_core::attribution_from_lemma;
use crate::api::types::{AnnotatedCoreLiteral, AnnotatedUnsatCore, SolverError, TheoryAttribution};
use crate::api::Solver;

impl Solver {
    /// Theory-attributed UNSAT core.
    ///
    /// After `check_sat()` returns `Unsat`, this method returns an enriched
    /// UNSAT core where each named assertion carries theory-specific
    /// certificates explaining its role in the UNSAT proof.
    ///
    /// Returns `None` if:
    /// - The last result was not UNSAT
    /// - Proof production or unsat-core production was not enabled
    /// - No proof data is available
    ///
    /// # Requirements
    ///
    /// Both `:produce-proofs` and `:produce-unsat-cores` must be enabled
    /// before calling `check_sat()`.
    ///
    /// # Theory Attributions
    ///
    /// - **LRA:** [`TheoryAttribution::Farkas`] with Farkas coefficients
    /// - **LIA:** [`TheoryAttribution::LiaGeneric`] with optional Farkas
    ///   coefficients and LIA reasoning kind
    /// - **EUF:** [`TheoryAttribution::EufTransitive`] or
    ///   [`TheoryAttribution::EufCongruent`]
    /// - **BV:** [`TheoryAttribution::BvBitBlast`]
    /// - **Other:** [`TheoryAttribution::Generic`] with theory name
    #[must_use]
    pub fn annotated_unsat_core(&self) -> Option<AnnotatedUnsatCore> {
        self.try_annotated_unsat_core().ok()
    }

    /// Farkas-annotated UNSAT core (external-consumer alias for
    /// [`annotated_unsat_core`](Self::annotated_unsat_core)).
    ///
    /// Introduced for downstream consumers (`model-checker-consumer`, `VerifierConsumer`, `deductive-checks`,
    /// proof-emission pipelines) that need structured access to Farkas
    /// coefficients + the literal set of the UNSAT core produced by the
    /// linear-arithmetic theories. This is a stable, discoverable entry
    /// point dedicated to that use case -- issue #8769.
    ///
    /// This method is a thin wrapper over `annotated_unsat_core`: the
    /// returned [`AnnotatedUnsatCore`] exposes each core literal together
    /// with its theory attributions. For LRA and LIA conflicts, the
    /// attribution carries the [`TheoryAttribution::Farkas`] variant (or
    /// [`TheoryAttribution::LiaGeneric`], which may also wrap Farkas
    /// coefficients) with `coefficients: Vec<Rational64>`.
    ///
    /// # Requirements
    ///
    /// Both `:produce-proofs` and `:produce-unsat-cores` must be enabled
    /// before calling [`check_sat`](Self::check_sat). Named assertions
    /// (`(assert (! <term> :named <name>))` or
    /// [`try_assert_named`](Self::try_assert_named)) are required for the
    /// core to carry back-references by name.
    ///
    /// # Returns
    ///
    /// `Some(AnnotatedUnsatCore)` after an UNSAT result with the required
    /// options enabled; `None` otherwise. Use
    /// [`try_annotated_unsat_core`](Self::try_annotated_unsat_core) to
    /// distinguish specific failure modes via [`SolverError`].
    ///
    /// # Example
    ///
    /// ```no_run
    /// use ay_dpll::api::{Logic, Solver, Sort, TheoryAttribution};
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// solver.set_produce_proofs(true);
    /// solver.set_produce_unsat_cores(true);
    ///
    /// let x = solver.declare_const("x", Sort::Int);
    /// let five = solver.int_const(5);
    /// let three = solver.int_const(3);
    /// let gt = solver.gt(x, five);
    /// let lt = solver.lt(x, three);
    /// solver.try_assert_named(gt, "lb").unwrap();
    /// solver.try_assert_named(lt, "ub").unwrap();
    ///
    /// let result = solver.check_sat();
    /// assert!(result.is_unsat());
    ///
    /// let core = solver
    ///     .unsat_core_with_farkas()
    ///     .expect("UNSAT + proofs enabled yields an annotated core");
    /// assert!(!core.is_empty());
    ///
    /// // Walk the attributions and pull Farkas coefficients when present.
    /// for entry in core.entries() {
    ///     for attr in &entry.attributions {
    ///         match attr {
    ///             TheoryAttribution::Farkas { coefficients } => {
    ///                 assert!(!coefficients.is_empty(), "{}", entry.name);
    ///             }
    ///             TheoryAttribution::LiaGeneric { coefficients: Some(cs), .. } => {
    ///                 assert!(!cs.is_empty(), "{}", entry.name);
    ///             }
    ///             _ => {}
    ///         }
    ///     }
    /// }
    /// ```
    #[must_use]
    pub fn unsat_core_with_farkas(&self) -> Option<AnnotatedUnsatCore> {
        self.annotated_unsat_core()
    }

    /// Fallible version of [`annotated_unsat_core`](Self::annotated_unsat_core).
    ///
    /// Returns a typed error distinguishing:
    /// - [`SolverError::NoResult`] -- no `check_sat` has been called
    /// - [`SolverError::NotUnsat`] -- last result was not UNSAT
    /// - [`SolverError::UnsatCoreGenerationFailed`] -- proof or core data unavailable
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_annotated_unsat_core(&self) -> Result<AnnotatedUnsatCore, SolverError> {
        // 1. Get the plain UNSAT core (assertion names)
        let core_names = self.try_get_unsat_core()?;
        if core_names.is_empty() {
            return Ok(AnnotatedUnsatCore::new(Vec::new(), Vec::new()));
        }

        // 2. Get the proof
        let proof = self.executor.last_proof().ok_or_else(|| {
            SolverError::UnsatCoreGenerationFailed(
                "no proof available; enable :produce-proofs before check_sat".into(),
            )
        })?;

        // 3. Collect theory lemma attributions from the proof.
        //    For each theory lemma step, we record which TermIds participate
        //    and what theory/certificate applies.
        let mut term_attributions: BTreeMap<TermId, Vec<TheoryAttribution>> = BTreeMap::new();
        let mut theories_seen: BTreeSet<String> = BTreeSet::new();

        for step in &proof.steps {
            if let ProofStep::TheoryLemma {
                theory,
                clause,
                farkas,
                kind,
                lia,
            } = step
            {
                theories_seen.insert(theory.clone());
                let attr = attribution_from_lemma(
                    kind,
                    farkas.as_ref(),
                    lia.as_ref(),
                    theory,
                    clause,
                    self.terms(),
                    &|term_id| self.wrap_term(term_id),
                );
                for term_id in clause {
                    // Strip negation to get the base atom
                    let base = self.strip_negation_term_id(*term_id);
                    term_attributions
                        .entry(base)
                        .or_default()
                        .push(attr.clone());
                }
            }
        }

        // 4. Map assertion names to TermIds using the executor's named assertion map.
        //    Then look up attributions for each core name.
        // Build name -> attributions by checking which proof assumptions match
        // named assertions and which theory lemma clauses reference them.
        let mut entries: Vec<AnnotatedCoreLiteral> = Vec::with_capacity(core_names.len());

        for name in &core_names {
            // Look up the TermId for this named assertion
            let attributions = if let Some(term_id) = self.named_assertion_term_id(name) {
                term_attributions.get(&term_id).cloned().unwrap_or_default()
            } else {
                Vec::new()
            };

            entries.push(AnnotatedCoreLiteral {
                name: name.clone(),
                attributions,
            });
        }

        let theories_involved: Vec<String> = theories_seen.into_iter().collect();
        Ok(AnnotatedUnsatCore::new(entries, theories_involved))
    }

    /// Strip negation from a TermId to get the base atom.
    fn strip_negation_term_id(&self, term_id: TermId) -> TermId {
        use ay_core::term::TermData;
        match self.terms().get(term_id) {
            TermData::Not(inner) => *inner,
            _ => term_id,
        }
    }

    /// Look up the TermId for a named assertion.
    ///
    /// Named assertions are stored in the executor's context from
    /// `(assert (! expr :named foo))` commands.
    fn named_assertion_term_id(&self, name: &str) -> Option<TermId> {
        self.executor.named_assertion_term_id(name)
    }
}
