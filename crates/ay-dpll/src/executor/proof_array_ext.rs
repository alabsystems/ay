// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certification of the SOLVER-INJECTED array extensionality axioms.
//!
//! ## The problem
//!
//! The eager array lane Skolemizes the array theory's `diff` function: for an
//! array-equality atom `(= a b)` whose negation the search can assert, it mints
//! one or more fresh AY-internal index symbols and INJECTS an axiom of the form
//!
//! ```text
//! (or (= a b) (not (= (select a k) (select b k))))
//! ```
//!
//! into the assertion stack. That is not a problem premise, so the proof
//! pipeline saw it as a preprocessing-derived formula and disposed of it in one
//! of two equally uncertifiable ways: the surface-rewrite pass DEMOTED it to a
//! `:rule trust` step, or (when the demotion whitelist happened to cover the
//! solver-time assertion stack) it survived as an `assume` that the export-time
//! problem-scope gate then rejected as a "non-problem term". Either way the
//! `--self-check` gate degraded a correct QF_AX UNSAT to `unknown`.
//!
//! ## Why it could not simply be labelled a theory lemma
//!
//! Because the clause is NOT a theory tautology. `(select a k) = (select b k)`
//! is entirely consistent with `a != b` for an arbitrary index `k`; the clause
//! is sound only for a witness that is FRESH and minted for exactly this pair.
//! Labelling it `ArrayExtensionality` and letting the checker accept it on
//! shape would have been an "assume valid" arm, which is exactly what the
//! checker refused to grow.
//!
//! ## What this module does instead
//!
//! It gives the checker the missing provenance, as proof content:
//!
//!  * [`Executor::promote_array_extensionality_axioms`] replaces each injected
//!    extensionality assumption with a `TheoryLemma` of kind
//!    `ArrayExtensionality`, and APPENDS one clause-free
//!    `array_ext_diff_intro` step per witness recording its exact intermediate
//!    array pair.
//!  * `ay-proof`'s `ExtDiffRegistry` then independently re-derives whether that
//!    is believable: the witness must be bound exactly ONCE, must not occur
//!    inside the arrays it differentiates, must have acyclic dependencies on
//!    other introduced witnesses, and must be genuinely FRESH — verified
//!    against the problem's own assertions, not taken on faith from the
//!    `__ay_ext_diff` name or from any solver-side flag.
//!
//! Promotion is fail-closed at every step: a clause that does not match the
//! exact schema, any witness/pair missing an exact active generation-site
//! record, a witness bound to two different pairs, or an assumption the solver
//! did not actually inject all leave the step exactly as it was (trust /
//! foreign assume), so the gate keeps degrading those UNSATs to `unknown`.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{AletheRule, Proof, ProofStep, TermId, TheoryLemmaKind};

use super::Executor;

impl Executor {
    /// Recover one generation-site-authenticated extensionality chain.
    ///
    /// Shape and provenance are independent checks: `ay-proof` recognizes the
    /// exact one-or-more-level schema, while the per-query cache proves that
    /// every witness identity and intermediate pair were recorded at the
    /// generator that minted this exact clause. A reserved-looking name alone
    /// carries no authority.
    fn recorded_array_extensionality_chain(
        &self,
        clause: TermId,
    ) -> Option<Vec<(TermId, TermId, TermId)>> {
        let recorded = self
            .array_ext_witness_cache
            .generated_clause_bindings(&self.ctx.terms, clause)?;
        if let Some(recognized) =
            ay_proof::recognize_array_extensionality_chain(&self.ctx.terms, &[clause])
        {
            if recognized.len() != recorded.len() {
                return None;
            }

            let mut bindings = Vec::with_capacity(recognized.len());
            for ((array_a, array_b, witness), generated) in
                recognized.into_iter().zip(recorded.iter())
            {
                if witness != generated.witness
                    || ordered(array_a, array_b) != ordered(generated.array_a, generated.array_b)
                {
                    return None;
                }
                bindings.push((witness, array_a, array_b));
            }
            return Some(bindings);
        }

        // The datatype-array lane folds a synthesized select through
        // const/store/ITE terms because ordinary ROW preprocessing has already
        // run. Authenticate that one-level operational shape independently;
        // cache provenance alone never licenses a folded claim.
        let [generated] = recorded else {
            return None;
        };
        ay_proof::recognize_folded_array_extensionality(
            &self.ctx.terms,
            &[clause],
            generated.array_a,
            generated.array_b,
            generated.witness,
        )
        .then_some(vec![(
            generated.witness,
            generated.array_a,
            generated.array_b,
        )])
    }

    /// Replace injected extensionality assumptions with certified
    /// `ArrayExtensionality` theory lemmas plus their witness introductions.
    ///
    /// The proof pipeline calls this once before strict-gated certified rewrites
    /// (so authenticated extensionality is not mistaken for unrelated trust),
    /// and once more after every rewrite, demotion, prune, and rebuild pass. The
    /// final call sees the axiom in whichever shape those passes left it
    /// (`Assume`, or a `trust` step demoted from one) and ensures introductions
    /// cannot be pruned away again. Repeated calls are idempotent: an already
    /// promoted lemma is not promotable, and witnesses are introduced once.
    ///
    /// The introductions are APPENDED, never inserted: appending leaves every
    /// existing `ProofId` — and therefore every premise reference — untouched,
    /// and an introduction produces no clause, so it cannot disturb the
    /// terminal empty-clause requirement either.
    pub(super) fn promote_array_extensionality_axioms(&mut self, proof: &mut Proof) {
        let mut problem: DetHashSet<TermId> = DetHashSet::default();
        problem.extend(self.proof_original_problem_assertions());
        problem.extend(self.proof_problem_assertions());

        // Collect only claims that actually occur in this proof. This also
        // covers generated clauses installed below the assertion-stack layer,
        // while the cache record prevents an arbitrary trust step from being
        // mistaken for a solver-generated axiom.
        let mut injected: DetHashMap<TermId, Vec<(TermId, TermId, TermId)>> = DetHashMap::default();
        let mut pair_of_witness: DetHashMap<TermId, (TermId, TermId)> = DetHashMap::default();
        let mut conflicted: DetHashSet<TermId> = DetHashSet::default();
        for step in &proof.steps {
            let Some(clause_term) = promotable_clause_term(step) else {
                continue;
            };
            if problem.contains(&clause_term) || injected.contains_key(&clause_term) {
                continue;
            }
            let Some(bindings) = self.recorded_array_extensionality_chain(clause_term) else {
                continue;
            };
            for &(witness, array_a, array_b) in &bindings {
                let pair = ordered(array_a, array_b);
                match pair_of_witness.get(&witness) {
                    Some(&seen) if seen != pair => {
                        // One witness, two pairs: no single introduction can
                        // justify either claim, so every clause using it stays
                        // uncertified.
                        conflicted.insert(witness);
                    }
                    Some(_) => {}
                    None => {
                        pair_of_witness.insert(witness, pair);
                    }
                }
            }
            injected.insert(clause_term, bindings);
        }
        injected.retain(|_, bindings| {
            bindings
                .iter()
                .all(|(witness, _, _)| !conflicted.contains(witness))
        });
        if injected.is_empty() {
            return;
        }

        // Witnesses that already carry an introduction in this proof (an
        // earlier pass, or a previous incremental round, could in principle
        // have added one). Re-introducing would trip the checker's bound-once
        // rule and reject the whole proof.
        let mut introduced: DetHashSet<TermId> = proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Step {
                    rule: AletheRule::ArrayExtDiffIntro,
                    args,
                    ..
                } => args.first().copied(),
                _ => None,
            })
            .collect();

        let mut promoted: Vec<(TermId, TermId, TermId)> = Vec::new();
        for step in &mut proof.steps {
            // The injected axiom reaches the proof in one of three equivalent
            // uncertified shapes, depending on which pipeline stage handled it:
            // as the `Generic`/trust theory lemma `push_array_axiom_assertion_site`
            // records, as a bare `assume` of the injected assertion, or as the
            // `trust` step the surface-rewrite demotion turns that assume into.
            // All three are the SAME claim; promote whichever is present.
            let Some(clause_term) = promotable_clause_term(step) else {
                continue;
            };
            let Some(bindings) = injected.get(&clause_term) else {
                continue;
            };
            *step = ProofStep::TheoryLemma {
                theory: "arrays".to_string(),
                clause: vec![clause_term],
                farkas: None,
                kind: TheoryLemmaKind::ArrayExtensionality,
                lia: None,
            };
            promoted.extend(bindings.iter().copied());
        }

        for (witness, array_a, array_b) in promoted {
            if !introduced.insert(witness) {
                continue;
            }
            proof.add_step(ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                clause: Vec::new(),
                premises: Vec::new(),
                args: vec![witness, array_a, array_b],
            });
        }
    }

    /// Fail-closed re-validation of the proof's extensionality content for the
    /// `--self-check` / `--strict-proofs` acceptance gates.
    ///
    /// The gates consult the PARTIAL (non-strict) checker, which admits a
    /// theory lemma on the strength of its recorded kind alone. The ordinary
    /// array kinds are theory-valid clauses, but an `ArrayExtensionality`
    /// clause is a fresh-witness conservative extension and is only as good as
    /// its witness's provenance. Re-running the real check here is what stops a
    /// mere relabelling from shipping a bare `unsat`.
    ///
    /// Returns `true` when the proof's extensionality content (if any) is fully
    /// certified. A proof with no extensionality steps returns `true`
    /// trivially.
    #[must_use]
    pub(in crate::executor) fn unsat_proof_extensionality_certified(&self, proof: &Proof) -> bool {
        // Use exactly the same authored/export premise scope as the strict
        // checker. In addition to freshness, that shared scope covers active
        // check-sat assumptions and authenticated rebuilt source terms.
        let problem = self.problem_assertions_for_strict_proof();
        ay_proof::validate_array_extensionality_provenance(proof, &self.ctx.terms, &problem).is_ok()
    }
}

/// The three uncertified single-formula shapes an injected solver axiom can
/// have after proof rewriting. Keeping this matcher shared between collection
/// and mutation prevents the two passes from disagreeing about eligibility.
fn promotable_clause_term(step: &ProofStep) -> Option<TermId> {
    match step {
        ProofStep::Assume(term) => Some(*term),
        ProofStep::TheoryLemma { kind, clause, .. } if kind.is_trust() && clause.len() == 1 => {
            Some(clause[0])
        }
        ProofStep::Step {
            rule: AletheRule::Trust,
            clause,
            premises,
            args,
        } if premises.is_empty() && args.is_empty() && clause.len() == 1 => Some(clause[0]),
        _ => None,
    }
}

fn ordered(a: TermId, b: TermId) -> (TermId, TermId) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}
