// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certification of the SOLVER-INJECTED array extensionality axioms.
//!
//! ## The problem
//!
//! The eager array lane Skolemizes the array theory's `diff` function: for an
//! array-equality atom `(= a b)` whose negation the search can assert, it mints
//! a fresh index symbol `__ext_diff_*` and INJECTS the axiom
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
//!    `array_ext_diff_intro` step per witness recording the array pair it was
//!    minted for.
//!  * `ay-proof`'s `ExtDiffRegistry` then independently re-derives whether that
//!    is believable: the witness must be bound exactly ONCE, must not occur
//!    inside the arrays it differentiates, and must be genuinely FRESH —
//!    verified against the problem's own assertions, not taken on faith from
//!    the `__ext_diff` name or from any solver-side flag.
//!
//! Promotion is fail-closed at every step: a clause that does not match the
//! exact schema, a witness that is not an AY-internal `__ext_diff` symbol, a
//! witness bound to two different pairs, or an assumption the solver did not
//! actually inject all leave the step exactly as it was (trust / foreign
//! assume), so the gate keeps degrading those UNSATs to `unknown`.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{AletheRule, Proof, ProofStep, TermData, TermId, TheoryLemmaKind};

use super::Executor;

/// Namespace prefix of the extensionality difference witnesses AY mints.
///
/// Used ONLY to keep promotion inside AY's own internal symbol space — a
/// conservative emitter-side filter, never a soundness argument. Freshness is
/// established by the checker against the problem's symbols, so a user symbol
/// that happens to share this prefix is caught there rather than here.
const EXT_DIFF_PREFIX: &str = "__ext_diff";

impl Executor {
    /// Injected extensionality axioms of the current solve, as
    /// `clause_term -> (witness, array_a, array_b)`.
    ///
    /// The candidate set is the assertions the SOLVER added — everything on the
    /// stack that is not one of the problem's own assertions. Reading it back
    /// off the assertion stack (rather than from a per-mint-site registry)
    /// keeps this correct across all four places the eager lane mints an
    /// extensionality witness, and ties the recorded binding to the axiom that
    /// was actually asserted.
    ///
    /// A witness that appears with TWO different array pairs is dropped
    /// entirely: it cannot be given a single well-defined introduction, so
    /// every clause over it stays uncertified.
    fn injected_array_extensionality_axioms(&self) -> DetHashMap<TermId, (TermId, TermId, TermId)> {
        let mut problem: DetHashSet<TermId> = DetHashSet::default();
        problem.extend(self.proof_original_problem_assertions());
        problem.extend(self.proof_problem_assertions());

        let mut by_clause: DetHashMap<TermId, (TermId, TermId, TermId)> = DetHashMap::default();
        let mut pair_of_witness: DetHashMap<TermId, (TermId, TermId)> = DetHashMap::default();
        let mut conflicted: DetHashSet<TermId> = DetHashSet::default();

        for &assertion in &self.ctx.assertions {
            if problem.contains(&assertion) {
                continue;
            }
            let Some((array_a, array_b, witness)) =
                ay_proof::recognize_array_extensionality(&self.ctx.terms, &[assertion])
            else {
                continue;
            };
            let TermData::Var(name, _) = self.ctx.terms.get(witness) else {
                continue;
            };
            if !name.starts_with(EXT_DIFF_PREFIX) {
                continue;
            }
            let pair = ordered(array_a, array_b);
            match pair_of_witness.get(&witness) {
                Some(&seen) if seen != pair => {
                    // One witness, two pairs: no single introduction can be
                    // true, so neither clause may be certified.
                    conflicted.insert(witness);
                }
                Some(_) => {}
                None => {
                    pair_of_witness.insert(witness, pair);
                }
            }
            by_clause.insert(assertion, (witness, array_a, array_b));
        }

        by_clause.retain(|_, &mut (witness, _, _)| !conflicted.contains(&witness));
        by_clause
    }

    /// Replace injected extensionality assumptions with certified
    /// `ArrayExtensionality` theory lemmas plus their witness introductions.
    ///
    /// Runs LAST in the proof pipeline, after every rewrite, demotion, prune,
    /// and rebuild pass, so it sees the axiom in whichever shape those passes
    /// left it (`Assume`, or a `trust` step demoted from one) and so the
    /// appended introductions cannot be pruned away again.
    ///
    /// The introductions are APPENDED, never inserted: appending leaves every
    /// existing `ProofId` — and therefore every premise reference — untouched,
    /// and an introduction produces no clause, so it cannot disturb the
    /// terminal empty-clause requirement either.
    pub(super) fn promote_array_extensionality_axioms(&mut self, proof: &mut Proof) {
        let injected = self.injected_array_extensionality_axioms();
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
            let clause_term = match step {
                ProofStep::Assume(term) => *term,
                ProofStep::TheoryLemma { kind, clause, .. }
                    if kind.is_trust() && clause.len() == 1 =>
                {
                    clause[0]
                }
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    args,
                } if premises.is_empty() && args.is_empty() && clause.len() == 1 => clause[0],
                _ => continue,
            };
            let Some(&(witness, array_a, array_b)) = injected.get(&clause_term) else {
                continue;
            };
            *step = ProofStep::TheoryLemma {
                theory: "arrays".to_string(),
                clause: vec![clause_term],
                farkas: None,
                kind: TheoryLemmaKind::ArrayExtensionality,
                lia: None,
            };
            promoted.push((witness, array_a, array_b));
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
    /// theory lemma on the strength of its recorded kind alone. For every other
    /// array kind that is fine — the clause is a tautology — but an
    /// `ArrayExtensionality` clause is only as good as its witness's
    /// provenance, so re-running the real check here is what stops a mere
    /// relabelling from shipping a bare `unsat`.
    ///
    /// Returns `true` when the proof's extensionality content (if any) is fully
    /// certified. A proof with no extensionality steps returns `true`
    /// trivially.
    #[must_use]
    pub(in crate::executor) fn unsat_proof_extensionality_certified(&self, proof: &Proof) -> bool {
        // The AUTHORED assertion window when available: it is captured before
        // any in-place preprocessing runs, so it is the truest statement of
        // "the problem's symbols". Otherwise fall back to the parsed-prefix
        // assertions. Both are unioned with the provenance-tracked problem
        // assertions — a SUPERSET only ever makes the freshness test stricter.
        let mut problem: Vec<TermId> = Vec::new();
        if let Some(authored) = self.self_check_authored_assertions.as_ref() {
            problem.extend(authored.iter().copied());
        }
        problem.extend(self.proof_original_problem_assertions());
        problem.extend(self.proof_problem_assertions());
        ay_proof::validate_array_extensionality_provenance(proof, &self.ctx.terms, &problem).is_ok()
    }
}

fn ordered(a: TermId, b: TermId) -> (TermId, TermId) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}
