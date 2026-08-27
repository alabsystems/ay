// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Replace each certified congruence-closure EXPLANATION lemma with a
//! derivation an external Alethe checker can re-run.
//!
//! # The gap this closes
//!
//! `TheoryLemmaKind::EufCongruenceExplanation` is validated by
//! `ay_proof::checker::euf_congruence_explanation` — soundly, from the clause
//! alone — so AY certifies these clauses itself. But
//! `euf_congruence_explanation` is not a pinned Alethe rule, so
//! `wire_rule_name` lowers it to `hole` and the emitted document tells an
//! external checker nothing. That is the difference between "AY trusts its own
//! checker" and "anyone can verify the proof".
//!
//! # What is emitted
//!
//! `ay_proof::plan_euf_congruence_derivation` runs a PROOF-PRODUCING
//! congruence closure over the clause's own sub-term DAG and returns a
//! fragment of `eq_congruent` / `eq_transitive` / `th_resolution` /
//! `contraction` / `weakening` / `reordering` steps whose LAST clause is the
//! recorded clause, byte for byte. The lemma step is replaced by that
//! fragment:
//!
//! ```text
//!  before                                          after
//!  i: (cl l1 .. ln)  EufCongruenceExplanation      i+0 .. i+k  the derivation
//!                                                  i+k: (cl l1 .. ln)
//! ```
//!
//! For the packed `(cl (or l1 .. ln))` form the census measures, the fragment
//! derives the FLAT clause and the leaf's single `or` consumer — whose clause
//! is already exactly those children — is re-justified as `reordering`, the
//! same trick `packed_euf_reordering` uses. No consumer's clause changes, so
//! every downstream premise reference, resolution and pivot sees exactly the
//! clause it saw before.
//!
//! # Authority
//!
//! Nothing here is asserted. Before a plan may be committed, the fragment is
//! CLOSED into a self-contained refutation and re-validated by the untouched
//! `check_proof_strict` — the same checker the mandatory gate runs, with no
//! rule relaxed and none added. A fragment that does not replay is dropped and
//! its lemma stays byte-identical, so this pass can only move a proof from
//! `hole` toward a checkable rule, never the reverse. The whole-proof
//! `check_proof` gate at the end reverts every replacement if the rebuilt
//! proof does not check — and so does a second gate, which re-runs the
//! MANDATORY strict certification on both proofs and reverts if the rewrite
//! costs a certification the original had.
//!
//! # Guards
//!
//! Each is mutation-checked in `congruence_explanation_tests.rs`
//! (`GUARD_MUTATION_LEDGER` there).
//!
//! 1. **No anchors.** Their forward references the in-order remap cannot
//!    resolve — the same guard `split_euf_congruence_lemmas` uses.
//! 2. **A payload-free `EufCongruenceExplanation` lemma.** A surviving
//!    positional certificate is consumed by trace rebinding and the printer,
//!    not by these validators; splitting the step would strand it.
//! 3. **The packed form's single consumer is the matching `or` step.** The
//!    leaf stops being the packed unit, so an `or` consumer would break.
//! 4. **The fragment renders.** Every emitted step is run through the PRINTER
//!    with the export's own surface overrides, and a hypothesis a boolean
//!    wrapper re-spells is refused by the same predicate the `eq_transitive`
//!    demotion uses. A step the printer refuses would make the whole export
//!    refuse to publish; a step it renders unsoundly would ship an invalid
//!    document.
//! 5. **The closed fragment strict-checks.** The whole authority.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId, TheoryLemmaKind};
use ay_proof::CongruenceDerivation;

use super::super::Executor;
use super::packed_euf_reordering::{packed_or_children, reference_map};

/// Largest packed disjunction the RE-PACK arm will rebuild. Each disjunct
/// costs one `or_neg` step whose clause carries the WHOLE disjunction, so the
/// arm is quadratic in the packed term; the measured population is 2 and this
/// bounds an adversarial one. Recorded as SCOPE: a wider packed unit with a
/// non-`or` consumer keeps its byte-identical lemma.
pub(super) const MAX_REPACK_DISJUNCTS: usize = 8;

/// The flat literals of a candidate lemma, and how the fragment must end.
struct Candidate {
    literals: Vec<TermId>,
    /// The single matching `or` consumer to re-justify as `reordering`, when
    /// the packed leaf has one.
    consumer: Option<usize>,
    /// The packed `(or ..)` term the fragment must REBUILD, when the leaf is
    /// packed and its consumers are NOT the single matching `or` step. The
    /// leaf's clause is then reproduced byte for byte and no consumer is
    /// touched at all.
    repack: Option<TermId>,
}

impl Executor {
    /// Lower every extractable congruence-closure explanation. Returns the
    /// number of lemmas replaced, which the tests assert on.
    pub(in crate::executor) fn derive_congruence_explanations(
        &mut self,
        proof: &mut Proof,
    ) -> usize {
        if proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Anchor { .. }))
        {
            return 0;
        }
        if !proof.steps.iter().any(is_explanation_lemma) {
            return 0;
        }
        let citations = reference_map(proof);
        let mut plans: Vec<Option<CongruenceDerivation>> = std::iter::repeat_with(|| None)
            .take(proof.steps.len())
            .collect();
        let mut rejustified = vec![false; proof.steps.len()];
        let candidates: Vec<usize> = proof
            .steps
            .iter()
            .enumerate()
            .filter(|(_, step)| is_explanation_lemma(step))
            .map(|(index, _)| index)
            .collect();
        for index in candidates {
            let Some(candidate) = self.explanation_candidate(proof, &citations, index) else {
                continue;
            };
            let derivation =
                ay_proof::plan_euf_congruence_derivation(&mut self.ctx.terms, &candidate.literals)
                    .and_then(|derivation| match candidate.repack {
                        None => Some(derivation),
                        Some(packed) => self.repack_derivation(derivation, packed),
                    });
            let Some(derivation) = derivation else {
                continue;
            };
            if self.derivation_is_unrenderable(&derivation) {
                continue;
            }
            // Guard 5: the untouched strict checker replays every emitted step
            // before any of them may enter the proof.
            let closed = ay_proof::close_congruence_derivation(&mut self.ctx.terms, &derivation);
            if ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_err() {
                continue;
            }
            if let Some(consumer) = candidate.consumer {
                rejustified[consumer] = true;
            }
            plans[index] = Some(derivation);
        }
        if plans.iter().all(Option::is_none) {
            return 0;
        }
        self.commit_congruence_derivations(proof, plans, &rejustified)
    }

    /// The flat literals of the lemma at `index`, or `None` when it is not a
    /// candidate.
    fn explanation_candidate(
        &self,
        proof: &Proof,
        citations: &[Vec<usize>],
        index: usize,
    ) -> Option<Candidate> {
        // Guard 2: a payload-free explanation lemma.
        let ProofStep::TheoryLemma {
            clause,
            farkas: None,
            kind: TheoryLemmaKind::EufCongruenceExplanation,
            lia: None,
            ..
        } = &proof.steps[index]
        else {
            return None;
        };
        let Some(children) = packed_or_children(&self.ctx.terms, clause) else {
            return Some(Candidate {
                literals: clause.clone(),
                consumer: None,
                repack: None,
            });
        };
        let packed = clause[0];
        // Guard 3: exactly one consumer, and it is the matching `or` step.
        // When that holds the leaf becomes the FLAT clause and the `or`
        // consumer becomes the permutation it now is. When it does not, the
        // fragment REBUILDS the packed unit instead and no consumer is
        // touched — measured, that is the whole residual of this class: six
        // lemmas whose packed unit is consumed DIRECTLY by `Resolution`
        // steps (1-3 of them), never by an `or` step.
        if let Some(consumer) = self.matching_or_consumer(proof, citations, index, &children) {
            return Some(Candidate {
                literals: children,
                consumer: Some(consumer),
                repack: None,
            });
        }
        if children.len() > MAX_REPACK_DISJUNCTS {
            return None;
        }
        Some(Candidate {
            literals: children,
            consumer: None,
            repack: Some(packed),
        })
    }

    /// Guard 4: whether the emitted fragment would fail to PUBLISH.
    ///
    /// Two independent failure modes, both measured on this corpus:
    ///
    /// * the printer REFUSES a step outright (`InvalidCongruenceStep`), which
    ///   makes the whole export refuse and turns a published `unsat` into no
    ///   answer at all. Decided by running the printer itself, with the same
    ///   overrides, so producer and exporter cannot drift;
    /// * a boolean wrapper re-spells a `(not (= a b))` hypothesis as
    ///   `(= (= a b) false)`, which the printer renders happily and an
    ///   external checker then rejects. Decided by the SAME predicate the
    ///   `eq_transitive` demotion uses, for the same reason.
    fn derivation_is_unrenderable(&self, derivation: &CongruenceDerivation) -> bool {
        let overrides = self.last_proof_term_overrides.as_ref();
        if !ay_proof::congruence_derivation_renders(&self.ctx.terms, overrides, derivation) {
            return true;
        }
        let Some(overrides) = overrides else {
            return false;
        };
        derivation.steps.iter().any(|step| match step {
            ProofStep::Step { clause, .. } => {
                Self::eq_transitive_clause_is_unrenderable(&self.ctx.terms, overrides, clause)
            }
            _ => false,
        })
    }

    /// Splice every planned fragment in, remapping premise references, and
    /// revert wholesale if the rebuilt proof does not check.
    fn commit_congruence_derivations(
        &self,
        proof: &mut Proof,
        mut plans: Vec<Option<CongruenceDerivation>>,
        rejustified: &[bool],
    ) -> usize {
        let original = proof.steps.clone();
        let original_named = proof.named_steps.clone();
        let old = std::mem::take(&mut proof.steps);
        let mut remap: Vec<ProofId> = Vec::with_capacity(old.len());
        let mut steps: Vec<ProofStep> = Vec::with_capacity(old.len());
        let mut derived = 0usize;
        for (index, step) in old.into_iter().enumerate() {
            // Premises reference only EARLIER steps, already remapped.
            let step = super::remap_step_premises(step, &remap);
            if let Some(derivation) = plans[index].take() {
                let base = steps.len();
                for fragment_step in derivation.steps {
                    steps.push(offset_premises(fragment_step, base));
                }
                remap.push(ProofId(u32::try_from(steps.len() - 1).unwrap_or(u32::MAX)));
                derived += 1;
                continue;
            }
            if rejustified.get(index).copied().unwrap_or(false) {
                // The leaf is no longer a packed unit, so its `or` consumer
                // becomes the permutation it now is. Its CLAUSE is untouched.
                if let ProofStep::Step {
                    clause, premises, ..
                } = step
                {
                    remap.push(ProofId(u32::try_from(steps.len()).unwrap_or(u32::MAX)));
                    steps.push(ProofStep::Step {
                        rule: AletheRule::Reordering,
                        clause,
                        premises,
                        args: Vec::new(),
                    });
                    continue;
                }
                // Unreachable: only an `or` Step is ever marked.
                proof.steps = original;
                proof.named_steps = original_named;
                return 0;
            }
            remap.push(ProofId(u32::try_from(steps.len()).unwrap_or(u32::MAX)));
            steps.push(step);
        }
        let mut named = original_named.clone();
        named.retain(|_, id| {
            let old_index = id.0 as usize;
            if !matches!(original.get(old_index), Some(ProofStep::Assume(_))) {
                return false;
            }
            let Some(new_id) = remap.get(old_index) else {
                return false;
            };
            *id = *new_id;
            true
        });
        proof.steps = steps;
        proof.named_steps = named;
        // Whole-proof backstop: never ship a proof this rebuild broke.
        // #diagnostic-envelope: the whole-proof backstop runs under the
        // caller's solve controls; a refusal reverts, exactly like a rejection.
        if crate::executor::proof::check::check_proof_gate_with_executor_progress(self, proof)
            .is_err()
            || self.rewrite_loses_certification(proof, &original, &original_named)
        {
            proof.steps = original;
            proof.named_steps = original_named;
            return 0;
        }
        derived
    }

    /// Whether the rewrite costs the MANDATORY gate a proof it certified
    /// before — the "must not change WHICH UNSATs certify" constraint, decided
    /// by running that exact gate on both proofs.
    ///
    /// This is not hypothetical. Measured on
    /// `smt/QF_AUFLIA/storeinv_nf_size7.smt2`: the strict checker's SEMANTIC
    /// PRECHARGE for `reordering` / `weakening` is `class=General`, the square
    /// of the TREE-unfolded payload, and this population's clauses are exactly
    /// the heavily-shared `store` chains where tree unfolding dwarfs the DAG —
    /// one 34 KB clause precharges 133 M work units. Replacing ONE lemma that
    /// debits its ACTUAL work with several steps that take that precharge
    /// exhausted the envelope (309 M of 350 M) and turned a published `unsat`
    /// into `unknown (self-check-rejected)`.
    ///
    /// The cheap direction is checked FIRST: when the rebuilt proof certifies,
    /// nothing can have been lost and the second check is never run.
    fn rewrite_loses_certification(
        &self,
        rebuilt: &Proof,
        original: &[ProofStep],
        original_named: &DetHashMap<String, ProofId>,
    ) -> bool {
        if self.check_proof_strict_with_datatypes(rebuilt).is_ok() {
            return false;
        }
        let mut before = Proof::new();
        before.steps = original.to_vec();
        before.named_steps = original_named.clone();
        self.check_proof_strict_with_datatypes(&before).is_ok()
    }
}

fn is_explanation_lemma(step: &ProofStep) -> bool {
    matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::EufCongruenceExplanation,
            ..
        }
    )
}

/// Rebase a fragment step's premise ids onto the proof it is spliced into.
pub(super) fn offset_premises(step: ProofStep, base: usize) -> ProofStep {
    match step {
        ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } => ProofStep::Step {
            rule,
            clause,
            premises: premises
                .into_iter()
                .map(|premise| {
                    ProofId(
                        u32::try_from(base)
                            .unwrap_or(u32::MAX)
                            .saturating_add(premise.0),
                    )
                })
                .collect(),
            args,
        },
        other => other,
    }
}

#[cfg(test)]
#[path = "congruence_explanation_tests.rs"]
mod tests;
