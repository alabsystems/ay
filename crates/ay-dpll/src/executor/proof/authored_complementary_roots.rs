// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact refutation of a COMPLEMENTARY AUTHORED ROOT PAIR: the problem
//! asserts some `t` and, as another root, literally `(not t)` — the same
//! `TermId` under the negation.
//!
//! ## The class, and why it is new at this merge
//!
//! Alpha-quantifier sharing (`elaborate/term.rs::share_alpha_equivalent_quantifier`)
//! makes two alpha-equivalent authored quantifiers ONE term. deductive-checks's
//! `seq_contains` obligations (#negated-exists-cegqi-witness-hints) assert a
//! positive existential and, as a separate root, the negation of the same
//! existential spelled with a different binder name:
//!
//! ```text
//! (assert (exists ((i Int)) (and (<= 0 i) (< i n) (= needle (select s i)))))
//! (assert (not (exists ((j Int)) (and (<= 0 j) (< j n) (= needle (select s j))))))
//! ```
//!
//! Before sharing the two quantifiers were distinct atoms: the CEGQI witness
//! lane Skolemized the positive one, refuted the negated one against the
//! Skolem constant and minted the strict authored-scope certificate. With
//! sharing they are `t` and `(not t)`, and on the shapes that carry an
//! `int2bv` conversion the pre-quantifier BV/LIA bridge
//! (`check_sat.rs`, `solve_bv_lia_bridge`) refutes that pair propositionally
//! BEFORE the quantifier pipeline runs. That verdict is right, but the bridge
//! records no SAT clause trace, the assembly closes the proof with a bare
//! terminal `trust` step, and the input-syntax rewrite pass then poisons it
//! because a canonical root carries a binder. Measured at the merge of
//! `deductive-checks/solver-fixes-2026-09-16` onto main: the three BV-indexed
//! `seq_contains` controls published `unsat` through the independent
//! re-decision arm only (`unsat_independently_verified`), no longer through
//! the strict certificate they carried on either parent.
//!
//! ## The argument
//!
//! It is the shortest one there is, and it needs no evaluation, no
//! instantiation and no surface rewriting:
//!
//! ```text
//! (assume h0 t)
//! (assume h1 (not t))
//! (step t2 (cl) :rule resolution :premises (h0 h1))
//! ```
//!
//! Both assumes are authored problem roots — the pair is found in the exact
//! concrete authored scope, never in preprocessed residue — so the strict
//! checker's premise authority and the exporter's problem-scope gate hold by
//! construction. The UNCHANGED strict checker commits the candidate; this
//! module grants no authority of its own.
//!
//! ## What it replaces, and only that
//!
//! A proof that carries NO derivation at all: every step a premiseless
//! `trust`/`hole` closer. It also repairs an incomplete candidate with NO
//! empty-clause derivation: retained Assume/helper steps do not refute the
//! query, but must not block an independently checked refutation of its exact
//! authored complementary pair. A proof with an empty-clause derivation and
//! real steps is left to the passes that own it. The one exception is a derivation
//! kept behind a presentation bound (`last_proof_surface_withheld`), which is
//! where this pass used to find the `(cl)` poison: it has no authored
//! document to lose.

use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofStep, TermId};

use super::Executor;

/// Does the proof carry no derivation at all — nothing but premiseless
/// `trust`/`hole` closers? That is the shape the assembly leaves when the
/// solve recorded no clause trace, and the shape the input-syntax rewrite
/// pass leaves when it poisons a document.
fn proof_carries_no_derivation(proof: &Proof) -> bool {
    !proof.steps.is_empty()
        && proof.steps.iter().all(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Trust | AletheRule::Hole,
                    premises,
                    ..
                } if premises.is_empty()
            )
        })
}

impl Executor {
    /// Replace an incomplete or derivation-free closed proof with the exact resolution of a
    /// complementary authored root pair. `true` when a strictly-checked,
    /// export-authorized replacement was committed; the proof is untouched
    /// on every decline.
    pub(super) fn replace_bare_closure_with_authored_complementary_roots_refutation(
        &mut self,
        proof: &mut Proof,
    ) -> bool {
        // #certify-before-presentation. A derivation KEPT behind a
        // presentation bound stands exactly where this pass used to find the
        // one-line `(cl)` poison, and the binder veto that withheld it is the
        // shape this module was written for. Measured on the sharing-on
        // `seq_contains` pair: left alone, the kept CEGQI Skolem derivation
        // reached the end of the assembly instead of this two-assume
        // resolution, and its document printed both shared quantifiers under
        // one canonical binder name — an `assume` pinned Carcara cannot match
        // to the input. The candidate is still committed only through the
        // unchanged strict checker and the exporter's scope gate below.
        if Self::proof_derives_empty_clause(proof)
            && !proof_carries_no_derivation(proof)
            && self.last_proof_surface_withheld.is_none()
        {
            return false;
        }
        let Some((positive, negative)) = self.authored_complementary_root_pair() else {
            return false;
        };
        let mut candidate = Proof::new();
        let assume_positive = candidate.add_assume(positive, None);
        let assume_negative = candidate.add_assume(negative, None);
        // `add_resolution` wants the premise carrying the pivot's NEGATIVE
        // occurrence first.
        candidate.add_resolution(Vec::new(), positive, assume_negative, assume_positive);
        // DERIVATION. The unchanged strict checker is the only authority that
        // commits this: it re-runs the resolution against the two assumes.
        if !Self::proof_derives_empty_clause(&candidate)
            || !self
                .check_proof_strict_with_datatypes(&candidate)
                .is_ok_and(|quality| quality.is_complete())
        {
            return false;
        }
        // EXPORT AUTHORITY. Both assumes are authored roots, but ask the
        // exporter's own scope check before committing, exactly as the
        // sibling authored-leaf passes do.
        if ay_proof::validate_reachable_assumes_in_problem_scope(
            &candidate,
            &self.proof_export_scope_assertions(),
        )
        .is_err()
        {
            return false;
        }
        *proof = candidate;
        true
    }

    /// An authored root `t` and an authored root that is literally `(not t)`,
    /// as `(t, (not t))`; `None` when the exact concrete authored scope holds
    /// no such pair.
    fn authored_complementary_root_pair(&self) -> Option<(TermId, TermId)> {
        let roots = self.exact_concrete_authored_scope();
        let root_set: ay_core::kani_compat::DetHashSet<TermId> = roots.iter().copied().collect();
        roots
            .iter()
            .find_map(|&root| match self.ctx.terms.get(root) {
                TermData::Not(inner) if root_set.contains(inner) => Some((*inner, root)),
                _ => None,
            })
    }
}

#[cfg(test)]
mod tests {

    use ay_core::{AletheRule, Proof, ProofStep};

    use crate::Executor;

    /// The deductive-checks `seq_contains` shape minimized: a positive existential and
    /// the negation of the same existential under another binder name. With
    /// alpha-quantifier sharing on (the default) the two are one term.
    const COMPLEMENTARY: &str = "(set-logic ALL)\n\
         (declare-const n Int)\n\
         (assert (exists ((i Int)) (and (<= 0 i) (< i n))))\n\
         (assert (not (exists ((j Int)) (and (<= 0 j) (< j n)))))";

    /// Same two roots, but the second quantifier differs in its body, so the
    /// pair is not complementary and this pass has nothing to say.
    const UNRELATED: &str = "(set-logic ALL)\n\
         (declare-const n Int)\n\
         (assert (exists ((i Int)) (and (<= 0 i) (< i n))))\n\
         (assert (not (exists ((j Int)) (and (<= 1 j) (< j n)))))";

    fn executed(script: &str) -> Executor {
        let commands = ay_frontend::parse(script).expect("fixture must parse");
        let mut executor = Executor::new();
        executor.set_produce_proofs(true);
        executor
            .execute_all(&commands)
            .expect("fixture must elaborate");
        executor
    }

    fn bare_trust_closure() -> Proof {
        let mut proof = Proof::new();
        proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
        proof
    }

    #[test]
    fn a_shared_complementary_pair_replaces_the_bare_closure() {
        let mut executor = executed(COMPLEMENTARY);
        assert_eq!(executor.ctx.assertions.len(), 2);
        let mut proof = bare_trust_closure();
        assert!(
            executor.replace_bare_closure_with_authored_complementary_roots_refutation(&mut proof),
            "the pair `t` / `(not t)` must be refuted by one resolution"
        );
        assert_eq!(proof.steps.len(), 3, "two assumes and one resolution");
        assert!(matches!(proof.steps[0], ProofStep::Assume(_)));
        assert!(matches!(proof.steps[1], ProofStep::Assume(_)));
        assert!(matches!(proof.steps[2], ProofStep::Resolution { .. }));
        assert!(Executor::proof_derives_empty_clause(&proof));
        assert!(executor
            .check_proof_strict_with_datatypes(&proof)
            .is_ok_and(|quality| quality.is_complete()));
    }

    #[test]
    fn an_unrelated_pair_declines_and_leaves_the_proof_untouched() {
        let mut executor = executed(UNRELATED);
        let mut proof = bare_trust_closure();
        assert!(
            !executor.replace_bare_closure_with_authored_complementary_roots_refutation(&mut proof)
        );
        assert_eq!(proof.steps.len(), 1);
        assert!(matches!(
            proof.steps[0],
            ProofStep::Step {
                rule: AletheRule::Trust,
                ..
            }
        ));
    }

    #[test]
    fn a_proof_with_a_derivation_is_never_replaced() {
        let mut executor = executed(COMPLEMENTARY);
        let root = executor.ctx.assertions[0];
        let mut proof = Proof::new();
        let assume = proof.add_assume(root, None);
        proof.add_rule_step(AletheRule::Trust, Vec::new(), vec![assume], Vec::new());
        assert!(
            !executor.replace_bare_closure_with_authored_complementary_roots_refutation(&mut proof),
            "a document with an assume on its path belongs to the passes that own it"
        );
        assert_eq!(proof.steps.len(), 2);
    }

    #[test]
    fn an_assume_only_incomplete_proof_uses_the_exact_authored_pair() {
        let mut executor = executed(COMPLEMENTARY);
        let mut proof = Proof::new();
        proof.add_assume(executor.ctx.assertions[0], Some("partial".into()));
        assert!(!Executor::proof_derives_empty_clause(&proof));
        assert!(
            executor.replace_bare_closure_with_authored_complementary_roots_refutation(&mut proof)
        );
        assert_eq!(proof.steps.len(), 3);
        assert!(Executor::proof_derives_empty_clause(&proof));
        assert!(executor
            .check_proof_strict_with_datatypes(&proof)
            .is_ok_and(|quality| quality.is_complete()));
        ay_proof::validate_reachable_assumes_in_problem_scope(
            &proof,
            &executor.proof_export_scope_assertions(),
        )
        .expect("every reachable assume remains an exact authored root");
    }

    #[test]
    fn an_incomplete_proof_without_an_authored_pair_is_unchanged() {
        let mut executor = executed(UNRELATED);
        let mut proof = Proof::new();
        proof.add_assume(executor.ctx.assertions[0], Some("partial".into()));
        let before = proof.clone();
        assert!(
            !executor.replace_bare_closure_with_authored_complementary_roots_refutation(&mut proof)
        );
        assert_eq!(proof.steps, before.steps);
        assert_eq!(proof.named_steps, before.named_steps);
    }

    #[test]
    fn a_strict_closed_refutation_is_retained_byte_for_byte() {
        let mut executor = executed(COMPLEMENTARY);
        let (positive, negative) = executor
            .authored_complementary_root_pair()
            .expect("actual authored pair");
        let mut proof = Proof::new();
        let pos = proof.add_assume(positive, Some("positive".into()));
        let neg = proof.add_assume(negative, Some("negative".into()));
        proof.add_assume(positive, Some("retained".into()));
        proof.add_resolution(Vec::new(), positive, neg, pos);
        assert!(executor
            .check_proof_strict_with_datatypes(&proof)
            .is_ok_and(|quality| quality.is_complete()));
        let before = proof.clone();
        assert!(
            !executor.replace_bare_closure_with_authored_complementary_roots_refutation(&mut proof)
        );
        assert_eq!(proof.steps, before.steps);
        assert_eq!(proof.named_steps, before.named_steps);
    }
}
