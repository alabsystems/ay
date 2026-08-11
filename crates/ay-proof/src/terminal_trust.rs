// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Terminal-trust detection for strict-proof UNSAT acceptance (#8759).
//!
//! An UNSAT verdict is only trustworthy if the proof's derivation of the
//! empty clause does not ride on unverified `:rule trust` steps. This module
//! performs a backwards walk from every empty-clause step through the
//! `premises` graph; if any step on the transitive closure is a `trust`
//! fallback (either `AletheRule::Trust` or a `TheoryLemmaKind` that exports
//! as `trust`, like `Generic`), we flag the proof as trust-tainted.
//!
//! See issue #8759 for the motivating evidence: on QF_LRA false-UNSAT cases
//! (#8511, #8754, #8758) the Alethe writer emits `:rule trust` for 32/113
//! steps including the terminal empty-clause derivation, while the control
//! (true UNSAT) produces a clean `th_resolution`-terminated proof with zero
//! trust. Rejecting any `trust` on the path to `(cl)` automatically
//! downgrades those false-UNSAT cases to `unknown`.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId};

/// Report returned by [`terminal_trust_report`].
///
/// The report distinguishes proofs that never reach `(cl)` at all (a
/// separate bug — see `build_unsat_proof` post-conditions) from proofs that
/// reach `(cl)` but rely on a trust fallback somewhere in the derivation
/// chain.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct TerminalTrustReport {
    /// Number of empty-clause steps in the proof.
    pub empty_clause_steps: u32,
    /// Number of `AletheRule::Trust` steps reachable from an empty-clause
    /// step by walking backwards through `premises`.
    pub trust_rule_on_path: u32,
    /// Number of `TheoryLemma` steps with a trust-emitting kind
    /// (e.g., `TheoryLemmaKind::Generic`) reachable from an empty-clause
    /// step by walking backwards through `premises`.
    pub trust_theory_lemma_on_path: u32,
    /// Number of `AletheRule::Hole` steps reachable from an empty-clause step
    /// by walking backwards through `premises`. A `hole` is the Alethe spec's
    /// attributed placeholder for an unchecked gap — external checkers accept
    /// the document as *holey*, but the step is exactly as unverified as a
    /// `trust` fallback, so the strict-proofs acceptance gate must treat it
    /// identically (C5: the BV bit-blast collapse rescue emits `hole`).
    pub hole_rule_on_path: u32,
    /// Number of `ProofStep::Assume` steps reachable from an empty-clause step
    /// whose asserted term is NOT backed by the problem's provenance (leak-2):
    /// neither an original asserted formula nor a quantifier instantiation that
    /// traces back to an asserted `forall`. Such an `assume` is a free axiom an
    /// external checker accepts blindly — the theory used it to launder an
    /// unverified fact (e.g. an injected `seq.len` axiom) into a "certified"
    /// UNSAT. It is exactly as unverified as a `trust` fallback, so the
    /// strict-proofs / self-check acceptance gate must treat it identically.
    ///
    /// Only ever nonzero when the report was produced by
    /// [`terminal_trust_report_with_provenance`]; the provenance-free
    /// [`terminal_trust_report`] treats every `assume` leaf as trust-free (0).
    pub foreign_assume_on_path: u32,
}

impl TerminalTrustReport {
    /// True when the proof derives `(cl)` and no trust fallback appears on
    /// the path to any empty-clause step.
    #[must_use]
    pub fn is_trust_free(&self) -> bool {
        self.empty_clause_steps > 0
            && self.trust_rule_on_path == 0
            && self.trust_theory_lemma_on_path == 0
            && self.hole_rule_on_path == 0
            && self.foreign_assume_on_path == 0
    }

    /// True when a trust fallback (rule, theory lemma, hole, or a
    /// provenance-unbacked `assume`) appears on the transitive closure of
    /// premises rooted at any empty-clause step.
    #[must_use]
    pub fn has_terminal_trust(&self) -> bool {
        self.trust_rule_on_path > 0
            || self.trust_theory_lemma_on_path > 0
            || self.hole_rule_on_path > 0
            || self.foreign_assume_on_path > 0
    }
}

/// Walk backwards from every empty-clause step and classify any trust
/// fallback reachable via `premises`.
///
/// This is cheap: O(steps) with a small bit-set for the visited front.
///
/// This variant treats every `assume` leaf as trust-free (a problem
/// hypothesis). To also flag `assume` leaves NOT backed by the problem's
/// provenance (leak-2), use [`terminal_trust_report_with_provenance`].
#[must_use]
pub fn terminal_trust_report(proof: &Proof) -> TerminalTrustReport {
    terminal_trust_report_with_provenance(proof, |_| true)
}

/// Walk backwards from every empty-clause step and classify any trust
/// fallback reachable via `premises`, additionally flagging any `assume`
/// leaf whose asserted term is NOT accepted by `is_legit_assume`.
///
/// `is_legit_assume(term)` must return `true` exactly for the terms an
/// external checker may accept as free hypotheses: the original asserted
/// formulas and the quantifier instantiations that trace back to an asserted
/// `forall`. Any other reachable `assume` is counted in
/// [`TerminalTrustReport::foreign_assume_on_path`] and makes the report
/// [`TerminalTrustReport::has_terminal_trust`] — it is a provenance-unbacked
/// axiom, exactly as unverified as a `:rule trust` fallback.
///
/// This is cheap: O(steps) with a small bit-set for the visited front.
#[must_use]
pub fn terminal_trust_report_with_provenance<F>(
    proof: &Proof,
    is_legit_assume: F,
) -> TerminalTrustReport
where
    F: Fn(TermId) -> bool,
{
    let mut report = TerminalTrustReport::default();
    let n = proof.steps.len();
    if n == 0 {
        return report;
    }

    let mut on_path = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();

    // Seed the walk with every step whose conclusion clause is empty. The
    // empty clause can appear from a Resolution step, a ThResolution step,
    // a Drup step, a Trust step (!), or any Step rule that the SAT proof
    // manager elected to use. We accept whichever shape is there — all we
    // care about is that the step *derives* `(cl)`.
    for (idx, step) in proof.steps.iter().enumerate() {
        if derives_empty_clause(step) {
            report.empty_clause_steps = report.empty_clause_steps.saturating_add(1);
            if !on_path[idx] {
                on_path[idx] = true;
                stack.push(idx);
            }
        }
    }

    while let Some(idx) = stack.pop() {
        let step = &proof.steps[idx];
        match step {
            ProofStep::Step { rule, premises, .. } => {
                if matches!(rule, AletheRule::Trust) {
                    report.trust_rule_on_path = report.trust_rule_on_path.saturating_add(1);
                }
                if matches!(rule, AletheRule::Hole) {
                    report.hole_rule_on_path = report.hole_rule_on_path.saturating_add(1);
                }
                push_premises(premises, &mut on_path, &mut stack);
            }
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                push_one(*clause1, &mut on_path, &mut stack);
                push_one(*clause2, &mut on_path, &mut stack);
            }
            ProofStep::TheoryLemma { kind, .. } if kind.is_trust() => {
                report.trust_theory_lemma_on_path =
                    report.trust_theory_lemma_on_path.saturating_add(1);
                // TheoryLemma steps have no premises in our representation —
                // they are leaf axioms whose clause is justified by the
                // theory. The `is_trust()` check above captures the fallback.
            }
            // Assume leaves are problem hypotheses UNLESS the provenance
            // predicate rejects the asserted term (leak-2): a reachable
            // `assume` of a term the problem never asserted (and no quantifier
            // instantiation justifies) is a laundered free axiom, flagged here
            // exactly like a `trust`/`hole` fallback.
            ProofStep::Assume(term) if !is_legit_assume(*term) => {
                report.foreign_assume_on_path = report.foreign_assume_on_path.saturating_add(1);
            }
            // Anchor is a leaf node; nothing to traverse.
            ProofStep::Anchor { .. } => {}
            _ => {
                // Exhaustive over current ProofStep variants. If a new
                // variant is added, the default is to treat it as a leaf —
                // callers that need to reason about it must update this
                // match.
            }
        }
    }

    report
}

fn derives_empty_clause(step: &ProofStep) -> bool {
    match step {
        // An `array_ext_diff_intro` is a DEFINITION and carries no clause at
        // all. Its empty `clause` field must NOT be read as "derives (cl)" —
        // doing so would seed the terminal-trust walk from a step that proves
        // nothing (and, worse, make a trust-free report out of a proof whose
        // real empty clause is trust-tainted).
        ProofStep::Step {
            rule: AletheRule::ArrayExtDiffIntro,
            ..
        } => false,
        ProofStep::Step { clause, .. } | ProofStep::Resolution { clause, .. } => clause.is_empty(),
        // TheoryLemma cannot derive the empty clause in a well-formed proof
        // (a theory never asserts `false` directly), but we accept any step
        // whose conclusion clause is empty as a defensive measure.
        ProofStep::TheoryLemma { clause, .. } => clause.is_empty(),
        ProofStep::Assume(_) | ProofStep::Anchor { .. } => false,
        _ => false,
    }
}

fn push_premises(premises: &[ProofId], on_path: &mut [bool], stack: &mut Vec<usize>) {
    for pid in premises {
        push_one(*pid, on_path, stack);
    }
}

fn push_one(pid: ProofId, on_path: &mut [bool], stack: &mut Vec<usize>) {
    let idx = pid.0 as usize;
    if idx < on_path.len() && !on_path[idx] {
        on_path[idx] = true;
        stack.push(idx);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{FarkasAnnotation, TermStore, TheoryLemmaKind};

    #[test]
    fn empty_proof_has_no_empty_clause() {
        let proof = Proof::new();
        let r = terminal_trust_report(&proof);
        assert_eq!(r.empty_clause_steps, 0);
        assert!(!r.is_trust_free());
        assert!(!r.has_terminal_trust());
    }

    #[test]
    fn th_resolution_terminal_is_trust_free() {
        let terms = TermStore::new();
        let t = terms.true_term();
        let mut proof = Proof::new();
        // assume t
        let a = proof.add_assume(t, None);
        // th_resolution on empty clause with premise `a`
        let _ = proof.add_rule_step(AletheRule::ThResolution, vec![], vec![a], vec![]);
        let r = terminal_trust_report(&proof);
        assert_eq!(r.empty_clause_steps, 1);
        assert!(r.is_trust_free());
        assert!(!r.has_terminal_trust());
    }

    #[test]
    fn trust_rule_on_terminal_path_is_flagged() {
        let terms = TermStore::new();
        let t = terms.true_term();
        let mut proof = Proof::new();
        let a = proof.add_assume(t, None);
        // Terminal empty clause step uses `:rule trust`.
        let _ = proof.add_rule_step(AletheRule::Trust, vec![], vec![a], vec![]);
        let r = terminal_trust_report(&proof);
        assert_eq!(r.empty_clause_steps, 1);
        assert_eq!(r.trust_rule_on_path, 1);
        assert!(r.has_terminal_trust());
        assert!(!r.is_trust_free());
    }

    #[test]
    fn trust_theory_lemma_on_terminal_path_is_flagged() {
        let terms = TermStore::new();
        let t = terms.true_term();
        let mut proof = Proof::new();
        // A Generic theory lemma — exports as :rule trust in Alethe.
        let lemma = proof.add_theory_lemma_with_kind("LRA", vec![t], TheoryLemmaKind::Generic);
        // Resolution deriving the empty clause using the trust lemma.
        let _ = proof.add_resolution(vec![], t, lemma, lemma);
        let r = terminal_trust_report(&proof);
        assert_eq!(r.empty_clause_steps, 1);
        assert_eq!(r.trust_theory_lemma_on_path, 1);
        assert!(r.has_terminal_trust());
    }

    #[test]
    fn fp_forward_error_lemma_on_terminal_path_is_not_flagged() {
        // `FpForwardError` is a strict-checkable kind (`is_trust() == false`):
        // a proof closing through it must be reported trust-free, unlike the
        // `Generic` lemma it is promoted from.
        let terms = TermStore::new();
        let t = terms.true_term();
        let mut proof = Proof::new();
        let lemma =
            proof.add_theory_lemma_with_kind("trust", vec![t], TheoryLemmaKind::FpForwardError);
        let _ = proof.add_resolution(vec![], t, lemma, lemma);
        let r = terminal_trust_report(&proof);
        assert_eq!(r.empty_clause_steps, 1);
        assert_eq!(
            r.trust_theory_lemma_on_path, 0,
            "FpForwardError is internally validated, not a Generic trust lemma"
        );
        assert!(r.is_trust_free());
        assert!(!r.has_terminal_trust());
    }

    #[test]
    fn trust_off_terminal_path_is_not_flagged() {
        let terms = TermStore::new();
        let t = terms.true_term();
        let mut proof = Proof::new();
        let a = proof.add_assume(t, None);
        // Unreachable trust step (not referenced as a premise of any
        // empty-clause step).
        let _orphan = proof.add_rule_step(AletheRule::Trust, vec![t], vec![], vec![]);
        // Terminal step uses clean th_resolution and only references `a`.
        let _ = proof.add_rule_step(AletheRule::ThResolution, vec![], vec![a], vec![]);
        let r = terminal_trust_report(&proof);
        assert_eq!(r.empty_clause_steps, 1);
        assert_eq!(
            r.trust_rule_on_path, 0,
            "orphan trust must not taint terminal"
        );
        assert!(r.is_trust_free());
        // Silence unused warning for `terms` and the Farkas import — the
        // latter is used by other tests in this module.
        let _ = FarkasAnnotation::from_ints(&[]);
    }

    // ---- leak-2: provenance-aware assume gate ----

    /// Red-team: an `assume` of a term the provenance predicate rejects
    /// (a laundered free axiom) reachable from the empty clause is flagged
    /// as `foreign_assume_on_path`, making the report NOT trust-free — even
    /// though it uses no `trust`/`hole` rule and every step is a "real"
    /// resolution. This is the leak-2 core.
    #[test]
    fn foreign_assume_on_terminal_path_is_flagged() {
        let terms = TermStore::new();
        let legit = terms.true_term();
        let foreign = terms.false_term();
        let mut proof = Proof::new();
        let a_legit = proof.add_assume(legit, None);
        let a_foreign = proof.add_assume(foreign, None);
        // Empty-clause step resolves both assumes; both are on the terminal
        // path.
        let mid = proof.add_rule_step(
            AletheRule::ThResolution,
            vec![foreign],
            vec![a_legit],
            vec![],
        );
        let _ = proof.add_rule_step(
            AletheRule::ThResolution,
            vec![],
            vec![mid, a_foreign],
            vec![],
        );

        // Only `legit` is backed by the problem's provenance.
        let r = terminal_trust_report_with_provenance(&proof, |t| t == legit);
        assert_eq!(r.empty_clause_steps, 1);
        assert_eq!(
            r.foreign_assume_on_path, 1,
            "the provenance-unbacked assume must be flagged"
        );
        assert_eq!(r.trust_rule_on_path, 0, "no trust rule is present");
        assert!(r.has_terminal_trust());
        assert!(!r.is_trust_free());

        // The provenance-FREE walk treats every assume as a trust-free
        // hypothesis (backward-compatible), so it would ACCEPT this leak.
        let base = terminal_trust_report(&proof);
        assert_eq!(base.foreign_assume_on_path, 0);
        assert!(base.is_trust_free());
    }

    /// A proof whose every reachable `assume` IS backed by the provenance
    /// predicate stays trust-free under the provenance-aware walk (F03 /
    /// Farkas class — must not regress a clean UNSAT).
    #[test]
    fn all_backed_assumes_are_trust_free_under_provenance() {
        let terms = TermStore::new();
        let t = terms.true_term();
        let mut proof = Proof::new();
        let a = proof.add_assume(t, None);
        let _ = proof.add_rule_step(AletheRule::ThResolution, vec![], vec![a], vec![]);
        let r = terminal_trust_report_with_provenance(&proof, |x| x == t);
        assert_eq!(r.empty_clause_steps, 1);
        assert_eq!(r.foreign_assume_on_path, 0);
        assert!(r.is_trust_free());
        assert!(!r.has_terminal_trust());
    }

    /// A foreign `assume` that is NOT reachable from any empty-clause step
    /// must not taint the terminal derivation (dead assumes are not printed
    /// on the empty-clause path).
    #[test]
    fn foreign_assume_off_terminal_path_is_not_flagged() {
        let terms = TermStore::new();
        let legit = terms.true_term();
        let foreign = terms.false_term();
        let mut proof = Proof::new();
        let a = proof.add_assume(legit, None);
        let _orphan = proof.add_assume(foreign, None);
        // Terminal step references only the legit assume.
        let _ = proof.add_rule_step(AletheRule::ThResolution, vec![], vec![a], vec![]);
        let r = terminal_trust_report_with_provenance(&proof, |t| t == legit);
        assert_eq!(
            r.foreign_assume_on_path, 0,
            "orphan foreign assume must not taint terminal"
        );
        assert!(r.is_trust_free());
    }
}
