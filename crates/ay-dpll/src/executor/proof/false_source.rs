// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final proof-wire authority for canonical Boolean-false assumptions.

use super::*;

fn set_empty_hole(proof: &mut Proof) {
    proof.steps.clear();
    proof.named_steps.clear();
    let _ = proof.add_rule_step(AletheRule::Hole, Vec::new(), Vec::new(), Vec::new());
}

pub(super) fn demote_unattributed_assumed_false(executor: &mut Executor, proof: &mut Proof) {
    let false_term = executor.ctx.terms.false_term();
    let has_reachable_false_assume =
        ay_proof::terminal_trust_report_with_provenance(proof, |term| term != false_term)
            .foreign_assume_on_path
            > 0;
    if !has_reachable_false_assume {
        return;
    }
    if executor.boolean_constant_premises_authored().1 {
        if let Some(overrides) = &mut executor.last_proof_term_overrides {
            overrides.remove(&false_term);
        }
        return;
    }
    // The proof rests on an `assume false` that the PREPROCESSOR manufactured
    // by folding an authored assertion, keeping no record of the rewrite.
    // Erasing it is right — `false |- bottom` proves nothing about the input,
    // and carcara rejects such a document at its first step — but the erasure
    // used to be silent, and the resulting one-line artifact was
    // indistinguishable from every other cause of a bare hole.
    //
    // Before giving up, try to RECORD the argument the preprocessor actually
    // had: the fold happened because some conjunct of an authored assertion
    // evaluates to `false` on its own, and that evaluation is expressible.
    // Only a candidate the strict checker accepts whole can replace the proof;
    // otherwise the erasure proceeds exactly as before, now attributed.
    if executor.replace_with_exact_authored_conjunct_eval_refutation(proof) {
        return;
    }
    // The conjunct scan only recognises a self-false `(not X)` LEAF. A closed
    // authored assertion — `(or (< 2 0) (>= 2 32))`, `(not (bvule #x0 #x1))` —
    // has no such leaf, yet its refutation is fully re-derivable by the strict
    // checker's own bounded interpreter. Try that before giving up.
    if executor.replace_with_exact_authored_bv_lia_refutation(proof) {
        return;
    }
    set_empty_hole(proof);
    executor.record_proof_decline(ProofDeclineMechanism::PreprocessorFoldToFalseUnrecorded);
}
