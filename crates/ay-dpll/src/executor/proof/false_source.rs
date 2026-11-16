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

/// `--trace-cegqi-attr`-gated note naming which fold rescue ran and what it
/// answered, so a census of `preprocessor-fold-to-false` declines can read
/// the decision off the trace instead of inferring it from the artifact.
fn fold_note(message: &'static str) {
    authored_consequence_replay::replay_note(|| format!("[fold-to-false] {message}"));
}

/// Whether `proof` reaches the empty clause through an `assume false`.
fn has_reachable_false_assume(executor: &Executor, proof: &Proof) -> bool {
    let false_term = executor.ctx.terms.false_term();
    ay_proof::terminal_trust_report_with_provenance(proof, |term| term != false_term)
        .foreign_assume_on_path
        > 0
}

/// Whether `proof` rests on an `assume false` the PREPROCESSOR manufactured
/// (no authored Boolean-constant premise). [`demote_unattributed_assumed_false`]
/// owns such a proof: it runs after the replacement cascade and tries the
/// specialized fold rescues before any general one.
pub(super) fn rests_on_unattributed_false(executor: &Executor, proof: &Proof) -> bool {
    has_reachable_false_assume(executor, proof) && !executor.boolean_constant_premises_authored().1
}

pub(super) fn demote_unattributed_assumed_false(executor: &mut Executor, proof: &mut Proof) {
    let false_term = executor.ctx.terms.false_term();
    if !has_reachable_false_assume(executor, proof) {
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
    fold_note("erasure reached; trying the fold rescues");
    // Name the authored root(s) the fold erased, for the shape census: the
    // provenance ledger is aligned with the parsed stack, so a row whose
    // elaborated term is the constant `false` is a root the elaborator folded.
    authored_consequence_replay::replay_note(|| {
        let parsed = executor.ctx.assertions_parsed();
        let originals = executor.proof_original_problem_assertions_slice();
        let mut named = Vec::new();
        if originals.len() == parsed.len() {
            for (index, (&term, source)) in originals.iter().zip(parsed).enumerate() {
                if term == false_term {
                    let text = crate::executor::proof_surface_syntax::format_frontend_term(
                        crate::executor::proof_surface_syntax::strip_frontend_annotations(source),
                    );
                    let head: String = text.chars().take(400).collect();
                    named.push(format!("root#{index} ({} bytes): {head}", text.len()));
                }
            }
        } else {
            named.push(format!(
                "provenance/parsed length mismatch ({} vs {})",
                originals.len(),
                parsed.len()
            ));
        }
        format!("[fold-to-false] folded roots: {}", named.join(" | "))
    });
    // FIRST, and charged per candidate root rather than per parsed stack: a
    // root whose refuted conjunct is a DISEQUALITY between two spellings of
    // one normalized term — the `let`-rooted QF_UFLIA hash family, where
    // `(+ v v)` and `(* 2 v)` are one term and `(distinct t t)` folded the
    // whole root. None of the three passes below can see a `let`-rooted
    // root, and each charges four source passes before finding that out;
    // measured on `hash_uns_03_18` that left 2.7 MB of the 32 MB envelope
    // for a 2.8 MB pass. The identity's own argument is derivable with
    // `cong` over Farkas-verified bounds (`authored_fold_identity`).
    if executor.replace_with_exact_authored_fold_identity_refutation(proof) {
        fold_note("fold-identity committed");
        return;
    }
    fold_note("fold-identity declined");
    if executor.replace_with_exact_authored_conjunct_eval_refutation(proof) {
        fold_note("conjunct-eval committed");
        return;
    }
    fold_note("conjunct-eval declined");
    // The conjunct scan only recognises a self-false `(not X)` LEAF. A closed
    // authored assertion — `(or (< 2 0) (>= 2 32))`, `(not (bvule #x0 #x1))` —
    // has no such leaf, yet its refutation is fully re-derivable by the strict
    // checker's own bounded interpreter. Try that before giving up.
    if executor.replace_with_exact_authored_bv_lia_refutation(proof) {
        fold_note("bv-lia committed");
        return;
    }
    fold_note("bv-lia declined");
    // Neither scan can see a root that carries a BINDER: both rebuild the
    // authored assertion through `raw_intern_surface`, which fails closed on
    // every quantifier, so one `forall` anywhere in the tree denied the whole
    // assertion its re-intern. That is exactly the alpha-shared class — two
    // identical authored quantifiers folded a propositional tautology's
    // negation to `false` — and its argument needs no evaluation at all, only
    // the propositional skeleton the author wrote.
    if executor.replace_with_exact_authored_shared_tautology_refutation(proof) {
        fold_note("shared-tautology committed");
        return;
    }
    fold_note("shared-tautology declined");
    rescue_by_bitblast_or_erase(executor, proof);
}

/// The last fold rescues, then the erasure. An OPEN bit-vector root over free
/// words (`x / 2^k` against `x >> k`, folded by term construction) needs no
/// evaluation and no identity spelling: the checker's own bit-blaster decides
/// it (`authored_bv_bitblast_refutation`). A fold that took a closed index
/// spelling or a hit write with it (`(select (store .. (bvadd #x3f #x01) v)
/// #x40)` folded to `v`) is re-derived over the raw authored roots by the
/// ground closure (`authored_ground_closure`). Only when both decline is the
/// proof erased, attributed.
fn rescue_by_bitblast_or_erase(executor: &mut Executor, proof: &mut Proof) {
    if executor.replace_with_exact_authored_bv_bitblast_refutation(proof) {
        fold_note("bv-bitblast committed");
        return;
    }
    fold_note("bv-bitblast declined");
    if executor.rescue_fold_with_raw_ground_closure(proof) {
        fold_note("raw-ground-closure committed");
        return;
    }
    fold_note("raw-ground-closure declined; erasing to the bare hole");
    set_empty_hole(proof);
    executor.record_proof_decline(ProofDeclineMechanism::PreprocessorFoldToFalseUnrecorded);
}
