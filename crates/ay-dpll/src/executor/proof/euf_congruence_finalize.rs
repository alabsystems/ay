// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Commit gate for rebuilt EUF congruence proofs.

use ay_core::{Proof, ProofId, ProofStep, TermStore};

pub(super) fn finalize_euf_congruence_split(
    proof: &mut Proof,
    terms: &TermStore,
    original: Vec<ProofStep>,
    original_named: ay_core::kani_compat::KaniHashMap<String, ProofId>,
    remap: &[ProofId],
    new_steps: Vec<ProofStep>,
    changed: bool,
    should_stop: &dyn Fn() -> bool,
    memory_limit: Option<usize>,
) {
    if !changed {
        proof.steps = original;
        return;
    }

    let mut remapped_named = original_named.clone();
    remapped_named.retain(|_, id| {
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
    proof.steps = new_steps;
    proof.named_steps = remapped_named;

    // Whole-proof revert gate: never ship a split that strict checking rejects.
    if super::check::check_proof_gate_under_controls(proof, terms, should_stop, memory_limit)
        .is_err()
    {
        proof.steps = original;
        proof.named_steps = original_named;
    }
}
