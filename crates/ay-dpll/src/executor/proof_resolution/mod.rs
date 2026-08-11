// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Empty-clause derivation strategies for UNSAT proofs.
//!
//! Contains multiple resolution strategies (th_resolution, packet resolution,
//! congruence bridging, SAT resolution, contradictory assumptions, trust
//! fallback) for deriving the empty clause from assumptions and theory lemmas.
//!
//! Extracted from `proof.rs` as part of #6763.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep};

mod checked_sat_refutation;
pub(crate) mod congruence;
pub(crate) mod empty_clause;
mod sat_resolution;

pub(in crate::executor) use checked_sat_refutation::CheckedSatRefutation;

/// Remove trailing ThResolution/Resolution steps from the proof.
/// The chain is always appended at the end by the derive-empty-clause
/// functions, so truncating from the last non-resolution step preserves
/// ProofId indexing for the remaining base steps.
pub(crate) fn strip_resolution_steps(proof: &mut Proof) {
    let last_base = proof
        .steps
        .iter()
        .rposition(|step| {
            !matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::ThResolution | AletheRule::Resolution,
                    ..
                } | ProofStep::Resolution { .. }
            )
        })
        .map_or(0, |idx| idx + 1);
    proof.steps.truncate(last_base);
}

pub(crate) fn proof_structure_is_well_formed(proof: &Proof) -> bool {
    let len = proof.steps.len() as u32;
    proof.steps.iter().all(|step| match step {
        ProofStep::Resolution {
            clause1, clause2, ..
        } => clause1.0 < len && clause2.0 < len,
        ProofStep::Step { premises, .. } => premises.iter().all(|premise| premise.0 < len),
        ProofStep::Anchor { end_step, .. } => end_step.0 < len,
        ProofStep::Assume(_) | ProofStep::TheoryLemma { .. } => true,
        other => unreachable!(
            "unhandled ProofStep variant in proof_structure_is_well_formed(): {other:?}"
        ),
    })
}

/// Keep only proof steps required to derive the final empty clause.
///
/// This drops unreachable assumptions and helper lemmas that are not part of
/// the exported contradiction chain.
pub(crate) fn prune_to_empty_clause_derivation(proof: &mut Proof) {
    let Some(target_idx) = proof.steps.iter().rposition(|step| match step {
        ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. } => clause.is_empty(),
        _ => false,
    }) else {
        return;
    };

    let _ = prune_to_empty_clause_derivation_at(proof, target_idx);
}

/// Keep only the dependency cone of one exact empty-clause step.
///
/// The caller supplies the root so proof publication can compare multiple
/// independently derived contradictions instead of unconditionally selecting
/// the last one. Returns `false` without changing `proof` when the target is not
/// an empty clause or a premise cannot be remapped.
pub(crate) fn prune_to_empty_clause_derivation_at(proof: &mut Proof, target_idx: usize) -> bool {
    if !matches!(
        proof.steps.get(target_idx),
        Some(ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. })
            if clause.is_empty()
    ) {
        return false;
    }

    let mut keep = vec![false; proof.steps.len()];
    let mut stack = vec![target_idx];
    while let Some(idx) = stack.pop() {
        if idx >= proof.steps.len() || keep[idx] {
            continue;
        }
        keep[idx] = true;
        match &proof.steps[idx] {
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                stack.push(clause1.0 as usize);
                stack.push(clause2.0 as usize);
            }
            ProofStep::Step { premises, .. } => {
                for premise in premises {
                    stack.push(premise.0 as usize);
                }
            }
            ProofStep::Anchor { end_step, .. } => {
                stack.push(end_step.0 as usize);
            }
            ProofStep::Assume(_) | ProofStep::TheoryLemma { .. } => {}
            other => unreachable!(
                "unhandled ProofStep variant in prune_to_empty_clause_derivation(): {other:?}"
            ),
        }
    }

    if keep.iter().all(|&k| k) {
        proof
            .named_steps
            .retain(|_, id| matches!(proof.steps.get(id.0 as usize), Some(ProofStep::Assume(_))));
        return true;
    }

    let mut remap: HashMap<u32, u32> = HashMap::default();
    let mut new_steps = Vec::with_capacity(keep.iter().filter(|&&k| k).count());
    for (old_idx, step) in proof.steps.iter().enumerate() {
        if keep[old_idx] {
            let new_idx = new_steps.len() as u32;
            remap.insert(old_idx as u32, new_idx);
            new_steps.push(step.clone());
        }
    }

    // Validate that every premise reference in kept steps can be remapped.
    // If any premise points to a pruned step, abort to avoid dangling IDs (#7959).
    let all_remappable = new_steps.iter().all(|step| match step {
        ProofStep::Resolution {
            clause1, clause2, ..
        } => remap.contains_key(&clause1.0) && remap.contains_key(&clause2.0),
        ProofStep::Step { premises, .. } => premises.iter().all(|p| remap.contains_key(&p.0)),
        ProofStep::Anchor { end_step, .. } => remap.contains_key(&end_step.0),
        ProofStep::Assume(_) | ProofStep::TheoryLemma { .. } => true,
        _ => true,
    });
    if !all_remappable {
        tracing::warn!(
            kept = new_steps.len(),
            total = proof.steps.len(),
            "proof pruning aborted: premises reference pruned steps"
        );
        return false;
    }

    for step in &mut new_steps {
        match step {
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                *clause1 = ProofId(remap[&clause1.0]);
                *clause2 = ProofId(remap[&clause2.0]);
            }
            ProofStep::Step { premises, .. } => {
                for premise in premises {
                    *premise = ProofId(remap[&premise.0]);
                }
            }
            ProofStep::Anchor { end_step, .. } => {
                *end_step = ProofId(remap[&end_step.0]);
            }
            ProofStep::Assume(_) | ProofStep::TheoryLemma { .. } => {}
            other => unreachable!(
                "unhandled ProofStep variant in prune_to_empty_clause_derivation(): {other:?}"
            ),
        }
    }

    // Named steps are printer metadata for source assumptions.  Pruning must
    // keep that metadata in lockstep with the positional step ids: retaining a
    // stale id can make a later proof-rebuild pass abort or print the wrong
    // assumption.  Drop names for pruned, dangling, or non-assume steps and
    // remap the surviving assumptions exactly as premises were remapped above.
    let mut new_named_steps = proof.named_steps.clone();
    new_named_steps.retain(|_, id| {
        let old_idx = id.0 as usize;
        if !matches!(proof.steps.get(old_idx), Some(ProofStep::Assume(_))) {
            return false;
        }
        let Some(&new_idx) = remap.get(&id.0) else {
            return false;
        };
        *id = ProofId(new_idx);
        true
    });

    proof.steps = new_steps;
    proof.named_steps = new_named_steps;
    true
}
