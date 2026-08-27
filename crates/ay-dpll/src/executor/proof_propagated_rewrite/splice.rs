// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backward-reference-preserving proof-chain splicing.

use super::*;

fn remap(id: ProofId, id_map: &[ProofId]) -> ProofId {
    id_map.get(id.0 as usize).copied().unwrap_or(id)
}

fn append_planned_chain(proof: &mut Proof, chain: Proof, conclusion: ProofId) -> ProofId {
    let mut chain_map = Vec::with_capacity(chain.steps.len());
    for step in chain.steps {
        let appended = match step {
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => proof.add_step(ProofStep::Step {
                rule,
                clause,
                premises: premises
                    .into_iter()
                    .map(|premise| remap(premise, &chain_map))
                    .collect(),
                args,
            }),
            ProofStep::Resolution {
                clause,
                pivot,
                clause1,
                clause2,
            } => proof.add_step(ProofStep::Resolution {
                clause,
                pivot,
                clause1: remap(clause1, &chain_map),
                clause2: remap(clause2, &chain_map),
            }),
            other => proof.add_step(other),
        };
        chain_map.push(appended);
    }
    remap(conclusion, &chain_map)
}

fn append_original_step(proof: &mut Proof, step: ProofStep, id_map: &[ProofId]) -> ProofId {
    let remapped = match step {
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
                .map(|premise| remap(premise, id_map))
                .collect(),
            args,
        },
        ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        } => ProofStep::Resolution {
            clause,
            pivot,
            clause1: remap(clause1, id_map),
            clause2: remap(clause2, id_map),
        },
        ProofStep::Anchor {
            end_step,
            variables,
        } => ProofStep::Anchor {
            end_step: remap(end_step, id_map),
            variables,
        },
        other => other,
    };
    proof.add_step(remapped)
}

/// The planner's output: one SHARED chain serving every non-constant
/// candidate (inserted once, at the first shared conclusion's position),
/// plus per-candidate solo chains for Boolean-constant targets (#4751
/// shared-plan lane).
pub(super) struct PlannedPropagationChains {
    pub(super) shared_chain: Proof,
    /// Assume index → conclusion id WITHIN `shared_chain`.
    pub(super) shared_conclusions: HashMap<usize, ProofId>,
    /// Assume index → self-contained chain and its conclusion.
    pub(super) solo: HashMap<usize, (Proof, ProofId)>,
}

/// Replace replayable assumptions while keeping every premise reference
/// backward in both the inserted chains and the retained proof.
///
/// The shared chain is appended ONCE, when the first assume it serves is
/// reached; every later shared conclusion references those already-inserted
/// steps, which stay backward because proof positions only grow.
pub(super) fn splice_propagated_plans(proof: &mut Proof, mut planned: PlannedPropagationChains) {
    let old_steps = std::mem::take(&mut proof.steps);
    let mut rebuilt = Proof::new();
    let mut id_map = Vec::with_capacity(old_steps.len());
    // Once inserted: chain-local ProofId -> rebuilt ProofId.
    let mut shared_map: Option<Vec<ProofId>> = None;
    for (idx, step) in old_steps.into_iter().enumerate() {
        let id = if let Some(conclusion) = planned.shared_conclusions.remove(&idx) {
            let map = shared_map.get_or_insert_with(|| {
                let chain = std::mem::replace(&mut planned.shared_chain, Proof::new());
                let mut chain_map = Vec::with_capacity(chain.steps.len());
                for chain_step in chain.steps {
                    let appended = match chain_step {
                        ProofStep::Step {
                            rule,
                            clause,
                            premises,
                            args,
                        } => rebuilt.add_step(ProofStep::Step {
                            rule,
                            clause,
                            premises: premises
                                .into_iter()
                                .map(|premise| remap(premise, &chain_map))
                                .collect(),
                            args,
                        }),
                        ProofStep::Resolution {
                            clause,
                            pivot,
                            clause1,
                            clause2,
                        } => rebuilt.add_step(ProofStep::Resolution {
                            clause,
                            pivot,
                            clause1: remap(clause1, &chain_map),
                            clause2: remap(clause2, &chain_map),
                        }),
                        other => rebuilt.add_step(other),
                    };
                    chain_map.push(appended);
                }
                chain_map
            });
            remap(conclusion, map)
        } else if let Some((chain, conclusion)) = planned.solo.remove(&idx) {
            append_planned_chain(&mut rebuilt, chain, conclusion)
        } else {
            append_original_step(&mut rebuilt, step, &id_map)
        };
        id_map.push(id);
    }
    *proof = rebuilt;
}
