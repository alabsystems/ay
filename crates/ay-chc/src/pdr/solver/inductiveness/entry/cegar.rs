// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::obligation::ProofObligation;
use crate::pdr::solver::{BlockResult, EntryCegarDischarge, PdrSolver};
use crate::{ChcExpr, PredicateId};

pub(super) fn entry_cegar_discharge_state(
    solver: &mut PdrSolver,
    predicate: PredicateId,
    state: ChcExpr,
    level: usize,
    timeout_ms: u64,
) -> EntryCegarDischarge {
    const MAX_STEPS: usize = 128;
    let deadline = ay_core::time::Instant::now() + std::time::Duration::from_millis(timeout_ms);

    // Local blocking loop: attempt to prove `state` unreachable at `level`.
    // If unreachable, learn blocking lemmas along the way so the entry SAT model
    // disappears on retry.
    let mut stack: Vec<ProofObligation> = vec![ProofObligation::new(predicate, state, level)];
    let mut unknown_predecessors: Vec<(usize, PredicateId, ChcExpr)> = Vec::new();

    for _ in 0..MAX_STEPS {
        // #2901: Check cancellation before each CEGAR iteration.
        if solver.is_cancelled() {
            return EntryCegarDischarge::Unknown;
        }
        // Phase 2 (#1624): Timeout check to bound Entry-CEGAR overhead
        if ay_core::time::Instant::now() > deadline {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: Entry-CEGAR timeout ({}ms) for pred {} at level {}",
                    timeout_ms,
                    predicate.index(),
                    level
                );
            }
            return EntryCegarDischarge::Unknown;
        }
        let Some(mut pob) = stack.pop() else {
            return EntryCegarDischarge::Unreachable;
        };

        match solver.block_obligation_with_local_blocked(&mut pob, &[], &unknown_predecessors) {
            BlockResult::Blocked(lemma) => {
                let lvl = lemma.level;
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Entry-CEGAR: blocked pred {} at level {} with lemma {}",
                        lemma.predicate.index(),
                        lvl,
                        lemma.formula
                    );
                }
                // #2459: Blocking context — entry-CEGAR blocking.
                solver.add_blocking_lemma(lemma, lvl);
                if stack.is_empty() {
                    return EntryCegarDischarge::Unreachable;
                }
            }
            BlockResult::AlreadyBlocked => {
                if stack.is_empty() {
                    return EntryCegarDischarge::Unreachable;
                }
            }
            BlockResult::Reachable(predecessor) => {
                if pob.level == 0 {
                    return EntryCegarDischarge::Reachable;
                }

                let child_level = pob.level - 1;
                let parent_for_chain = pob
                    .clone()
                    .with_incoming_clause(predecessor.clause_index)
                    .with_smt_model(predecessor.smt_model.clone());

                // Re-try the parent after attempting to discharge the child.
                stack.push(pob);
                let mut child_pob =
                    ProofObligation::new(predecessor.predicate, predecessor.state, child_level)
                        .with_parent(parent_for_chain)
                        .with_smt_model(predecessor.smt_model);
                // #1275: Propagate derivation_id for hyperedge tracking.
                if let Some(deriv_id) = predecessor.derivation_id {
                    child_pob = child_pob.with_derivation_id(deriv_id);
                }
                stack.push(child_pob);
            }
            BlockResult::Unknown => {
                if let Some(parent) = pob.parent.as_deref() {
                    unknown_predecessors.push((parent.level, pob.predicate, pob.state.clone()));
                    continue;
                }
                return EntryCegarDischarge::Unknown;
            }
        }
    }

    EntryCegarDischarge::Unknown
}
