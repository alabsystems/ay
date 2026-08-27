// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Classification of substitution-bridge candidate leaves.

use super::*;

impl Executor {
    pub(super) fn substitution_bridge_leaf_term(step: &ProofStep) -> Option<TermId> {
        match step {
            ProofStep::Assume(term) => Some(*term),
            // The provenance demotion pass runs before this final repair and
            // converts a generated Assume into an explicit unit `trust`. It is
            // still repairable only when the same substitution planner derives
            // that exact unit from authored premises; arbitrary trust clauses
            // remain untouched.
            ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            } if premises.is_empty() && clause.len() == 1 => Some(clause[0]),
            // A GENERIC-kind unit theory lemma is the same defect in a different
            // coat: an unpedigreed leaf the strict checker rejects by kind. The
            // DT lazy lane's indexed-authority recording (2026-08-20) moved its
            // propagated selector-through-equality leaves from unit `trust`
            // steps to exactly this shape, which silently disengaged the bridge.
            // The leaf is unchanged, only its spelling moved. Same repair
            // contract: derivable from authored premises or left as-is.
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                clause,
                ..
            } if clause.len() == 1 => Some(clause[0]),
            _ => None,
        }
    }
}
