// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Proof, TermId};

use super::super::Executor;

impl Executor {
    pub(super) fn finish_input_syntax_rewrite(
        &mut self,
        proof: &mut Proof,
        rewrites: &HashMap<TermId, TermId>,
        term_overrides: HashMap<TermId, String>,
        aux_assume_steps: &HashSet<u32>,
    ) {
        if !term_overrides.is_empty() {
            self.last_proof_term_overrides = Some(term_overrides);
        }
        let extended_assertions = self.proof_exportable_assertions(rewrites);
        Self::demote_auxiliary_non_problem_assumptions(
            proof,
            &extended_assertions,
            aux_assume_steps,
        );
        // Conjunct assumes introduced by top-level and-flattening are DERIVED
        // from their asserted conjunction before demotion can turn them into
        // unverified `trust` steps and fail-close the strict checker.
        Self::derive_conjunct_assumptions_from_problem_roots(
            &mut self.ctx.terms,
            proof,
            &extended_assertions,
        );
        // Replay propagation rewrites before demotion; a missing or invalid
        // record still falls through to the existing fail-closed path.
        self.derive_propagated_value_assumptions(proof, &extended_assertions);
        Self::demote_non_problem_assumptions(proof, &extended_assertions);
        // Last resort: rebuild from the original assertions only. Failure keeps
        // the existing proof unchanged.
        self.rebuild_trust_leaf_proof_from_original_assertions(proof);
    }
}
