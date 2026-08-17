// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array closure for the assumptions-based solve path.

use super::super::Executor;
use crate::logic_detection::TheoryKind;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::TermId;

impl Executor {
    pub(super) fn prepare_assumption_array_assertions(
        &mut self,
        preprocessed_assertions: Vec<TermId>,
        preprocessed_assumptions: &[(TermId, TermId)],
        theory_kind: TheoryKind,
    ) -> Vec<TermId> {
        let assumption_terms: Vec<TermId> = preprocessed_assumptions
            .iter()
            .map(|(term, _)| *term)
            .collect();

        // Install the actual rewritten base window and activate exact finite
        // coverage before generic Skolem extensionality. This lets the latter
        // skip only equality atoms whose exact biconditional is live, while
        // keeping assumption-only terms in the same scope.
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, preprocessed_assertions);
        let _ = self.add_finite_index_array_closure_with_roots(&assumption_terms);
        let axiom_start = self.ctx.assertions.len();

        // Both legacy fixpoints deduplicate the assertion vector. Identify
        // generated axioms by exact identity instead of by a fragile suffix.
        let mut base_set: HashSet<TermId> =
            ay_core::kani_compat::det_hash_set_with_capacity(self.ctx.assertions.len());
        base_set.extend(self.ctx.assertions.iter().copied());
        if theory_kind == TheoryKind::ArrayEuf {
            self.run_array_axiom_fixpoint_5_with_roots(&assumption_terms);
        } else {
            self.run_array_axiom_full_fixpoint_at_with_roots(axiom_start, &assumption_terms);
        }

        let array_axioms: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .filter(|axiom| !base_set.contains(axiom))
            .collect();
        self.ctx.assertions.retain(|axiom| base_set.contains(axiom));
        let mut closed_assertions = std::mem::replace(&mut self.ctx.assertions, saved_assertions);
        closed_assertions.extend(array_axioms);

        // The legacy fixpoint can synthesize nested array-valued ROW
        // equalities. Enumerate again after it finishes so those new atoms
        // cannot bypass finite closure.
        self.close_finite_arrays_in_owned_assertion_window(closed_assertions, &assumption_terms)
    }
}
