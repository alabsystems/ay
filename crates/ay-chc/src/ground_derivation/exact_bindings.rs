// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Each step of a derivation binds exactly its clause's variables.
//!
//! A back-translated step can carry bindings its clause never mentions: the
//! clause inliner expands one composite step into its source chain and hands
//! every source step the composite's whole environment. Native validation
//! reads only the clause's variables (and AY's private UF observations, whose
//! names start with NUL), so such a derivation validates. The ground-derivation
//! artifact the checked replay exports does not accept it: a step must bind
//! exactly its source clause's variable surface (`binding_set_mismatch`).

use super::GroundDerivation;
use crate::ChcProblem;
use ay_core::kani_compat::DetHashSet as FxHashSet;

impl GroundDerivation {
    /// Drop every binding of a step that its clause does not mention, keeping
    /// the private UF-observation entries. Validation reads nothing else, so
    /// the result validates exactly when `self` does.
    pub(crate) fn retain_clause_bindings(&mut self, problem: &ChcProblem) {
        for step in &mut self.steps {
            let Some(clause) = problem.clauses().get(step.clause_index) else {
                continue;
            };
            let names: FxHashSet<String> = clause.vars().into_iter().map(|var| var.name).collect();
            step.env
                .retain(|name, _| name.starts_with('\0') || names.contains(name));
        }
    }
}

#[cfg(test)]
mod tests;
