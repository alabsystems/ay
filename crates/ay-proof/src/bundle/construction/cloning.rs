// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Metered raw copying for already sealed bundles; never renew their authority.

use super::*;

impl SerializableProofBundle {
    /// Clone every serialized field under the caller's cumulative resource control.
    ///
    /// Work and owned-copy bytes are charged before copying, including unused
    /// positional entries, nested sorts and the exact schema string. Unlike
    /// reconstructing a bundle from a live solver, this preserves even malformed
    /// metadata and never refreshes a seal or changes the claimed problem.
    /// Successful copying grants no proof authority; independent strict checking
    /// and external source binding are still required. The callback must retain
    /// its allowance across this copy and every subsequent replay. This is not
    /// an aggregate process-RSS limit or a JSON decoding budget.
    pub fn try_clone_with_progress(
        &self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Self, ProofCheckError> {
        charge(progress, 0, 0)?;
        let schema = copy_string(&self.schema, progress)?;
        let term_entries =
            TermStore::copy_snapshot_entries_with_progress(&self.term_entries, progress)
                .map_err(|_| ProofCheckError::ResourceLimit)?;
        let steps = copy_steps(&self.steps, progress)?;
        let obligation_assertions = copy_slice(&self.obligation_assertions, progress)?;
        let datatype_declarations = copy_names(&self.datatype_declarations, progress)?;
        let constructor_selectors = copy_names(&self.constructor_selectors, progress)?;
        let datatype_member_signatures =
            copy_signatures(&self.datatype_member_signatures, progress)?;
        let mut declared_function_identities =
            vector(self.declared_function_identities.len(), progress)?;
        for identity in &self.declared_function_identities {
            declared_function_identities.push(copy_string(identity, progress)?);
        }
        let copied = Self {
            schema,
            steps,
            term_entries,
            true_term: self.true_term,
            false_term: self.false_term,
            var_counter: self.var_counter,
            obligation_assertions,
            datatype_declarations,
            constructor_selectors,
            datatype_member_signatures,
            declared_function_identities,
        };
        charge(progress, 0, 0)?;
        Ok(copied)
    }
}

#[cfg(test)]
mod tests;
