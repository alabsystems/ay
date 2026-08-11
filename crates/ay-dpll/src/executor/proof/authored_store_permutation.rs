// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod alias_index;
mod alias_select;
mod direct;
mod scalar_select;

#[cfg(test)]
#[path = "authored_store_permutation_scalar_tests.rs"]
mod scalar_tests;
#[cfg(test)]
#[path = "authored_store_permutation_tests.rs"]
mod tests;

impl Executor {
    /// Rebuild a STORE-PERMUTATION refutation from exact authored roots.
    ///
    /// The direct arm discharges authored index disequalities against the
    /// checker's `ArrayStorePermutation` schema. The alias/select arm also
    /// transports that chain equality through authored array aliases and an
    /// `ArrayRowChain` read equality. The scalar/select arm transports that
    /// equality through exact authored scalar bindings. Every arm is
    /// fail-closed: the checker's recognizers authorize every theory lemma,
    /// all reachable assumptions must be exact authored roots, and the
    /// completed candidate must pass the native strict checker before it
    /// replaces `proof`.
    ///
    /// The Alethe surface for `ArrayStorePermutation` remains the existing
    /// honest holey wire; native strict checking is its authority.
    pub(super) fn replace_with_exact_authored_store_permutation_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        let Some(authored_index) = alias_index::AuthoredIndex::build(&self.ctx.terms, &authored)
        else {
            return;
        };
        if direct::try_reconstruct(self, proof, &authored) {
            return;
        }
        if alias_select::try_reconstruct(self, proof, &authored, &authored_index) {
            return;
        }
        let _ = scalar_select::try_reconstruct(self, proof, &authored, &authored_index);
    }
}
