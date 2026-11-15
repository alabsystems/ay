// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Meter sealed declaration copies without turning stale capability presence
//! into permission to use the generic export lane.

use super::*;
use crate::executor::proof::check::declarations::{
    copy_registry, copy_signatures, Control, ProofDeclarationInventories,
};
use ay_proof::ProofCheckError;

#[cfg(test)]
mod tests;

impl Executor {
    /// `Ok(None)` means absent/stale finite-enum authority, not permission for
    /// the caller to rebuild a generic proof when a finite-enum sidecar exists.
    pub(crate) fn checked_finite_enum_export_declarations_with_progress(
        &self,
        proof: &Proof,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Option<ProofDeclarationInventories>, ProofCheckError> {
        Control::new(progress).run(|control| {
            let Some(seal) = self.finite_enum_export_seal(proof, control)? else {
                return Ok(None);
            };
            let datatypes = copy_registry(
                seal.datatype_decls.len(),
                seal.datatype_decls
                    .iter()
                    .map(|(n, c)| (n.as_str(), c.as_slice())),
                control,
            )?;
            let selectors = copy_registry(
                seal.selector_decls.len(),
                seal.selector_decls
                    .iter()
                    .map(|(n, c)| (n.as_str(), c.as_slice())),
                control,
            )?;
            let members = copy_signatures(&seal.member_signatures, control)?;
            Ok(Some((datatypes, selectors, members)))
        })
    }

    /// Copy only the current canonical proof's selected direct authored roots.
    /// Sidecar presence remains terminal when this returns `Ok(None)`.
    pub(crate) fn finite_enum_scope_for_proof_with_progress(
        &self,
        proof: &Proof,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Option<Vec<TermId>>, ProofCheckError> {
        Control::new(progress).run(|control| {
            let Some(seal) = self.finite_enum_export_seal(proof, control)? else {
                return Ok(None);
            };
            let mut scope = control.vector(seal.sources.len())?;
            scope.extend(seal.assumptions());
            Ok(Some(scope))
        })
    }

    fn finite_enum_export_seal(
        &self,
        proof: &Proof,
        control: &mut Control<'_>,
    ) -> Result<Option<&CheckedFiniteEnumPigeonholeProof>, ProofCheckError> {
        let Some(seal) = self.last_checked_finite_enum_pigeonhole.as_ref() else {
            return Ok(None);
        };
        control.charge(2, 0)?;
        if self.ctx.terms.instance_term_bytes() > MAX_BUNDLE_TERM_BYTES
            || self.ctx.terms.true_memory_bytes() > MAX_BUNDLE_TERM_BYTES
        {
            return Ok(None);
        }
        if !self.plain_unsat_query_epoch_is_current_with_resource_control(&mut |work, bytes| {
            control.charge(work, bytes).is_ok()
        })? {
            return Ok(None);
        }
        let Some((roots, assumptions)) =
            self.unsat_query_epoch_inventory_lengths_for_resource_control()
        else {
            return Ok(None);
        };
        let Some(stored) = self.last_proof.as_ref() else {
            return Ok(None);
        };
        let count = [
            roots,
            assumptions,
            seal.root_len,
            seal.sources.len(),
            seal.members.len(),
            seal.equalities.len(),
            stored.steps.len(),
            proof.steps.len(),
        ]
        .into_iter()
        .try_fold(1usize, usize::checked_add)
        .and_then(|n| n.checked_mul(16))
        .ok_or(ProofCheckError::ResourceLimit)?;
        // Price the repeated legacy currency scan, including proof comparisons,
        // entry stamps and the full original-root/provenance comparison. The
        // exact epoch helper above has already admitted its actual root window.
        control.charge(count, 0)?;
        Ok(self.checked_finite_enum_capability_for_proof(proof))
    }
}
