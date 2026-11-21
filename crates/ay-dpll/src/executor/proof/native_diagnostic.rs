// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded diagnostic copying at the actual pre-publication proof boundary.
//! This owns no result certificate and changes no public artifact accessor.

use std::sync::Arc;

use ay_proof::{ProofCheckError, SerializableProofBundle};

use super::native_source_scope::NativeProofSourceScope;
use crate::executor::Executor;

pub(crate) struct NativeDiagnosticSnapshot {
    pub(crate) source: Arc<NativeProofSourceScope>,
    pub(crate) proof: SerializableProofBundle,
}

impl Executor {
    pub(crate) fn capture_native_diagnostic_snapshot_with_progress(
        &self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Option<NativeDiagnosticSnapshot>, ProofCheckError> {
        if !progress(1, 0) {
            return Err(ProofCheckError::ResourceLimit);
        }
        let Some(source) = self.native_proof_source_scope.as_ref() else {
            return Ok(None);
        };
        // Mandatory retained classes have their own evidence ownership; this
        // initial native route must not copy a generic substitute for them.
        if self.last_unsat_proof_reconstruction_suppressed
            || self.has_strict_native_nra_sos_bundle_state()
            || self.has_strict_native_bv_lia_bundle_state()
            || self.last_proof_has_finite_enum_sidecar()
            || !self
                .unsat_query_epoch
                .as_ref()
                .is_some_and(|epoch| epoch.proof_output_is_current(self))
        {
            return Ok(None);
        }
        if !source
            .is_current_with_progress(self, progress)
            .ok_or(ProofCheckError::ResourceLimit)?
        {
            return Ok(None);
        }
        if !source
            .diagnostic_applications_are_declared_with_progress(self, progress)
            .ok_or(ProofCheckError::ResourceLimit)?
        {
            return Ok(None);
        }
        let Some(proof) = self.last_proof.as_ref() else {
            return Ok(None);
        };
        if !progress(0, self.ctx.terms.true_memory_bytes()) {
            return Err(ProofCheckError::ResourceLimit);
        }
        let declarations = self.datatype_decls_for_strict_proof_with_progress(progress)?;
        let selectors = self.ctor_selector_decls_for_strict_proof_with_progress(progress)?;
        let Some(signatures) =
            self.datatype_member_signatures_for_strict_proof_with_progress(progress)?
        else {
            return Ok(None);
        };
        let proof = SerializableProofBundle::from_proof_with_typed_context_and_progress(
            proof,
            &self.ctx.terms,
            source.roots(),
            &declarations,
            &selectors,
            &signatures,
            progress,
        )?;
        if !source
            .is_current_with_progress(self, progress)
            .ok_or(ProofCheckError::ResourceLimit)?
        {
            return Ok(None);
        }
        if !progress(1, std::mem::size_of::<NativeDiagnosticSnapshot>()) {
            return Err(ProofCheckError::ResourceLimit);
        }
        Ok(Some(NativeDiagnosticSnapshot {
            source: Arc::clone(source),
            proof,
        }))
    }
}
