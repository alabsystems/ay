// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Diagnostic transport keeps the original INPUT and actual v4 proof distinct.
//! Reading requires the opaque issued-source owner, never a serialized digest.

use super::*;
use ay_proof::{read_retained_proof_bundle_with_resource_control, RetainedProofTransportLimits};

/// Source input plus independently checked retained-v4 proof bytes. These
/// documents carry no serialized solver, query-epoch or publication authority.
/// Keep the input and proof together when persisting diagnostics; fresh
/// readers must supply their independently authenticated expected source.
pub struct NativeQueryDiagnosticDocument {
    input_json: String,
    proof_v4: Vec<u8>,
}

impl NativeQueryDiagnosticDocument {
    pub fn issued_input_json(&self) -> &str {
        &self.input_json
    }
    pub fn retained_proof_bytes(&self) -> &[u8] {
        &self.proof_v4
    }
    pub fn into_parts(self) -> (String, Vec<u8>) {
        (self.input_json, self.proof_v4)
    }
}

impl NativeQueryProofEnvelope {
    /// Copy the actual issued INPUT and encode the complete retained v4 payload
    /// under one cumulative caller owner. The combined output must fit the
    /// requested JSON-byte ceiling. No raw-v3 fallback or evidence synthesis
    /// occurs. A post-solve envelope without issued INPUT declines.
    pub fn encode_diagnostic_document_with_resource_control(
        &self,
        solver: &Solver,
        requested: RetainedProofTransportLimits,
        deadline: Instant,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Option<NativeQueryDiagnosticDocument>, ProofCheckError> {
        let mut original =
            |w, b| Instant::now() < deadline && progress(w, b) && Instant::now() < deadline;
        Control::new(&mut original).run_retained(|control| {
            let Some(input) = self.issued_input_json() else {
                return Ok(None);
            };
            if !self.binding.is_current(solver, control)? {
                return Ok(None);
            }
            if input.len() > requested.max_json_bytes {
                return Err(ProofCheckError::ResourceLimit);
            }
            let proof_v4 =
                self.proof
                    .encode_with_resource_control(requested, deadline, &mut |w, b| {
                        control.charge(w, b).is_ok()
                    })?;
            let output = input
                .len()
                .checked_add(proof_v4.len())
                .ok_or(ProofCheckError::ResourceLimit)?;
            if output > requested.max_json_bytes {
                return Err(ProofCheckError::ResourceLimit);
            }
            control.charge(
                input.len(),
                input
                    .len()
                    .checked_add(std::mem::size_of::<NativeQueryDiagnosticDocument>())
                    .ok_or(ProofCheckError::ResourceLimit)?,
            )?;
            let mut input_json = String::new();
            input_json
                .try_reserve_exact(input.len())
                .map_err(|_| ProofCheckError::ResourceLimit)?;
            input_json.push_str(input);
            if !self.binding.is_current(solver, control)? {
                return Ok(None);
            }
            Ok(Some(NativeQueryDiagnosticDocument {
                input_json,
                proof_v4,
            }))
        })
    }

    /// Independently decode/rebuild and strictly replay an untrusted v4 proof,
    /// then compare its full original typed source to this still-live actual
    /// issued query. The exact input bytes must match the independently held
    /// input owner. Both checks, context comparisons and decoder allocations
    /// use the same caller callback and deadline; no solve/search is performed.
    ///
    /// This initial reader deliberately requires the original live query and
    /// exact arena ids. It does not claim fresh-process nominal alpha-rebinding
    /// or grant authority to serialized ids, source hashes or source spelling.
    /// It never changes public result/proof/model admission.
    pub fn recheck_diagnostic_document_against_live_query_with_resource_control(
        &self,
        solver: &Solver,
        input_json: &str,
        proof_v4: &[u8],
        requested: RetainedProofTransportLimits,
        deadline: Instant,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Option<BundleReCheck>, ProofCheckError> {
        let mut original =
            |w, b| Instant::now() < deadline && progress(w, b) && Instant::now() < deadline;
        Control::new(&mut original).run_retained(|control| {
            let Some(expected_input) = self.issued_input_json() else {
                return Ok(None);
            };
            if !self.binding.is_current(solver, control)? {
                return Ok(None);
            }
            let output = input_json
                .len()
                .checked_add(proof_v4.len())
                .ok_or(ProofCheckError::ResourceLimit)?;
            if output > requested.max_json_bytes {
                return Err(ProofCheckError::ResourceLimit);
            }
            control.charge(
                input_json
                    .len()
                    .checked_add(expected_input.len())
                    .ok_or(ProofCheckError::ResourceLimit)?,
                0,
            )?;
            if input_json != expected_input {
                return Ok(None);
            }
            let (proof, first) = read_retained_proof_bundle_with_resource_control(
                proof_v4,
                requested,
                deadline,
                &mut |w, b| control.charge(w, b).is_ok(),
            )?;
            if !first.quality.is_complete()
                || first.assume_terms.is_empty()
                || !control.all_ids_in(&first.assume_terms, self.binding.source.roots())?
            {
                return Ok(None);
            }
            let checked = proof.with_checked_source_view_with_resource_control(
                deadline,
                &mut |w, b| control.charge(w, b).is_ok(),
                |view, checked, progress| {
                    if !checked.quality.is_complete()
                        || checked.assume_terms.is_empty()
                        || !self.binding.source.matches_retained_source_with_progress(
                            &solver.executor,
                            &view,
                            progress,
                        )?
                    {
                        return Ok(None);
                    }
                    Ok(Some(checked))
                },
            )?;
            if !self.binding.is_current(solver, control)? {
                return Ok(None);
            }
            Ok(checked)
        })
    }
}
