// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl AffineAggregationCertificate {
    #[must_use]
    pub fn claim(&self) -> &AffineAggregationClaim {
        &self.claim
    }

    #[must_use]
    pub fn inner_proof(&self) -> &AffineAggregationInnerProof {
        &self.inner_proof
    }

    #[must_use]
    pub fn source_primal(&self) -> Option<&[BigRational]> {
        self.source_primal.as_deref()
    }

    pub fn verify(
        &self,
        source: &Model,
    ) -> Result<AffineAggregationVerification, AffineAggregationCertificateError> {
        if crate::cert_io::canonical_digest(source) != self.analysis.source_digest {
            return Err(AffineAggregationCertificateError::SourceDigest);
        }
        validate_analysis_caps(source, &self.analysis)?;
        validate_certificate_payload_caps(self, source.num_cols())?;
        let closure = threshold_free_propagation_box(source, &self.analysis.caps)?;
        validate_analysis_box(source, &closure, &self.analysis.bounds)?;
        let (reduced, post) = replay_analysis(source, &self.analysis)?;
        if crate::cert_io::canonical_digest(&reduced) != self.analysis.reduced_digest {
            return Err(AffineAggregationCertificateError::ReducedDigest);
        }
        if post.const_delta != self.analysis.objective_delta {
            return Err(AffineAggregationCertificateError::ObjectiveDelta);
        }

        let mut verification = AffineAggregationVerification {
            primal_verified: false,
            infeasibility_verified: false,
            optimality_verified: false,
        };
        match (&self.claim, &self.inner_proof) {
            (AffineAggregationClaim::Infeasible, AffineAggregationInnerProof::Farkas(cert)) => {
                cert.verify(&reduced)
                    .map_err(|_| AffineAggregationCertificateError::InnerProof)?;
                verification.infeasibility_verified = true;
            }
            (
                AffineAggregationClaim::Infeasible,
                AffineAggregationInnerProof::InfeasibilityTree(tree),
            ) => {
                tree.verify(&reduced)
                    .map_err(|_| AffineAggregationCertificateError::InnerProof)?;
                verification.infeasibility_verified = true;
            }
            (
                AffineAggregationClaim::Optimal { value },
                AffineAggregationInnerProof::Optimality(cert),
            ) => {
                cert.verify(&reduced)
                    .map_err(|_| AffineAggregationCertificateError::InnerProof)?;
                if !optimality_certificate_matches_model(cert, &reduced) {
                    return Err(AffineAggregationCertificateError::InnerProof);
                }
                if &cert.bound + reduced.obj_offset_exact() + &self.analysis.objective_delta
                    != *value
                {
                    return Err(AffineAggregationCertificateError::InnerProof);
                }
                verification.optimality_verified = true;
            }
            (_, AffineAggregationInnerProof::Unsupported) => {}
            _ => return Err(AffineAggregationCertificateError::InnerProof),
        }

        match (
            &self.claim,
            self.reduced_primal.as_deref(),
            self.source_primal.as_deref(),
        ) {
            (AffineAggregationClaim::Infeasible, None, None) => {}
            (
                AffineAggregationClaim::Feasible | AffineAggregationClaim::Optimal { .. },
                Some(reduced_point),
                Some(source_point),
            ) => {
                reduced
                    .check_point(reduced_point)
                    .map_err(|_| AffineAggregationCertificateError::Primal)?;
                source
                    .check_point(source_point)
                    .map_err(|_| AffineAggregationCertificateError::Primal)?;
                let widened = post
                    .widen(reduced_point, None, None)
                    .ok_or(AffineAggregationCertificateError::Primal)?;
                if widened != source_point
                    || source.objective_value_at(source_point)
                        != reduced.objective_value_at(reduced_point)
                            + &self.analysis.objective_delta
                {
                    return Err(AffineAggregationCertificateError::Primal);
                }
                if let AffineAggregationClaim::Optimal { value } = &self.claim {
                    if source.objective_value_at(source_point) != *value {
                        return Err(AffineAggregationCertificateError::Primal);
                    }
                }
                verification.primal_verified = true;
            }
            _ => return Err(AffineAggregationCertificateError::Primal),
        }
        Ok(verification)
    }
}

pub(super) fn optimality_certificate_matches_model(
    cert: &OptimalityCertificate,
    model: &Model,
) -> bool {
    if cert.sense != model.sense() {
        return false;
    }
    let mut named = vec![BigRational::zero(); model.num_cols()];
    for (column, coefficient) in &cert.objective {
        let Some(slot) = named.get_mut(*column as usize) else {
            return false;
        };
        *slot += coefficient;
    }
    (0..model.num_cols()).all(|column| {
        let handle = Col(column as u32);
        exact(model.obj_coeff(handle)).is_some_and(|coefficient| named[column] == coefficient)
    })
}

pub(crate) fn validate_certificate_payload_caps(
    certificate: &AffineAggregationCertificate,
    source_columns: usize,
) -> Result<(), AffineAggregationCertificateError> {
    validate_certificate_values(certificate, source_columns)?;
    validate_inner_proof_caps(&certificate.inner_proof, source_columns)
}

fn validate_certificate_values(
    certificate: &AffineAggregationCertificate,
    source_columns: usize,
) -> Result<(), AffineAggregationCertificateError> {
    let mut recovery_terms = 0usize;
    for recovery in certificate.analysis.steps.iter() {
        match recovery {
            AffineRecovery::Fixed { value, .. } => {
                if !rational_fits(value) {
                    return Err(AffineAggregationCertificateError::Caps);
                }
            }
            AffineRecovery::Equality {
                constant, terms, ..
            } => {
                recovery_terms = recovery_terms
                    .checked_add(terms.len())
                    .ok_or(AffineAggregationCertificateError::Caps)?;
                if terms.len() > MAX_ROW_TERMS
                    || recovery_terms > MAX_RECOVERY_TERMS
                    || !rational_fits(constant)
                    || terms
                        .iter()
                        .any(|(_, coefficient)| !rational_fits(coefficient))
                {
                    return Err(AffineAggregationCertificateError::Caps);
                }
            }
        }
    }
    if !rational_fits(&certificate.analysis.objective_delta)
        || certificate.analysis.bounds.iter().any(|bound| {
            bound
                .lower
                .as_ref()
                .is_some_and(|value| !rational_fits(value))
                || bound
                    .upper
                    .as_ref()
                    .is_some_and(|value| !rational_fits(value))
        })
        || certificate.reduced_primal.as_ref().is_some_and(|point| {
            point.len() > source_columns || point.iter().any(|value| !rational_fits(value))
        })
        || certificate.source_primal.as_ref().is_some_and(|point| {
            point.len() != source_columns || point.iter().any(|value| !rational_fits(value))
        })
        || matches!(
            &certificate.claim,
            AffineAggregationClaim::Optimal { value } if !rational_fits(value)
        )
    {
        return Err(AffineAggregationCertificateError::Caps);
    }
    Ok(())
}

fn validate_inner_proof_caps(
    proof: &AffineAggregationInnerProof,
    source_columns: usize,
) -> Result<(), AffineAggregationCertificateError> {
    match proof {
        AffineAggregationInnerProof::Unsupported => {}
        AffineAggregationInnerProof::Farkas(proof) => {
            if proof.multipliers.len() > MAX_AFFINE_PROOF_MULTIPLIERS
                || proof
                    .multipliers
                    .iter()
                    .any(|multiplier| !rational_fits(&multiplier.coeff))
            {
                return Err(AffineAggregationCertificateError::Caps);
            }
        }
        AffineAggregationInnerProof::Optimality(proof) => {
            if proof.objective.len() > source_columns
                || proof.multipliers.len() > MAX_AFFINE_PROOF_MULTIPLIERS
                || !rational_fits(&proof.bound)
                || proof
                    .objective
                    .iter()
                    .any(|(_, coefficient)| !rational_fits(coefficient))
                || proof
                    .multipliers
                    .iter()
                    .any(|multiplier| !rational_fits(&multiplier.coeff))
            {
                return Err(AffineAggregationCertificateError::Caps);
            }
        }
        AffineAggregationInnerProof::InfeasibilityTree(proof) => validate_tree_caps(proof)?,
    }
    Ok(())
}

fn validate_tree_caps(
    proof: &MilpInfeasibilityCertificate,
) -> Result<(), AffineAggregationCertificateError> {
    let mut stack = vec![(&proof.root, 0usize)];
    let mut nodes = 0usize;
    let mut multipliers = 0usize;
    while let Some((node, depth)) = stack.pop() {
        nodes = nodes
            .checked_add(1)
            .ok_or(AffineAggregationCertificateError::Caps)?;
        if nodes > MAX_AFFINE_TREE_NODES || depth > MAX_AFFINE_TREE_DEPTH {
            return Err(AffineAggregationCertificateError::Caps);
        }
        match node {
            crate::tree_cert::TreeNode::Split { cut, lo, hi, .. } => {
                if !rational_fits(cut) {
                    return Err(AffineAggregationCertificateError::Caps);
                }
                let child_depth = depth
                    .checked_add(1)
                    .ok_or(AffineAggregationCertificateError::Caps)?;
                stack.push((hi, child_depth));
                stack.push((lo, child_depth));
            }
            crate::tree_cert::TreeNode::Leaf { farkas } => {
                multipliers = multipliers
                    .checked_add(farkas.multipliers.len())
                    .ok_or(AffineAggregationCertificateError::Caps)?;
                if multipliers > MAX_AFFINE_PROOF_MULTIPLIERS
                    || farkas
                        .multipliers
                        .iter()
                        .any(|multiplier| !rational_fits(&multiplier.coeff))
                {
                    return Err(AffineAggregationCertificateError::Caps);
                }
            }
        }
    }
    Ok(())
}

pub(super) fn planned_certificate_bytes(
    outcome: &Outcome,
    source_columns: usize,
    reduced_columns: usize,
) -> Option<usize> {
    let mut bytes = 0usize;
    match outcome {
        Outcome::Optimal { cert, .. } => {
            checked_charge(
                &mut bytes,
                source_columns.checked_add(reduced_columns)?,
                ESTIMATED_BYTES_PER_EXACT_VALUE,
            )?;
            if let Some(cert) = cert {
                if cert.objective.len() > source_columns
                    || cert.multipliers.len() > MAX_AFFINE_PROOF_MULTIPLIERS
                {
                    return None;
                }
                checked_charge(
                    &mut bytes,
                    cert.objective.len(),
                    ESTIMATED_BYTES_PER_EXACT_TERM,
                )?;
                checked_charge(
                    &mut bytes,
                    cert.multipliers.len(),
                    ESTIMATED_PROOF_MULTIPLIER_BYTES,
                )?;
            }
        }
        Outcome::Feasible { .. } => checked_charge(
            &mut bytes,
            source_columns.checked_add(reduced_columns)?,
            ESTIMATED_BYTES_PER_EXACT_VALUE,
        )?,
        Outcome::Infeasible { cert, tree_cert } => {
            if let Some(cert) = cert {
                if cert.multipliers.len() > MAX_AFFINE_PROOF_MULTIPLIERS {
                    return None;
                }
                checked_charge(
                    &mut bytes,
                    cert.multipliers.len(),
                    ESTIMATED_PROOF_MULTIPLIER_BYTES,
                )?;
            } else if let Some(tree) = tree_cert {
                let mut stack = vec![(&tree.root, 0usize)];
                let mut nodes = 0usize;
                let mut multipliers = 0usize;
                while let Some((node, depth)) = stack.pop() {
                    nodes = nodes.checked_add(1)?;
                    if nodes > MAX_AFFINE_TREE_NODES || depth > MAX_AFFINE_TREE_DEPTH {
                        return None;
                    }
                    match node {
                        crate::tree_cert::TreeNode::Split { lo, hi, .. } => {
                            let child_depth = depth.checked_add(1)?;
                            stack.push((hi, child_depth));
                            stack.push((lo, child_depth));
                        }
                        crate::tree_cert::TreeNode::Leaf { farkas } => {
                            multipliers = multipliers.checked_add(farkas.multipliers.len())?;
                        }
                    }
                }
                if multipliers > MAX_AFFINE_PROOF_MULTIPLIERS {
                    return None;
                }
                checked_charge(&mut bytes, nodes, ESTIMATED_PROOF_TREE_NODE_BYTES)?;
                checked_charge(&mut bytes, multipliers, ESTIMATED_PROOF_MULTIPLIER_BYTES)?;
            }
        }
        _ => return None,
    }
    // Vec/Arc headers, allocator rounding, and bigint limb growth.
    bytes.checked_mul(2)
}
