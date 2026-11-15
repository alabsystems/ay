// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Metered structural proof-step equality, without copying or proof authority.

use super::*;
use ay_core::{FarkasAnnotation, LiaAnnotation};

impl SerializableProofBundle {
    /// Compare all serialized steps with the supplied proof, including unused
    /// steps and malformed metadata. This does not check proof validity or the
    /// proof's separate `named_steps` map; callers must authenticate those.
    ///
    /// Both complete owning payloads are priced before structural comparison.
    /// Copy-byte prices are added to work (checked), and zero bytes are charged.
    /// Rational coefficients compare by raw numerator AND denominator, not
    /// numeric equivalence. Identical malformed encodings can match without
    /// acquiring validity. No term store/seal is rebuilt or payload cloned.
    pub fn proof_steps_match_with_progress(
        &self,
        proof: &Proof,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<bool, ProofCheckError> {
        charge(progress, 1, 0)?;
        if self.steps.len() != proof.steps.len() {
            return Ok(false);
        }
        for (stored, supplied) in self.steps.iter().zip(&proof.steps) {
            charge(progress, 1, 0)?;
            let mut compare_progress = |work: usize, bytes: usize| {
                work.checked_add(bytes)
                    .is_some_and(|work| progress(work, 0))
            };
            payload::step(stored, &mut compare_progress)?;
            payload::step(supplied, &mut compare_progress)?;
            if !raw_step_eq(stored, supplied) {
                charge(progress, 0, 0)?;
                return Ok(false);
            }
        }
        charge(progress, 0, 0)?;
        Ok(true)
    }
}

fn raw_step_eq(left: &ProofStep, right: &ProofStep) -> bool {
    match (left, right) {
        (
            ProofStep::TheoryLemma {
                theory: lt,
                clause: lc,
                farkas: lf,
                kind: lk,
                lia: ll,
            },
            ProofStep::TheoryLemma {
                theory: rt,
                clause: rc,
                farkas: rf,
                kind: rk,
                lia: rl,
            },
        ) => {
            lt == rt
                && lc == rc
                && lk == rk
                && raw_farkas_eq(lf.as_ref(), rf.as_ref())
                && raw_lia_eq(ll.as_ref(), rl.as_ref())
        }
        // All other supported variants are structural: SOS uses explicit raw
        // BigInt pairs, not Ratio. Unknown future owning variants fail pricing.
        _ => left == right,
    }
}

fn raw_farkas_eq(left: Option<&FarkasAnnotation>, right: Option<&FarkasAnnotation>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => {
            left.coefficients.len() == right.coefficients.len()
                && left
                    .coefficients
                    .iter()
                    .zip(&right.coefficients)
                    .all(|(left, right)| {
                        left.numer() == right.numer() && left.denom() == right.denom()
                    })
        }
        (None, None) => true,
        _ => false,
    }
}

fn raw_lia_eq(left: Option<&LiaAnnotation>, right: Option<&LiaAnnotation>) -> bool {
    match (left, right) {
        (Some(LiaAnnotation::CuttingPlane(left)), Some(LiaAnnotation::CuttingPlane(right))) => {
            left.divisor == right.divisor && raw_farkas_eq(Some(&left.farkas), Some(&right.farkas))
        }
        (None, None)
        | (Some(LiaAnnotation::BoundsGap), Some(LiaAnnotation::BoundsGap))
        | (Some(LiaAnnotation::Divisibility), Some(LiaAnnotation::Divisibility))
        | (Some(LiaAnnotation::LinearIdentity), Some(LiaAnnotation::LinearIdentity)) => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests;
