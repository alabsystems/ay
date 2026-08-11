// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Volume census for live proof vectors copied through trust surgery.

use ay_core::{LiaAnnotation, Proof, ProofStep};

use super::Volume;

pub(super) fn spend_original_proof(volume: &mut Volume, proof: &Proof, live: &[bool]) -> bool {
    if proof.steps.len() != live.len() {
        return false;
    }
    for (index, step) in proof.steps.iter().enumerate() {
        if !live[index] {
            continue;
        }
        let ok = match step {
            ProofStep::Assume(_) => volume.spend(1),
            ProofStep::Step {
                clause,
                premises,
                args,
                ..
            } => {
                volume.clause(clause.len())
                    && volume.spend(premises.len())
                    && volume.spend(args.len())
            }
            ProofStep::Resolution { clause, .. } => volume.clause(clause.len()),
            ProofStep::TheoryLemma {
                theory,
                clause,
                farkas,
                lia,
                ..
            } => {
                volume.clause(clause.len())
                    && volume.spend(theory.len())
                    && farkas
                        .as_ref()
                        .is_none_or(|certificate| volume.spend(certificate.coefficients.len()))
                    && lia.as_ref().is_none_or(|annotation| match annotation {
                        LiaAnnotation::CuttingPlane(cut) => {
                            volume.spend(cut.farkas.coefficients.len())
                        }
                        _ => true,
                    })
            }
            ProofStep::Anchor { .. } => false,
            _ => false,
        };
        if !ok {
            return false;
        }
    }
    true
}
