// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Metered structural checks only: a well-shaped proof is not a valid proof.

use super::*;

mod meter;
mod safety;
mod sos;
#[cfg(test)]
mod tests;

use meter::ProofMeter;

#[cfg(test)]
pub(super) fn validate_proof_snapshot(
    steps: &[ProofStep],
    entries: &[(TermData, Sort)],
) -> Result<(), ProofCheckError> {
    validate_proof_snapshot_with_progress(steps, entries, &mut |_, _| true)
}

pub(super) fn validate_proof_snapshot_with_progress(
    steps: &[ProofStep],
    entries: &[(TermData, Sort)],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut meter = ProofMeter::new(progress);
    meter.charge(0, 0)?;
    if steps.len() > u32::MAX as usize {
        return meter.invalid(
            0,
            "proof contains too many steps, exceeding ProofId capacity",
        );
    }
    for (step_index, step) in steps.iter().enumerate() {
        meter.charge(1, 0)?;
        validate_step(step, steps.len(), entries, step_index, &mut meter)?;
    }
    meter.charge(0, 0)
}

fn validate_step(
    step: &ProofStep,
    step_count: usize,
    entries: &[(TermData, Sort)],
    index: usize,
    meter: &mut ProofMeter<'_>,
) -> Result<(), ProofCheckError> {
    match step {
        ProofStep::Assume(term) => {
            meter.boolean(entries, *term, index, "assumption")?;
        }
        ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        } => {
            meter.clause(entries, clause, index, "resolution clause")?;
            meter.boolean(entries, *pivot, index, "resolution pivot")?;
            validate_premise(*clause1, index, step_count, meter)?;
            validate_premise(*clause2, index, step_count, meter)?;
        }
        ProofStep::TheoryLemma { clause, kind, .. } => {
            meter.clause(entries, clause, index, "theory clause")?;
            safety::validate(entries, index, clause, kind, meter)?;
        }
        ProofStep::NraSos {
            clause,
            certificate,
        } => {
            sos::validate(entries, index, clause, certificate, meter)?;
        }
        ProofStep::FiniteFieldLinear {
            clause,
            multipliers,
        } => {
            meter.clause(entries, clause, index, "finite-field linear clause")?;
            if clause.is_empty()
                || clause.len() != multipliers.len()
                || u32::try_from(clause.len()).is_err()
            {
                return Err(ProofCheckError::ResourceLimit);
            }
            for _ in multipliers {
                meter.charge(1, 0)?;
            }
        }
        ProofStep::Step {
            clause,
            premises,
            args,
            ..
        } => {
            meter.clause(entries, clause, index, "conclusion clause")?;
            for &premise in premises {
                validate_premise(premise, index, step_count, meter)?;
            }
            for &arg in args {
                meter.term(entries, arg, index, "argument")?;
            }
        }
        ProofStep::Anchor {
            end_step,
            variables,
        } => {
            if end_step.0 as usize >= step_count {
                return meter.invalid(index, "proof anchor references missing end step");
            }
            // These owning sorts must be validated before replay copies steps.
            // Delegate the actual recursive walk, never a guessed phase price.
            for (_, sort) in variables {
                meter.charge(1, 0)?;
                validate_sort_with_progress(
                    sort,
                    index,
                    "proof anchor binding sort",
                    0,
                    meter.progress,
                )?;
            }
        }
        _ => return meter.invalid(index, "uses an unsupported proof-step variant"),
    }
    Ok(())
}

fn validate_premise(
    premise: ProofId,
    step_index: usize,
    step_count: usize,
    meter: &mut ProofMeter<'_>,
) -> Result<(), ProofCheckError> {
    meter.charge(1, 0)?;
    if premise.0 as usize >= step_count {
        return meter.invalid(step_index, "premise references missing proof step");
    }
    if premise.0 as usize >= step_index {
        return meter.invalid(step_index, "premise references non-prior proof step");
    }
    Ok(())
}
