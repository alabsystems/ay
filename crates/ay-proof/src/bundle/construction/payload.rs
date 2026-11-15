// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Price owning payloads without following term IDs or trusting the producer.

use ay_core::{AletheRule, LiaAnnotation, NraSosCertificate, NraSosRational};

use super::*;

fn slice<T>(values: &[T], progress: Progress<'_>) -> Result<(), ProofCheckError> {
    charge(
        progress,
        values.len(),
        product(values.len(), size_of::<T>())?,
    )
}

fn string(value: &str, progress: Progress<'_>) -> Result<(), ProofCheckError> {
    charge(progress, value.len(), value.len())
}

pub(super) fn sort(
    value: &Sort,
    progress: Progress<'_>,
    depth: usize,
) -> Result<(), ProofCheckError> {
    charge(progress, 1, 0)?;
    if depth > 256 {
        return Err(ProofCheckError::ResourceLimit);
    }
    match value {
        Sort::Array(array) => {
            charge(progress, 1, size_of::<ay_core::ArraySort>())?;
            sort(&array.index_sort, progress, depth + 1)?;
            sort(&array.element_sort, progress, depth + 1)
        }
        Sort::Seq(element) => {
            charge(progress, 1, size_of::<Sort>())?;
            sort(element, progress, depth + 1)
        }
        Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
            string(name, progress)
        }
        Sort::Datatype(datatype) => {
            string(&datatype.name, progress)?;
            slice(&datatype.constructors, progress)?;
            for constructor in &datatype.constructors {
                string(&constructor.name, progress)?;
                slice(&constructor.fields, progress)?;
                for field in &constructor.fields {
                    string(&field.name, progress)?;
                    sort(&field.sort, progress, depth + 1)?;
                }
            }
            Ok(())
        }
        Sort::Bool
        | Sort::Int
        | Sort::Real
        | Sort::BitVec(_)
        | Sort::String
        | Sort::RegLan
        | Sort::FloatingPoint(..)
        | Sort::FiniteField(_)
        | Sort::Char => Ok(()),
        _ => Err(ProofCheckError::ResourceLimit),
    }
}

pub(super) fn step(value: &ProofStep, progress: Progress<'_>) -> Result<(), ProofCheckError> {
    charge(progress, 1, 0)?;
    match value {
        ProofStep::Assume(_) => Ok(()),
        ProofStep::FiniteFieldLinear {
            clause,
            multipliers,
        } => {
            slice(clause, progress)?;
            slice(multipliers, progress)
        }
        ProofStep::Resolution { clause, .. } => slice(clause, progress),
        ProofStep::TheoryLemma {
            theory,
            clause,
            farkas,
            lia,
            ..
        } => {
            string(theory, progress)?;
            slice(clause, progress)?;
            if let Some(farkas) = farkas {
                slice(&farkas.coefficients, progress)?;
            }
            match lia {
                Some(LiaAnnotation::CuttingPlane(cut)) => slice(&cut.farkas.coefficients, progress),
                None
                | Some(
                    LiaAnnotation::BoundsGap
                    | LiaAnnotation::Divisibility
                    | LiaAnnotation::LinearIdentity,
                ) => Ok(()),
                _ => Err(ProofCheckError::ResourceLimit),
            }
        }
        ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } => {
            if let AletheRule::Custom(name) = rule {
                string(name, progress)?;
            }
            slice(clause, progress)?;
            slice(premises, progress)?;
            slice(args, progress)
        }
        ProofStep::Anchor { variables, .. } => {
            slice(variables, progress)?;
            for (name, variable_sort) in variables {
                string(name, progress)?;
                sort(variable_sort, progress, 0)?;
            }
            Ok(())
        }
        ProofStep::NraSos {
            clause,
            certificate,
        } => {
            slice(clause, progress)?;
            sos(certificate, progress)
        }
        _ => Err(ProofCheckError::ResourceLimit),
    }
}

fn sos(certificate: &NraSosCertificate, progress: Progress<'_>) -> Result<(), ProofCheckError> {
    // No algebraic/shape claim is made here. Even malformed programmatically
    // authored data is charged in full, or refused before it can be copied.
    slice(&certificate.basis, progress)?;
    for monomial in &certificate.basis {
        slice(monomial, progress)?;
    }
    slice(&certificate.gram, progress)?;
    for row in &certificate.gram {
        slice(row, progress)?;
        for value in row {
            rational(value, progress)?;
        }
    }
    slice(&certificate.terms, progress)?;
    for term in &certificate.terms {
        rational(&term.multiplier, progress)?;
    }
    rational(&certificate.rhs, progress)
}

fn rational(value: &NraSosRational, progress: Progress<'_>) -> Result<(), ProofCheckError> {
    for integer in [&value.numerator, &value.denominator] {
        let bits = usize::try_from(integer.bits()).map_err(|_| ProofCheckError::ResourceLimit)?;
        // BigInt clones whole base-2^32/64 limbs, not only significant bytes.
        // An additional limb conservatively covers an empty/small payload.
        let limbs = (bits / 64)
            .checked_add(1)
            .ok_or(ProofCheckError::ResourceLimit)?;
        charge(progress, limbs, product(limbs, 8)?)?;
    }
    Ok(())
}
