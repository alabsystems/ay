// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sort-shape validation before recursive cloning, hashing or equality.

use std::collections::BTreeSet;
use std::mem::size_of;

use super::*;

#[cfg(test)]
mod tests;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

fn add(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_add(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

fn mul(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_mul(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

fn charge(progress: Progress<'_>, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(ProofCheckError::ResourceLimit)
    }
}

fn invalid(
    role: &str,
    progress: Progress<'_>,
    diagnostic: impl FnOnce() -> String,
) -> Result<(), ProofCheckError> {
    // Every diagnostic below contains one borrowed role plus fixed text and
    // at most three bounded scalar fields, never a recursively displayed sort.
    let bound = mul(add(role.len(), 256)?, 4)?;
    charge(progress, bound, bound)?;
    Err(malformed_bundle(diagnostic()))
}

fn insert_name<'a>(
    names: &mut BTreeSet<&'a str>,
    name: &'a str,
    progress: Progress<'_>,
) -> Result<bool, ProofCheckError> {
    let levels = add(names.len().bit_width() as usize, 1)?;
    let comparisons = add(names.len(), 1)?.min(mul(levels, 12)?);
    charge(progress, mul(comparisons, add(name.len(), 1)?)?, 0)?;
    // alloc's B=6 tree has 11 keys/12 edges. One sibling per visited level
    // plus a new root bounds splits, node allocation and key/edge movement.
    let slots = mul(add(levels, 1)?, 32)?;
    charge(
        progress,
        slots,
        mul(slots, add(size_of::<&str>(), size_of::<usize>())?)?,
    )?;
    Ok(names.insert(name))
}

pub(super) fn validate_sort_with_progress(
    sort: &Sort,
    node_index: usize,
    role: &str,
    depth: usize,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    charge(progress, 2, 0)?;
    if depth > MAX_BUNDLE_SORT_DEPTH {
        return invalid(role, progress, || {
            format!("term t{node_index} {role} exceeds the maximum sort nesting depth")
        });
    }
    match sort {
        Sort::Bool
        | Sort::Int
        | Sort::Real
        | Sort::Complex
        | Sort::FiniteField(_)
        | Sort::String
        | Sort::RegLan
        | Sort::Char => {}
        Sort::BitVec(bitvec) => {
            if !(1..=MAX_BUNDLE_BITVECTOR_WIDTH).contains(&bitvec.width) {
                return invalid(role, progress, || {
                    format!(
                        "term t{node_index} {role} has invalid bit-vector width {}",
                        bitvec.width
                    )
                });
            }
        }
        Sort::Array(array) => {
            validate_sort_with_progress(
                &array.index_sort,
                node_index,
                "array index sort",
                depth + 1,
                progress,
            )?;
            validate_sort_with_progress(
                &array.element_sort,
                node_index,
                "array element sort",
                depth + 1,
                progress,
            )?;
        }
        Sort::FloatingPoint(exponent, significand) => {
            if !(2..=MAX_BUNDLE_FP_EXPONENT_WIDTH).contains(exponent)
                || !(2..=MAX_BUNDLE_FP_SIGNIFICAND_WIDTH).contains(significand)
            {
                return invalid(role, progress, || {
                    format!("term t{node_index} {role} has invalid floating-point format ({exponent}, {significand})")
                });
            }
        }
        Sort::Uninterpreted(name) | Sort::TypeVar(name) => {
            charge(progress, add(name.len(), 1)?, 0)?;
        }
        Sort::Datatype(datatype) => {
            validate_datatype(datatype, node_index, role, depth, progress)?;
        }
        Sort::Seq(element) => {
            validate_sort_with_progress(
                element,
                node_index,
                "sequence element sort",
                depth + 1,
                progress,
            )?;
        }
        Sort::FiniteDomain(name, size) => {
            charge(progress, add(name.len(), 1)?, 0)?;
            if *size == 0 {
                return invalid(role, progress, || {
                    format!("term t{node_index} {role} has a zero-cardinality finite-domain sort")
                });
            }
        }
        _ => {
            return invalid(role, progress, || {
                format!("term t{node_index} {role} uses an unsupported sort variant")
            })
        }
    }
    charge(progress, 0, 0)
}

/// Refuses an empty constructor set, a duplicate constructor name in the
/// datatype or field name in a constructor, and a field sort that
/// `validate_sort_with_progress` refuses. Names are raw symbol text, so an
/// empty name (the SMT-LIB symbol `||`) is admitted like any other.
fn validate_datatype(
    datatype: &ay_core::DatatypeSort,
    node_index: usize,
    role: &str,
    depth: usize,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    charge(progress, add(datatype.name.len(), 1)?, 0)?;
    if datatype.constructors.is_empty() {
        return invalid(role, progress, || {
            format!("term t{node_index} {role} has an empty constructor set")
        });
    }
    let mut constructors = BTreeSet::new();
    for constructor in &datatype.constructors {
        charge(progress, add(constructor.name.len(), 1)?, 0)?;
        if !insert_name(&mut constructors, &constructor.name, progress)? {
            return invalid(role, progress, || {
                format!("term t{node_index} {role} has a duplicate datatype constructor")
            });
        }
        let mut fields = BTreeSet::new();
        for field in &constructor.fields {
            charge(progress, add(field.name.len(), 1)?, 0)?;
            if !insert_name(&mut fields, &field.name, progress)? {
                return invalid(role, progress, || {
                    format!("term t{node_index} {role} has a duplicate datatype field")
                });
            }
            validate_sort_with_progress(
                &field.sort,
                node_index,
                "datatype field sort",
                depth + 1,
                progress,
            )?;
        }
    }
    Ok(())
}
