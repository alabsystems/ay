// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A sufficient, bounded identity check for already admitted variable sorts.
//!
//! It answers what `ChcSort`'s `Eq` answers (datatype lists are interned, so
//! their identity is a pointer comparison), but walks arrays iteratively and
//! charges the admission's work and depth envelope. Equal datatype names alone
//! are insufficient: a structurally different definition must reach the
//! collector even when its emitted outer signature looks identical.

use super::{bounded_add, ChcSort, DatatypeDeclarationError, WalkLimits, MAX_DT_NESTING_DEPTH};

pub(super) fn same_metadata_shape(
    left: &ChcSort,
    right: &ChcSort,
    work: &mut usize,
    name_bytes: &mut usize,
    limits: WalkLimits,
) -> Result<bool, DatatypeDeclarationError> {
    let mut stack = vec![(left, right, 0usize)];
    while let Some((left, right, depth)) = stack.pop() {
        if depth > MAX_DT_NESTING_DEPTH {
            return Err(DatatypeDeclarationError::ResourceLimit(
                "variable sort comparison depth",
            ));
        }
        charge(work, 1, limits)?;
        if std::ptr::eq(left, right) {
            continue;
        }
        match (left, right) {
            (ChcSort::Bool, ChcSort::Bool)
            | (ChcSort::Int, ChcSort::Int)
            | (ChcSort::Real, ChcSort::Real) => {}
            (ChcSort::BitVec(left), ChcSort::BitVec(right)) if left == right => {}
            (ChcSort::Array(left_key, left_value), ChcSort::Array(right_key, right_value)) => {
                stack.push((left_value.as_ref(), right_value.as_ref(), depth + 1));
                stack.push((left_key.as_ref(), right_key.as_ref(), depth + 1));
            }
            (
                ChcSort::Datatype {
                    name: left_name,
                    constructors: left_metadata,
                },
                ChcSort::Datatype {
                    name: right_name,
                    constructors: right_metadata,
                },
            ) => {
                if !crate::ChcDtConstructors::ptr_eq(left_metadata, right_metadata) {
                    return Ok(false);
                }
                charge_names(name_bytes, left_name.len().max(right_name.len()), limits)?;
                if left_name != right_name {
                    return Ok(false);
                }
            }
            (ChcSort::Uninterpreted(left), ChcSort::Uninterpreted(right)) => {
                charge_names(name_bytes, left.len().max(right.len()), limits)?;
                if left != right {
                    return Ok(false);
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn charge(
    work: &mut usize,
    amount: usize,
    limits: WalkLimits,
) -> Result<(), DatatypeDeclarationError> {
    *work = bounded_add(
        *work,
        amount,
        limits.compare_work,
        "variable sort comparison",
    )?;
    Ok(())
}

fn charge_names(
    bytes: &mut usize,
    amount: usize,
    limits: WalkLimits,
) -> Result<(), DatatypeDeclarationError> {
    // Preserve the existing shared name-byte envelope on cache hits. Long
    // datatype names must not newly consume the smaller node-work allowance.
    *bytes = bounded_add(*bytes, amount, limits.name_bytes, "datatype name bytes")?;
    Ok(())
}
