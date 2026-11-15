// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed candidate decoding and original-DAG replay, never a public SAT result.

use super::*;
use crate::{ChcOp, ChcSort};

mod arrays;
mod free;
mod operations;
mod replay;
#[cfg(test)]
mod tests;

/// Cannot be constructed with a foreign numeric model/term mapping.
/// Scalar values retain their source binding order, including same-name/
/// different-sort variables. Arrays retain separate total typed witnesses.
/// No name-only public model projection is performed.
pub(in crate::smt::check_sat) struct ScalarCandidate<'encoding, 'scope, 'source> {
    encoding: &'encoding ScalarEncoding<'scope, 'source>,
    values: Vec<ScalarValue>,
    arrays: free::Model,
}

impl ScalarCandidate<'_, '_, '_> {
    pub(in crate::smt::check_sat) fn values(&self) -> &[ScalarValue] {
        &self.values
    }
}

impl<'scope, 'source> ScalarEncoding<'scope, 'source> {
    /// Check actual attached clauses, decode their original typed variables,
    /// then independently evaluate the original source. No SAT search occurs.
    /// The returned candidate borrows this exact encoding, not just its size.
    pub(in crate::smt::check_sat) fn check_scalar_candidate(
        &self,
        assignment: &[bool],
    ) -> Result<ScalarCandidate<'_, 'scope, 'source>> {
        let owner = self.admission();
        let result = owner.with_work(|_| Ok(check(self, assignment)));
        owner.check()?;
        result?
    }

    /// Re-check identity and source truth; numeric equality of two namespaces
    /// is insufficient. Primarily useful at later internal handoff boundaries.
    pub(in crate::smt::check_sat) fn replay_scalar_candidate(
        &self,
        candidate: &ScalarCandidate<'_, '_, '_>,
    ) -> Result<()> {
        let owner = self.admission();
        let result = owner.with_work(|_| {
            Ok((|| {
                owner.admit(1, 0)?;
                if std::ptr::eq(self, candidate.encoding) {
                    replay::original(self, &candidate.values, &candidate.arrays)
                } else {
                    Err(Error::InvalidCandidate)
                }
            })())
        });
        owner.check()?;
        result?
    }
}

fn check<'encoding, 'scope, 'source>(
    encoding: &'encoding ScalarEncoding<'scope, 'source>,
    assignment: &[bool],
) -> Result<ScalarCandidate<'encoding, 'scope, 'source>> {
    let owner = encoding.admission();
    owner.admit(1, 0)?;
    if encoding.context.census().max_bitvector_width > 128 {
        return Err(Error::Unsupported);
    }
    if assignment.len() != encoding.num_vars as usize {
        return Err(Error::InvalidCandidate);
    }
    // Check every row and literal, including satisfied-row tails.
    for row in &encoding.rows {
        owner.admit(1, 0)?;
        let mut satisfied = false;
        for &literal in &row.literals {
            owner.admit(1, 0)?;
            satisfied |= assigned(assignment, literal)?;
        }
        if !satisfied {
            return Err(Error::InvalidCandidate);
        }
    }
    let mut values = Vec::new();
    memory::reserve(&mut values, encoding.context.bindings().len(), owner)?;
    for binding in encoding.context.bindings() {
        owner.admit(1, 0)?;
        if !matches!(&binding.original.sort, ChcSort::Array(..)) {
            values.push(decode(encoding, binding, assignment)?);
        }
    }
    let arrays = free::Model::decode(encoding, assignment)?;
    replay::original(encoding, &values, &arrays)?;
    Ok(ScalarCandidate {
        encoding,
        values,
        arrays,
    })
}

fn decode(
    encoding: &ScalarEncoding<'_, '_>,
    binding: &Binding<'_>,
    assignment: &[bool],
) -> Result<ScalarValue> {
    decode_term(
        encoding,
        binding.term,
        free::scalar_sort(&binding.original.sort)?,
        assignment,
    )
}

fn decode_term(
    encoding: &ScalarEncoding<'_, '_>,
    term: TermId,
    sort: ay_arrays::counted_reads::ScalarSort,
    assignment: &[bool],
) -> Result<ScalarValue> {
    use ay_arrays::counted_reads::ScalarSort;
    let value = match sort {
        ScalarSort::Bool => {
            let bit = encoding.bv.literal(term).map_err(bv_error)?;
            ScalarValue::Bool(assigned(
                assignment,
                attachment::shifted(bit, encoding.offset)?,
            )?)
        }
        ScalarSort::BitVec(width) if (1..=128).contains(&width) => {
            let bits = encoding.bv.bits(term).map_err(bv_error)?;
            if bits.len() != width as usize {
                return Err(Error::InvalidCandidate);
            }
            let mut value = 0u128;
            for (index, &bit) in bits.iter().enumerate() {
                encoding.admission().admit(1, 0)?;
                if assigned(assignment, attachment::shifted(bit, encoding.offset)?)? {
                    value |= 1u128 << index;
                }
            }
            ScalarValue::BitVec(value, width)
        }
        _ => return Err(Error::Unsupported),
    };
    Ok(value)
}

fn assigned(assignment: &[bool], literal: i32) -> Result<bool> {
    let index = literal
        .checked_abs()
        .filter(|id| *id != 0)
        .ok_or(Error::InvalidCandidate)?;
    let value = assignment
        .get(index as usize - 1)
        .copied()
        .ok_or(Error::InvalidCandidate)?;
    Ok(value == (literal > 0))
}
