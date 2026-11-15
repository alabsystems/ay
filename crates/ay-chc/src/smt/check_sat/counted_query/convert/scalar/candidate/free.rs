// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private total witnesses, never a sampled model or a proof credential.
//! A default is a choice for a FREE variable's unconstrained cells. Every
//! observed cell is retained and the original DAG is replayed independently.

use super::*;
use ay_arrays::counted_reads::{ScalarSort, Unresolved};

mod decode;
#[cfg(test)]
mod tests;
mod validate;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ReadValue {
    pub(super) index: ScalarValue,
    pub(super) value: ScalarValue,
}

struct Array {
    term: TermId,
    index: ScalarSort,
    element: ScalarSort,
    default: ScalarValue,
    cells: Vec<ReadValue>,
}

pub(super) struct Model {
    arrays: Vec<Array>,
    pub(super) reads: Vec<ReadValue>,
}

impl Array {
    fn empty(term: TermId, index: ScalarSort, element: ScalarSort) -> Self {
        Self {
            term,
            index,
            element,
            default: zero(element),
            cells: Vec::new(),
        }
    }
}

impl Model {
    pub(super) fn empty() -> Self {
        Self {
            arrays: Vec::new(),
            reads: Vec::new(),
        }
    }

    pub(super) fn decode(encoding: &ScalarEncoding<'_, '_>, assignment: &[bool]) -> Result<Self> {
        if !encoding.context.census().has_arrays {
            return Ok(Self::empty());
        }
        decode::model(encoding, assignment)
    }

    pub(super) fn validate(&self, encoding: &ScalarEncoding<'_, '_>) -> Result<()> {
        validate::model(self, encoding)
    }

    pub(super) fn observations(&self) -> &[ReadValue] {
        &self.reads
    }

    pub(super) fn array_index(&self, term: TermId, owner: &CountedAdmission) -> Result<usize> {
        for (index, array) in self.arrays.iter().enumerate() {
            owner.admit(1, 0)?;
            if array.term == term {
                return Ok(index);
            }
        }
        Err(Error::InvalidCandidate)
    }

    pub(super) fn read(
        &self,
        array: usize,
        key: ScalarValue,
        owner: &CountedAdmission,
    ) -> Result<ScalarValue> {
        owner.admit(1, 0)?;
        let array = self.arrays.get(array).ok_or(Error::InvalidCandidate)?;
        if !value_has_sort(key, array.index) {
            return Err(Error::InvalidCandidate);
        }
        for cell in &array.cells {
            owner.admit(1, 0)?;
            if cell.index == key {
                return Ok(cell.value);
            }
        }
        Ok(array.default)
    }
}

pub(super) fn scalar_sort(sort: &ChcSort) -> Result<ScalarSort> {
    match sort {
        ChcSort::Bool => Ok(ScalarSort::Bool),
        ChcSort::BitVec(width) if (1..=128).contains(width) => Ok(ScalarSort::BitVec(*width)),
        _ => Err(Error::Unsupported),
    }
}

fn zero(sort: ScalarSort) -> ScalarValue {
    match sort {
        ScalarSort::Bool => ScalarValue::Bool(false),
        ScalarSort::BitVec(width) => ScalarValue::BitVec(0, width),
    }
}

fn value_has_sort(value: ScalarValue, sort: ScalarSort) -> bool {
    match (value, sort) {
        (ScalarValue::Bool(_), ScalarSort::Bool) => true,
        (ScalarValue::BitVec(value, actual), ScalarSort::BitVec(width)) => {
            actual == width && operations::canonical(value, width)
        }
        _ => false,
    }
}
