// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn model(model: &Model, encoding: &ScalarEncoding<'_, '_>) -> Result<()> {
    let owner = encoding.admission();
    owner.admit(1, 0)?;
    let mut position = 0;
    for binding in encoding.context.bindings() {
        owner.admit(1, 0)?;
        let ChcSort::Array(index, element) = &binding.original.sort else {
            continue;
        };
        let array = model.arrays.get(position).ok_or(Error::InvalidCandidate)?;
        position += 1;
        if array.term != binding.term
            || array.index != scalar_sort(index)?
            || array.element != scalar_sort(element)?
            || !value_has_sort(array.default, array.element)
        {
            return Err(Error::InvalidCandidate);
        }
        cells(array, owner)?;
    }
    if position != model.arrays.len() {
        return Err(Error::InvalidCandidate);
    }
    match encoding.array_read_obligations() {
        Some(closure) => {
            if model.reads.len() != closure.reads().len() {
                return Err(Error::InvalidCandidate);
            }
            for (read, value) in closure.reads().iter().zip(&model.reads) {
                owner.admit(1, 0)?;
                if !value_has_sort(value.index, read.index_sort)
                    || !value_has_sort(value.value, read.element_sort)
                {
                    return Err(Error::InvalidCandidate);
                }
            }
            for obligation in closure.unresolved() {
                owner.admit(1, 0)?;
                if matches!(obligation, Unresolved::ArrayRelation { .. }) {
                    return Err(Error::Unsupported);
                }
            }
        }
        None if !model.reads.is_empty() || !model.arrays.is_empty() => {
            return Err(Error::InvalidCandidate);
        }
        None => {}
    }
    owner.check()?;
    Ok(())
}

fn cells(array: &Array, owner: &CountedAdmission) -> Result<()> {
    for (position, cell) in array.cells.iter().enumerate() {
        owner.admit(1, 0)?;
        if !value_has_sort(cell.index, array.index) || !value_has_sort(cell.value, array.element) {
            return Err(Error::InvalidCandidate);
        }
        for earlier in &array.cells[..position] {
            owner.admit(1, 0)?;
            if earlier.index == cell.index {
                return Err(Error::InvalidCandidate);
            }
        }
    }
    Ok(())
}
