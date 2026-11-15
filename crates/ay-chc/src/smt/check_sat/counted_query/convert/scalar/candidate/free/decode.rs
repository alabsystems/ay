// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn model(encoding: &ScalarEncoding<'_, '_>, assignment: &[bool]) -> Result<Model> {
    let owner = encoding.admission();
    let closure = encoding
        .array_read_obligations()
        .ok_or(Error::InvalidCandidate)?;
    let mut result = Model::empty();
    for binding in encoding.context.bindings() {
        owner.admit(1, 0)?;
        if let ChcSort::Array(index, element) = &binding.original.sort {
            let index = scalar_sort(index)?;
            let element = scalar_sort(element)?;
            memory::push(
                &mut result.arrays,
                Array::empty(binding.term, index, element),
                owner,
            )?;
        }
    }
    memory::reserve(&mut result.reads, closure.reads().len(), owner)?;
    for read in closure.reads() {
        owner.admit(1, 0)?;
        result.reads.push(ReadValue {
            index: decode_term(encoding, read.index, read.index_sort, assignment)?,
            value: decode_term(encoding, read.select, read.element_sort, assignment)?,
        });
    }
    for obligation in closure.unresolved() {
        owner.admit(1, 0)?;
        let Unresolved::FreeRead { read } = *obligation else {
            return Err(Error::Unsupported);
        };
        let source = closure.reads().get(read).ok_or(Error::InvalidCandidate)?;
        let cell = *result.reads.get(read).ok_or(Error::InvalidCandidate)?;
        let at = result.array_index(source.array, owner)?;
        let array = &mut result.arrays[at];
        if array.index != source.index_sort || array.element != source.element_sort {
            return Err(Error::InvalidCandidate);
        }
        insert(array, cell, owner)?;
    }
    result.validate(encoding)?;
    owner.check()?;
    Ok(result)
}

pub(super) fn insert(array: &mut Array, cell: ReadValue, owner: &CountedAdmission) -> Result<()> {
    owner.admit(1, 0)?;
    if !value_has_sort(cell.index, array.index) || !value_has_sort(cell.value, array.element) {
        return Err(Error::InvalidCandidate);
    }
    for existing in &array.cells {
        owner.admit(1, 0)?;
        if existing.index == cell.index {
            return if existing.value == cell.value {
                Ok(())
            } else {
                Err(Error::InvalidCandidate)
            };
        }
    }
    memory::push(&mut array.cells, cell, owner)
}
