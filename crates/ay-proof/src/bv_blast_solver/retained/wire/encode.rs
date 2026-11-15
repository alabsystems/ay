// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use control::Item;
use std::io::{self, Write};

pub(super) fn write(
    payload: &RetainedBvRefutation,
    control: &mut Control<'_>,
) -> Result<Vec<u8>, WireError> {
    let length = census(payload, control)?;
    shape::validate(payload, control)?;
    control.cap(
        "JSON bytes",
        length as u128,
        control.limits.max_json_bytes as u128,
    )?;
    // Opaque serializer/I/O-error allowance, not an allocator-exact guarantee.
    control.retain(lexical::OPAQUE_BYTES)?;
    control.charge(lexical::OPAQUE_BYTES)?;
    let borrowed_and_scratch = control.storage;
    control.retain(size_of::<Vec<u8>>())?;
    let mut output = Vec::new();
    control.reserve(&mut output, length)?;
    let result = {
        let mut writer = Output {
            output: &mut output,
            length,
            control,
        };
        serde_json::to_writer(&mut writer, payload)
    };
    if let Err(error) = result {
        drop(error);
        return Err(control.serde_error());
    }
    if output.len() != length {
        return control.fail(WireError::InvalidPayload("JSON size mismatch"));
    }
    control.poll()?;
    control.usage.returned_owned_bytes = control.storage - borrowed_and_scratch;
    Ok(output)
}

/// Count canonical JSON before allocating any output. Caller-owned payload
/// capacities coexist with output, including unused but still owned capacity.
fn census(payload: &RetainedBvRefutation, control: &mut Control<'_>) -> Result<usize, WireError> {
    control.charge(1)?;
    control.cap(
        "rows",
        payload.rows.len() as u128,
        control.limits.max_rows as u128,
    )?;
    control.retain(size_of::<RetainedBvRefutation>())?;
    let rows = control.product(payload.rows.capacity(), size_of::<RetainedRupRow>())?;
    control.retain(rows)?;
    let mut length =
        b"{\"version\":".len() + digits(u64::from(payload.version)) + b",\"rows\":[".len();
    for (index, row) in payload.rows.iter().enumerate() {
        control.item(Item::Row)?;
        let literals = control.product(row.literals.capacity(), size_of::<u32>())?;
        let hints = control.product(row.hints.capacity(), size_of::<u64>())?;
        control.retain(literals)?;
        control.retain(hints)?;
        length = control.add(
            length,
            usize::from(index != 0) + b"{\"id\":".len() + digits(row.id) + b",\"literals\":[".len(),
        )?;
        let literal_len = numbers(
            row.literals.iter().copied().map(u64::from),
            Item::Literal,
            control,
        )?;
        length = control.add(length, literal_len)?;
        length = control.add(length, b"],\"hints\":[".len())?;
        let hint_len = numbers(row.hints.iter().copied(), Item::Hint, control)?;
        length = control.add(length, hint_len)?;
        length = control.add(length, b"]}".len())?;
    }
    control.add(
        length,
        b"],\"empty_clause_id\":".len() + digits(payload.empty_clause_id) + 1,
    )
}

fn numbers(
    values: impl Iterator<Item = u64>,
    item: Item,
    control: &mut Control<'_>,
) -> Result<usize, WireError> {
    let mut length = 0;
    for (index, value) in values.enumerate() {
        control.item(item)?;
        length = control.add(length, digits(value) + usize::from(index != 0))?;
    }
    Ok(length)
}

fn digits(mut value: u64) -> usize {
    let mut length = 1;
    while value >= 10 {
        value /= 10;
        length += 1;
    }
    length
}

struct Output<'a, 'p> {
    output: &'a mut Vec<u8>,
    length: usize,
    control: &'a mut Control<'p>,
}

impl Write for Output<'_, '_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let refused = |_| io::Error::from(io::ErrorKind::Other);
        self.control.charge(bytes.len()).map_err(refused)?;
        let length = self
            .control
            .add(self.output.len(), bytes.len())
            .map_err(refused)?;
        self.control
            .cap("JSON bytes", length as u128, self.length as u128)
            .map_err(refused)?;
        // reserve_exact's admitted actual capacity is the only buffer owner.
        if length > self.output.capacity() {
            self.control
                .fail::<()>(WireError::Allocation)
                .map_err(refused)?;
        }
        self.output.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        self.control
            .poll()
            .map_err(|_| io::Error::from(io::ErrorKind::Other))
    }
}
