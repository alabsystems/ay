// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
#[cfg(test)]
use std::io::{self, Write};

/// Admit borrowed payload views without copying an inventory-sized buffer.
/// The caller separately controls any subsequent JSON emission and ownership.
pub(super) fn prepare<'a>(
    entries: &'a [RetainedStepPayload],
    wire: &WireLimits,
    control: &mut Control<'_>,
) -> Result<view::Inventory<'a>, TransportError> {
    control.cap(
        "retained entries",
        entries.len(),
        MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF,
    )?;
    lexical::parser_reservation(control)?;
    let mut view = view::Inventory::empty();
    for (index, entry) in entries.iter().enumerate() {
        control.cap(
            "source payload capacity",
            entry.payload.capacity(),
            wire.max_storage_bytes,
        )?;
        lexical::admit(&entry.payload, wire, lexical::Container::Payload, control)?;
        let parsed = serde_json::from_slice::<&RawValue>(&entry.payload).map_err(|error| {
            drop(error);
            TransportError::InvalidJson
        });
        control.charge(0, 0)?;
        let payload = parsed?;
        if !matches!(payload.get().as_bytes().first(), Some(b'{' | b'[')) {
            return control.fail(TransportError::InvalidShape(
                "payload must be an object or array",
            ));
        }
        view.entries[index] = Some(view::Entry {
            step: entry.step,
            payload,
        });
        view.len += 1;
    }
    Ok(view)
}

#[cfg(test)]
pub(super) fn write(
    entries: &[RetainedStepPayload],
    wire: &WireLimits,
    control: &mut Control<'_>,
) -> Result<Vec<u8>, TransportError> {
    let view = prepare(entries, wire, control)?;
    let maximum = lexical::inventory_cap(wire, control)?;
    let (result, length) = {
        let mut writer = Counter {
            length: 0,
            maximum,
            control,
        };
        let result = serde_json::to_writer(&mut writer, &view);
        (result, writer.length)
    };
    map_serde(result, control)?;
    let mut output = control.vector::<u8>(length)?;
    let result = {
        let mut writer = Output {
            output: &mut output,
            length,
            control,
        };
        serde_json::to_writer(&mut writer, &view)
    };
    map_serde(result, control)?;
    if output.len() != length {
        return control.fail(TransportError::InvalidShape("output census differs"));
    }
    control.usage.returned_owned_bytes = output.capacity();
    Ok(output)
}

#[cfg(test)]
fn map_serde(
    result: Result<(), serde_json::Error>,
    control: &mut Control<'_>,
) -> Result<(), TransportError> {
    match result {
        Ok(()) => control.charge(0, 0),
        Err(error) => {
            drop(error);
            control.fail(TransportError::InvalidJson)
        }
    }
}

#[cfg(test)]
fn io_error(_: TransportError) -> io::Error {
    io::Error::other("retained transport refused")
}

#[cfg(test)]
struct Counter<'a, 'b> {
    length: usize,
    maximum: usize,
    control: &'a mut Control<'b>,
}
#[cfg(test)]
impl Write for Counter<'_, '_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        for chunk in bytes.chunks(lexical::WINDOW) {
            self.control.charge(chunk.len(), 0).map_err(io_error)?;
            self.length = self
                .control
                .add(self.length, chunk.len())
                .map_err(io_error)?;
            self.control
                .cap("inventory JSON bytes", self.length, self.maximum)
                .map_err(io_error)?;
        }
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
struct Output<'a, 'b> {
    output: &'a mut Vec<u8>,
    length: usize,
    control: &'a mut Control<'b>,
}
#[cfg(test)]
impl Write for Output<'_, '_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        for chunk in bytes.chunks(lexical::WINDOW) {
            self.control.charge(chunk.len(), 0).map_err(io_error)?;
            let length = self
                .control
                .add(self.output.len(), chunk.len())
                .map_err(io_error)?;
            self.control
                .cap("output census", length, self.length)
                .map_err(io_error)?;
            self.output.extend_from_slice(chunk);
        }
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
