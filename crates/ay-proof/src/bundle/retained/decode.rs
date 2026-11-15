// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn read(
    bytes: &[u8],
    wire: &WireLimits,
    control: &mut Control<'_>,
) -> Result<RetainedField, TransportError> {
    lexical::admit(bytes, wire, lexical::Container::Inventory, control)?;
    lexical::parser_reservation(control)?;
    let parsed = serde_json::from_slice::<view::Inventory<'_>>(bytes).map_err(|error| {
        drop(error);
        TransportError::InvalidJson
    });
    control.charge(0, 0)?;
    let view = parsed?;
    // Validate every borrowed payload before allocating any payload owner.
    for entry in view.entries.iter().take(view.len).flatten() {
        let bytes = entry.payload.get().as_bytes();
        control.cap("payload JSON bytes", bytes.len(), wire.max_json_bytes)?;
        if !matches!(bytes.first(), Some(b'{' | b'[')) {
            return control.fail(TransportError::InvalidShape(
                "payload must be an object or array",
            ));
        }
    }
    let mut entries = control.vector::<RetainedStepPayload>(view.len)?;
    let mut owner_bytes = control.product(entries.capacity(), size_of::<RetainedStepPayload>())?;
    for entry in view.entries.iter().take(view.len).flatten() {
        let payload = control.copied_bytes(entry.payload.get().as_bytes())?;
        owner_bytes = control.add(owner_bytes, payload.capacity())?;
        entries.push(RetainedStepPayload {
            step: entry.step,
            payload,
        });
    }
    control.usage.returned_owned_bytes = owner_bytes;
    Ok(RetainedField::Present(entries))
}
