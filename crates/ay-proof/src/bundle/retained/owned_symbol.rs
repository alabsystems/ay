// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Controlled Symbol decoding with explicit admission of the shared name copy.
//!
//! SymName is currently constructed through infallible Arc<str> APIs. The
//! pinned Trust allocator requests the Arc header plus the decoded string,
//! while the temporary String is still live. Account both owners; do not treat
//! SymName::capacity (text length only) as the hidden allocation's capacity.
//! The Arc copy is prepaid and post-polled, not recoverable allocator failure,
//! observed capacity, an RSS guarantee or a hard cancellation-latency bound.

use super::owned_values::{owned_string, tagged, tuple, u32_value, vector, RawSlice};
use super::{Control, TransportError};
use ay_core::Symbol;
use std::{alloc::Layout, sync::atomic::AtomicUsize};

pub(super) fn read(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<Symbol, TransportError> {
    control.charge(1, 0)?;
    let tag = tagged(raw, &["Named", "Indexed"], control)?;
    let payload = required(tag.payload, control)?;
    let symbol = match tag.index {
        0 => {
            let name = owned_string(payload, control)?;
            shared_name(&name, control)?;
            Symbol::named(name)
        }
        1 => {
            let [name, indices] = tuple(payload, control)?;
            let name = owned_string(required(name, control)?, control)?;
            let indices = required(indices, control)?;
            let indices = vector(indices, indices.as_str().len(), control, u32_value)?;
            shared_name(&name, control)?;
            Symbol::indexed(name, indices)
        }
        _ => return control.fail(TransportError::InvalidShape("unsupported Symbol variant")),
    };
    // Public constructors consumed/dropped the temporary String after copying
    // it into Arc. Its earlier reservation stays consumed; there is no refund.
    control.charge(0, 0)?;
    Ok(symbol)
}

fn required<'a>(
    field: Option<RawSlice<'a>>,
    control: &mut Control<'_>,
) -> Result<RawSlice<'a>, TransportError> {
    field
        .ok_or(TransportError::InvalidShape(
            "missing required Symbol payload",
        ))
        .or_else(|error| control.fail(error))
}

fn shared_name(name: &str, control: &mut Control<'_>) -> Result<(), TransportError> {
    // Trust 5f8066 alloc::sync::ArcInner has repr(C), two AtomicUsize counts
    // followed by the str data. arcinner_layout_for_value_layout uses exactly
    // this extend+pad construction. Empty names still require the header.
    let payload = Layout::array::<u8>(name.len())
        .map_err(|_| TransportError::Overflow)
        .or_else(|error| control.fail(error))?;
    let (layout, _) = Layout::new::<[AtomicUsize; 2]>()
        .extend(payload)
        .map_err(|_| TransportError::Overflow)
        .or_else(|error| control.fail(error))?;
    control.charge(name.len(), layout.pad_to_align().size())
}

#[cfg(test)]
mod tests;
