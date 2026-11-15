// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole-document emission, not proof or external-query authentication.
//!
//! Two deterministic passes count before allocating the output owner. The
//! inventory remains a fixed-size borrowed view, not a second encoded buffer.
//! Every source value passes through the serializer adapter, so long strings
//! are priced BEFORE serde scans them. Actual JSON nesting is bounded before
//! recursive serialization descends. Input destruction and an individual
//! accepted string scan remain opaque; neither stack/RSS nor hard latency is
//! certified by these logical work and owner charges.

use super::*;
use crate::bundle::SerializableProofBundle;
use ay_core::{ProofStep, Sort, TermData, TermId};
use std::cell::RefCell;
use std::io::{self, Write};

#[derive(Serialize)]
struct Document<'a> {
    schema: &'static str,
    steps: &'a [ProofStep],
    term_entries: &'a [(TermData, Sort)],
    true_term: Option<TermId>,
    false_term: Option<TermId>,
    var_counter: u32,
    obligation_assertions: &'a [TermId],
    datatype_declarations: &'a [(String, Vec<String>)],
    constructor_selectors: &'a [(String, Vec<String>)],
    datatype_member_signatures: &'a [crate::DatatypeMemberSignature],
    declared_function_identities: &'a [String],
    #[serde(skip_serializing_if = "Option::is_none")]
    retained: Option<&'a view::Inventory<'a>>,
}

/// Encode a borrowed v5 snapshot with an explicit retained-field state.
#[cfg(test)]
pub(super) fn write(
    bundle: &SerializableProofBundle,
    field: &RetainedField,
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    control: &mut Control<'_>,
) -> Result<Vec<u8>, TransportError> {
    control.charge(bundle.schema.len(), 0)?;
    if bundle.schema != SNAPSHOT_SCHEMA {
        return control.fail(TransportError::Presence(PresenceError::UnsupportedSchema));
    }
    let schema = if field.is_absent() {
        SNAPSHOT_SCHEMA
    } else {
        RETAINED_SCHEMA
    };
    let inventory = prepare_inventory(field, wire, deadline, control)?;
    write_snapshot(bundle, schema, inventory.as_ref(), limits, control)
}

/// Re-emit an actual owning v6 document without normalizing its schema or
/// detaching its mandatory inventory. Borrowing these parts grants no proof
/// authority and does not create another payload owner.
pub(super) fn write_versioned(
    envelope: &RetainedBundle,
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    control: &mut Control<'_>,
) -> Result<Vec<u8>, TransportError> {
    let (bundle, entries) = envelope.parts();
    control.charge(bundle.schema.len(), 0)?;
    if bundle.schema != RETAINED_SCHEMA {
        return control.fail(TransportError::Presence(PresenceError::UnsupportedSchema));
    }
    let inventory = prepare_entries(entries, wire, deadline, control)?;
    write_snapshot(bundle, RETAINED_SCHEMA, Some(&inventory), limits, control)
}

fn write_snapshot(
    bundle: &SerializableProofBundle,
    schema: &'static str,
    inventory: Option<&view::Inventory<'_>>,
    limits: &BundleLimits,
    control: &mut Control<'_>,
) -> Result<Vec<u8>, TransportError> {
    let document = Document {
        schema,
        steps: &bundle.steps,
        term_entries: &bundle.term_entries,
        true_term: bundle.true_term,
        false_term: bundle.false_term,
        var_counter: bundle.var_counter,
        obligation_assertions: &bundle.obligation_assertions,
        datatype_declarations: &bundle.datatype_declarations,
        constructor_selectors: &bundle.constructor_selectors,
        datatype_member_signatures: &bundle.datatype_member_signatures,
        declared_function_identities: &bundle.declared_function_identities,
        retained: inventory,
    };
    let output = emit(&document, limits.max_json_bytes, control)?;
    control.charge(0, 0)?;
    control.usage.returned_owned_bytes = output.capacity();
    Ok(output)
}

#[cfg(test)]
fn prepare_inventory<'a>(
    field: &'a RetainedField,
    wire: &WireLimits,
    deadline: Instant,
    control: &mut Control<'_>,
) -> Result<Option<view::Inventory<'a>>, TransportError> {
    let RetainedField::Present(entries) = field else {
        return Ok(None);
    };
    prepare_entries(entries, wire, deadline, control).map(Some)
}

fn prepare_entries<'a>(
    entries: &'a [RetainedStepPayload],
    wire: &WireLimits,
    deadline: Instant,
    control: &mut Control<'_>,
) -> Result<view::Inventory<'a>, TransportError> {
    // Inventory/source parsing obeys the wire's local ceilings AND this same
    // outer ledger. Framing/emission belongs to the complete document's
    // ceilings. A locally refused reservation creates no refundable credit.
    let admitted = control::run(
        deadline,
        &mut |work, bytes| control.charge(work, bytes).is_ok(),
        |inner| {
            inner.constrain(wire.max_work, wire.max_storage_bytes)?;
            encode::prepare(entries, wire, inner)
        },
    );
    admitted.result
}

fn emit(
    document: &Document<'_>,
    maximum: usize,
    control: &mut Control<'_>,
) -> Result<Vec<u8>, TransportError> {
    // Includes fixed short serde/io diagnostics on refusal. Successful JSON
    // serialization uses borrowed source and stack numeric formatting buffers.
    lexical::parser_reservation(control)?;
    let shared = RefCell::new(control);
    let guarded = serialization::Guarded {
        value: document,
        control: &shared,
        max_string_bytes: maximum,
    };
    let length = {
        let mut counter = Sink {
            output: None,
            length: 0,
            maximum,
            depth: Depth::default(),
            control: &shared,
        };
        let result = serde_json::to_writer(&mut counter, &guarded);
        map_result(result, &mut shared.borrow_mut())?;
        counter.depth.finish(&mut shared.borrow_mut())?;
        counter.length
    };
    let mut output = shared.borrow_mut().vector::<u8>(length)?;
    {
        let mut writer = Sink {
            output: Some(&mut output),
            length: 0,
            maximum: length,
            depth: Depth::default(),
            control: &shared,
        };
        let result = serde_json::to_writer(&mut writer, &guarded);
        map_result(result, &mut shared.borrow_mut())?;
        writer.depth.finish(&mut shared.borrow_mut())?;
        if writer.length != length {
            return shared
                .borrow_mut()
                .fail(TransportError::InvalidShape("output census differs"));
        }
    }
    shared.borrow_mut().charge(0, 0)?;
    Ok(output)
}

fn map_result(
    result: Result<(), serde_json::Error>,
    control: &mut Control<'_>,
) -> Result<(), TransportError> {
    match result {
        Ok(()) => control.charge(0, 0),
        Err(error) => {
            drop(error);
            // A serializer or writer refusal has already latched its actual
            // cause. Control::fail preserves it instead of laundering it.
            control.fail(TransportError::InvalidJson)
        }
    }
}

struct Sink<'a, 'b, 'c> {
    output: Option<&'a mut Vec<u8>>,
    length: usize,
    maximum: usize,
    depth: Depth,
    control: &'a RefCell<&'b mut Control<'c>>,
}

impl Write for Sink<'_, '_, '_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        for chunk in bytes.chunks(lexical::WINDOW) {
            let mut control = self.control.borrow_mut();
            // Byte emission/copy and the depth scan are separate work.
            control.charge(chunk.len() * 2, 0).map_err(io_error)?;
            let length = control.add(self.length, chunk.len()).map_err(io_error)?;
            control
                .cap("bundle JSON bytes", length, self.maximum)
                .map_err(io_error)?;
            self.depth.admit(chunk, &mut control).map_err(io_error)?;
            if let Some(output) = &mut self.output {
                // The census allocated the full capacity before this pass.
                // Never allow a Vec growth/reallocation to escape admission.
                control
                    .cap("output capacity", length, output.capacity())
                    .map_err(io_error)?;
                output.extend_from_slice(chunk);
            }
            self.length = length;
        }
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        self.control.borrow_mut().charge(0, 0).map_err(io_error)
    }
}

fn io_error(_: TransportError) -> io::Error {
    // No dynamically formatted payload: diagnostics are covered by the fixed
    // reservation before serialization. The original error stays in Control.
    io::Error::from(io::ErrorKind::Other)
}

#[derive(Default)]
struct Depth {
    quoted: bool,
    escaped: bool,
    level: usize,
}

impl Depth {
    fn admit(&mut self, bytes: &[u8], control: &mut Control<'_>) -> Result<(), TransportError> {
        for &byte in bytes {
            if self.quoted {
                if byte == b'"' && !self.escaped {
                    self.quoted = false;
                }
                self.escaped = byte == b'\\' && !self.escaped;
            } else {
                match byte {
                    b'"' => {
                        self.quoted = true;
                        self.escaped = false;
                    }
                    b'{' | b'[' => {
                        self.level += 1; // At most OUTER_DEPTH before this byte.
                        control.cap("bundle JSON depth", self.level, lexical::OUTER_DEPTH)?;
                    }
                    b'}' | b']' if self.level > 0 => self.level -= 1,
                    b'}' | b']' => return control.fail(TransportError::InvalidJson),
                    _ => {}
                }
            }
        }
        Ok(())
    }

    fn finish(&self, control: &mut Control<'_>) -> Result<(), TransportError> {
        if self.quoted || self.level != 0 {
            control.fail(TransportError::InvalidJson)
        } else {
            control.charge(0, 0)
        }
    }
}

#[cfg(test)]
mod tests;
