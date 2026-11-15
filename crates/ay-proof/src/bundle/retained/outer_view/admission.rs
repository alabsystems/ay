// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

// Every recognized top-level key and schema is ASCII and no longer than this
// key. Six encoded bytes per character admits even fully escaped spelling.
pub(super) const MAX_METADATA_BYTES: usize = b"declared_function_identities".len() * 6;
const PARSER_PASSES: usize = 16;

/// The prior depth pass bounds RawValue's scratch stack. This pass additionally
/// bounds escaped top-level keys/schema before any serde call. It does not cap
/// nested legacy strings: those remain raw and require later owned admission.
pub(super) fn metadata(bytes: &[u8], control: &mut Control<'_>) -> Result<(), TransportError> {
    let mut depth = 0_usize;
    let mut quoted = false;
    let mut escaped = false;
    let mut metadata_bytes = None;
    let mut started = false;
    for chunk in bytes.chunks(lexical::WINDOW) {
        // Pay for this scan and the subsequent opaque borrowed parse, including
        // its bounded top-level/schema diagnostics and error-position scans.
        // RawValue skips nested containers without nested owning serde visitors.
        let work = control.product(chunk.len(), PARSER_PASSES + 1)?;
        control.charge(work, 0)?;
        for &byte in chunk {
            if !started {
                if matches!(byte, b' ' | b'\n' | b'\r' | b'\t') {
                    continue;
                }
                if byte != b'{' {
                    return control.fail(TransportError::InvalidJson);
                }
                started = true;
            }
            if quoted {
                if byte == b'"' && !escaped {
                    quoted = false;
                    metadata_bytes = None;
                } else if let Some(count) = &mut metadata_bytes {
                    *count += 1;
                    if *count > MAX_METADATA_BYTES {
                        return control
                            .fail(TransportError::InvalidShape("outer metadata too long"));
                    }
                }
                escaped = byte == b'\\' && !escaped;
                continue;
            }
            match byte {
                b'"' => {
                    quoted = true;
                    escaped = false;
                    metadata_bytes = (depth == 1).then_some(0_usize);
                }
                b'{' | b'[' => depth += 1,
                b'}' | b']' if depth > 0 => depth -= 1,
                b'}' | b']' => return control.fail(TransportError::InvalidJson),
                _ => {}
            }
        }
    }
    if !started || quoted || depth != 0 {
        return control.fail(TransportError::InvalidJson);
    }
    Ok(())
}
