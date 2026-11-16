// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Allocation-free conservative parser-storage census after lexical admission.

use ay_frontend::SExpr;

/// Includes parser vectors and iterative S-expression destruction scratch.
/// Bare bytes deliberately overcount tokens (juxtaposed tokens need not have
/// whitespace). Quoted payloads count once, and their owned bytes separately.
pub(super) fn allowance(text: &str) -> Option<(usize, usize)> {
    let bytes = text.as_bytes();
    let mut position = 0usize;
    let mut nodes = 1usize;
    let mut lines = 1usize;
    for byte in bytes {
        lines = lines.checked_add(usize::from(*byte == b'\n'))?;
    }
    while let Some(&byte) = bytes.get(position) {
        position += 1;
        match byte {
            b' ' | b'\t' | b'\r' | b'\n' => {}
            b';' => {
                while bytes
                    .get(position)
                    .is_some_and(|b| *b != b'\n' && *b != b'\r')
                {
                    position += 1;
                }
            }
            b'"' | b'|' => {
                nodes = nodes.checked_add(1)?;
                let start = position;
                position = quoted_end(bytes, position, byte)?;
                // SExpr erases quoting. Never reinterpret a quoted reserved
                // grammar word or indexed BV numeral as literal syntax.
                if byte == b'|' && reserved_syntax(bytes.get(start..position - 1)?) {
                    return None;
                }
            }
            _ => nodes = nodes.checked_add(1)?,
        }
    }
    // Multiple geometrically grown AST/parse/drop vectors, per-node slack,
    // decoded spelling copies, and the parser's error-only line-offset table.
    let node_bytes = size_of::<SExpr>()
        .checked_mul(4)?
        .checked_add(size_of::<Vec<SExpr>>().checked_mul(4)?)?
        .checked_add(64)?;
    let copy = nodes
        .checked_mul(node_bytes)?
        .checked_add(text.len().checked_mul(2)?)?
        .checked_add(lines.checked_mul(size_of::<usize>().checked_mul(2)?)?)?;
    let work = text.len().checked_mul(3)?.checked_add(nodes)?;
    Some((work, copy))
}

fn reserved_syntax(name: &[u8]) -> bool {
    matches!(
        name,
        b"_" | b"as" | b"!" | b"let" | b"forall" | b"exists" | b"match" | b"par"
    ) || name
        .strip_prefix(b"bv")
        .is_some_and(|digits| !digits.is_empty() && digits.iter().all(u8::is_ascii_digit))
}

fn quoted_end(bytes: &[u8], mut position: usize, delimiter: u8) -> Option<usize> {
    while let Some(&byte) = bytes.get(position) {
        position += 1;
        if delimiter == b'|' && byte == b'\\' {
            bytes.get(position)?;
            position += 1;
        } else if byte == delimiter {
            if delimiter == b'"' && bytes.get(position) == Some(&b'"') {
                position += 1;
            } else {
                return Some(position);
            }
        }
    }
    None
}
