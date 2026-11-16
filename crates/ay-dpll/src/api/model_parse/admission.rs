// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Allocation-free lexical preflight, not an alternative SMT-LIB parser.
//! The frontend still checks token validity and escape semantics afterward.

pub(super) const MAX_BYTES: usize = 8 * 1024 * 1024;
pub(super) const MAX_NODES: usize = 131_072;
/// Lexical paren-nesting bound for the preflight scan.
///
/// NOT a call-stack bound. Nothing downstream recurses on this depth:
/// `parse_sexps` uses an explicit heap stack (its own `MAX_PARSE_DEPTH` is
/// 1,000,000 and guards memory, not the call stack), and the typed decoder
/// walks a `store` chain ITERATIVELY — its real recursion, into datatype and
/// sequence structure, is separately capped at `typed::MAX_DEPTH`. Total memory
/// is bounded by `MAX_NODES` and `MAX_BYTES` regardless of what this is.
///
/// It was 128, which is SHALLOWER THAN AY'S OWN OUTPUT for an ordinary sort. An
/// array model prints as a left-nested `(store (store … ) i v)` chain, so its
/// lexical depth is its entry count: a fully-expanded `(Array (_ BitVec 8) _)`
/// is 256 entries and ~258 deep. `(get-model)` printed it and the typed
/// extractor then refused to read it back, which cost the whole SAT verdict —
/// `try_get_model_map` turns a refusal into `ModelGenerationFailed`, and the
/// bridge reports that as `model extraction failed: …` instead of `sat` (trust
/// shape `ABVFP`). 4096 covers every byte-indexed array and the next few index
/// widths with room to spare, and stays far below what `MAX_NODES` admits.
pub(super) const MAX_DEPTH: usize = 4096;

pub(super) struct Admission {
    bytes_left: usize,
    nodes_left: usize,
}

impl Admission {
    pub(super) fn new() -> Self {
        Self {
            bytes_left: MAX_BYTES,
            nodes_left: MAX_NODES,
        }
    }

    pub(super) fn admit(&mut self, text: &str) -> Option<()> {
        self.bytes_left = self.bytes_left.checked_sub(text.len())?;
        let bytes = text.as_bytes();
        let mut offset = 0;
        let mut depth = 0usize;
        while let Some(&byte) = bytes.get(offset) {
            match byte {
                b' ' | b'\t' | b'\r' | b'\n' => offset += 1,
                b';' => {
                    while bytes
                        .get(offset)
                        .is_some_and(|b| !matches!(b, b'\n' | b'\r'))
                    {
                        offset += 1;
                    }
                }
                b')' => {
                    depth = depth.checked_sub(1)?;
                    offset += 1;
                }
                _ => {
                    self.nodes_left = self.nodes_left.checked_sub(1)?;
                    offset += 1;
                    match byte {
                        b'(' => {
                            depth += 1;
                            if depth > MAX_DEPTH {
                                return None;
                            }
                        }
                        b'"' | b'|' => offset = quoted_end(bytes, offset, byte)?,
                        _ => {
                            // A delimiter-free run can contain several frontend
                            // tokens (`#b1#b0`, `:a:a`, digit/symbol boundaries).
                            // Charge every byte, an upper bound on its atoms;
                            // treating a whole run as one node undercounts it.
                            while bytes.get(offset).is_some_and(|b| {
                                !matches!(
                                    b,
                                    b' ' | b'\t' | b'\r' | b'\n' | b'(' | b')' | b';' | b'"' | b'|'
                                )
                            }) {
                                self.nodes_left = self.nodes_left.checked_sub(1)?;
                                offset += 1;
                            }
                        }
                    }
                }
            }
        }
        (depth == 0).then_some(())
    }
}

fn quoted_end(bytes: &[u8], mut offset: usize, delimiter: u8) -> Option<usize> {
    while let Some(&byte) = bytes.get(offset) {
        offset += 1;
        if delimiter == b'|' && byte == b'\\' {
            // Match the frontend lexer's quoted-symbol escape token boundary.
            bytes.get(offset)?;
            offset += 1;
        } else if byte == delimiter {
            if delimiter == b'"' && bytes.get(offset) == Some(&b'"') {
                offset += 1;
            } else {
                return Some(offset);
            }
        }
    }
    None
}
