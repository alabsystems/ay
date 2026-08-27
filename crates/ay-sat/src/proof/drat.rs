// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DRAT proof writer for generating UNSAT certificates.

use super::{has_duplicate_literal, ToDimacs};
use crate::literal::Literal;
use std::io::{self, Write};

const DRAT_TEXT_LINE_INITIAL_CAPACITY: usize = 128;
const DRAT_TEXT_LINE_MAX_RETAINED_CAPACITY: usize = 256 * 1024;
const DRAT_TEXT_LIT_BYTES_ESTIMATE: usize = 12; // i32 DIMACS literal plus trailing space.

fn push_u64_decimal(buf: &mut Vec<u8>, mut value: u64) {
    if value == 0 {
        buf.push(b'0');
        return;
    }

    let mut digits = [0u8; 20];
    let mut len = 0;
    while value != 0 {
        digits[len] = b'0' + (value % 10) as u8;
        value /= 10;
        len += 1;
    }
    for digit in digits[..len].iter().rev() {
        buf.push(*digit);
    }
}

fn push_i32_decimal_field(buf: &mut Vec<u8>, value: i32) {
    if value < 0 {
        buf.push(b'-');
        push_u64_decimal(buf, (-i64::from(value)) as u64);
    } else {
        push_u64_decimal(buf, value as u64);
    }
    buf.push(b' ');
}

fn drat_text_clause_capacity_estimate(clause_len: usize, is_delete: bool) -> usize {
    let prefix = if is_delete { 2 } else { 0 };
    prefix + clause_len.saturating_mul(DRAT_TEXT_LIT_BYTES_ESTIMATE) + 2 // "0\n"
}

fn prepare_reusable_text_line(buf: &mut Vec<u8>, needed: usize) {
    debug_assert!(needed <= DRAT_TEXT_LINE_MAX_RETAINED_CAPACITY);

    if needed > buf.capacity() || buf.capacity() > DRAT_TEXT_LINE_MAX_RETAINED_CAPACITY {
        *buf = Vec::with_capacity(needed.max(DRAT_TEXT_LINE_INITIAL_CAPACITY));
    } else {
        buf.clear();
    }
}

fn write_drat_text_line<W: Write>(
    writer: &mut W,
    reusable_line: &mut Vec<u8>,
    needed: usize,
    build: impl FnOnce(&mut Vec<u8>),
) -> io::Result<()> {
    if needed <= DRAT_TEXT_LINE_MAX_RETAINED_CAPACITY {
        prepare_reusable_text_line(reusable_line, needed);
        build(reusable_line);
        writer.write_all(reusable_line)
    } else {
        let mut line = Vec::with_capacity(needed);
        build(&mut line);
        writer.write_all(&line)
    }
}

fn build_text_clause_line(buf: &mut Vec<u8>, clause: &[Literal], is_delete: bool) {
    if is_delete {
        buf.extend_from_slice(b"d ");
    }
    for lit in clause {
        push_i32_decimal_field(buf, lit.to_dimacs());
    }
    buf.extend_from_slice(b"0\n");
}

/// DRAT proof writer for generating UNSAT certificates
///
/// Tracks I/O errors internally (CaDiCaL-style): on first write failure,
/// `io_failed` is set and all subsequent writes become no-ops. Callers can
/// check `has_io_error()` at proof finalization to detect truncated proofs.
pub struct DratWriter<W: Write> {
    writer: W,
    binary: bool,
    /// Reusable buffer for text DRAT lines.
    text_line: Vec<u8>,
    /// Count of clauses successfully added (does not count failed writes)
    added_count: u64,
    /// Count of clauses successfully deleted (does not count failed writes)
    deleted_count: u64,
    /// Set on first I/O error; subsequent writes become no-ops
    io_failed: bool,
}

impl<W: Write> DratWriter<W> {
    /// Create a new DRAT writer with text format
    pub fn new_text(writer: W) -> Self {
        Self {
            writer,
            binary: false,
            text_line: Vec::with_capacity(DRAT_TEXT_LINE_INITIAL_CAPACITY),
            added_count: 0,
            deleted_count: 0,
            io_failed: false,
        }
    }

    /// Create a new DRAT writer with binary format
    pub fn new_binary(writer: W) -> Self {
        Self {
            writer,
            binary: true,
            text_line: Vec::new(),
            added_count: 0,
            deleted_count: 0,
            io_failed: false,
        }
    }

    /// Log addition of a learned clause
    ///
    /// After an I/O failure, subsequent calls are no-ops (CaDiCaL-style).
    /// The counter only increments on successful writes.
    pub fn add(&mut self, clause: &[Literal]) -> io::Result<()> {
        debug_assert!(
            !has_duplicate_literal(clause),
            "BUG: DRAT add contains duplicate literal in clause of length {}",
            clause.len()
        );
        if self.io_failed {
            return Ok(());
        }
        let result = if self.binary {
            self.write_binary_clause(clause, false)
        } else {
            self.write_text_clause(clause, false)
        };
        match result {
            Ok(()) => {
                self.added_count += 1;
                Ok(())
            }
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Log a caller-supplied propagation-redundancy step in DPR format.
    ///
    /// This public serializer establishes wire shape only: `witness` must begin
    /// with `clause[0]`, and the caller is responsible for supplying a valid PR
    /// witness. The resulting step requires an independent PR/LPR checker; the
    /// ordinary RUP/RAT checker cannot validate it.
    pub fn add_pr(&mut self, clause: &[Literal], witness: &[Literal]) -> io::Result<()> {
        debug_assert!(
            !clause.is_empty() && witness.first() == clause.first(),
            "BUG: DPR witness must begin by repeating the clause pivot clause[0]"
        );
        if self.io_failed {
            return Ok(());
        }
        let result = if self.binary {
            self.write_binary_pr(clause, witness)
        } else {
            self.write_text_pr(clause, witness)
        };
        match result {
            Ok(()) => {
                self.added_count += 1;
                Ok(())
            }
            Err(error) => {
                self.io_failed = true;
                Err(error)
            }
        }
    }

    /// Write a witnessed DRAT-family `a`-line in text format.
    fn write_text_pr(&mut self, clause: &[Literal], witness: &[Literal]) -> io::Result<()> {
        let needed = drat_text_clause_capacity_estimate(clause.len() + witness.len(), false);
        write_drat_text_line(&mut self.writer, &mut self.text_line, needed, |line| {
            for lit in clause {
                push_i32_decimal_field(line, lit.to_dimacs());
            }
            for lit in witness {
                push_i32_decimal_field(line, lit.to_dimacs());
            }
            line.extend_from_slice(b"0\n");
        })
    }

    /// Write a witnessed DRAT-family `a`-line in binary format.
    fn write_binary_pr(&mut self, clause: &[Literal], witness: &[Literal]) -> io::Result<()> {
        self.writer.write_all(b"a")?;
        for lit in clause {
            self.write_binary_lit(*lit)?;
        }
        for lit in witness {
            self.write_binary_lit(*lit)?;
        }
        self.writer.write_all(&[0])
    }

    /// Log addition of an SR (substitution-redundant) clause in DSR format
    /// (#8011 SR route).
    ///
    /// The DSR `a`-line is `clause… witness… 0`, where the `witness` is the
    /// substitution-witness token stream emitted by a family-specific symmetry
    /// construction. By the
    /// SR/DSR convention (see `dsr-trim`'s `parse_sr_clause_and_witness`), the
    /// witness begins by repeating the clause pivot `clause[0]`: the SECOND
    /// occurrence of the pivot opens the witness (PR part, pivot↦true), the THIRD
    /// occurrence acts as the separator that opens the literal↦literal substitution
    /// part. The writer is layout-agnostic and just appends `witness` after
    /// `clause`. Verified externally by `dsr-trim → drat/lsr → cake_lpr`; the
    /// internal RUP/RAT checker cannot verify it. After an I/O
    /// failure subsequent calls are no-ops (CaDiCaL-style).
    pub fn add_sr(&mut self, clause: &[Literal], witness: &[Literal]) -> io::Result<()> {
        debug_assert!(
            !clause.is_empty() && witness.first() == clause.first(),
            "BUG: SR/DSR witness must begin by repeating the clause pivot clause[0]"
        );
        if self.io_failed {
            return Ok(());
        }
        // The on-wire layout is identical to a DPR a-line (`clause… witness… 0`);
        // only the witness token stream is richer (carries the substitution part).
        let result = if self.binary {
            self.write_binary_pr(clause, witness)
        } else {
            self.write_text_pr(clause, witness)
        };
        match result {
            Ok(()) => {
                self.added_count += 1;
                Ok(())
            }
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Log deletion of a clause
    ///
    /// After an I/O failure, subsequent calls are no-ops (CaDiCaL-style).
    /// The counter only increments on successful writes.
    pub fn delete(&mut self, clause: &[Literal]) -> io::Result<()> {
        if self.io_failed {
            return Ok(());
        }
        let result = if self.binary {
            self.write_binary_clause(clause, true)
        } else {
            self.write_text_clause(clause, true)
        };
        match result {
            Ok(()) => {
                self.deleted_count += 1;
                Ok(())
            }
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Write clause in text format
    fn write_text_clause(&mut self, clause: &[Literal], is_delete: bool) -> io::Result<()> {
        let needed = drat_text_clause_capacity_estimate(clause.len(), is_delete);
        write_drat_text_line(&mut self.writer, &mut self.text_line, needed, |line| {
            build_text_clause_line(line, clause, is_delete)
        })
    }

    /// Write clause in binary format
    fn write_binary_clause(&mut self, clause: &[Literal], is_delete: bool) -> io::Result<()> {
        // Write marker byte
        self.writer
            .write_all(&[if is_delete { b'd' } else { b'a' }])?;

        // Write each literal in binary encoding
        for lit in clause {
            self.write_binary_lit(*lit)?;
        }

        // Write terminating 0
        self.writer.write_all(&[0])
    }

    /// Write a literal in binary (variable-length) encoding
    ///
    /// Binary literal encoding: positive lit v -> 2*(v+1), negative -> 2*(v+1)+1
    /// Then encoded as variable-length integer (LEB128-style).
    ///
    /// Uses checked arithmetic to prevent silent overflow for large variable
    /// indices (see #4474).
    fn write_binary_lit(&mut self, lit: Literal) -> io::Result<()> {
        let var = lit
            .variable()
            .0
            .checked_add(1) // 1-indexed
            .expect("BUG: variable index overflow in binary DRAT encoding");
        let encoded = var
            .checked_mul(2)
            .expect("BUG: literal encoding overflow in binary DRAT encoding")
            + u32::from(!lit.is_positive()); // +0 or +1; safe since 2*var is even

        // Variable-length encoding (similar to LEB128)
        let mut val = encoded;
        while val > 127 {
            self.writer.write_all(&[(val as u8 & 0x7f) | 0x80])?;
            val >>= 7;
        }
        self.writer.write_all(&[val as u8])
    }

    /// Get the number of clauses successfully added
    pub fn added_count(&self) -> u64 {
        self.added_count
    }

    /// Get the number of clauses successfully deleted
    pub fn deleted_count(&self) -> u64 {
        self.deleted_count
    }

    /// Returns true if any I/O error occurred during proof writing
    pub fn has_io_error(&self) -> bool {
        self.io_failed
    }

    #[cfg(test)]
    pub(crate) fn text_line_capacity_for_tests(&self) -> usize {
        self.text_line.capacity()
    }

    #[cfg(test)]
    pub(crate) const fn max_retained_text_line_capacity_for_tests() -> usize {
        DRAT_TEXT_LINE_MAX_RETAINED_CAPACITY
    }

    /// Flush the writer (no-op after I/O failure)
    pub fn flush(&mut self) -> io::Result<()> {
        if self.io_failed {
            return Ok(());
        }
        match self.writer.flush() {
            Ok(()) => Ok(()),
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Get the inner writer back
    ///
    /// Returns an error if an I/O failure occurred during proof writing,
    /// indicating the proof stream is truncated/corrupted.
    pub fn into_inner(self) -> io::Result<W> {
        if self.io_failed {
            return Err(io::Error::other(
                "DRAT proof writer encountered I/O error during solve",
            ));
        }
        Ok(self.writer)
    }
}
