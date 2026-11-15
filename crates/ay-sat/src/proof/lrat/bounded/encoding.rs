// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Byte-identical LRAT encoding with checks between fields and sink writes.

use super::*;

fn encoding_overflow() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidInput,
        "value overflow in bounded binary LRAT encoding",
    )
}

impl<W: Write> LratWriter<W> {
    pub(super) fn write_all_controlled(
        &mut self,
        mut bytes: &[u8],
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        while !bytes.is_empty() {
            self.poll_bounded_emission(keep_going)?;
            match self.writer.write(bytes) {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::WriteZero,
                        "failed to write whole buffer",
                    ))
                }
                Ok(written) => bytes = &bytes[written..],
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) => return Err(error),
            }
        }
        Ok(())
    }

    pub(super) fn write_varint_controlled(
        &mut self,
        mut value: u64,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        while value > 127 {
            self.write_all_controlled(&[(value as u8 & 0x7f) | 0x80], keep_going)?;
            value >>= 7;
        }
        self.write_all_controlled(&[value as u8], keep_going)
    }

    pub(super) fn write_bounded_add(
        &mut self,
        id: u64,
        clause: &[Literal],
        hints: Hints<'_>,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        if self.binary {
            self.write_all_controlled(b"a", keep_going)?;
            let encoded = id.checked_mul(2).ok_or_else(encoding_overflow)?;
            self.write_varint_controlled(encoded, keep_going)?;
            for &literal in clause {
                self.poll_bounded_emission(keep_going)?;
                let variable = literal
                    .variable()
                    .0
                    .checked_add(1)
                    .ok_or_else(encoding_overflow)?;
                let encoded = variable.checked_mul(2).ok_or_else(encoding_overflow)?
                    + u32::from(!literal.is_positive());
                self.write_varint_controlled(u64::from(encoded), keep_going)?;
            }
            self.write_all_controlled(&[0], keep_going)?;
            match hints {
                Hints::Unsigned(hints) => {
                    for &hint in hints {
                        self.poll_bounded_emission(keep_going)?;
                        let encoded = hint.checked_mul(2).ok_or_else(encoding_overflow)?;
                        self.write_varint_controlled(encoded, keep_going)?;
                    }
                }
                Hints::Signed(hints) => {
                    for &hint in hints {
                        self.poll_bounded_emission(keep_going)?;
                        if hint == 0 {
                            return Err(io::Error::new(
                                io::ErrorKind::InvalidInput,
                                "zero signed hint in bounded binary LRAT encoding",
                            ));
                        }
                        let mut encoded = hint
                            .unsigned_abs()
                            .checked_mul(2)
                            .ok_or_else(encoding_overflow)?;
                        if hint < 0 {
                            encoded = encoded.checked_add(1).ok_or_else(encoding_overflow)?;
                        }
                        self.write_varint_controlled(encoded, keep_going)?;
                    }
                }
            }
            self.write_all_controlled(&[0], keep_going)?;
        } else {
            self.write_bounded_add_text(id, clause, hints, keep_going)?;
        }
        self.poll_bounded_emission(keep_going)
    }

    fn controlled_text_line(&mut self, needed: usize) -> Vec<u8> {
        if needed <= LRAT_TEXT_LINE_MAX_RETAINED_CAPACITY {
            let mut line = std::mem::take(&mut self.text_line);
            prepare_reusable_text_line(&mut line, needed);
            line
        } else {
            Vec::with_capacity(needed)
        }
    }

    fn finish_controlled_text_line(
        &mut self,
        line: Vec<u8>,
        needed: usize,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        self.write_all_controlled(&line, keep_going)?;
        if needed <= LRAT_TEXT_LINE_MAX_RETAINED_CAPACITY {
            self.text_line = line;
        }
        Ok(())
    }

    fn write_bounded_add_text(
        &mut self,
        id: u64,
        clause: &[Literal],
        hints: Hints<'_>,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        self.poll_bounded_emission(keep_going)?;
        let hint_len = match &hints {
            Hints::Unsigned(hints) => hints.len(),
            Hints::Signed(hints) => hints.len(),
        };
        let needed = lrat_text_add_capacity_estimate(clause.len(), hint_len);
        let mut line = self.controlled_text_line(needed);
        push_u64_decimal_field(&mut line, id);
        for &literal in clause {
            self.poll_bounded_emission(keep_going)?;
            push_i32_decimal_field(&mut line, literal.to_dimacs());
        }
        line.extend_from_slice(b"0 ");
        match hints {
            Hints::Unsigned(hints) => {
                for &hint in hints {
                    self.poll_bounded_emission(keep_going)?;
                    push_u64_decimal_field(&mut line, hint);
                }
            }
            Hints::Signed(hints) => {
                for &hint in hints {
                    self.poll_bounded_emission(keep_going)?;
                    push_i64_decimal_field(&mut line, hint);
                }
            }
        }
        line.extend_from_slice(b"0\n");
        self.finish_controlled_text_line(line, needed, keep_going)
    }

    pub(super) fn write_bounded_delete_text(
        &mut self,
        id: u64,
        deletions: &[u64],
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<()> {
        self.poll_bounded_emission(keep_going)?;
        let needed = lrat_text_delete_capacity_estimate(deletions.len());
        let mut line = self.controlled_text_line(needed);
        push_u64_decimal_field(&mut line, id);
        line.extend_from_slice(b"d ");
        for &deletion in deletions {
            self.poll_bounded_emission(keep_going)?;
            push_u64_decimal_field(&mut line, deletion);
        }
        line.extend_from_slice(b"0\n");
        self.finish_controlled_text_line(line, needed, keep_going)
    }
}
