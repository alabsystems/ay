// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use std::io::{Cursor, Error, Seek, SeekFrom, Write};

struct Fragmented<'a> {
    bytes: &'a [u8],
    interrupted: usize,
    calls: usize,
}
impl Read for Fragmented<'_> {
    fn read(&mut self, out: &mut [u8]) -> std::io::Result<usize> {
        self.calls += 1;
        if self.interrupted > 0 {
            self.interrupted -= 1;
            return Err(ErrorKind::Interrupted.into());
        }
        if self.bytes.is_empty() {
            return Ok(0);
        }
        out[0] = self.bytes[0];
        self.bytes = &self.bytes[1..];
        Ok(1)
    }
}

#[test]
fn seven_maximum_host_width_fields_fit_and_keep_original_second_field() {
    let input = std::iter::repeat_n(usize::MAX.to_string(), 7)
        .collect::<Vec<_>>()
        .join(" ")
        + "\n";
    assert!(input.len() < CAPACITY);
    assert_eq!(read_resident_pages(&mut input.as_bytes()), Some(usize::MAX));
}

#[test]
fn fragmented_and_interrupted_reads_match_complete_input() {
    let input = b"123456 777 23 9 0 99 0\n";
    for interrupted in [0, 1, 7] {
        let mut reader = Fragmented {
            bytes: input,
            interrupted,
            calls: 0,
        };
        assert_eq!(read_resident_pages(&mut reader), Some(777));
        assert_eq!(reader.calls, input.len() + interrupted + 1);
    }
}

#[test]
fn repeated_interrupts_are_bounded_and_never_supply_a_measurement() {
    let mut reader = Fragmented {
        bytes: b"1 2\n",
        interrupted: usize::MAX,
        calls: 0,
    };
    assert_eq!(read_resident_pages(&mut reader), None);
    assert_eq!(reader.calls, MAX_READS);
}

#[test]
fn partial_second_field_followed_by_error_is_not_accepted() {
    struct Failed {
        prefix: Cursor<&'static [u8]>,
    }
    impl Read for Failed {
        fn read(&mut self, out: &mut [u8]) -> std::io::Result<usize> {
            let n = self.prefix.read(out)?;
            if n == 0 {
                Err(Error::from(ErrorKind::PermissionDenied))
            } else {
                Ok(n)
            }
        }
    }
    let mut reader = Failed {
        prefix: Cursor::new(b"12 345"),
    };
    assert_eq!(read_resident_pages(&mut reader), None);
}

#[test]
fn overlong_input_never_accepts_a_valid_prefix_or_truncated_resident_value() {
    let mut suffix = b"1 2 ".to_vec();
    suffix.resize(CAPACITY + 1, b' ');
    assert_eq!(read_resident_pages(&mut suffix.as_slice()), None);
    let mut resident = b"1 ".to_vec();
    resident.resize(CAPACITY + 1, b'7');
    assert_eq!(read_resident_pages(&mut resident.as_slice()), None);
}

#[test]
fn malformed_encoding_missing_field_and_integer_overflow_keep_zero_fallback() {
    for mut input in [b"".as_slice(), b"1", b"1 nope", b"1 -2", b"1 \xff"] {
        assert_eq!(read_resident_pages(&mut input), None);
    }
    let input = format!("1 {}0", usize::MAX);
    assert_eq!(read_resident_pages(&mut input.as_bytes()), None);
}

#[test]
fn complete_boundary_input_and_original_whitespace_grammar_are_retained() {
    let mut input = b"1 17".to_vec();
    input.resize(CAPACITY, b' ');
    assert_eq!(read_resident_pages(&mut input.as_slice()), Some(17));
    assert_eq!(
        read_resident_pages(&mut "\t1\u{2003}19\n".as_bytes()),
        Some(19)
    );
    assert_eq!(read_resident_pages(&mut b"ignored 21".as_slice()), Some(21));
}

#[test]
fn actual_file_reader_uses_the_same_bounded_parser() {
    let mut file = tempfile::tempfile().unwrap();
    file.write_all(b"100 33 20 0 0 7 0\n").unwrap();
    file.seek(SeekFrom::Start(0)).unwrap();
    assert_eq!(read_resident_pages(&mut file), Some(33));
    assert!(resident_pages().is_some_and(|pages| pages > 0));
}
