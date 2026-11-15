// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded-memory byte scanner for the authenticated corpus. It recognizes
//! exactly the same decision epochs as the original slice scanner; it is not
//! an SMT parser and does not grant solver or certificate acceptance.

use super::{CorpusQuery, EXPECTED_QUERY_COUNT};
use sha2::{Digest, Sha256};
use std::io::Read;

const BUFFER_BYTES: usize = 32 * 1024;
const MAX_DECISION_HEAD_BYTES: usize = b"check-sat-assuming".len();

#[derive(Debug)]
pub(super) struct ScannedFile {
    pub(super) size: u64,
    pub(super) sha256: String,
    pub(super) queries: Vec<CorpusQuery>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Lexical {
    Normal,
    Comment,
    String { quote_pending: bool },
    Quoted { escaped: bool },
}

struct HeadToken {
    prefix: [u8; MAX_DECISION_HEAD_BYTES],
    length: u64,
    utf8: [u8; 4],
    utf8_len: usize,
}

impl HeadToken {
    fn new() -> Self {
        Self {
            prefix: [0; MAX_DECISION_HEAD_BYTES],
            length: 0,
            utf8: [0; 4],
            utf8_len: 0,
        }
    }

    fn push(&mut self, byte: u8) -> Result<(), String> {
        if self.length < MAX_DECISION_HEAD_BYTES as u64 {
            self.prefix[self.length as usize] = byte;
        }
        self.length = self
            .length
            .checked_add(1)
            .ok_or("command head length overflow")?;
        if self.utf8_len == 0 && byte.is_ascii() {
            return Ok(());
        }
        if self.utf8_len == self.utf8.len() {
            return Err("top-level command head is not UTF-8".to_string());
        }
        self.utf8[self.utf8_len] = byte;
        self.utf8_len += 1;
        match std::str::from_utf8(&self.utf8[..self.utf8_len]) {
            Ok(_) => self.utf8_len = 0,
            Err(error) if error.error_len().is_some() => {
                return Err("top-level command head is not UTF-8".to_string());
            }
            Err(_) => {}
        }
        Ok(())
    }

    fn finish(&self) -> Result<Option<String>, String> {
        if self.utf8_len != 0 {
            return Err("top-level command head is not UTF-8".to_string());
        }
        if self.length > MAX_DECISION_HEAD_BYTES as u64 {
            return Ok(None);
        }
        let bytes = &self.prefix[..self.length as usize];
        Ok(match bytes {
            b"check-sat" => Some("check-sat".to_string()),
            b"check-sat-assuming" => Some("check-sat-assuming".to_string()),
            b"check-sat-using" => Some("check-sat-using".to_string()),
            _ => None,
        })
    }
}

enum Head {
    Awaiting,
    Reading(HeadToken),
    Finished(Option<String>),
}

struct Scanner {
    size: u64,
    prefix_hash: Sha256,
    expression_hash: Option<Sha256>,
    expression_start: u64,
    depth: u64,
    lexical: Lexical,
    head: Head,
    queries: Vec<CorpusQuery>,
}

impl Scanner {
    fn new() -> Self {
        Self {
            size: 0,
            prefix_hash: Sha256::new(),
            expression_hash: None,
            expression_start: 0,
            depth: 0,
            lexical: Lexical::Normal,
            head: Head::Finished(None),
            queries: Vec::new(),
        }
    }

    fn head_byte(&mut self, byte: u8) -> Result<(), String> {
        match &mut self.head {
            Head::Reading(token) => {
                if byte.is_ascii_whitespace() || matches!(byte, b'(' | b')' | b';') {
                    self.head = Head::Finished(token.finish()?);
                } else {
                    token.push(byte)?;
                }
            }
            Head::Awaiting if self.lexical == Lexical::Normal && self.depth == 1 => {
                if byte.is_ascii_whitespace() || byte == b';' {
                    return Ok(());
                }
                if matches!(byte, b'(' | b')' | b'"' | b'|') {
                    self.head = Head::Finished(None);
                } else {
                    let mut token = HeadToken::new();
                    token.push(byte)?;
                    self.head = Head::Reading(token);
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn feed(&mut self, bytes: &[u8]) -> Result<(), String> {
        let mut prefix_start = 0;
        let mut expression_start = 0;
        for (index, byte) in bytes.iter().copied().enumerate() {
            self.head_byte(byte)?;
            match self.lexical {
                Lexical::Comment => {
                    if matches!(byte, b'\n' | b'\r') {
                        self.lexical = Lexical::Normal;
                    }
                    continue;
                }
                Lexical::String {
                    quote_pending: true,
                } if byte == b'"' => {
                    self.lexical = Lexical::String {
                        quote_pending: false,
                    };
                    continue;
                }
                Lexical::String {
                    quote_pending: true,
                } => {
                    // The prior quote closed the string. This byte belongs to
                    // the enclosing command and must be processed below.
                    self.lexical = Lexical::Normal;
                }
                Lexical::String { .. } => {
                    self.lexical = Lexical::String {
                        quote_pending: byte == b'"',
                    };
                    continue;
                }
                Lexical::Quoted { escaped: true } => {
                    self.lexical = Lexical::Quoted { escaped: false };
                    continue;
                }
                Lexical::Quoted { escaped: false } => {
                    self.lexical = if byte == b'|' {
                        Lexical::Normal
                    } else {
                        Lexical::Quoted {
                            escaped: byte == b'\\',
                        }
                    };
                    continue;
                }
                Lexical::Normal => {}
            }
            match byte {
                b';' => self.lexical = Lexical::Comment,
                b'"' => {
                    self.lexical = Lexical::String {
                        quote_pending: false,
                    }
                }
                b'|' => self.lexical = Lexical::Quoted { escaped: false },
                b'(' => {
                    if self.depth == 0 {
                        self.expression_start = self
                            .size
                            .checked_add(index as u64)
                            .ok_or("query offset overflow")?;
                        self.expression_hash = Some(Sha256::new());
                        expression_start = index;
                        self.head = Head::Awaiting;
                    }
                    self.depth = self
                        .depth
                        .checked_add(1)
                        .ok_or("parenthesis depth overflow")?;
                }
                b')' => {
                    self.depth = self.depth.checked_sub(1).ok_or_else(|| {
                        format!("unexpected `)` at byte {}", self.size + index as u64)
                    })?;
                    if self.depth == 0 {
                        let mut expression_hash = self
                            .expression_hash
                            .take()
                            .ok_or("missing expression start")?;
                        expression_hash.update(&bytes[expression_start..=index]);
                        self.prefix_hash.update(&bytes[prefix_start..=index]);
                        prefix_start = index + 1;
                        if let Head::Finished(Some(command)) =
                            std::mem::replace(&mut self.head, Head::Finished(None))
                        {
                            if self.queries.len() == EXPECTED_QUERY_COUNT {
                                return Err("one corpus file exceeds the complete official query population".to_string());
                            }
                            self.queries.push(CorpusQuery {
                                ordinal: self.queries.len() + 1,
                                command,
                                byte_start: self.expression_start,
                                byte_end: self
                                    .size
                                    .checked_add(index as u64 + 1)
                                    .ok_or("query offset overflow")?,
                                command_sha256: format!("{:x}", expression_hash.finalize()),
                                prefix_sha256: format!("{:x}", self.prefix_hash.clone().finalize()),
                            });
                        }
                    }
                }
                byte if self.depth == 0 && !byte.is_ascii_whitespace() => {
                    return Err(format!(
                        "top-level SMT-LIB input is not a parenthesized command at byte {}",
                        self.size + index as u64
                    ));
                }
                _ => {}
            }
        }
        self.prefix_hash.update(&bytes[prefix_start..]);
        if let Some(hash) = self.expression_hash.as_mut() {
            hash.update(&bytes[expression_start..]);
        }
        self.size = self
            .size
            .checked_add(bytes.len() as u64)
            .ok_or("corpus byte count overflow")?;
        Ok(())
    }

    fn finish(self) -> Result<ScannedFile, String> {
        match self.lexical {
            Lexical::String {
                quote_pending: false,
                ..
            } => return Err("unterminated string literal".to_string()),
            Lexical::Quoted { .. } => return Err("unterminated quoted symbol".to_string()),
            _ => {}
        }
        if let Head::Reading(token) = &self.head {
            token.finish()?;
        }
        if self.depth != 0 {
            return Err("unterminated top-level S-expression".to_string());
        }
        Ok(ScannedFile {
            size: self.size,
            sha256: format!("{:x}", self.prefix_hash.finalize()),
            queries: self.queries,
        })
    }
}

pub(super) fn scan(reader: &mut impl Read, limit: u64) -> Result<ScannedFile, String> {
    let mut scanner = Scanner::new();
    let mut buffer = [0u8; BUFFER_BYTES];
    loop {
        let remaining = limit.saturating_sub(scanner.size);
        let request = usize::try_from(remaining.saturating_add(1))
            .unwrap_or(usize::MAX)
            .min(buffer.len());
        let count = match reader.read(&mut buffer[..request]) {
            Ok(count) => count,
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(format!("reading corpus byte stream: {error}")),
        };
        if count == 0 {
            break;
        }
        if count as u64 > remaining {
            return Err("corpus byte stream exceeds authenticated expansion budget".to_string());
        }
        scanner.feed(&buffer[..count])?;
    }
    scanner.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{self, Cursor};

    struct Chunked<'a> {
        bytes: &'a [u8],
        chunk: usize,
        maximum_request: usize,
        interrupt: bool,
    }

    impl Read for Chunked<'_> {
        fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
            self.maximum_request = self.maximum_request.max(out.len());
            if self.interrupt {
                self.interrupt = false;
                return Err(io::Error::from(io::ErrorKind::Interrupted));
            }
            let count = out.len().min(self.chunk).min(self.bytes.len());
            out[..count].copy_from_slice(&self.bytes[..count]);
            self.bytes = &self.bytes[count..];
            Ok(count)
        }
    }

    #[test]
    fn modern_string_backslashes_preserve_real_query_boundaries_and_prefixes() {
        // Backslashes are ordinary string bytes in the pinned Z3 scanner.
        // Only doubled quotes escape a quote; a terminal backslash cannot
        // consume the closing quote or the following decision command.
        let input = br#"(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(declare-const slash String)
(assert (= slash "\"))
(assert (= "\\" "\\"))
(assert (= "slash\""(check-sat)" "slash\""(check-sat)"))
(check-sat)
(assert (= slash """"))
(check-sat)
"#;
        let marker = b"\n(check-sat)\n";
        let offsets: Vec<_> = input
            .windows(marker.len())
            .enumerate()
            .filter_map(|(offset, bytes)| (bytes == marker).then_some(offset + 1))
            .collect();
        assert_eq!(offsets.len(), 2);
        for chunk in 1..=64 {
            let mut reader = Chunked {
                bytes: input,
                chunk,
                maximum_request: 0,
                interrupt: true,
            };
            let scanned = scan(&mut reader, input.len() as u64).unwrap();
            assert_eq!(scanned.size, input.len() as u64);
            assert_eq!(scanned.sha256, super::super::sha256_bytes(input));
            assert_eq!(scanned.queries.len(), 2);
            for (ordinal, (query, start)) in scanned.queries.iter().zip(&offsets).enumerate() {
                let end = start + b"(check-sat)".len();
                assert_eq!(query.ordinal, ordinal + 1);
                assert_eq!(query.command, "check-sat");
                assert_eq!(query.byte_start, *start as u64);
                assert_eq!(query.byte_end, end as u64);
                assert_eq!(
                    query.command_sha256,
                    super::super::sha256_bytes(&input[*start..end])
                );
                assert_eq!(
                    query.prefix_sha256,
                    super::super::sha256_bytes(&input[..end])
                );
            }
            assert!(reader.maximum_request <= BUFFER_BYTES);
        }
    }

    #[test]
    fn query_identity_matches_slice_scanner_across_lexical_boundaries() {
        let inputs: &[&[u8]] = &[
            b"(check-sat)",
            b"; (check-sat)\r\n( ;comment\n check-sat ) ;last",
            b"(set-info :notes \"quotes\"\" and (check-sat)\")\n(check-sat)",
            b"(set-info :notes \"old\\\"escaped\") (check-sat-assuming (|p\\|q|))",
            b"(push 1)(assert |(check-sat)|)(check-sat)(pop 1)(reset)(check-sat-using (then smt))",
            "(declare-const |雪| Bool) (assert |雪|) (check-sat)".as_bytes(),
            "(未知 a) ((check-sat)) (check-sat)".as_bytes(),
            b"(assert \"\xff\") (check-sat)",
            b";\xff fake (check-sat)\r\n(check-sat)(exit)",
            b"(\"not-a-command\") (|not-a-command|) (check-sat)",
            b"(check-sat;comment\n)(check-sat-assuming ())",
            b"(assert \"unterminated)",
            b"(assert |unterminated)",
            b"(assert \"dangling\\",
            b"(assert |dangling\\",
            b"(\xff)(check-sat)",
            b"(\xe2\x82)(check-sat)",
            b"(check-sat))",
            b"invalid (check-sat)",
        ];
        for input in inputs {
            let expected = super::super::scan_queries_legacy(input);
            for chunk in 1..=64 {
                let mut reader = Chunked {
                    bytes: input,
                    chunk,
                    maximum_request: 0,
                    interrupt: true,
                };
                let actual = scan(&mut reader, input.len() as u64);
                match (&expected, &actual) {
                    (Ok(expected), Ok(actual)) => {
                        assert_eq!(actual.queries, *expected, "input={input:?}; chunk={chunk}");
                        assert_eq!(actual.size, input.len() as u64);
                        assert_eq!(actual.sha256, super::super::sha256_bytes(input));
                    }
                    (Err(_), Err(_)) => {}
                    _ => panic!("legacy/stream disagreement: input={input:?}; chunk={chunk}"),
                }
                assert!(reader.maximum_request <= BUFFER_BYTES);
            }
        }
    }

    #[test]
    fn large_unknown_head_does_not_require_a_token_sized_buffer() {
        let input = [
            b"(".as_slice(),
            &vec![b'x'; 3 * 1024 * 1024],
            b") (check-sat)",
        ]
        .concat();
        let expected = super::super::scan_queries_legacy(&input).unwrap();
        let mut reader = Chunked {
            bytes: &input,
            chunk: 509,
            maximum_request: 0,
            interrupt: false,
        };
        let actual = scan(&mut reader, input.len() as u64).unwrap();
        assert_eq!(actual.queries, expected);
        assert_eq!(actual.sha256, super::super::sha256_bytes(&input));
        assert!(reader.maximum_request <= BUFFER_BYTES);
        let mut reader = Chunked {
            bytes: &input,
            chunk: 509,
            maximum_request: 0,
            interrupt: false,
        };
        assert!(scan(&mut reader, input.len() as u64 - 1)
            .unwrap_err()
            .contains("expansion budget"));
    }

    #[test]
    fn adversarial_lexical_streams_preserve_legacy_admission_and_epoch_hashes() {
        let alphabet = b"() ;\r\n\t\"|\\abcdefgh-checksat\xc2\xa2\xff";
        let mut state = 0x3918_122du32;
        for _ in 0..4096 {
            let mut input = Vec::new();
            for _ in 0..127 {
                state = state.wrapping_mul(1664525).wrapping_add(1013904223);
                input.push(alphabet[state as usize % alphabet.len()]);
            }
            input.extend_from_slice(b"\n(check-sat)");
            let expected = super::super::scan_queries_legacy(&input);
            for chunk in [1, 7, 31, BUFFER_BYTES] {
                let mut reader = Chunked {
                    bytes: &input,
                    chunk,
                    maximum_request: 0,
                    interrupt: false,
                };
                let actual = scan(&mut reader, input.len() as u64);
                match (expected.as_ref(), actual) {
                    (Ok(expected), Ok(actual)) => assert_eq!(actual.queries, *expected),
                    (Err(_), Err(_)) => {}
                    _ => panic!("legacy/stream admission differs for {input:?}"),
                }
            }
        }
    }

    #[test]
    fn reset_keeps_prior_bytes_in_later_prefix_and_trailing_bytes_in_file_hash() {
        let a = b"; A\n(check-sat)(reset)(check-sat)\n; end-one";
        let b = b"; B\n(check-sat)(reset)(check-sat)\n; end-one";
        let c = b"; A\n(check-sat)(reset)(check-sat)\n; end-two";
        let a = scan(&mut Cursor::new(a), a.len() as u64).unwrap();
        let b = scan(&mut Cursor::new(b), b.len() as u64).unwrap();
        let c = scan(&mut Cursor::new(c), c.len() as u64).unwrap();
        assert_eq!(a.queries.len(), 2);
        assert_eq!(a.queries[1].ordinal, 2);
        assert_eq!(a.queries[1].command_sha256, b.queries[1].command_sha256);
        assert_ne!(a.queries[1].prefix_sha256, b.queries[1].prefix_sha256);
        assert_eq!(a.queries, c.queries);
        assert_ne!(a.sha256, c.sha256);
    }

    #[test]
    #[ignore = "streams the measured 1.17 GB member size; run under build-slot for large-input acceptance"]
    fn streaming_query_after_more_than_one_gib_of_comment_has_exact_u64_offsets() {
        let comment_bytes = 1_169_487_267u64;
        let suffix = b"\n(check-sat)\n";
        let mut input = Cursor::new(b";")
            .chain(io::repeat(b'x').take(comment_bytes))
            .chain(Cursor::new(suffix));
        let size = 1 + comment_bytes + suffix.len() as u64;
        let actual = scan(&mut input, size).unwrap();
        assert_eq!(actual.size, size);
        assert_eq!(actual.queries.len(), 1);
        assert_eq!(actual.queries[0].byte_start, comment_bytes + 2);
        assert_eq!(actual.queries[0].byte_end, size - 1);
        assert_eq!(
            actual.queries[0].command_sha256,
            super::super::sha256_bytes(b"(check-sat)")
        );
        let mut independent = Sha256::new();
        independent.update(b";");
        let chunk = [b'x'; 16381];
        let mut remaining = comment_bytes;
        while remaining > 0 {
            let count = remaining.min(chunk.len() as u64) as usize;
            independent.update(&chunk[..count]);
            remaining -= count as u64;
        }
        independent.update(b"\n(check-sat)");
        assert_eq!(
            actual.queries[0].prefix_sha256,
            format!("{:x}", independent.clone().finalize())
        );
        independent.update(b"\n");
        assert_eq!(actual.sha256, format!("{:x}", independent.finalize()));
    }
}
