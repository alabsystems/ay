// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY-SAT-1: a large input is parsed from the file after a line-by-line
//! pre-scan; the pre-scan must report exactly what the in-memory path
//! computes on the whole buffer, and the parse must refuse bytes that differ.

use super::*;

/// A CNF whose header declares more clauses than the XOR route accepts.
fn large_header_cnf(body: &str) -> Vec<u8> {
    format!(
        "c comment\nc another\np cnf 9 {}\n{body}",
        XOR_EXTENSION_MAX_CLAUSES + 1
    )
    .into_bytes()
}

#[test]
fn prescan_matches_whole_buffer_facts() {
    let bytes = large_header_cnf("1 -2 0\n  3 9 -4 0\nc 99 in a comment\n-7 5 0\n\n 8 0");
    let (sha256, max_var) = prescan_dimacs_lines(io::Cursor::new(bytes.clone()))
        .ok()
        .flatten()
        .expect("a large header streams");
    assert_eq!(sha256, sha256_digest(&bytes));
    assert_eq!(max_var, scan_max_variable(&bytes));
    assert_eq!(max_var, 9);
}

#[test]
fn prescan_stops_the_variable_scan_at_percent_like_the_buffer_scan() {
    let bytes = large_header_cnf("1 2 0\n%\n0\n77 0\n");
    let (_, max_var) = prescan_dimacs_lines(io::Cursor::new(bytes.clone()))
        .ok()
        .flatten()
        .expect("a large header streams");
    assert_eq!(max_var, scan_max_variable(&bytes));
    assert_eq!(max_var, 2);
}

#[test]
fn prescan_keeps_small_headers_in_memory() {
    let bytes = b"c x\np cnf 3 2\n1 2 0\n-3 0\n".to_vec();
    assert!(matches!(
        prescan_dimacs_lines(io::Cursor::new(bytes)),
        Ok(None)
    ));
    let no_header = b"1 2 0\n".to_vec();
    assert!(matches!(
        prescan_dimacs_lines(io::Cursor::new(no_header)),
        Ok(None)
    ));
}

#[test]
fn prescan_rejects_invalid_utf8() {
    let mut bytes = large_header_cnf("1 2 0\n");
    bytes.extend_from_slice(b"c \xff\n");
    assert!(matches!(
        prescan_dimacs_lines(io::Cursor::new(bytes)),
        Err(LargeDimacsPrescanError::Utf8(_))
    ));
}

#[test]
fn checking_reader_refuses_changed_bytes() {
    let bytes = large_header_cnf("1 2 0\n");
    let digest = sha256_digest(&bytes);
    let mut same = Sha256CheckingReader::new(io::Cursor::new(bytes.clone()), digest);
    let mut out = Vec::new();
    assert!(same.read_to_end(&mut out).is_ok());
    assert_eq!(out, bytes);

    let mut changed_bytes = bytes;
    changed_bytes.push(b'\n');
    let mut changed = Sha256CheckingReader::new(io::Cursor::new(changed_bytes), digest);
    let error = changed
        .read_to_end(&mut Vec::new())
        .expect_err("changed bytes must not parse");
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
}

/// A header behind more than `STREAM_DIMACS_HEADER_PREFIX_MAX` bytes of
/// comments is not looked for: the input stays in memory. Just under the cap
/// it is found and the input streams.
#[test]
fn prescan_header_prefix_cap_keeps_the_input_in_memory() {
    let comment = format!("c {}\n", "x".repeat(1021));
    assert_eq!(comment.len(), 1024);
    let comments_over = comment.repeat(STREAM_DIMACS_HEADER_PREFIX_MAX / 1024 + 1);
    let mut over = comments_over.into_bytes();
    over.extend_from_slice(&large_header_cnf("1 2 0\n"));
    assert!(matches!(
        prescan_dimacs_lines(io::Cursor::new(over)),
        Ok(None)
    ));

    let comments_under = comment.repeat(STREAM_DIMACS_HEADER_PREFIX_MAX / 1024 - 1);
    let mut under = comments_under.into_bytes();
    under.extend_from_slice(&large_header_cnf("1 2 0\n"));
    assert!(matches!(
        prescan_dimacs_lines(io::Cursor::new(under)),
        Ok(Some(_))
    ));
}

/// Every parser event of `reader`, rendered, and the parse result.
fn parsed_events<R: Read>(reader: R) -> (Vec<String>, String) {
    let mut events = Vec::new();
    let result = ay_sat::dimacs_core::parse_dimacs_events(reader, |event| {
        events.push(format!("{event:?}"));
        Ok(())
    });
    (events, format!("{result:?}"))
}

fn write_cnf(dir: &tempfile::TempDir, bytes: &[u8]) -> PathBuf {
    let path = dir.path().join("large.cnf");
    std::fs::write(&path, bytes).expect("write the fixture");
    path
}

/// The large-file route (threshold lowered) feeds the parser exactly the
/// events the in-memory route feeds it, with the same SHA-256 and maximum
/// variable, and drains a `%` trailer through the check; at the production
/// threshold the same small file stays in memory.
#[test]
fn large_prescan_stream_route_matches_in_memory_route() {
    let dir = tempfile::tempdir().expect("tempdir");
    let bytes = large_header_cnf("1 -2 0\n3 9 -4 0\nc 99\n-7 5 0\n%\n0\n77 0\n");
    let path = write_cnf(&dir, &bytes);

    assert!(matches!(
        prescan_large_dimacs(&path, STREAM_DIMACS_MIN_BYTES),
        Ok(LargeDimacsPrescan::InMemory)
    ));
    let Ok(LargeDimacsPrescan::Stream { sha256, max_var }) = prescan_large_dimacs(&path, 0) else {
        panic!("a large header streams at a zero threshold");
    };
    assert_eq!(sha256, sha256_digest(&bytes));
    assert_eq!(max_var, scan_max_variable(&bytes));

    let mut streamed = open_streamed_dimacs(&path, sha256).expect("open");
    let streamed_events = parsed_events(&mut streamed);
    assert_eq!(
        streamed_events,
        parsed_events(io::Cursor::new(bytes.clone()))
    );
    assert!(!streamed_events.0.is_empty());
    drain_streamed_dimacs(streamed).expect("unchanged bytes pass the check");
}

/// Bytes changed behind the `%` line after the pre-scan: the parser stops
/// before them and accepts, but the drain reads them through the SHA-256
/// check and refuses, so the run ends as a parse error before any solve.
#[test]
fn large_prescan_change_behind_percent_trailer_is_refused() {
    let dir = tempfile::tempdir().expect("tempdir");
    let bytes = large_header_cnf("1 2 0\n%\n0\n");
    let path = write_cnf(&dir, &bytes);
    let Ok(LargeDimacsPrescan::Stream { sha256, .. }) = prescan_large_dimacs(&path, 0) else {
        panic!("a large header streams at a zero threshold");
    };
    let mut changed = bytes.clone();
    changed.extend_from_slice(b"5 0\n");
    std::fs::write(&path, &changed).expect("change the file");

    let mut streamed = open_streamed_dimacs(&path, sha256).expect("open");
    let (_, result) = parsed_events(&mut streamed);
    assert!(
        result.starts_with("Ok("),
        "the parse stops at '%': {result}"
    );
    let error = drain_streamed_dimacs(streamed).expect_err("changed bytes are refused");
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
}
