//! Regression tests for silent formula truncation (bugs A and B).
//!
//! Before the fix all three formula parsers iterated with
//! `lines.map_while(Result::ok)`, which *ends* the iteration on the first
//! `Err` returned by [`std::io::BufRead::lines`] instead of propagating it.
//! Any non-UTF-8 byte (or genuine I/O error) therefore silently discarded
//! every remaining constraint, and the proof was then checked against a
//! strict subset of the real formula.
//!
//! Additionally the CNF/WCNF parsers dropped an unterminated final clause
//! (one not followed by `0`) on the floor, and the declared
//! `p cnf <vars> <clauses>` counts were never compared against the file.

use std::io::Write;
use std::path::{Path, PathBuf};

use veripb_parser::{
    cnf_parser::{CnfParserOptions, parse_cnf_from_file, parse_cnf_from_file_with_options},
    error::ParserError,
    opb_parser::parse_opb_from_file,
    wcnf_parser::parse_wcnf_from_file,
};

/// Write `bytes` to a fresh file inside a temporary directory and return both
/// (the directory keeps the file alive for the duration of the test).
fn write_temp(name: &str, bytes: &[u8]) -> (tempfile::TempDir, PathBuf) {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let path = dir.path().join(name);
    let mut file = std::fs::File::create(&path).expect("failed to create temporary file");
    file.write_all(bytes).expect("failed to write test input");
    file.flush().expect("failed to flush test input");
    (dir, path)
}

/// A byte sequence that is not valid UTF-8 (a lone continuation byte).
const BAD_BYTE: &[u8] = b"\xff";

fn bytes(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

// --------------------------------------------------------------------------
// A. non-UTF-8 byte mid-file must be an error, not a silent truncation
// --------------------------------------------------------------------------

#[test]
fn opb_non_utf8_comment_is_error_not_truncation() {
    // This is reproducer 01-formula-truncation-utf8: the bad byte sits in a
    // comment between two constraints. Before the fix the parser returned
    // `Ok` with only the *first* constraint, so `x2` was unconstrained.
    let input = bytes(&[
        b"* ok\n+1 x1 >= 1 ;\n* bad ",
        BAD_BYTE,
        b" byte\n+1 x2 >= 1 ;\n",
    ]);
    let (_dir, path) = write_temp("t.opb", &input);

    match parse_opb_from_file(&path) {
        Ok((formula, _, _, _)) => panic!(
            "expected an error, but the parser silently returned {} of 2 constraints",
            formula.len()
        ),
        Err(e) => assert!(
            matches!(e, ParserError::LineReadError { .. }),
            "expected LineReadError, got: {e:?}"
        ),
    }
}

#[test]
fn cnf_non_utf8_comment_is_error_not_truncation() {
    let input = bytes(&[b"p cnf 2 2\n1 0\nc bad ", BAD_BYTE, b" byte\n2 0\n"]);
    let (_dir, path) = write_temp("t.cnf", &input);

    match parse_cnf_from_file(&path) {
        Ok((formula, _)) => panic!(
            "expected an error, but the parser silently returned {} of 2 clauses",
            formula.len()
        ),
        Err(e) => assert!(
            matches!(e, ParserError::LineReadError { .. }),
            "expected LineReadError, got: {e:?}"
        ),
    }
}

#[test]
fn wcnf_non_utf8_comment_is_error_not_truncation() {
    let input = bytes(&[b"h 1 0\nc bad ", BAD_BYTE, b" byte\nh 2 0\n"]);
    let (_dir, path) = write_temp("t.wcnf", &input);

    match parse_wcnf_from_file(&path) {
        Ok((formula, _)) => panic!(
            "expected an error, but the parser silently returned {} of 2 clauses",
            formula.len()
        ),
        Err(e) => assert!(
            matches!(e, ParserError::LineReadError { .. }),
            "expected LineReadError, got: {e:?}"
        ),
    }
}

// --------------------------------------------------------------------------
// A. a genuine (non-UTF-8-unrelated) I/O error must also be propagated
// --------------------------------------------------------------------------

/// Reading a *directory* as a file: `File::open` succeeds on Unix, but the
/// first `read` fails with `EISDIR`. That is a real `std::io::Error` with no
/// UTF-8 involvement, so it exercises the error path of `lines()` directly.
///
/// Before the fix the OPB parser reported `Ok(<empty formula>)` for this.
#[test]
fn opb_read_error_is_propagated() {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let path: &Path = dir.path();
    // Guard: if the platform refuses to open a directory at all we get
    // `FileError` instead, which is still an error, so the assertion below
    // holds either way.
    match parse_opb_from_file(path) {
        Ok((formula, _, _, _)) => panic!(
            "expected an I/O error, but the parser returned Ok with {} constraints",
            formula.len()
        ),
        Err(ParserError::LineReadError { .. } | ParserError::FileError(_)) => {}
        Err(e) => panic!("expected LineReadError or FileError, got: {e:?}"),
    }
}

#[test]
fn wcnf_read_error_is_propagated() {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    match parse_wcnf_from_file(dir.path()) {
        Ok((formula, _)) => panic!(
            "expected an I/O error, but the parser returned Ok with {} constraints",
            formula.len()
        ),
        Err(ParserError::LineReadError { .. } | ParserError::FileError(_)) => {}
        Err(e) => panic!("expected LineReadError or FileError, got: {e:?}"),
    }
}

// --------------------------------------------------------------------------
// B. unterminated final clause must be an error, not a silent drop
// --------------------------------------------------------------------------

#[test]
fn cnf_unterminated_final_clause_is_error() {
    // This is reproducer 02-cnf-unterminated-clause: the final clause `3` has
    // no terminating `0`, so before the fix it was dropped and `x3` was
    // unconstrained.
    let (_dir, path) = write_temp("t.cnf", b"p cnf 3 3\n1 0\n2 0\n3\n");

    match parse_cnf_from_file(&path) {
        Ok((formula, _)) => panic!(
            "expected an error, but the parser silently returned {} of 3 clauses",
            formula.len()
        ),
        Err(e) => assert!(
            matches!(e, ParserError::UnterminatedClause { .. }),
            "expected UnterminatedClause, got: {e:?}"
        ),
    }
}

#[test]
fn cnf_unterminated_final_clause_without_trailing_newline_is_error() {
    let (_dir, path) = write_temp("t.cnf", b"p cnf 3 3\n1 0\n2 0\n-3 1");

    assert!(
        matches!(
            parse_cnf_from_file(&path),
            Err(ParserError::UnterminatedClause { .. })
        ),
        "unterminated final clause must be rejected"
    );
}

#[test]
fn wcnf_unterminated_final_clause_is_error() {
    let (_dir, path) = write_temp("t.wcnf", b"h 1 0\nh 2 0\nh 3\n");

    match parse_wcnf_from_file(&path) {
        Ok((formula, _)) => panic!(
            "expected an error, but the parser silently returned {} of 3 clauses",
            formula.len()
        ),
        Err(e) => assert!(
            matches!(e, ParserError::UnterminatedClause { .. }),
            "expected UnterminatedClause, got: {e:?}"
        ),
    }
}

#[test]
fn wcnf_dangling_weight_is_error() {
    // A soft-clause weight with no clause after it.
    let (_dir, path) = write_temp("t.wcnf", b"h 1 0\n5 2 0\n7\n");

    assert!(
        matches!(
            parse_wcnf_from_file(&path),
            Err(ParserError::UnterminatedClause { .. })
        ),
        "a dangling weight at end of file must be rejected"
    );
}

// --------------------------------------------------------------------------
// `p cnf <vars> <clauses>` header counts
// --------------------------------------------------------------------------

#[test]
fn cnf_missing_clauses_rejected_in_strict_mode() {
    // A file truncated at a clause boundary: nothing is syntactically wrong,
    // only the declared clause count reveals the loss.
    let (_dir, path) = write_temp("t.cnf", b"p cnf 3 3\n1 0\n2 0\n");

    match parse_cnf_from_file_with_options(&path, CnfParserOptions::strict()) {
        Ok((formula, _)) => panic!(
            "expected an error, but the parser accepted {} of the 3 declared clauses",
            formula.len()
        ),
        Err(e) => assert!(
            matches!(e, ParserError::HeaderCountMismatch { .. }),
            "expected HeaderCountMismatch, got: {e:?}"
        ),
    }
}

#[test]
fn cnf_extra_clauses_rejected_in_strict_mode() {
    let (_dir, path) = write_temp("t.cnf", b"p cnf 3 1\n1 0\n2 0\n");

    assert!(
        matches!(
            parse_cnf_from_file_with_options(&path, CnfParserOptions::strict()),
            Err(ParserError::HeaderCountMismatch { .. })
        ),
        "more clauses than declared must be rejected in strict mode"
    );
}

#[test]
fn cnf_variable_beyond_declared_count_rejected_in_strict_mode() {
    let (_dir, path) = write_temp("t.cnf", b"p cnf 2 2\n1 0\n7 0\n");

    assert!(
        matches!(
            parse_cnf_from_file_with_options(&path, CnfParserOptions::strict()),
            Err(ParserError::HeaderCountMismatch { .. })
        ),
        "a literal beyond the declared variable count must be rejected in strict mode"
    );
}

#[test]
fn cnf_header_count_mismatch_is_lenient_by_default() {
    // The default (backwards-compatible) entry point only warns; this keeps
    // `veripb-parser/tests/instances/cnf_header_init.cnf` (which declares 732
    // clauses and contains none) parseable.
    let (_dir, path) = write_temp("t.cnf", b"p cnf 3 3\n1 0\n2 0\n");
    let (formula, num_vars) =
        parse_cnf_from_file(&path).expect("default mode must stay lenient about header counts");
    assert_eq!(formula.len(), 2);
    assert_eq!(num_vars, 3);
}

#[test]
fn cnf_matching_header_counts_accepted_in_strict_mode() {
    let (_dir, path) = write_temp("t.cnf", b"p cnf 3 2\n1 -3 0\n2 0\n");
    let (formula, num_vars) = parse_cnf_from_file_with_options(&path, CnfParserOptions::strict())
        .expect("a well-formed file must be accepted in strict mode");
    assert_eq!(formula.len(), 2);
    assert_eq!(num_vars, 3);
}
