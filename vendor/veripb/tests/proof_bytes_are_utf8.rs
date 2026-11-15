//! Bytes read out of a proof file must not be turned into a `&str` without checking.
//!
//! The pbp reader and lexer built `str`s straight out of file bytes with
//! `from_utf8_unchecked` in three places: the source-line snippet an error message quotes
//! (`StreamReader::get_chunk`), the `--trace` buffer (`StreamReader::print_trace`) and the body of
//! a `%` comment (`Lexer::comment`). A proof file is untrusted input and is not required to be
//! UTF-8, so each of those produced a `&str` that is not UTF-8 whenever the file held a byte
//! outside it — undefined behaviour at the moment of construction, before anything reads the
//! result, and then `str::replace`, `str::lines`, `trim_ascii` and `Display` ran over it.
//!
//! Two of the three are on the *accepting* path, which is what makes this worth pinning rather
//! than shrugging at: a `%` comment is skipped, and the free text of an `a` (assertion) rule is
//! skipped by `Lexer::skip_to_semicolon` whenever annotations are not being stored. Both leave
//! their raw bytes in the trace buffer and both let the run go on to print a verdict.
//!
//! These tests drive the compiled binary so the bytes it emits can be inspected directly. The
//! observable each pins is the same: no byte that was invalid UTF-8 in the file may appear
//! verbatim in the checker's output, because its being there means it travelled through a `&str`.
//! Measured against the unfixed tree, every one of the three fails; the raw `\xff\xfe` is in the
//! output byte for byte.

use std::io::Write;
use std::process::{Command, Output};

/// The two bytes used throughout: `0xff` is not a legal UTF-8 byte anywhere, and `0xfe` is not
/// either, so no valid encoding of any text can contain them.
const INVALID: [u8; 2] = [0xff, 0xfe];

fn write_file(dir: &std::path::Path, name: &str, bytes: &[u8]) -> std::path::PathBuf {
    let path = dir.join(name);
    let mut file = std::fs::File::create(&path).expect("failed to create temporary file");
    file.write_all(bytes).expect("failed to write");
    file.flush().expect("failed to flush");
    path
}

/// Build a proof file whose body is `body`, with `INVALID` spliced in where `body` has `@@`.
fn proof_bytes(body: &str) -> Vec<u8> {
    let mut out = Vec::new();
    for (index, piece) in body.split("@@").enumerate() {
        if index > 0 {
            out.extend_from_slice(&INVALID);
        }
        out.extend_from_slice(piece.as_bytes());
    }
    out
}

/// Run the binary on a generated formula/proof pair and return its raw output.
fn run(formula: &str, proof_body: &str, extra_args: &[&str]) -> Output {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let formula = write_file(dir.path(), "f.opb", formula.as_bytes());
    let proof = write_file(dir.path(), "p.pbp", &proof_bytes(proof_body));
    Command::new(env!("CARGO_BIN_EXE_veripb"))
        .args(extra_args)
        .args([formula.as_os_str(), proof.as_os_str()])
        .output()
        .expect("failed to run veripb binary")
}

/// Every byte the binary wrote, on both streams.
fn emitted(output: &Output) -> Vec<u8> {
    let mut bytes = output.stdout.clone();
    bytes.extend_from_slice(&output.stderr);
    bytes
}

/// Neither `0xff` nor `0xfe` can occur in any valid UTF-8 encoding of anything, so finding either
/// in the output means the byte came straight from the file through a `str` that was never
/// checked. The escaped spelling `\xff` that error messages print is seven ASCII bytes and does
/// not trip this; the multi-byte text in the positive controls below is `0xc3`/`0xe6`/… and does
/// not either.
fn assert_no_raw_invalid_bytes(output: &Output, what: &str) {
    let bytes = emitted(output);
    assert!(
        !bytes.iter().any(|byte| INVALID.contains(byte)),
        "{what}: a byte the proof file could not legally encode was emitted verbatim, so it was \
         converted to a `str` without being checked. Output was:\n{}",
        String::from_utf8_lossy(&bytes)
    );
}

const FORMULA: &str = "* #variable= 10 #constraint= 1\n1 x10 >= 1 ;\n";

// ---------------------------------------------------------------------------
// the three unchecked conversions
// ---------------------------------------------------------------------------

#[test]
fn a_comment_holding_invalid_utf8_is_refused() {
    // `Lexer::comment` collects the whole comment body and made a `String` of it. The comment is
    // then discarded, so before the fix this proof *verified* — the undefined behaviour was on
    // the accepting path and left no trace in the verdict.
    let output = run(
        FORMULA,
        "pseudo-Boolean proof version 3.0\nf 1;\n% a comment @@ with bad bytes\n\
         output NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n",
        &[],
    );
    let rendered = String::from_utf8_lossy(&emitted(&output)).into_owned();
    assert!(
        rendered.contains("Invalid UTF-8 in comment"),
        "a comment that is not UTF-8 must be a parse error naming what is wrong, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("VERIFIED"),
        "a proof the checker cannot read must not verify, got:\n{rendered}"
    );
    assert_no_raw_invalid_bytes(&output, "comment body");
}

#[test]
fn tracing_a_skipped_assertion_annotation_does_not_emit_raw_bytes() {
    // `Lexer::skip_to_semicolon` consumes the free text of an `a` rule without looking at it
    // whenever assertion annotations are not stored, but every consumed byte still goes into the
    // `--trace` buffer, which `StreamReader::print_trace` turned into a `&str` wholesale. This
    // proof is *accepted* (`s UNDER ASSERTIONS NO CONCLUSION`, exit 0) either way; only the bytes
    // on stdout differ.
    let output = run(
        FORMULA,
        "pseudo-Boolean proof version 3.0\nf 1;\na +1 x10 >= 1 :::\n   free text @@ here\n;\n\
         output NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n",
        &["-t"],
    );
    assert!(
        output.status.success(),
        "the assertion proof must still be accepted: {}",
        String::from_utf8_lossy(&emitted(&output))
    );
    let rendered = String::from_utf8_lossy(&emitted(&output)).into_owned();
    assert!(
        rendered.contains("free text"),
        "the traced line must still be printed, got:\n{rendered}"
    );
    assert_no_raw_invalid_bytes(&output, "trace buffer");
}

#[test]
fn an_error_quoting_a_line_holding_invalid_utf8_does_not_emit_raw_bytes() {
    // `Lexer::report_error` quotes the source line through `StreamReader::get_chunk`, which
    // re-reads the file's bytes for that line. Any parse error on a line holding a non-UTF-8 byte
    // reached the unchecked conversion, and `report_error` then ran `str::replace` over the
    // result.
    let output = run(
        FORMULA,
        "pseudo-Boolean proof version 3.0\nf 1;\n@@ zz\n",
        &[],
    );
    let rendered = String::from_utf8_lossy(&emitted(&output)).into_owned();
    assert!(
        rendered.contains("Unexpected character") && rendered.contains("line 3"),
        "the parse error must still name the character and the line, got:\n{rendered}"
    );
    assert_no_raw_invalid_bytes(&output, "error source line");
}

// ---------------------------------------------------------------------------
// positive controls: valid UTF-8 above ASCII must keep working
// ---------------------------------------------------------------------------

#[test]
fn a_comment_holding_multi_byte_utf8_still_verifies() {
    // The refusal is about bytes that are not UTF-8, not about bytes above 0x7f. A comment in any
    // language must still be skipped, and the checked conversion must not have narrowed that.
    let output = run(
        FORMULA,
        "pseudo-Boolean proof version 3.0\nf 1;\n% ° é 日本語 — a comment\n\
         output NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n",
        &[],
    );
    let rendered = String::from_utf8_lossy(&emitted(&output)).into_owned();
    assert!(
        output.status.success() && rendered.contains("VERIFIED"),
        "a comment that is valid UTF-8 must still verify, got:\n{rendered}"
    );
}

#[test]
fn tracing_still_prints_multi_byte_utf8_unchanged() {
    let output = run(
        FORMULA,
        "pseudo-Boolean proof version 3.0\nf 1;\na +1 x10 >= 1 :::\n   frëe text 日本語\n;\n\
         output NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n",
        &["-t"],
    );
    let rendered = String::from_utf8_lossy(&emitted(&output)).into_owned();
    assert!(
        rendered.contains("frëe text 日本語"),
        "valid non-ASCII text must be traced unchanged, got:\n{rendered}"
    );
}

#[test]
fn an_error_on_an_ascii_line_still_quotes_the_source() {
    // `get_chunk` returning `Err` costs the source snippet, so the snippet must still be there
    // for every line that is valid UTF-8 — which is every line of every real proof.
    let output = run(
        FORMULA,
        "pseudo-Boolean proof version 3.0\nf 1;\nzz zz\n",
        &[],
    );
    let rendered = String::from_utf8_lossy(&emitted(&output)).into_owned();
    assert!(
        rendered.contains("zz") && rendered.contains('^'),
        "the error must still quote the offending line and underline it, got:\n{rendered}"
    );
}
