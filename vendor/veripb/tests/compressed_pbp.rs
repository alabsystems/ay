//! Tests that zstd-compressed (`.pbp.zst`) derivation files are read identically to their
//! uncompressed (`.pbp`) counterparts, for both proof version 2 and version 3.

use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
};

use flate2::{Compression, write::GzEncoder};
use tempfile::Builder;
use veripb::args::Args;
use veripb_parser::io::open_maybe_compressed;

/// Compress `derivation` with zstd into a fresh temp file ending in `.pbp.zst` and return its
/// path. The temp file is kept alive for the lifetime of the returned `NamedTempFile`.
fn compress_to_temp_zst(derivation: &Path) -> tempfile::NamedTempFile {
    let data = fs::read(derivation).expect("failed to read derivation file");
    let compressed = zstd::stream::encode_all(&*data, 0).expect("failed to compress derivation");

    let mut temp = Builder::new()
        .suffix(".pbp.zst")
        .tempfile()
        .expect("failed to create temp file");
    temp.write_all(&compressed)
        .expect("failed to write temp file");
    temp.flush().expect("failed to flush temp file");
    temp
}

fn compress_to_temp_gz(derivation: &Path) -> tempfile::NamedTempFile {
    let data = fs::read(derivation).expect("failed to read derivation file");
    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    encoder
        .write_all(&data)
        .expect("failed to compress derivation");
    let compressed = encoder.finish().expect("failed to finish gzip stream");

    let mut temp = Builder::new()
        .suffix(".pbp.gz")
        .tempfile()
        .expect("failed to create temp file");
    temp.write_all(&compressed)
        .expect("failed to write temp file");
    temp.flush().expect("failed to flush temp file");
    temp
}

fn compress_to_temp_xz(derivation: &Path) -> tempfile::NamedTempFile {
    let data = fs::read(derivation).expect("failed to read derivation file");
    let compressed = xz2::stream::Stream::new_easy_encoder(6, xz2::stream::Check::Crc64)
        .map(|stream| {
            let mut encoder = xz2::write::XzEncoder::new_stream(Vec::new(), stream);
            encoder
                .write_all(&data)
                .expect("failed to compress derivation");
            encoder.finish().expect("failed to finish xz stream")
        })
        .expect("failed to create xz encoder");

    let mut temp = Builder::new()
        .suffix(".pbp.xz")
        .tempfile()
        .expect("failed to create temp file");
    temp.write_all(&compressed)
        .expect("failed to write temp file");
    temp.flush().expect("failed to flush temp file");
    temp
}

// Keep the old name as an alias so existing call-sites don't need updating.
fn compress_to_temp(derivation: &Path) -> tempfile::NamedTempFile {
    compress_to_temp_zst(derivation)
}

fn run(formula: PathBuf, derivation: PathBuf) -> anyhow::Result<()> {
    let args = Args {
        formula,
        derivation,
        print_verification_result: false,
        ..Default::default()
    };
    // Our `run_checker` returns a `RunOutcome` (the verdict, which
    // `--kernel-verify` and the exit-code path consume); upstream's version
    // returned `()`. This test only cares that the run succeeds.
    veripb::run_checker(args).map(|_| ())
}

/// A correct proof should verify whether read from disk uncompressed or decompressed on the fly.
fn assert_compressed_matches_uncompressed(formula: &str, derivation: &str) {
    let formula = PathBuf::from(formula);
    let derivation = PathBuf::from(derivation);

    let uncompressed_result = run(formula.clone(), derivation.clone());
    let compressed_derivation = compress_to_temp(&derivation);
    let compressed_result = run(formula, compressed_derivation.path().to_path_buf());

    assert_eq!(
        uncompressed_result.is_ok(),
        compressed_result.is_ok(),
        "compressed and uncompressed runs disagreed: uncompressed = {uncompressed_result:?}, compressed = {compressed_result:?}"
    );
}

#[test]
fn correct_version2_proof_compressed_matches_uncompressed() {
    assert_compressed_matches_uncompressed(
        "./tests/instances/correct/version2/rup.opb",
        "./tests/instances/correct/version2/rup.pbp",
    );
}

#[test]
fn correct_version3_proof_compressed_matches_uncompressed() {
    assert_compressed_matches_uncompressed(
        "./tests/instances/correct/version3/rup.opb",
        "./tests/instances/correct/version3/rup.pbp",
    );
}

#[test]
fn incorrect_version2_proof_compressed_matches_uncompressed() {
    assert_compressed_matches_uncompressed(
        "./tests/instances/incorrect/version2/rup.opb",
        "./tests/instances/incorrect/version2/rup.pbp",
    );
}

#[test]
fn compressed_proof_actually_verifies_as_correct() {
    // Guard against the equivalence check above passing only because both sides fail
    // (e.g. if compression silently broke parsing for both runs in the same way).
    let compressed_derivation =
        compress_to_temp(Path::new("./tests/instances/correct/version3/rup.pbp"));
    let result = run(
        PathBuf::from("./tests/instances/correct/version3/rup.opb"),
        compressed_derivation.path().to_path_buf(),
    );
    assert!(
        result.is_ok(),
        "expected compressed proof to verify, got {result:?}"
    );
}

/// `open_maybe_compressed` cannot recover a file size from a zstd stream (without relying on the
/// optional `--content-size` frame header), so progress reporting must fall back to `None`. The
/// uncompressed path must still report a `Some` size so the percentage-based progress bar works.
#[test]
fn file_size_is_unknown_for_compressed_and_known_for_uncompressed() {
    let compressed_derivation =
        compress_to_temp(Path::new("./tests/instances/correct/version3/rup.pbp"));
    let (_, compressed_size) = open_maybe_compressed(compressed_derivation.path())
        .expect("failed to open compressed derivation");
    assert_eq!(
        compressed_size, None,
        "compressed derivation should report an unknown file size"
    );

    let (_, uncompressed_size) =
        open_maybe_compressed("./tests/instances/correct/version3/rup.pbp")
            .expect("failed to open uncompressed derivation");
    assert!(
        uncompressed_size.is_some(),
        "uncompressed derivation should report a known file size"
    );
}

/// With `show_progress` enabled, the parser takes the "bytes read" fallback branch instead of
/// the percentage branch when the file size is unknown (see `Parser::process_rule` in
/// `veripb-parser/src/pbp_parser/parser.rs`). This must not panic when reading a compressed file.
#[test]
fn show_progress_does_not_panic_on_compressed_proof() {
    let compressed_derivation =
        compress_to_temp(Path::new("./tests/instances/correct/version3/rup.pbp"));
    let args = Args {
        formula: PathBuf::from("./tests/instances/correct/version3/rup.opb"),
        derivation: compressed_derivation.path().to_path_buf(),
        print_verification_result: false,
        show_progress: true,
        ..Default::default()
    };
    let result = veripb::run_checker(args);
    assert!(
        result.is_ok(),
        "expected compressed proof to verify, got {result:?}"
    );
}

// ── gzip (.pbp.gz) ──────────────────────────────────────────────────────────

#[test]
fn correct_version2_proof_gz_matches_uncompressed() {
    let formula = PathBuf::from("./tests/instances/correct/version2/rup.opb");
    let derivation = PathBuf::from("./tests/instances/correct/version2/rup.pbp");
    let uncompressed_result = run(formula.clone(), derivation.clone());
    let compressed = compress_to_temp_gz(&derivation);
    let compressed_result = run(formula, compressed.path().to_path_buf());
    assert_eq!(
        uncompressed_result.is_ok(),
        compressed_result.is_ok(),
        "gz/uncompressed disagreed: uncompressed={uncompressed_result:?}, gz={compressed_result:?}"
    );
}

#[test]
fn correct_version3_proof_gz_matches_uncompressed() {
    let formula = PathBuf::from("./tests/instances/correct/version3/rup.opb");
    let derivation = PathBuf::from("./tests/instances/correct/version3/rup.pbp");
    let uncompressed_result = run(formula.clone(), derivation.clone());
    let compressed = compress_to_temp_gz(&derivation);
    let compressed_result = run(formula, compressed.path().to_path_buf());
    assert_eq!(
        uncompressed_result.is_ok(),
        compressed_result.is_ok(),
        "gz/uncompressed disagreed: uncompressed={uncompressed_result:?}, gz={compressed_result:?}"
    );
}

#[test]
fn gz_proof_actually_verifies_as_correct() {
    let compressed = compress_to_temp_gz(Path::new("./tests/instances/correct/version3/rup.pbp"));
    let result = run(
        PathBuf::from("./tests/instances/correct/version3/rup.opb"),
        compressed.path().to_path_buf(),
    );
    assert!(
        result.is_ok(),
        "expected gz proof to verify, got {result:?}"
    );
}

// ── xz (.pbp.xz) ────────────────────────────────────────────────────────────

#[test]
fn correct_version2_proof_xz_matches_uncompressed() {
    let formula = PathBuf::from("./tests/instances/correct/version2/rup.opb");
    let derivation = PathBuf::from("./tests/instances/correct/version2/rup.pbp");
    let uncompressed_result = run(formula.clone(), derivation.clone());
    let compressed = compress_to_temp_xz(&derivation);
    let compressed_result = run(formula, compressed.path().to_path_buf());
    assert_eq!(
        uncompressed_result.is_ok(),
        compressed_result.is_ok(),
        "xz/uncompressed disagreed: uncompressed={uncompressed_result:?}, xz={compressed_result:?}"
    );
}

#[test]
fn correct_version3_proof_xz_matches_uncompressed() {
    let formula = PathBuf::from("./tests/instances/correct/version3/rup.opb");
    let derivation = PathBuf::from("./tests/instances/correct/version3/rup.pbp");
    let uncompressed_result = run(formula.clone(), derivation.clone());
    let compressed = compress_to_temp_xz(&derivation);
    let compressed_result = run(formula, compressed.path().to_path_buf());
    assert_eq!(
        uncompressed_result.is_ok(),
        compressed_result.is_ok(),
        "xz/uncompressed disagreed: uncompressed={uncompressed_result:?}, xz={compressed_result:?}"
    );
}

#[test]
fn xz_proof_actually_verifies_as_correct() {
    let compressed = compress_to_temp_xz(Path::new("./tests/instances/correct/version3/rup.pbp"));
    let result = run(
        PathBuf::from("./tests/instances/correct/version3/rup.opb"),
        compressed.path().to_path_buf(),
    );
    assert!(
        result.is_ok(),
        "expected xz proof to verify, got {result:?}"
    );
}
