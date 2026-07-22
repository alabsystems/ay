// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test-only helper for `.xz` benchmark fixtures.
//!
//! Several fixture tests decompress committed `.xz` SAT benchmarks by shelling
//! out to the system `xz` tool. When `xz` is not installed those tests used to
//! fail with a cryptic `No such file or directory (os error 2)` spawn error.
//!
//! [`decompress_repo_xz`] distinguishes the three cases for explicitly
//! optional test lanes:
//!  - tool missing  -> return `None` with a clear, actionable skip notice, so
//!    the test degrades to a no-op skip (keeps the suite runnable with plain
//!    `cargo` and no machine-local tools — see `.cargo/config.toml`);
//!  - tracked fixture genuinely absent, or decompression fails -> panic, since
//!    that is a real repository/data problem rather than a missing optional dep.
//!
//! Required regression lanes use [`decompress_required_xz_path`] or
//! [`decompress_required_repo_xz`]; those also treat a missing `xz` executable
//! as a fatal unsatisfied test prerequisite and can never silently skip.

use std::path::Path;
use std::process::Command;

/// Decompress an already-resolved `.xz` file to raw bytes by shelling out to
/// the system `xz` tool.
///
/// Returns `None` (after printing an actionable skip notice) when `xz` is not
/// installed, so callers can skip the enclosing test (`?` / early return).
/// Panics if `xz` runs but exits non-zero — a real decompression failure.
pub(crate) fn decompress_xz_path(path: &Path) -> Option<Vec<u8>> {
    match Command::new("xz").arg("-dc").arg(path).output() {
        Ok(output) => {
            assert!(
                output.status.success(),
                "xz -dc failed for {}: {}",
                path.display(),
                String::from_utf8_lossy(&output.stderr)
            );
            Some(output.stdout)
        }
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            eprintln!(
                "SKIP: system `xz` tool not found on PATH — skipping `.xz` fixture {}. \
                 Install it (`brew install xz` on macOS, `apt-get install xz-utils` on \
                 Debian/Ubuntu) to run this test.",
                path.display()
            );
            None
        }
        Err(err) => panic!("failed to spawn `xz` for {}: {err}", path.display()),
    }
}

/// Decompress a required tracked `.xz` fixture, failing on every unavailable
/// or invalid input instead of turning the regression into a no-op.
pub(crate) fn decompress_required_xz_path(path: &Path) -> Vec<u8> {
    assert!(
        path.is_file(),
        "required tracked .xz fixture missing: {}",
        path.display()
    );
    decompress_xz_path(path).unwrap_or_else(|| {
        panic!(
            "system `xz` is required to run tracked fixture regression {}",
            path.display()
        )
    })
}

/// Decompress a repository-root-relative `.xz` fixture to a `String`.
///
/// Returns `None` (after printing a skip notice) when the system `xz` tool is
/// not on `PATH`. Panics if the tracked fixture is missing, if `xz` runs but
/// exits non-zero, or if the output is not UTF-8 — all real failures.
pub(crate) fn decompress_repo_xz(repo_root_relative: &str) -> Option<String> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(repo_root_relative);
    assert!(
        path.is_file(),
        "tracked .xz fixture missing from repository: {repo_root_relative} (looked at {})",
        path.display()
    );
    let bytes = decompress_xz_path(&path)?;
    Some(
        String::from_utf8(bytes)
            .unwrap_or_else(|err| panic!("{repo_root_relative} is not UTF-8 DIMACS: {err}")),
    )
}

/// Decompress a required repository-root-relative `.xz` fixture to UTF-8.
pub(crate) fn decompress_required_repo_xz(repo_root_relative: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(repo_root_relative);
    let bytes = decompress_required_xz_path(&path);
    String::from_utf8(bytes)
        .unwrap_or_else(|err| panic!("{repo_root_relative} is not UTF-8 DIMACS: {err}"))
}
