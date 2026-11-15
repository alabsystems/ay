// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native libraries shared by the C and C++ FFI consumers.

use sha2::{Digest, Sha256};
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process::Command;

/// Native landing supplies the exact compiler-artifact and its observed bytes.
/// A missing/corrupt bound artifact is an error, never compile-only coverage.
pub(super) fn find_static_lib() -> Option<PathBuf> {
    match (
        std::env::var_os("AY_FFI_STATIC_LIBRARY"),
        std::env::var_os("AY_FFI_STATIC_LIBRARY_SHA256"),
    ) {
        (Some(path), Some(digest)) => Some(
            verify_library(
                Path::new(&path),
                digest.to_str().expect("native library hash is UTF-8"),
            )
            .expect("produced native library binding refused"),
        ),
        (None, None) => {
            // Preserve ordinary developer compile-only behavior when no native
            // landing owns a library. These are fixed public output aliases.
            let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent()?.parent()?;
            let target = std::env::var_os("CARGO_TARGET_DIR")
                .map(PathBuf::from)
                .unwrap_or_else(|| root.join("target"));
            let profile = if cfg!(debug_assertions) {
                "debug"
            } else {
                "release"
            };
            [
                target.join(profile).join("libay_ffi.a"),
                target.join(profile).join("deps/libay_ffi.a"),
            ]
            .into_iter()
            .find(|p| p.is_file())
        }
        _ => panic!("incomplete native FFI artifact binding"),
    }
}

fn verify_library(path: &Path, digest: &str) -> io::Result<PathBuf> {
    if digest.len() != 64
        || !digest
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
    {
        return Err(io::Error::other("invalid native artifact hash"));
    }
    let mut file = std::fs::File::open(path)?;
    if !file.metadata()?.is_file() {
        return Err(io::Error::other("native artifact is not a regular file"));
    }
    let mut hash = Sha256::new();
    let mut buffer = [0u8; 65536];
    loop {
        let n = file.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        hash.update(&buffer[..n]);
    }
    if format!("{:x}", hash.finalize()) != digest {
        return Err(io::Error::other("native artifact bytes changed"));
    }
    Ok(path.to_path_buf())
}

#[test]
fn native_library_binding_refuses_changed_and_invalid_outputs() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("library.a");
    std::fs::write(&path, b"original compiler output").unwrap();
    let digest = format!("{:x}", Sha256::digest(b"original compiler output"));
    assert_eq!(verify_library(&path, &digest).unwrap(), path);
    std::fs::write(&path, b"changed compiler output").unwrap();
    assert!(verify_library(&path, &digest).is_err());
    assert!(verify_library(&path, "not-a-hash").is_err());
    std::fs::remove_file(&path).unwrap();
    assert!(verify_library(&path, &digest).is_err());
}

/// Append AY's platform libraries after the caller's existing link arguments.
pub(super) fn add_native_libraries(command: &mut Command) {
    if cfg!(target_os = "macos") {
        // Measured by Trust's native-static-libs print for the normal AY 0.28.0
        // staticlib on Apple silicon. Preserve that order; C++ runtime selection
        // remains with the caller.
        command.args(["-lsandbox", "-liconv", "-lSystem", "-lc", "-lm"]);
    } else {
        command.args(["-lpthread", "-lm"]);
    }
}
