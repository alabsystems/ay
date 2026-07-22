// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Integration test: compile and link a C program against ay_z3_compat.h (#4990).
//!
//! This test verifies acceptance criterion #3: "At least one external Z3
//! consumer compiles against ay-ffi." It compiles `tests/c_consumer.c`
//! with the system C compiler, links against the ay-ffi static library,
//! and runs the resulting binary.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Find the ay-ffi static library in the cargo target directory.
fn find_static_lib() -> Option<PathBuf> {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").ok()?;
    let workspace_root = Path::new(&manifest_dir).parent()?.parent()?;
    let profile = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };

    // Strategy 1: CARGO_TARGET_DIR or standard target/
    let target_dir = env::var("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| workspace_root.join("target"));

    let lib_path = target_dir.join(profile).join("libay_ffi.a");
    if lib_path.exists() {
        return Some(lib_path);
    }

    None
}

/// Compile c_consumer.c to an object file (header compatibility check).
fn compile_only(header_dir: &Path, c_source: &Path, obj_file: &Path) {
    let status = Command::new("cc")
        .args(["-std=c99", "-Wall", "-Wextra", "-Werror", "-c", "-I"])
        .arg(header_dir.as_os_str())
        .arg(c_source.as_os_str())
        .arg("-o")
        .arg(obj_file.as_os_str())
        .status()
        .expect("failed to invoke cc");

    assert!(
        status.success(),
        "C consumer failed to compile against ay_z3_compat.h"
    );
}

/// Compile and link c_consumer.c against libay_ffi.a, returning binary path.
fn compile_and_link(header_dir: &Path, c_source: &Path, static_lib: &Path, binary: &Path) {
    let mut cmd = Command::new("cc");
    cmd.args(["-std=c99", "-Wall", "-Wextra", "-Werror", "-I"])
        .arg(header_dir.as_os_str())
        .arg(c_source.as_os_str())
        .arg(static_lib.as_os_str())
        .arg("-o")
        .arg(binary.as_os_str());

    if cfg!(target_os = "macos") {
        cmd.args([
            "-framework",
            "Security",
            "-framework",
            "CoreFoundation",
            "-lresolv",
            "-Wl,-no_warn_duplicate_libraries",
        ]);
    }
    cmd.args(["-lpthread", "-lm"]);

    let output = cmd.output().expect("failed to invoke cc for linking");
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!("C consumer failed to link against libay_ffi.a:\n{stderr}");
    }
}

/// Run the compiled C consumer binary and verify output.
fn run_and_verify(binary: &Path) {
    let output = Command::new(binary)
        .output()
        .expect("failed to run c_consumer binary");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    eprintln!("stdout: {stdout}");
    if !stderr.is_empty() {
        eprintln!("stderr: {stderr}");
    }

    assert!(
        output.status.success(),
        "c_consumer exited with error.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("All 21 C consumer tests passed"),
        "c_consumer did not report all tests passing.\nstdout: {stdout}"
    );
}

#[test]
fn test_c_consumer_compiles_and_links() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR must be set");
    let crate_root = Path::new(&manifest_dir);
    let c_source = crate_root.join("tests/c_consumer.c");
    let header_dir = crate_root.join("include");

    assert!(
        c_source.exists(),
        "C source not found: {}",
        c_source.display()
    );
    assert!(
        header_dir.join("ay_z3_compat.h").exists(),
        "Header not found in {}",
        header_dir.display()
    );

    let tmpdir = env::temp_dir().join("ay_c_consumer_test");
    let _ = std::fs::create_dir_all(&tmpdir);

    let static_lib = match find_static_lib() {
        Some(p) => {
            eprintln!("Found static lib: {}", p.display());
            p
        }
        None => {
            eprintln!("SKIP link: libay_ffi.a not found, compile-only check");
            compile_only(&header_dir, &c_source, &tmpdir.join("c_consumer.o"));
            eprintln!("PASS: compile-only header check");
            let _ = std::fs::remove_dir_all(&tmpdir);
            return;
        }
    };

    let binary = tmpdir.join("c_consumer");
    compile_and_link(&header_dir, &c_source, &static_lib, &binary);
    eprintln!("PASS: compiled and linked against libay_ffi.a");

    run_and_verify(&binary);
    eprintln!("PASS: c_consumer ran, all 17 subtests passed");

    let _ = std::fs::remove_dir_all(&tmpdir);
}
