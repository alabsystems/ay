// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Integration test: compile, link and run the Z3_func_interp_*/Z3_func_entry_*
//! + Z3_model_* completion C consumer against ay_z3_compat.h + libay_ffi.
//!
//! `tests/capi_func_interp_consumer.c` solves a real UF query, reads a
//! function's interpretation (entries + else) from the model, translates the
//! model into a second context, and reads an uninterpreted sort's universe.
//! The SAME source is cross-checked against libz3 out-of-band (see the file's
//! header); here it must build and pass against ay.

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
    let target_dir = env::var("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| workspace_root.join("target"));
    let lib_path = target_dir.join(profile).join("libay_ffi.a");
    if lib_path.exists() {
        return Some(lib_path);
    }
    None
}

/// Compile-only header check (used when the static lib is not present).
fn compile_only(header_dir: &Path, c_source: &Path, obj_file: &Path) {
    let status = Command::new("cc")
        .args([
            "-std=c99", "-Wall", "-Wextra", "-Werror", "-DUSE_AY", "-c", "-I",
        ])
        .arg(header_dir.as_os_str())
        .arg(c_source.as_os_str())
        .arg("-o")
        .arg(obj_file.as_os_str())
        .status()
        .expect("failed to invoke cc");
    assert!(
        status.success(),
        "func_interp C consumer failed to compile against ay_z3_compat.h"
    );
}

/// Compile and link the consumer against libay_ffi.a.
fn compile_and_link(header_dir: &Path, c_source: &Path, static_lib: &Path, binary: &Path) {
    let mut cmd = Command::new("cc");
    cmd.args(["-std=c99", "-Wall", "-Wextra", "-Werror", "-DUSE_AY", "-I"])
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
        panic!("func_interp C consumer failed to link against libay_ffi.a:\n{stderr}");
    }
}

fn run_and_verify(binary: &Path) {
    let output = Command::new(binary)
        .output()
        .expect("failed to run func_interp consumer binary");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    eprintln!("stdout: {stdout}");
    if !stderr.is_empty() {
        eprintln!("stderr: {stderr}");
    }
    assert!(
        output.status.success(),
        "func_interp consumer exited with error.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("All 3 func_interp consumer tests passed"),
        "func_interp consumer did not report all tests passing.\nstdout: {stdout}"
    );
}

#[test]
fn test_capi_func_interp_consumer_compiles_links_runs() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR must be set");
    let crate_root = Path::new(&manifest_dir);
    let c_source = crate_root.join("tests/capi_func_interp_consumer.c");
    let header_dir = crate_root.join("include");
    assert!(
        c_source.exists(),
        "C source not found: {}",
        c_source.display()
    );

    let tmpdir = env::temp_dir().join("ay_capi_func_interp_test");
    let _ = std::fs::create_dir_all(&tmpdir);

    let static_lib = match find_static_lib() {
        Some(p) => p,
        None => {
            eprintln!("SKIP link: libay_ffi.a not found, compile-only check");
            compile_only(&header_dir, &c_source, &tmpdir.join("capi_func_interp.o"));
            let _ = std::fs::remove_dir_all(&tmpdir);
            return;
        }
    };

    let binary = tmpdir.join("capi_func_interp_consumer");
    compile_and_link(&header_dir, &c_source, &static_lib, &binary);
    run_and_verify(&binary);
    let _ = std::fs::remove_dir_all(&tmpdir);
}
