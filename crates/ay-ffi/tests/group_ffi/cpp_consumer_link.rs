// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Integration test: compile and link a C++ program against the header-only
//! C++ wrapper `bindings/cpp/ay.hpp` (over AY's Z3-compatible C API).
//!
//! This is the C++ analogue of `c_consumer_link.rs`. It compiles
//! `bindings/cpp/cpp_consumer.cpp` with the system C++ compiler (clang++),
//! links against the ay-ffi static library, runs the binary, and verifies the
//! C++ wrapper produces the correct SAT/UNSAT verdicts (z3-cross-checked).
//!
//! If the static lib is not present (e.g. a `cargo test` that did not build the
//! staticlib artifact), it falls back to a compile-only header check so the
//! wrapper's C++ correctness is still exercised.

use std::env;
use std::path::Path;
use std::process::Command;

use super::native_link::find_static_lib;

/// Pick a C++ compiler: $CXX if set, else clang++ (always present on macOS),
/// else c++.
fn cxx() -> String {
    if let Ok(cxx) = env::var("CXX") {
        if !cxx.is_empty() {
            return cxx;
        }
    }
    if cfg!(target_os = "macos") {
        "clang++".to_string()
    } else {
        "c++".to_string()
    }
}

/// Compile cpp_consumer.cpp to an object file (header compatibility check).
fn compile_only(header_dir: &Path, cpp_dir: &Path, src: &Path, obj: &Path) {
    let status = Command::new(cxx())
        .args(["-std=c++17", "-Wall", "-Wextra", "-Werror", "-c", "-I"])
        .arg(header_dir.as_os_str())
        .arg("-I")
        .arg(cpp_dir.as_os_str())
        .arg(src.as_os_str())
        .arg("-o")
        .arg(obj.as_os_str())
        .status()
        .expect("failed to invoke C++ compiler");

    assert!(
        status.success(),
        "C++ consumer failed to compile against ay.hpp"
    );
}

/// Compile and link cpp_consumer.cpp against libay_ffi.a, producing a binary.
fn compile_and_link(
    header_dir: &Path,
    cpp_dir: &Path,
    src: &Path,
    static_lib: &Path,
    binary: &Path,
) {
    let mut cmd = Command::new(cxx());
    cmd.args(["-std=c++17", "-Wall", "-Wextra", "-Werror", "-I"])
        .arg(header_dir.as_os_str())
        .arg("-I")
        .arg(cpp_dir.as_os_str())
        .arg(src.as_os_str())
        .arg(static_lib.as_os_str())
        .arg("-o")
        .arg(binary.as_os_str());

    if cfg!(target_os = "linux") {
        cmd.arg("-ldl");
    }
    super::native_link::add_native_libraries(&mut cmd);

    let output = cmd
        .output()
        .expect("failed to invoke C++ compiler for linking");
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!("C++ consumer failed to link against libay_ffi.a:\n{stderr}");
    }
}

/// Run the compiled C++ consumer binary and verify output.
fn run_and_verify(binary: &Path) {
    let output = Command::new(binary)
        .output()
        .expect("failed to run cpp_consumer binary");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    eprintln!("stdout: {stdout}");
    if !stderr.is_empty() {
        eprintln!("stderr: {stderr}");
    }

    assert!(
        output.status.success(),
        "cpp_consumer exited with error.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("All 10 C++ consumer tests passed"),
        "cpp_consumer did not report all tests passing.\nstdout: {stdout}"
    );
}

#[test]
fn test_cpp_consumer_compiles_and_links() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR must be set");
    let crate_root = Path::new(&manifest_dir);
    let workspace_root = crate_root
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");

    let cpp_dir = workspace_root.join("bindings/cpp");
    let cpp_source = cpp_dir.join("cpp_consumer.cpp");
    let header_dir = crate_root.join("include");

    assert!(
        cpp_source.exists(),
        "C++ source not found: {}",
        cpp_source.display()
    );
    assert!(
        cpp_dir.join("ay.hpp").exists(),
        "ay.hpp not found in {}",
        cpp_dir.display()
    );

    let temporary = tempfile::tempdir().expect("create isolated consumer directory");
    let tmpdir = temporary.path();

    let static_lib = match find_static_lib() {
        Some(p) => {
            eprintln!("Found static lib: {}", p.display());
            p
        }
        None => {
            eprintln!("SKIP link: libay_ffi.a not found, compile-only check");
            compile_only(
                &header_dir,
                &cpp_dir,
                &cpp_source,
                &tmpdir.join("cpp_consumer.o"),
            );
            eprintln!("PASS: compile-only header check");
            return;
        }
    };

    let binary = tmpdir.join("cpp_consumer");
    compile_and_link(&header_dir, &cpp_dir, &cpp_source, &static_lib, &binary);
    eprintln!("PASS: compiled and linked ay.hpp consumer against libay_ffi.a");

    run_and_verify(&binary);
    eprintln!("PASS: cpp_consumer ran, all 10 subtests passed");
}
