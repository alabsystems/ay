// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration test: compile, link and run
//! `tests/capi_model_validity_consumer.c` against the ay-ffi static library.
//!
//! The consumer pins that `Z3_solver_check` never publishes `sat` with a model
//! that violates the solver's own assertions (`Z3_mk_power` goals, an
//! irrational algebraic model), answers `unknown` with a reason for an
//! unsupported power, and that each solver's model lists exactly the symbols
//! of its own goal (no constants from sibling solvers of the same context),
//! across push/pop and check-with-assumptions.

use std::env;
use std::path::Path;
use std::process::Command;

use super::native_link::find_static_lib;

/// Compile the consumer to an object file only (header compatibility check).
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
        "model-validity consumer failed to compile against ay_z3_compat.h"
    );
}

/// Compile and link the consumer against libay_ffi.a.
fn compile_and_link(header_dir: &Path, c_source: &Path, static_lib: &Path, binary: &Path) {
    let mut cmd = Command::new("cc");
    cmd.args(["-std=c99", "-Wall", "-Wextra", "-Werror", "-I"])
        .arg(header_dir.as_os_str())
        .arg(c_source.as_os_str())
        .arg(static_lib.as_os_str())
        .arg("-o")
        .arg(binary.as_os_str());
    super::native_link::add_native_libraries(&mut cmd);
    let output = cmd.output().expect("failed to invoke cc for linking");
    assert!(
        output.status.success(),
        "model-validity consumer failed to link against libay_ffi.a:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn test_capi_model_validity_consumer_compiles_links_runs() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR must be set");
    let crate_root = Path::new(&manifest_dir);
    let c_source = crate_root.join("tests/capi_model_validity_consumer.c");
    let header_dir = crate_root.join("include");
    assert!(
        c_source.exists(),
        "C source not found: {}",
        c_source.display()
    );

    let temporary = tempfile::tempdir().expect("create isolated consumer directory");
    let tmpdir = temporary.path();

    let Some(static_lib) = find_static_lib() else {
        eprintln!("SKIP link: libay_ffi.a not found, compile-only check");
        compile_only(
            &header_dir,
            &c_source,
            &tmpdir.join("capi_model_validity.o"),
        );
        return;
    };

    let binary = tmpdir.join("capi_model_validity_consumer");
    compile_and_link(&header_dir, &c_source, &static_lib, &binary);

    let output = Command::new(&binary)
        .output()
        .expect("failed to run model-validity consumer binary");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "model-validity consumer exited with error.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("model validity consumer tests passed"),
        "model-validity consumer did not report all checks passing.\nstdout: {stdout}"
    );
}
