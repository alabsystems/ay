// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration test: compile, link and run `tests/capi_optimize_consumer.c`
//! against the ay-ffi static library.
//!
//! The consumer exercises the Z3-compatible Optimize completion C API
//! (`Z3_optimize_*`) — push/pop, get_objectives, get_assertions, get_upper/lower
//! and the `_as_vector` forms, assert_and_track + get_unsat_core, from_string,
//! get_statistics, get_reason_unknown, and set_params/get_help/get_param_descrs —
//! on real optimization problems, and asserts every value equals what libz3
//! returns for the SAME problem. The SAME source compiled with `-DAY_TWIN_USE_Z3`
//! against libz3 passes the identical assertions (the cross-check); here we build
//! it against ay-ffi and require all checks to pass.

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
        "optimize consumer failed to compile against ay_z3_compat.h"
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
        "optimize consumer failed to link against libay_ffi.a:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn test_capi_optimize_consumer_compiles_links_runs() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR must be set");
    let crate_root = Path::new(&manifest_dir);
    let c_source = crate_root.join("tests/capi_optimize_consumer.c");
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
        compile_only(&header_dir, &c_source, &tmpdir.join("capi_optimize.o"));
        return;
    };

    let binary = tmpdir.join("capi_optimize_consumer");
    compile_and_link(&header_dir, &c_source, &static_lib, &binary);

    let output = Command::new(&binary)
        .output()
        .expect("failed to run optimize consumer binary");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "optimize consumer exited with error.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("optimize C consumer checks passed"),
        "optimize consumer did not report all checks passing.\nstdout: {stdout}"
    );
}
