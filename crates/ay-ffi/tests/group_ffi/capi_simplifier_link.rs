// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration test: compile, link and run `tests/capi_simplifier_consumer.c`
//! against the ay-ffi static library.
//!
//! The consumer exercises the Z3-compatible simplifier C API (`Z3_mk_simplifier`,
//! `Z3_simplifier_inc_ref`/`_dec_ref`/`_and_then`/`_using_params`/`_get_descr`/
//! `_get_help`/`_get_param_descrs`, plus `Z3_solver_add_simplifier`). It builds a
//! `solve-eqs` and_then `propagate-values` simplifier, ATTACHES it to a solver,
//! asserts a formula, and confirms the verdict is PRESERVED — equal to both the
//! plain-solver verdict and what libz3 returns for the same goal+simplifier. The
//! SAME source compiled with `-DAY_TWIN_USE_Z3 -lz3` against libz3 passes the
//! shared subset of those assertions (the cross-check); here we build it against
//! ay-ffi and require all checks to pass.

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
    lib_path.exists().then_some(lib_path)
}

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
        "simplifier consumer failed to compile against ay_z3_compat.h"
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
    assert!(
        output.status.success(),
        "simplifier consumer failed to link against libay_ffi.a:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn test_capi_simplifier_consumer_compiles_links_runs() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR must be set");
    let crate_root = Path::new(&manifest_dir);
    let c_source = crate_root.join("tests/capi_simplifier_consumer.c");
    let header_dir = crate_root.join("include");
    assert!(
        c_source.exists(),
        "C source not found: {}",
        c_source.display()
    );

    let tmpdir = env::temp_dir().join("ay_capi_simplifier_test");
    let _ = std::fs::create_dir_all(&tmpdir);

    let Some(static_lib) = find_static_lib() else {
        eprintln!("SKIP link: libay_ffi.a not found, compile-only check");
        compile_only(&header_dir, &c_source, &tmpdir.join("capi_simplifier.o"));
        let _ = std::fs::remove_dir_all(&tmpdir);
        return;
    };

    let binary = tmpdir.join("capi_simplifier_consumer");
    compile_and_link(&header_dir, &c_source, &static_lib, &binary);

    let output = Command::new(&binary)
        .output()
        .expect("failed to run simplifier consumer binary");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "simplifier consumer exited with error.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("simplifier C consumer checks passed"),
        "simplifier consumer did not report all checks passing.\nstdout: {stdout}"
    );

    let _ = std::fs::remove_dir_all(&tmpdir);
}
