// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration test: compile, link and run `tests/capi_quantifier_meta_consumer.c`
//! against the ay-ffi static library.
//!
//! The consumer exercises Group B introspection: quantifier metadata
//! (`Z3_get_quantifier_id`/`Z3_get_quantifier_skolem_id`), pattern getters
//! (`Z3_get_pattern_num_terms`/`Z3_get_pattern`), `Z3_get_depth`, the
//! tactic/simplifier registry enumerators (`Z3_get_num_tactics`/
//! `Z3_get_tactic_name`/`Z3_get_num_simplifiers`/`Z3_get_simplifier_name`),
//! and `Z3_is_as_array`/`Z3_get_as_array_func_decl`. It builds a
//! ForAll-with-pattern, round-trips the pattern terms, asserts exact depths of
//! nested ground terms, enumerates both registries (every name buildable;
//! shared names present), and checks the honest as-array answers. The SAME
//! source compiled with `-DAY_TWIN_USE_Z3 -lz3` against libz3 passes the
//! shared subset of those assertions (the cross-check); here we build it
//! against ay-ffi and require all checks to pass.

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

/// The registry sizes the consumer pins, taken live from the Rust constants that
/// back `Z3_get_num_tactics` / `Z3_get_num_simplifiers`. Injecting them as `-D`
/// defines keeps the C-side expectation exactly in lock-step with the registries:
/// a hard-coded count silently drifted (13 → 17) and broke this consumer.
fn registry_defines() -> [String; 2] {
    [
        format!(
            "-DAY_EXPECTED_TACTICS={}",
            ay_frontend::SUPPORTED_TACTIC_NAMES.len()
        ),
        format!(
            "-DAY_EXPECTED_SIMPLIFIERS={}",
            ay_ffi::z3_compat::SUPPORTED_SIMPLIFIER_NAMES.len()
        ),
    ]
}

/// Compile the consumer to an object file only (header compatibility check).
fn compile_only(header_dir: &Path, c_source: &Path, obj_file: &Path) {
    let status = Command::new("cc")
        .args(["-std=c99", "-Wall", "-Wextra", "-Werror", "-c", "-I"])
        .arg(header_dir.as_os_str())
        .args(registry_defines())
        .arg(c_source.as_os_str())
        .arg("-o")
        .arg(obj_file.as_os_str())
        .status()
        .expect("failed to invoke cc");
    assert!(
        status.success(),
        "quantifier_meta consumer failed to compile against ay_z3_compat.h"
    );
}

/// Compile and link the consumer against libay_ffi.a.
fn compile_and_link(header_dir: &Path, c_source: &Path, static_lib: &Path, binary: &Path) {
    let mut cmd = Command::new("cc");
    cmd.args(["-std=c99", "-Wall", "-Wextra", "-Werror", "-I"])
        .arg(header_dir.as_os_str())
        .args(registry_defines())
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
        "quantifier_meta consumer failed to link against libay_ffi.a:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn test_capi_quantifier_meta_consumer_compiles_links_runs() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR must be set");
    let crate_root = Path::new(&manifest_dir);
    let c_source = crate_root.join("tests/capi_quantifier_meta_consumer.c");
    let header_dir = crate_root.join("include");
    assert!(
        c_source.exists(),
        "C source not found: {}",
        c_source.display()
    );

    let tmpdir = env::temp_dir().join("ay_capi_quantifier_meta_test");
    let _ = std::fs::create_dir_all(&tmpdir);

    let Some(static_lib) = find_static_lib() else {
        eprintln!("SKIP link: libay_ffi.a not found, compile-only check");
        compile_only(
            &header_dir,
            &c_source,
            &tmpdir.join("capi_quantifier_meta.o"),
        );
        let _ = std::fs::remove_dir_all(&tmpdir);
        return;
    };

    let binary = tmpdir.join("capi_quantifier_meta_consumer");
    compile_and_link(&header_dir, &c_source, &static_lib, &binary);

    let output = Command::new(&binary)
        .output()
        .expect("failed to run quantifier_meta consumer binary");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "quantifier_meta consumer exited with error.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("quantifier-meta C consumer checks passed"),
        "quantifier_meta consumer did not report all checks passing.\nstdout: {stdout}"
    );

    let _ = std::fs::remove_dir_all(&tmpdir);
}
