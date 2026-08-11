// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

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
    let profile_dir = target_dir.join(profile);
    [
        profile_dir.join("deps").join("libay_ffi.a"),
        profile_dir.join("libay_ffi.a"),
    ]
    .into_iter()
    .find(|library| library.exists())
}

#[test]
fn test_capi_finite_set_consumer_compiles_links_runs() {
    let crate_root =
        PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("manifest directory available"));
    let source = crate_root.join("tests/capi_finite_set_consumer.c");
    let include = crate_root.join("include");
    let temporary = env::temp_dir().join("ay_capi_finite_set_test");
    std::fs::create_dir_all(&temporary).expect("create C consumer temporary directory");
    let object = temporary.join("finite_set.o");

    let compile = Command::new("cc")
        .args(["-std=c99", "-Wall", "-Wextra", "-Werror", "-c", "-I"])
        .arg(&include)
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .status()
        .expect("invoke C compiler");
    assert!(
        compile.success(),
        "finite-set C header consumer did not compile"
    );

    let static_lib = find_static_lib()
        .expect("libay_ffi.a is required for the finite-set C compile/link/run compatibility gate");
    let binary = temporary.join("finite_set_consumer");
    let mut command = Command::new("cc");
    command
        .args(["-std=c99", "-Wall", "-Wextra", "-Werror", "-I"])
        .arg(&include)
        .arg(&source)
        .arg(&static_lib)
        .arg("-o")
        .arg(&binary);
    if cfg!(target_os = "macos") {
        command.args([
            "-framework",
            "Security",
            "-framework",
            "CoreFoundation",
            "-lresolv",
            "-Wl,-no_warn_duplicate_libraries",
        ]);
    }
    command.args(["-lpthread", "-lm"]);
    let link = command.output().expect("link finite-set C consumer");
    assert!(
        link.status.success(),
        "finite-set C consumer did not link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&binary)
        .output()
        .expect("run finite-set C consumer");
    assert!(
        run.status.success(),
        "finite-set C consumer failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(String::from_utf8_lossy(&run.stdout).contains("finite-set consumer tests passed"));
    let _ = std::fs::remove_dir_all(&temporary);
}
