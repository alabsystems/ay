// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compile and link all 805 exact Z3 5.0.0 public C declarations against AY.

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
fn exact_z3_500_typed_surface_compiles_links_and_resolves() {
    let crate_root =
        PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("manifest directory available"));
    let source = crate_root.join("tests/z3_500_typed_surface.c");
    let include = crate_root.join("include");
    let temporary = env::temp_dir().join(format!("ay_z3_500_typed_surface_{}", std::process::id()));
    std::fs::create_dir_all(&temporary).expect("create typed-surface temporary directory");
    let object = temporary.join("z3_500_typed_surface.o");

    let compile = Command::new("cc")
        .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-c", "-I"])
        .arg(&include)
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .status()
        .expect("invoke C compiler");
    assert!(
        compile.success(),
        "exact Z3 5.0.0 typed C surface did not compile"
    );

    let static_lib =
        find_static_lib().expect("libay_ffi.a is required for the exact Z3 5.0.0 typed link gate");
    let binary = temporary.join("z3_500_typed_surface");
    let mut command = Command::new("cc");
    command
        .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-I"])
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
    let link = command.output().expect("link exact typed C surface");
    assert!(
        link.status.success(),
        "exact Z3 5.0.0 typed C surface did not link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&binary)
        .output()
        .expect("run exact typed C surface resolver");
    assert!(
        run.status.success(),
        "exact Z3 5.0.0 typed C surface did not resolve all declarations:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    std::fs::remove_dir_all(&temporary).expect("remove typed-surface temporary directory");
}
