// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::env;
use std::path::PathBuf;
use std::process::Command;

use super::native_link::find_static_lib;

#[test]
fn test_capi_finite_set_consumer_compiles_links_runs() {
    run_consumer("finite_set", "finite-set consumer tests passed");
}

#[test]
fn test_capi_clause_trail_consumer_compiles_links_runs() {
    run_consumer("clause_trail", "clause-trail entries=");
}

fn run_consumer(name: &str, expected: &str) {
    let crate_root =
        PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("manifest directory available"));
    let source = crate_root.join(format!("tests/capi_{name}_consumer.c"));
    let include = crate_root.join("include");
    let temporary = env::temp_dir().join(format!("ay_capi_{name}_test_{}", std::process::id()));
    std::fs::create_dir_all(&temporary).expect("create C consumer temporary directory");
    let object = temporary.join("consumer.o");

    let compile = Command::new("cc")
        .args(["-std=c99", "-Wall", "-Wextra", "-Werror", "-c", "-I"])
        .arg(&include)
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .status()
        .expect("invoke C compiler");
    assert!(compile.success(), "C header consumer did not compile");

    let static_lib = find_static_lib()
        .expect("libay_ffi.a is required for the C compile/link/run compatibility gate");
    let binary = temporary.join("consumer");
    let mut command = Command::new("cc");
    command
        .args(["-std=c99", "-Wall", "-Wextra", "-Werror", "-I"])
        .arg(&include)
        .arg(&source)
        .arg(&static_lib)
        .arg("-o")
        .arg(&binary);
    super::native_link::add_native_libraries(&mut command);
    let link = command.output().expect("link C consumer");
    assert!(
        link.status.success(),
        "C consumer did not link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&binary).output().expect("run C consumer");
    assert!(
        run.status.success(),
        "C consumer failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(String::from_utf8_lossy(&run.stdout).contains(expected));
    let _ = std::fs::remove_dir_all(&temporary);
}
