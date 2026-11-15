// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::env;
use std::path::PathBuf;
use std::process::Command;

use super::native_link::find_static_lib;

#[test]
fn exact_z3_500_remaining_safe_calls_compile_link_and_run() {
    let crate_root =
        PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("manifest directory available"));
    let source = crate_root.join("tests/capi_z3_500_remaining_consumer.c");
    let include = crate_root.join("include");
    let temporary = env::temp_dir().join(format!("ay_z3_500_remaining_{}", std::process::id()));
    std::fs::create_dir_all(&temporary).expect("create remaining-probe temporary directory");
    let object = temporary.join("remaining.o");

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
        "remaining Z3 5.0.0 probes did not compile"
    );

    let static_lib = find_static_lib()
        .expect("libay_ffi.a is required for the remaining Z3 5.0.0 safe-call probes");
    let binary = temporary.join("remaining");
    let mut command = Command::new("cc");
    command
        .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-I"])
        .arg(&include)
        .arg(&source)
        .arg(&static_lib)
        .arg("-o")
        .arg(&binary);
    if cfg!(target_os = "linux") {
        command.arg("-ldl");
    }
    super::native_link::add_native_libraries(&mut command);
    let link = command.output().expect("link remaining Z3 5.0.0 probes");
    assert!(
        link.status.success(),
        "remaining Z3 5.0.0 probes did not link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&binary)
        .arg("--static")
        .output()
        .expect("run remaining Z3 5.0.0 probes");
    assert!(
        run.status.success(),
        "remaining Z3 5.0.0 probes failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    std::fs::remove_dir_all(&temporary).expect("remove remaining-probe temporary directory");
}
