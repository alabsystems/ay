// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Build script: embeds build provenance into ay-dpll.
//!
//! This keeps the executor's SMT-LIB `get-info :version` surface aligned with
//! the CLI build provenance contract without requiring the outer `ay` crate.

include!("../../build_support/provenance.rs");

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=../../build_support/provenance.rs");
    println!("cargo:rerun-if-env-changed=SOURCE_DATE_EPOCH");
    println!("cargo:rerun-if-env-changed=AY_SOURCE_GIT_COMMIT");
    println!("cargo:rerun-if-env-changed=AY_SOURCE_GIT_COMMIT_SHORT");
    println!("cargo:rerun-if-env-changed=AY_SOURCE_GIT_DIRTY");
    emit_git_rerun_paths();
    emit_repo_dirty_rerun_paths();

    let version = env::var("CARGO_PKG_VERSION").unwrap_or_else(|_| "unknown".to_string());
    let provenance = compute_build_provenance(&version);

    println!(
        "cargo:rustc-env=AY_BUILD_INCREMENT={}",
        provenance.build_increment
    );
    println!("cargo:rustc-env=AY_BUILD_COMMIT={}", provenance.commit);
    println!(
        "cargo:rustc-env=AY_BUILD_DATETIME_UTC={}",
        provenance.datetime_utc
    );
    println!("cargo:rustc-env=AY_BUILD_STAMP={}", provenance.stamp);
}
