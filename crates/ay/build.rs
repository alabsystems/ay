// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Build script: embeds build provenance into the binary. What the stamp
//! claims, and what it watches, is `build_support/provenance.rs`.

#[path = "../../build_support/provenance.rs"]
mod provenance;

include!("../../build_support/exact_provenance.rs");

use std::env;

fn main() {
    // Sentinel for dev-only CLI surface: `ay consumer-smoke` encodes the
    // private downstream repo topology and is excluded from the public
    // snapshot; every other maintainer command ships and is documented in
    // the development design notes (2026-07-21 ruling). The publish manifest denies
    // src/cmd_consumer_smoke.rs, so the exported build sees the cfg disabled.
    // Watched only while it exists: Cargo reruns a build script on every
    // build while a watched path is missing.
    println!("cargo:rustc-check-cfg=cfg(ay_internal_tools)");
    if std::path::Path::new("src/cmd_consumer_smoke.rs").is_file() {
        println!("cargo:rerun-if-changed=src/cmd_consumer_smoke.rs");
        println!("cargo:rustc-cfg=ay_internal_tools");
    }
    validate_exact_binary_provenance_env();
    let provenance = provenance::emit_build_provenance();
    let profile = env::var("PROFILE").unwrap_or_else(|_| "unknown".to_string());

    // Legacy exports retained for existing feature-report consumers.
    println!("cargo:rustc-env=AY_GIT_HASH={}", provenance.commit);
    println!("cargo:rustc-env=AY_BUILD_DATE={}", provenance.datetime_utc);
    println!(
        "cargo:rustc-env=AY_COMMIT_COUNT={}",
        provenance.build_increment
    );
    println!("cargo:rustc-env=AY_BUILD_PROFILE={profile}");
}
