// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Build script: embeds build provenance into the binary.

include!("../../build_support/provenance.rs");
include!("../../build_support/exact_provenance.rs");

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    // Sentinel for dev-only CLI surface: `ay consumer-smoke` encodes the
    // private downstream repo topology and is excluded from the public
    // snapshot; every other maintainer command ships and is documented in
    // the development design notes (2026-07-21 ruling). The publish manifest denies
    // src/cmd_consumer_smoke.rs, so the exported build sees the cfg disabled.
    println!("cargo:rerun-if-changed=src/cmd_consumer_smoke.rs");
    println!("cargo:rustc-check-cfg=cfg(ay_internal_tools)");
    if std::path::Path::new("src/cmd_consumer_smoke.rs").is_file() {
        println!("cargo:rustc-cfg=ay_internal_tools");
    }
    println!("cargo:rerun-if-changed=../../build_support/provenance.rs");
    println!("cargo:rerun-if-env-changed=SOURCE_DATE_EPOCH");
    println!("cargo:rerun-if-env-changed=AY_SOURCE_GIT_COMMIT");
    println!("cargo:rerun-if-env-changed=AY_SOURCE_GIT_COMMIT_SHORT");
    println!("cargo:rerun-if-env-changed=AY_SOURCE_GIT_DIRTY");
    validate_exact_binary_provenance_env();
    emit_git_rerun_paths();
    emit_repo_dirty_rerun_paths();

    let version = env::var("CARGO_PKG_VERSION").unwrap_or_else(|_| "unknown".to_string());
    let provenance = compute_build_provenance(&version);
    let profile = env::var("PROFILE").unwrap_or_else(|_| "unknown".to_string());

    // Legacy exports retained for existing feature-report consumers.
    println!("cargo:rustc-env=AY_GIT_HASH={}", provenance.commit);
    println!("cargo:rustc-env=AY_BUILD_DATE={}", provenance.datetime_utc);
    println!(
        "cargo:rustc-env=AY_COMMIT_COUNT={}",
        provenance.build_increment
    );
    println!("cargo:rustc-env=AY_BUILD_PROFILE={profile}");

    // Structured provenance exports for the CLI/session markers.
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

    // Startup-time fix (2026-07-14): gpu-feature builds statically import
    // OPENGL32.dll (wgpu's GLES/wgl fallback) and d3dcompiler_47.dll (DX12
    // FXC). OPENGL32 drags the GPU vendor's OpenGL ICD chain into EVERY
    // process start — measured +66ms on `ay --version` vs the default
    // build. Delay-load both so the cost is paid on first GPU use (which
    // is lazy and threshold-gated) instead of on every launch.
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let target_env = env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();
    if target_os == "windows" && target_env == "msvc" && env::var("CARGO_FEATURE_GPU").is_ok() {
        println!("cargo:rustc-link-arg-bins=/DELAYLOAD:OPENGL32.dll");
        println!("cargo:rustc-link-arg-bins=/DELAYLOAD:d3dcompiler_47.dll");
        println!("cargo:rustc-link-arg-bins=delayimp.lib");
    }
}
