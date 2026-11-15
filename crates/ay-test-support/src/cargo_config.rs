// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which Cargo configuration files a directory discovers, and which of their
//! keys can change what is compiled.
//!
//! Split out of `lib.rs` so that the two places that must answer this share one
//! definition of "semantic": the exact-source funnel, which binds every
//! discovered file into a nested build's identity and refuses an unbound one
//! that could change the build, and the trybuild lane
//! (`crate::trybuild_lane`), which must choose a working directory whose
//! discovery reaches no build posture at all.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

pub(crate) fn cargo_config_paths(workspace: &Path, cargo_home: &Path) -> Vec<PathBuf> {
    let mut candidates = BTreeSet::new();
    for ancestor in workspace.ancestors() {
        candidates.insert(ancestor.join(".cargo").join("config"));
        candidates.insert(ancestor.join(".cargo").join("config.toml"));
    }
    candidates.insert(cargo_home.join("config"));
    candidates.insert(cargo_home.join("config.toml"));
    candidates
        .into_iter()
        .filter(|path| std::fs::symlink_metadata(path).is_ok())
        .collect()
}

/// The first key of a parsed Cargo config that can change what is compiled,
/// or `None` when every key is one of the non-semantic tables below.
pub(crate) fn semantic_cargo_config_key<'a>(
    path: &Path,
    parsed: &'a toml::Value,
) -> Option<&'a str> {
    let table = parsed
        .as_table()
        .unwrap_or_else(|| panic!("Cargo config {} must be a TOML table", path.display()));
    for (key, value) in table {
        let nonsemantic = matches!(
            key.as_str(),
            "alias"
                | "cache"
                | "cargo-new"
                | "credential-alias"
                | "doc"
                | "future-incompat-report"
                | "http"
                | "net"
                | "registries"
                | "registry"
                | "term"
        ) || (key == "env"
            && value.as_table().is_some_and(|t| {
                // Empty, or purely sccache cache configuration. `SCCACHE_DIR`
                // and `SCCACHE_CACHE_SIZE` tell the wrapper where to keep its
                // cache and how large to let it grow; they do not reach rustc
                // and cannot change what is compiled. Same rationale as the
                // `build.rustc-wrapper` allowance below — the workspace config
                // directs sccache setup into a user-local config, and sccache
                // is unusable without these. Any other env key still fails,
                // because a build script can read it.
                t.is_empty() || t.keys().all(|k| k.starts_with("SCCACHE_"))
            }))
            // `build` is semantic in general, but two of its keys are BUILD
            // ACCELERATION rather than source identity, and the workspace's own
            // `.cargo/config.toml` explicitly directs developers to set them in
            // exactly this place:
            //
            //   "Do not set `build.rustc-wrapper` here: if `sccache` is useful on
            //    a given machine, opt into it with `RUSTC_WRAPPER=sccache` or a
            //    user-local Cargo config."
            //
            // Rejecting them here contradicted that instruction and turned three
            // LRAT tests red on any machine following it — which on this host is
            // not optional: the user-global sccache config was added after a
            // kernel panic caused by uncoordinated parallel rebuilds of the same
            // ~1,693-crate graph across worktrees.
            //
            // Neither key changes what the compiler is asked to build:
            // `rustc-wrapper = sccache` is a content-addressed cache keyed on the
            // rustc invocation (rustflags included), and `incremental` selects
            // codegen caching, not program semantics. Any OTHER `build` key
            // (`target`, `target-dir`, `rustflags`, `rustc`) still fails.
            // `jobs` joined the pair 2026-08-31: the trust superproject's
            // committed .cargo/config.toml (a5012b03c) bounds Cargo fanout with
            // `[build] jobs = 4` on a shared-UMA machine, and cargo's ancestor
            // discovery hands that file to every ay-inside-trust checkout.
            // Parallelism selects scheduling, never what the compiler is asked
            // to build, so it belongs with the cache keys, not the semantic
            // ones. Any OTHER `build` key (`target`, `target-dir`, `rustflags`,
            // `rustc`) still fails.
            || (key == "build"
                && value.as_table().is_some_and(|t| {
                    t.keys()
                        .all(|k| matches!(k.as_str(), "rustc-wrapper" | "incremental" | "jobs"))
                }));
        if !nonsemantic {
            return Some(key);
        }
    }
    None
}

pub(crate) fn reject_unbound_semantic_cargo_config(path: &Path, parsed: &toml::Value) {
    let key = semantic_cargo_config_key(path, parsed);
    assert!(
        key.is_none(),
        "Cargo config {} is outside exact source identity but sets semantic key {:?}; move it into the workspace or remove the override",
        path.display(),
        key.unwrap_or_default()
    );
}
