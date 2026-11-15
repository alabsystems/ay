// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The inputs of a stamping crate: the files whose content decides what it
//! compiles to, and so the only files its stamp may vouch for or watch.
//!
//! They are, for the crate's own package and every workspace package it is
//! built from (normal and build dependencies, transitively, every feature and
//! platform — an over-approximation, never an under-one):
//!
//! - the manifest;
//! - the directory holding each shipped target's root file (`lib`, `bin`,
//!   `proc-macro` and the library kinds), which holds its module tree;
//! - the build script;
//! - files the sources embed from elsewhere (`include_str!` of a script, a
//!   pin, a Lean file), declared next to the package as
//!   `[package.metadata.ay-provenance] inputs = ["relative/path", ...]`;
//!
//! and, once, the workspace build files in [`WORKSPACE_INPUTS`].
//!
//! Tests, benches, examples, documentation and every package outside the
//! closure are not inputs. `crates/ay/tests/group_misc/build_provenance_g9.rs`
//! holds the derivation to Cargo's own record of what the `ay` binary was
//! built from: a file compiled in but outside the scope fails it.
//!
//! The closure comes from `cargo metadata --no-deps`, which resolves nothing
//! and needs no network. If it cannot be read, the whole repository is the
//! scope: every change then retakes the stamp, as before this file existed.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use super::json::{self, Value};
use super::{canonical, lexically_normal, Repository};

/// Workspace files every stamping crate is built from, relative to the
/// workspace root: the manifests and lockfile, the compiler and its flags,
/// and the provenance code itself.
pub(crate) const WORKSPACE_INPUTS: [&str; 5] = [
    "Cargo.toml",
    "Cargo.lock",
    ".cargo/config.toml",
    "rust-toolchain.toml",
    "build_support",
];

/// Cargo target kinds that ship: their sources are compiled into the crate or
/// a binary built from it.
const SHIPPED_TARGET_KINDS: [&str; 7] = [
    "lib",
    "rlib",
    "dylib",
    "cdylib",
    "staticlib",
    "proc-macro",
    "bin",
];

/// How the scope was derived.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ScopeDerivation {
    /// From `cargo metadata`: the crate's dependency closure.
    CargoMetadata,
    /// `cargo metadata` could not be read: the whole repository.
    WholeRepository,
}

impl ScopeDerivation {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::CargoMetadata => "cargo-metadata",
            Self::WholeRepository => "whole-repository",
        }
    }
}

/// The inputs of one crate, as git pathspecs.
#[derive(Clone, Debug)]
pub(crate) struct InputScope {
    pub(crate) derivation: ScopeDerivation,
    /// The packages in the closure, by name.
    pub(crate) packages: BTreeSet<String>,
    /// Repository-relative, `/`-separated, none inside another.
    pub(crate) pathspecs: Vec<String>,
    /// An input lies outside the repository, where git cannot see a change.
    pub(crate) outside_repository: bool,
}

/// What the working tree says about a scope right now.
pub(crate) struct Observation {
    /// No input differs from HEAD, and no untracked file sits among them.
    pub(crate) clean: bool,
    /// Every file Cargo must watch to know when that could change.
    pub(crate) watched: BTreeSet<PathBuf>,
}

impl InputScope {
    /// The inputs of the package at `package_dir`, read with `cargo`.
    pub(crate) fn for_package(repository: &Repository, package_dir: &Path, cargo: &Path) -> Self {
        cargo_metadata(package_dir, cargo)
            .and_then(|metadata| Self::from_metadata(repository, package_dir, &metadata))
            .unwrap_or_else(Self::whole_repository)
    }

    fn whole_repository() -> Self {
        Self {
            derivation: ScopeDerivation::WholeRepository,
            packages: BTreeSet::new(),
            pathspecs: vec![".".to_string()],
            outside_repository: false,
        }
    }

    /// The scope `cargo metadata --no-deps` output describes for the package
    /// at `package_dir`, or `None` if it does not describe that package.
    pub(crate) fn from_metadata(
        repository: &Repository,
        package_dir: &Path,
        metadata: &Value,
    ) -> Option<Self> {
        let workspace_root = PathBuf::from(metadata.get("workspace_root")?.as_str()?);
        let mut by_dir = BTreeMap::new();
        for package in metadata.get("packages")?.as_array()? {
            let manifest = Path::new(package.get("manifest_path")?.as_str()?);
            by_dir.insert(canonical(manifest.parent()?), package);
        }
        let start = canonical(package_dir);
        by_dir.get(&start)?;

        let mut inputs: BTreeSet<PathBuf> = WORKSPACE_INPUTS
            .iter()
            .map(|input| workspace_root.join(input))
            .collect();
        let mut packages = BTreeSet::new();
        let mut visited = BTreeSet::new();
        let mut pending = vec![start];
        while let Some(dir) = pending.pop() {
            if !visited.insert(dir.clone()) {
                continue;
            }
            let Some(package) = by_dir.get(&dir) else {
                // A path dependency that is not a workspace member: all of it.
                inputs.insert(dir);
                continue;
            };
            packages.insert(package.get("name")?.as_str()?.to_string());
            inputs.extend(package_inputs(&dir, package)?);
            for dependency in package.get("dependencies")?.as_array()? {
                if dependency.get("kind").and_then(Value::as_str) == Some("dev") {
                    continue;
                }
                if let Some(path) = dependency.get("path").and_then(Value::as_str) {
                    pending.push(canonical(Path::new(path)));
                }
            }
        }

        let relative: Vec<Option<String>> = inputs
            .iter()
            .map(|input| repository.relative(input))
            .collect();
        Some(Self {
            derivation: ScopeDerivation::CargoMetadata,
            packages,
            pathspecs: outermost(relative.iter().flatten().cloned()),
            outside_repository: relative.iter().any(Option::is_none),
        })
    }

    /// Whether the inputs differ from HEAD, and what to watch. A git failure
    /// counts as a difference: the stamp never vouches for what it did not see.
    pub(crate) fn observe(&self, repository: &Repository) -> Observation {
        let clean = !self.outside_repository
            && repository
                .changes(&self.pathspecs)
                .is_some_and(|changes| changes.is_empty());
        let mut watched = BTreeSet::new();
        match repository.files(&self.pathspecs) {
            Some(files) => {
                for file in files {
                    // A deleted input is watched through the nearest directory
                    // that still exists: Cargo reruns a build script on every
                    // build while a watched path is missing.
                    let path = repository.root.join(&file);
                    if let Some(existing) = path.ancestors().find(|path| path.exists()) {
                        watched.insert(existing.to_path_buf());
                    }
                }
            }
            None => {
                for pathspec in &self.pathspecs {
                    let path = repository.root.join(pathspec);
                    if path.exists() {
                        watched.insert(path);
                    }
                }
            }
        }
        Observation { clean, watched }
    }
}

/// The inputs one package contributes.
fn package_inputs(dir: &Path, package: &Value) -> Option<Vec<PathBuf>> {
    let mut inputs = vec![PathBuf::from(package.get("manifest_path")?.as_str()?)];
    for target in package.get("targets")?.as_array()? {
        let root = Path::new(target.get("src_path")?.as_str()?);
        let kinds: Vec<&str> = target
            .get("kind")?
            .as_array()?
            .iter()
            .filter_map(Value::as_str)
            .collect();
        if kinds.contains(&"custom-build") {
            inputs.push(root.to_path_buf());
        } else if kinds.iter().any(|kind| SHIPPED_TARGET_KINDS.contains(kind)) {
            inputs.push(root.parent()?.to_path_buf());
        }
    }
    let declared = package
        .get("metadata")
        .and_then(|metadata| metadata.get("ay-provenance"))
        .and_then(|provenance| provenance.get("inputs"))
        .and_then(Value::as_array)
        .unwrap_or_default();
    for input in declared {
        inputs.push(lexically_normal(&dir.join(input.as_str()?)));
    }
    Some(inputs)
}

/// `pathspecs` sorted, without duplicates or any that lie inside another.
pub(crate) fn outermost(pathspecs: impl IntoIterator<Item = String>) -> Vec<String> {
    let sorted: BTreeSet<String> = pathspecs.into_iter().collect();
    if sorted.contains(".") {
        return vec![".".to_string()];
    }
    let mut kept: Vec<String> = Vec::new();
    for pathspec in sorted {
        let inside_kept = kept.iter().any(|outer| {
            pathspec
                .strip_prefix(outer.as_str())
                .is_some_and(|rest| rest.starts_with('/'))
        });
        if !inside_kept {
            kept.push(pathspec);
        }
    }
    kept
}

/// `cargo metadata --no-deps` for the workspace holding `package_dir`.
fn cargo_metadata(package_dir: &Path, cargo: &Path) -> Option<Value> {
    let output = Command::new(cargo)
        .current_dir(package_dir)
        .args([
            "metadata",
            "--format-version",
            "1",
            "--no-deps",
            "--offline",
        ])
        .arg("--manifest-path")
        .arg(package_dir.join("Cargo.toml"))
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    json::parse(std::str::from_utf8(&output.stdout).ok()?)
}
