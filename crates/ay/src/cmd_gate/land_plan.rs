// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::process::Step;
use super::scope::RustScope;
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};

const CLI_FEATURES: &str = "cli,bench";

#[path = "land_batch.rs"]
mod batch;
#[path = "land_local_paths.rs"]
mod local_paths;

#[derive(Deserialize)]
pub(super) struct Metadata {
    pub packages: Vec<Package>,
    pub workspace_members: Vec<String>,
    #[serde(default)]
    pub resolve: Option<Resolution>,
}

#[derive(Deserialize)]
pub(super) struct Resolution {
    pub nodes: Vec<ResolvedPackage>,
}
#[derive(Deserialize)]
pub(super) struct ResolvedPackage {
    pub id: String,
    #[serde(default)]
    pub dependencies: Vec<String>,
}

#[derive(Deserialize)]
pub(super) struct Package {
    pub id: String,
    pub name: String,
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub source: Option<String>,
    pub manifest_path: PathBuf,
    pub edition: String,
    pub targets: Vec<Target>,
    #[serde(default)]
    pub metadata: serde_json::Value,
}

#[derive(Deserialize)]
pub(super) struct Target {
    pub name: String,
    pub kind: Vec<String>,
    pub src_path: PathBuf,
    #[serde(default, rename = "required-features")]
    pub required_features: Vec<String>,
}

#[derive(Serialize)]
pub(super) struct Plan {
    pub changed_paths: Vec<PathBuf>,
    pub broad_compile: bool,
    pub steps: Vec<Step>,
}

#[derive(Default)]
struct TestSelection {
    all: bool,
    root: bool,
    modules: BTreeSet<String>,
}

#[derive(Default)]
struct Selection {
    unit: bool,
    cli_all: bool,
    cli_entry: bool,
    cli_modules: BTreeSet<String>,
    integration: BTreeMap<String, TestSelection>,
}

pub(super) fn select(
    root: &Path,
    metadata: &Metadata,
    paths: Vec<PathBuf>,
    old_lock: Option<&str>,
    scope: &RustScope,
) -> Result<Plan> {
    let packages: Vec<_> = metadata
        .packages
        .iter()
        .filter(|p| metadata.workspace_members.contains(&p.id))
        .collect();
    let local = local_paths::Graph::read(root, metadata)?;
    let mut selected: BTreeMap<String, Selection> = BTreeMap::new();
    let mut broad = false;
    let mut cli = false;
    let mut steps = Vec::new();
    let mut format_paths: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for path in &paths {
        if scope.retired_tooling.contains(path) {
            continue;
        }
        let absolute = root.join(path);
        let provenance: Vec<_> = local
            .packages
            .iter()
            .filter(|p| provenance_inputs(p).contains(&absolute))
            .collect();
        if documentation(path) && provenance.is_empty() {
            continue;
        }
        // Other workspaces own their source formatting and edition policy.
        // Compile their actual consumers; do not rewrite canonical imports to
        // the importing workspace's style or mistake them for unknown inputs.
        let owners = local.owners(&absolute, &provenance);
        let foreign_source = local
            .physical_owner(&absolute)
            .is_some_and(|package| !metadata.workspace_members.contains(&package.id));
        for package in owners
            .iter()
            .filter(|package| !metadata.workspace_members.contains(&package.id))
        {
            cli = true;
            let consumers = local.consumers(&package.id);
            broad |= consumers.is_empty();
            for consumer in consumers {
                select_dependency_consumer(&mut selected, consumer);
            }
        }
        let workspace_owners: Vec<_> = owners
            .iter()
            .copied()
            .filter(|package| metadata.workspace_members.contains(&package.id))
            .collect();
        let workspace_configuration = matches!(
            path.to_str(),
            Some("Cargo.toml" | "Cargo.lock" | "rust-toolchain" | "rust-toolchain.toml")
        ) || path.starts_with(".cargo");
        if workspace_owners.is_empty() && !owners.is_empty() && !workspace_configuration {
            continue;
        }
        if path.extension().is_some_and(|s| s == "rs") && absolute.is_file() && !foreign_source {
            let package = packages
                .iter()
                .filter(|p| {
                    p.manifest_path
                        .parent()
                        .is_some_and(|dir| absolute.starts_with(dir))
                })
                .max_by_key(|p| p.manifest_path.components().count());
            let edition = match package {
                Some(package) => package.edition.clone(),
                None => workspace_edition(root)?,
            };
            format_paths
                .entry(edition)
                .or_default()
                .push(path.to_str().context("Rust path is not UTF-8")?.to_string());
        }
        if scope.unchanged.contains(path) {
            continue;
        }
        if path == Path::new("Cargo.toml")
            && provenance.is_empty()
            && (scope.narrowed_package_recipe
                || local.only_adds_independent_exclusions(
                    scope.base_workspace_manifest.as_deref(),
                    scope.base_paths.as_ref(),
                )?)
        {
            // The recipe alone narrows package roots. Preserve the ordinary
            // CLI build that checks its workspace provenance, without treating
            // ignored Cargo metadata as changed Rust compilation settings.
            cli = true;
            continue;
        }
        if path == Path::new("Cargo.lock") {
            let current = std::fs::read_to_string(root.join(path)).context("read Cargo.lock")?;
            let (names, external) = lock_changes(
                old_lock.context("missing base lockfile")?,
                &current,
                &local.packages,
            )?;
            broad |= external;
            cli |= external || !names.is_empty();
            for name in names {
                for package in local.packages.iter().filter(|p| p.name == name) {
                    if metadata.workspace_members.contains(&package.id) {
                        select_runtime(&mut selected, &package.name);
                    } else {
                        let consumers = local.consumers(&package.id);
                        broad |= consumers.is_empty();
                        for consumer in consumers {
                            select_dependency_consumer(&mut selected, consumer);
                        }
                    }
                }
            }
            continue;
        }
        if workspace_configuration || workspace_owners.is_empty() {
            // Workspace configuration, build support, and otherwise unclassified
            // inputs get broad compilation, never unrelated script test suites.
            broad = true;
            cli = true;
        }
        for package in workspace_owners {
            let directory = package
                .manifest_path
                .parent()
                .context("manifest has no directory")?;
            let relative = absolute.strip_prefix(directory).ok();
            if relative.is_some_and(|p| p.starts_with("tests")) {
                select_test(&mut selected, package, &absolute, scope);
            } else {
                cli = true;
                if package.name == "ay" {
                    let entry = selected.entry(package.name.clone()).or_default();
                    match relative {
                        Some(p) if p == Path::new("src/main.rs") => {
                            entry.cli_entry = true;
                        }
                        Some(p) if p == Path::new("Cargo.toml") => {
                            entry.unit = true;
                            entry.cli_entry = true;
                        }
                        Some(p) if scope.cli_module(p).is_some() => {
                            let Some(module) = scope.cli_module(p) else {
                                continue;
                            };
                            if scope.production_modules.contains(module) {
                                entry.cli_modules.insert(module.into());
                            } else {
                                entry.cli_entry = true;
                            }
                        }
                        Some(p) if p.starts_with("src") && !absolute.exists() => {}
                        Some(p) if p.starts_with("src") => {
                            entry.unit = true;
                            entry.cli_all = true;
                        }
                        _ => entry.unit = true,
                    }
                } else {
                    select_runtime(&mut selected, &package.name);
                }
            }
        }
    }
    // One bounded invocation per edition/batch, not a process and Git census
    // for each file. Keep checking read-only so the validated commit is intact.
    for (edition, files) in format_paths {
        for batch in files.chunks(32) {
            let mut args = strings(&[
                "--check",
                "--edition",
                &edition,
                "--config",
                "skip_children=true",
                "--",
            ]);
            args.extend(batch.iter().cloned());
            steps.push(Step {
                program: "trustfmt".into(),
                args,
                kind: super::process::StepKind::Command,
            });
        }
    }
    if broad {
        steps.push(Step::compiler(strings(&[
            "check",
            "--profile",
            "test",
            "--locked",
            "--workspace",
            "--all-targets",
            "--features",
            "ay/cli,ay/bench",
        ])));
    }
    let ffi = selected.contains_key("ay-ffi");
    if cli {
        let mut args = strings(&["build", "--profile", "test", "--locked"]);
        args.extend(strings(&[
            "-p",
            "ay",
            "--features",
            CLI_FEATURES,
            "--bin",
            "ay",
        ]));
        steps.push(Step::compiler(args));
    }
    // CLI features affect shared dependencies. Keep them out of the native
    // library/consumer graph rather than rebuilding that graph on test entry.
    let ffi_target = packages
        .iter()
        .find(|p| p.name == "ay-ffi")
        .and_then(|p| p.targets.iter().find(|t| t.name == "group_ffi"))
        .filter(|_| {
            selected
                .get("ay-ffi")
                .is_some_and(|s| s.integration.contains_key("group_ffi"))
        });
    if ffi {
        let mut step = Step::compiler(strings(&[
            "build",
            "--profile",
            "test",
            "--locked",
            "-p",
            "ay-ffi",
            "--lib",
        ]));
        if let Some(target) = ffi_target {
            step.args
                .extend(strings(&["--test", &target.name, "--message-format=json"]));
            if !target.required_features.is_empty() {
                step.args
                    .extend(["--features".into(), target.required_features.join(",")]);
            }
            step.kind = super::process::StepKind::FfiArtifactBuild;
        }
        steps.push(step);
    }
    for package in packages {
        let Some(selection) = selected.get(&package.name) else {
            continue;
        };
        if selection.unit {
            let mut args = test_args(package);
            if package
                .targets
                .iter()
                .any(|t| t.kind.iter().any(|k| k == "lib" || k.ends_with("lib")))
            {
                args.push("--lib".into());
            }
            if package.name != "ay"
                && package
                    .targets
                    .iter()
                    .any(|t| t.kind.contains(&"bin".into()))
            {
                args.push("--bins".into());
            }
            if args.iter().any(|s| s == "--lib" || s == "--bins") {
                steps.push(Step::compiler(args));
            }
        }
        if package.name == "ay" {
            if selection.cli_all {
                let mut args = test_args(package);
                args.extend(strings(&["--bin", "ay"]));
                steps.push(Step::compiler(args));
            } else {
                if selection.cli_entry {
                    let mut args = test_args(package);
                    args.extend(strings(&["--bin", "ay", "--"]));
                    for module in &scope.production_modules {
                        if !selection.cli_modules.contains(module) {
                            args.extend(["--skip".into(), format!("{module}::")]);
                        }
                    }
                    steps.push(Step::compiler(args));
                } else if !selection.cli_modules.is_empty() {
                    let mut args = test_args(package);
                    args.extend(strings(&["--bin", "ay", "--"]));
                    args.extend(
                        selection
                            .cli_modules
                            .iter()
                            .map(|module| format!("{module}::")),
                    );
                    steps.push(Step::compiler(args));
                }
            }
        }
        for target in &package.targets {
            if let Some(tests) = selection.integration.get(&target.name) {
                let mut args = test_args(package);
                args.extend(["--test".into(), target.name.clone()]);
                if !target.required_features.is_empty() {
                    args.extend(["--features".into(), target.required_features.join(",")]);
                }
                if !tests.all {
                    if let Some(modules) = super::scope::source_modules(&target.src_path) {
                        args.push("--".into());
                        if tests.root {
                            for module in modules.values() {
                                if !tests.modules.contains(module) {
                                    args.extend(["--skip".into(), format!("{module}::")]);
                                }
                            }
                        } else {
                            args.extend(tests.modules.iter().map(|module| format!("{module}::")));
                        }
                    }
                }
                let mut step = Step::compiler(args);
                if package.name == "ay-ffi" && target.name == "group_ffi" && ffi_target.is_some() {
                    step.kind = super::process::StepKind::FfiArtifactTests;
                }
                steps.push(step);
            }
        }
    }
    if !scope.retired_tooling.is_empty() {
        steps.push(Step {
            program: "native AY script/publication integrity".into(),
            args: Vec::new(),
            kind: super::process::StepKind::ScriptIntegrity,
        });
    }
    let mut steps = batch::compatible(steps);
    // Drain all selected ordinary compiler/test work before reserving the
    // machine for benchmark-bearing controls. An early exclusive waiter
    // otherwise blocks both these later checks and unrelated admitted work.
    // Stable ordering preserves artifact-build/consumer dependencies and every
    // selected validation; the quiet leg still acquires its original lease.
    steps.sort_by_key(Step::needs_quiet_host);
    Ok(Plan {
        changed_paths: paths,
        broad_compile: broad,
        steps,
    })
}

fn select_runtime(selected: &mut BTreeMap<String, Selection>, name: &str) {
    let entry = selected.entry(name.into()).or_default();
    entry.unit = true;
}

fn select_dependency_consumer(selected: &mut BTreeMap<String, Selection>, package: &Package) {
    select_runtime(selected, &package.name);
    if package.name == "ay" {
        // A dependency can be used by any CLI module. The binary consumer
        // must receive actual runtime checks, not an empty library selection.
        selected.entry(package.name.clone()).or_default().cli_all = true;
    }
}

fn workspace_edition(root: &Path) -> Result<String> {
    let manifest: toml::Value = toml::from_str(&std::fs::read_to_string(root.join("Cargo.toml"))?)?;
    manifest
        .get("workspace")
        .and_then(|v| v.get("package"))
        .and_then(|v| v.get("edition"))
        .and_then(toml::Value::as_str)
        .map(str::to_string)
        .context("workspace manifest has no package edition for root Rust input")
}

fn select_test(
    selected: &mut BTreeMap<String, Selection>,
    package: &Package,
    path: &Path,
    scope: &RustScope,
) {
    let tests: Vec<_> = package
        .targets
        .iter()
        .filter(|t| t.kind.contains(&"test".into()))
        .collect();
    // Follow declared grouped modules. Unknown layouts and shared helpers
    // retain conservative whole-target coverage.
    let direct: Vec<_> = tests
        .iter()
        .filter(|t| t.src_path == path || path.starts_with(t.src_path.with_extension("")))
        .collect();
    let entry = selected.entry(package.name.clone()).or_default();
    if direct.is_empty() {
        for target in tests {
            entry
                .integration
                .entry(target.name.clone())
                .or_default()
                .all = true;
        }
    } else {
        for target in direct {
            let modules = super::scope::source_modules(&target.src_path);
            let matched = modules.as_ref().and_then(|modules| {
                modules.iter().find_map(|(source, name)| {
                    (path == source || path.starts_with(source.with_extension("")))
                        .then_some(name.clone())
                })
            });
            if path != target.src_path
                && matched.is_none()
                && !path.exists()
                && modules.as_ref().is_some_and(|m| !m.is_empty())
            {
                continue;
            }
            let selected = entry.integration.entry(target.name.clone()).or_default();
            if modules.as_ref().is_none_or(|m| m.is_empty()) {
                selected.all = true;
            } else if path == target.src_path {
                if scope.module_lists.contains(path) {
                    selected.root = true;
                    if let Some(changed) = scope.module_changes.get(path) {
                        selected.modules.extend(changed.iter().cloned());
                    }
                } else {
                    selected.all = true;
                }
            } else if let Some(module) = matched {
                selected.modules.insert(module);
            } else {
                selected.all = true;
            }
        }
    }
}

fn test_args(package: &Package) -> Vec<String> {
    let mut args = strings(&["test", "--locked", "-p", &package.name]);
    if package.name == "ay" {
        args.extend(strings(&["--features", CLI_FEATURES]));
    }
    args
}

fn strings(args: &[&str]) -> Vec<String> {
    args.iter().map(|s| (*s).into()).collect()
}

pub(super) fn documentation(path: &Path) -> bool {
    path.starts_with("docs")
        || path.starts_with("reports")
        || path
            .extension()
            .is_some_and(|s| matches!(s.to_str(), Some("md" | "rst")))
        || path == Path::new("LICENSE")
        || path == Path::new("NOTICE")
}

pub(super) fn provenance_inputs(package: &Package) -> Vec<PathBuf> {
    let Some(directory) = package.manifest_path.parent() else {
        return Vec::new();
    };
    package
        .metadata
        .get("ay-provenance")
        .and_then(|v| v.get("inputs"))
        .and_then(serde_json::Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(serde_json::Value::as_str)
        .map(|s| normalize(&directory.join(s)))
        .collect()
}

fn normalize(path: &Path) -> PathBuf {
    let mut result = PathBuf::new();
    for component in path.components() {
        match component {
            Component::ParentDir => {
                result.pop();
            }
            Component::CurDir => {}
            other => result.push(other.as_os_str()),
        }
    }
    result
}

/// Workspace package dependency-edge changes are local. Any alteration to an
/// external entry (including additions, removals, checksums) broadens compilation.
fn lock_changes(old: &str, new: &str, packages: &[&Package]) -> Result<(BTreeSet<String>, bool)> {
    let old: toml::Value = toml::from_str(old).context("parse base lockfile")?;
    let new: toml::Value = toml::from_str(new).context("parse current lockfile")?;
    let entries = |value: &toml::Value| -> Result<BTreeMap<String, toml::Value>> {
        let mut entries = BTreeMap::new();
        for package in value
            .get("package")
            .and_then(toml::Value::as_array)
            .context("lockfile has no packages")?
        {
            let name = package
                .get("name")
                .and_then(toml::Value::as_str)
                .context("lock package has no name")?;
            let version = package
                .get("version")
                .and_then(toml::Value::as_str)
                .context("lock package has no version")?;
            let source = package
                .get("source")
                .and_then(toml::Value::as_str)
                .unwrap_or("");
            entries.insert(format!("{name}\n{version}\n{source}"), package.clone());
        }
        Ok(entries)
    };
    let before = entries(&old)?;
    let after = entries(&new)?;
    let mut names = BTreeSet::new();
    let mut broad = false;
    for key in before.keys().chain(after.keys()).collect::<BTreeSet<_>>() {
        if before.get(key) == after.get(key) {
            continue;
        }
        let entry = after
            .get(key)
            .or_else(|| before.get(key))
            .context("missing lock entry")?;
        let name = entry
            .get("name")
            .and_then(toml::Value::as_str)
            .context("lock package has no name")?;
        if entry.get("source").is_none()
            && packages.iter().any(|p| {
                p.name == name
                    && p.version.as_deref().is_none_or(|version| {
                        entry.get("version").and_then(toml::Value::as_str) == Some(version)
                    })
            })
        {
            names.insert(name.into());
        } else {
            broad = true;
        }
    }
    // Changes to lockfile-level settings are also build inputs.
    let header = |mut value: toml::Value| {
        if let Some(t) = value.as_table_mut() {
            t.remove("package");
        }
        value
    };
    broad |= header(old) != header(new);
    Ok((names, broad))
}
