// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Local publication gate and its checked-in policy contract.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Stdio};
use std::time::UNIX_EPOCH;

use anyhow::{bail, Context, Result};
use serde_json::Value;

use super::{
    print_steps, render_command, resolve_critical_range, resolve_repo_root, run_external_step,
    run_health_checks, run_native_step, ExternalStep, PublishGateArgs, CRITICAL_SOLVER_POLICY_PATH,
};

const CONFIG_PATH: &str = "publish/config.sh";
const SHIM_PATH: &str = "publish/publish.sh";
const CHECK_PREFIX: &str = "CHECK_CMD_DEFAULT=\"";
const REQUIRED_CHECK: &str = "cargo check --locked --workspace --all-targets --all-features";
const SHIM_DELEGATION: &str = "cd \"$HERE\" && exec \"$ENGINE/bin/pub\" \"$@\"";

const REQUIRED_ASSETS: &[&str] = &[
    CRITICAL_SOLVER_POLICY_PATH,
    "scripts/check_doc_reality.sh",
    "scripts/check_no_python_test_skips.py",
    "publish/README.md",
    "publish/DECISIONS.md",
    CONFIG_PATH,
    "publish/manifest.txt",
    SHIM_PATH,
    "publish/transforms.sh",
    "rust-toolchain.toml",
    "README.md",
    "SECURITY.md",
    "SUPPORT.md",
    "CODE_OF_CONDUCT.md",
    "LICENSE",
    "NOTICE",
    "THIRD_PARTY.md",
];

const PUBLIC_CRATES: &[&str] = &[
    "ay",
    "ay-bindings",
    "ay-ffi",
    "ay-fzn2smt",
    "ay-drat-check",
    "ay-lrat-check",
];

pub(super) fn run(args: &PublishGateArgs) -> Result<i32> {
    let repo_root = resolve_repo_root(args.repo_root.as_deref())?;
    let critical_range = resolve_critical_range(
        &repo_root,
        args.critical_solver_range.as_deref(),
        "PUBLISH_GATE_CRITICAL_SOLVER_RANGE",
    )?;
    let external_steps = external_steps(&critical_range);

    println!("[publish-gate] Root: {}", repo_root.display());
    println!("[publish-gate] critical_solver_range={critical_range}");
    if args.list_steps {
        print_steps(
            "publish-gate",
            &external_steps,
            &[
                "release_gate_assets_present",
                "release_gate_wiring",
                "repository_health",
                "release_public_crate_metadata",
                "release_tarball_surface",
                "ay_help",
                "ay_version",
                "ay_flatzinc_help",
                "ay_flatzinc_solve_help",
                "ay_check_help",
                "ay_check_drat_help",
                "ay_check_lrat_help",
            ],
        );
        return Ok(0);
    }

    // Validate the local contract before invoking its shim. A stale shim must
    // fail with a precise in-process diagnostic, not an opaque child error.
    run_native_step("publish-gate", "release_gate_assets_present", || {
        check_assets(&repo_root)
    })?;
    run_native_step("publish-gate", "release_gate_wiring", || {
        check_policy_wiring(&repo_root)
    })?;
    for step in &external_steps {
        run_external_step("publish-gate", &repo_root, step)?;
    }
    run_native_step("publish-gate", "repository_health", || {
        if run_health_checks(&repo_root, false)? {
            bail!("repository health check failed");
        }
        Ok(())
    })?;
    run_native_step("publish-gate", "release_public_crate_metadata", || {
        check_public_crate_metadata(&repo_root)
    })?;
    run_native_step("publish-gate", "release_tarball_surface", || {
        check_tarball_surface(&repo_root)
    })?;
    run_binary_probes(&repo_root)?;

    println!("[publish-gate] PASS");
    Ok(0)
}

fn external_steps(critical_range: &str) -> Vec<ExternalStep> {
    vec![
        ExternalStep::new(
            "critical_solver_policy",
            "bash",
            &[
                "scripts/check_critical_solver_policy.sh",
                "--rev-range",
                critical_range,
            ],
        ),
        ExternalStep::new(
            "code_quality",
            "cargo",
            &[
                "run",
                "--locked",
                "-p",
                "ay-quality-gate",
                "--bin",
                "ay-quality-gate",
                "--",
            ],
        ),
        ExternalStep::new("rustfmt", "cargo", &["fmt", "--check", "--all"]),
        ExternalStep::new(
            "clippy",
            "cargo",
            &["clippy", "--locked", "--workspace", "--lib", "--bins"],
        ),
        ExternalStep::new(
            "python_zero_skip",
            "python3",
            &["scripts/check_no_python_test_skips.py"],
        ),
        ExternalStep::new(
            "cargo_check_workspace",
            "cargo",
            &["check", "--locked", "--workspace"],
        ),
        ExternalStep::new(
            "release_build_binaries",
            "cargo",
            &[
                "build",
                "--locked",
                "--release",
                "-p",
                "ay",
                "-p",
                "ay-fzn2smt",
                "-p",
                "ay-drat-check",
                "-p",
                "ay-lrat-check",
            ],
        ),
        ExternalStep::new("doc_reality", "bash", &["scripts/check_doc_reality.sh"]),
        ExternalStep::new(
            "doctests",
            "cargo",
            &["test", "--locked", "--workspace", "--doc"],
        ),
        // The trailing --check is load-bearing: `pub check ay` runs export
        // guards, while this form also executes CHECK_CMD_DEFAULT in a fresh
        // anonymous-style export with an isolated Cargo home.
        ExternalStep::new("publication_check", SHIM_PATH, &["check", "ay", "--check"]),
    ]
}

fn check_policy_wiring(repo_root: &Path) -> Result<()> {
    let config_path = repo_root.join(CONFIG_PATH);
    let config = fs::read_to_string(&config_path)
        .with_context(|| format!("read publication config {}", config_path.display()))?;
    let checks = config
        .lines()
        .filter_map(|line| {
            line.strip_prefix(CHECK_PREFIX)
                .and_then(|value| value.strip_suffix('"'))
        })
        .collect::<Vec<_>>();
    if checks.len() != 1 {
        bail!(
            "publication config must contain exactly one flat CHECK_CMD_DEFAULT=\"...\" assignment, found {}",
            checks.len()
        );
    }
    if checks[0].trim().is_empty() {
        bail!("publication CHECK_CMD_DEFAULT must not be empty");
    }
    if !checks[0].contains(REQUIRED_CHECK) {
        bail!(
            "publication CHECK_CMD_DEFAULT must check the pinned, locked workspace, all targets, and all features"
        );
    }

    let shim_path = repo_root.join(SHIM_PATH);
    let shim = fs::read_to_string(&shim_path)
        .with_context(|| format!("read publication shim {}", shim_path.display()))?;
    if !shim
        .lines()
        .map(str::trim)
        .any(|line| line == SHIM_DELEGATION)
    {
        bail!("publication shim must delegate exactly to the central $ENGINE/bin/pub driver");
    }
    Ok(())
}

fn check_assets(repo_root: &Path) -> Result<()> {
    for path in REQUIRED_ASSETS {
        if !repo_root.join(path).is_file() {
            bail!("missing required release asset: {path}");
        }
    }
    Ok(())
}

fn check_public_crate_metadata(repo_root: &Path) -> Result<()> {
    let output = command_output(
        repo_root,
        "cargo",
        &["metadata", "--locked", "--no-deps", "--format-version", "1"],
    )?;
    let metadata: Value = serde_json::from_slice(&output)
        .context("parse cargo metadata --no-deps --format-version 1 JSON")?;
    let packages = metadata
        .get("packages")
        .and_then(Value::as_array)
        .context("cargo metadata missing packages array")?;
    for crate_name in PUBLIC_CRATES {
        let package = packages
            .iter()
            .find(|package| package.get("name").and_then(Value::as_str) == Some(*crate_name))
            .with_context(|| format!("missing public release crate in metadata: {crate_name}"))?;
        let mut missing = [
            "description",
            "license",
            "repository",
            "homepage",
            "documentation",
            "readme",
        ]
        .into_iter()
        .filter(|field| package.get(field).is_none_or(is_empty_json_value))
        .collect::<Vec<_>>();
        if package
            .get("authors")
            .and_then(Value::as_array)
            .is_none_or(Vec::is_empty)
        {
            missing.push("authors");
        }
        if !missing.is_empty() {
            bail!(
                "public release crate metadata incomplete for {crate_name}: missing {}",
                missing.join(", ")
            );
        }
    }
    Ok(())
}

fn is_empty_json_value(value: &Value) -> bool {
    match value {
        Value::Null => true,
        Value::String(text) => text.is_empty(),
        Value::Array(items) => items.is_empty(),
        _ => false,
    }
}

fn check_tarball_surface(repo_root: &Path) -> Result<()> {
    for crate_name in PUBLIC_CRATES {
        let output = command_output(
            repo_root,
            "cargo",
            &[
                "package",
                "--locked",
                "-p",
                crate_name,
                "--allow-dirty",
                "--list",
            ],
        )
        .with_context(|| format!("list package files for {crate_name}"))?;
        let files = String::from_utf8_lossy(&output);
        for required in ["LICENSE", "README.md"] {
            if !files.lines().any(|line| line == required) {
                bail!("packaged crate missing {required}: {crate_name}");
            }
        }
    }
    Ok(())
}

fn command_output(repo_root: &Path, program: &str, args: &[&str]) -> Result<Vec<u8>> {
    let output = ProcessCommand::new(program)
        .args(args)
        .current_dir(repo_root)
        .output()
        .with_context(|| {
            format!(
                "spawn {}",
                render_command(program, args, &[] as &[(&str, &str)])
            )
        })?;
    if !output.status.success() {
        bail!(
            "{} failed with status {}:\n{}{}",
            render_command(program, args, &[] as &[(&str, &str)]),
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    Ok(output.stdout)
}

fn run_binary_probes(repo_root: &Path) -> Result<()> {
    let binary = require_built_binary(repo_root, "ay")?;
    for (name, args, quiet) in [
        ("ay_help", &["--help"][..], true),
        ("ay_version", &["--version"][..], false),
        ("ay_flatzinc_help", &["flatzinc", "--help"][..], true),
        (
            "ay_flatzinc_solve_help",
            &["flatzinc", "solve", "--help"][..],
            true,
        ),
        ("ay_check_help", &["check", "--help"][..], true),
        ("ay_check_drat_help", &["check", "drat", "--help"][..], true),
        ("ay_check_lrat_help", &["check", "lrat", "--help"][..], true),
    ] {
        run_binary_probe(repo_root, &binary, name, args, quiet)?;
    }
    Ok(())
}

fn require_built_binary(repo_root: &Path, name: &str) -> Result<PathBuf> {
    let target_dir = env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("target"));
    let explicit = env::var_os("CARGO_TARGET_DIR").is_some();
    let target_root = if target_dir.is_absolute() {
        target_dir
    } else {
        repo_root.join(target_dir)
    };
    let configured = target_root.join("release").join(name);
    if explicit {
        if is_executable_file(&configured) {
            return Ok(configured);
        }
        bail!(
            "expected configured release binary missing for {name}: {}",
            configured.display()
        );
    }
    [
        configured,
        repo_root.join("target/user/release").join(name),
        repo_root.join("target/release").join(name),
    ]
    .into_iter()
    .filter(|path| is_executable_file(path))
    .max_by_key(|path| binary_mtime_epoch(path).unwrap_or(0))
    .with_context(|| {
        format!(
            "expected repo-local release binary missing for {name}; searched target/release and target/user/release"
        )
    })
}

fn binary_mtime_epoch(path: &Path) -> Option<u64> {
    let modified = fs::metadata(path).ok()?.modified().ok()?;
    Some(modified.duration_since(UNIX_EPOCH).ok()?.as_secs())
}

pub(super) fn is_executable_file(path: &Path) -> bool {
    let Ok(metadata) = fs::metadata(path) else {
        return false;
    };
    if !metadata.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

fn run_binary_probe(
    repo_root: &Path,
    binary: &Path,
    name: &'static str,
    args: &[&str],
    quiet_stdout: bool,
) -> Result<()> {
    println!("[publish-gate] START {name}");
    println!("[publish-gate] ay_bin={}", binary.display());
    let mut command = ProcessCommand::new(binary);
    command.args(args).current_dir(repo_root);
    if quiet_stdout {
        command.stdout(Stdio::null());
    }
    let status = command
        .status()
        .with_context(|| format!("spawn {} {}", binary.display(), args.join(" ")))?;
    if !status.success() {
        bail!("{name} failed with status {status}");
    }
    println!("[publish-gate] DONE  {name}");
    Ok(())
}

#[cfg(test)]
#[path = "publish_tests.rs"]
mod tests;
