// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::env;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

pub(crate) struct BuildProvenance {
    pub(crate) build_increment: String,
    pub(crate) commit: String,
    pub(crate) datetime_utc: String,
    pub(crate) stamp: String,
}

const REPO_DIRTY_RERUN_PATHS: &[&str] = &[
    "../../.github",
    "../../benchmarks",
    "../../bindings",
    "../../build_support",
    "../../crates",
    "../../docs",
    "../../scripts",
    "../../CHANGELOG.md",
    "../../Cargo.lock",
    "../../Cargo.toml",
    "../../KNOWN_ISSUES.md",
    "../../README.md",
];

const REPO_DIRTY_GIT_PATHS: &[&str] = &[
    ".github",
    "benchmarks",
    "bindings",
    "build_support",
    "crates",
    "docs",
    "scripts",
    "CHANGELOG.md",
    "Cargo.lock",
    "Cargo.toml",
    "KNOWN_ISSUES.md",
    "README.md",
];

pub(crate) fn compute_build_provenance(version: &str) -> BuildProvenance {
    let build_increment = build_increment();
    let commit = git_commit();
    let datetime_utc = build_datetime_utc();
    let stamp = format!("{version}+build.{build_increment}.{commit}@{datetime_utc}");

    BuildProvenance {
        build_increment,
        commit,
        datetime_utc,
        stamp,
    }
}

pub(crate) fn emit_git_rerun_paths() {
    for path in ["HEAD", "index", "packed-refs"] {
        if let Some(git_path) = git_path(path) {
            println!("cargo:rerun-if-changed={git_path}");
        }
    }

    if let Some(head_ref) = run_git(["symbolic-ref", "-q", "HEAD"]).filter(|s| !s.is_empty()) {
        if let Some(git_path) = git_path(&head_ref) {
            println!("cargo:rerun-if-changed={git_path}");
        }
    }
}

pub(crate) fn emit_repo_dirty_rerun_paths() {
    if let Some(paths) = git_ls_files(REPO_DIRTY_GIT_PATHS) {
        for path in paths {
            println!("cargo:rerun-if-changed=../../{path}");
        }
        return;
    }

    for path in REPO_DIRTY_RERUN_PATHS {
        println!("cargo:rerun-if-changed={path}");
    }
}

fn git_commit() -> String {
    if let Some(commit) = source_git_commit_from_env() {
        return commit;
    }

    let Some(commit) = run_git(["rev-parse", "--verify", "HEAD"]).filter(|s| !s.is_empty())
    else {
        return "unknown".to_string();
    };

    let dirty = git_dirty_in_build_scope();

    if dirty {
        format!("{commit}-dirty")
    } else {
        commit
    }
}

fn source_git_commit_from_env() -> Option<String> {
    let commit = env::var("AY_SOURCE_GIT_COMMIT")
        .ok()
        .filter(|value| !value.trim().is_empty())
        .or_else(|| {
            env::var("AY_SOURCE_GIT_COMMIT_SHORT")
                .ok()
                .filter(|value| !value.trim().is_empty())
        })?;

    if source_git_dirty_from_env() {
        Some(format!("{commit}-dirty"))
    } else {
        Some(commit)
    }
}

fn source_git_dirty_from_env() -> bool {
    env::var("AY_SOURCE_GIT_DIRTY")
        .ok()
        .map(|value| {
            matches!(
                value.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "dirty"
            )
        })
        .unwrap_or(false)
}

fn git_dirty_in_build_scope() -> bool {
    let mut command = Command::new("git");
    command.current_dir("../..");
    command.args(["status", "--porcelain", "--untracked-files=no", "--"]);
    command.args(REPO_DIRTY_GIT_PATHS);

    command
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .map(|stdout| !stdout.trim().is_empty())
        .unwrap_or(false)
}

fn build_increment() -> String {
    run_git(["rev-list", "--count", "HEAD"]).unwrap_or_else(|| "0".to_string())
}

fn git_path(path: &str) -> Option<String> {
    run_git(["rev-parse", "--git-path", path]).filter(|s| !s.is_empty())
}

fn build_datetime_utc() -> String {
    let epoch_seconds = env::var("SOURCE_DATE_EPOCH")
        .ok()
        .and_then(|value| value.parse::<u64>().ok())
        .or_else(current_epoch_seconds)
        .or_else(git_commit_epoch_seconds);

    epoch_seconds
        .map(format_unix_timestamp_utc)
        .unwrap_or_else(|| "unknown".to_string())
}

fn current_epoch_seconds() -> Option<u64> {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .ok()
        .map(|duration| duration.as_secs())
}

fn git_commit_epoch_seconds() -> Option<u64> {
    run_git(["show", "-s", "--format=%ct", "HEAD"]).and_then(|value| value.parse::<u64>().ok())
}

fn git_ls_files(paths: &[&str]) -> Option<Vec<String>> {
    let mut command = Command::new("git");
    command.current_dir("../..");
    command.args(["ls-files", "-z", "--"]);
    command.args(paths);

    command
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| {
            output
                .stdout
                .split(|byte| *byte == 0)
                .filter_map(|entry| {
                    if entry.is_empty() {
                        return None;
                    }
                    String::from_utf8(entry.to_vec()).ok()
                })
                .collect()
        })
}

fn format_unix_timestamp_utc(epoch_seconds: u64) -> String {
    let days = i64::try_from(epoch_seconds / 86_400).unwrap_or(i64::MAX);
    let seconds_of_day = epoch_seconds % 86_400;
    let hour = seconds_of_day / 3_600;
    let minute = (seconds_of_day % 3_600) / 60;
    let second = seconds_of_day % 60;
    let (year, month, day) = civil_from_days(days);

    format!("{year:04}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}Z")
}

fn civil_from_days(days_since_epoch: i64) -> (i32, u32, u32) {
    let z = days_since_epoch + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let day_of_era = z - (era * 146_097);
    let year_of_era =
        (day_of_era - (day_of_era / 1_460) + (day_of_era / 36_524) - (day_of_era / 146_096)) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_param = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_param + 2) / 5 + 1;
    let month = month_param + if month_param < 10 { 3 } else { -9 };
    let year = year_of_era + era * 400 + if month <= 2 { 1 } else { 0 };

    (year as i32, month as u32, day as u32)
}

fn run_git<const N: usize>(args: [&str; N]) -> Option<String> {
    Command::new("git")
        .args(args)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .map(|stdout| stdout.trim().to_string())
}
