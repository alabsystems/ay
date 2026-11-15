// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Workspace roots with a chosen git state for the `ay submission worker
//! chc-comp` tests.
//!
//! The worker takes its workspace root to be the nearest ancestor of its
//! working directory holding `Cargo.toml` and `crates/ay/Cargo.toml`, records
//! that root's git HEAD, branch and porcelain status as the report's
//! provenance, and fails closed on `repo:commit` when the root has no HEAD. A
//! worker spawned from the test's inherited working directory therefore reads
//! the git state of whatever tree the test binary was built from: the run test
//! passed in a git worktree and failed in a `git archive` export, alone or in
//! parallel. Each test builds its own root here and confines git to it.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::{json, Value};
use tempfile::tempdir;

use super::assert_command_success;

/// Ambient variables that point git at a repository other than the one it
/// discovers from its working directory, or inject configuration that the
/// isolated global and system files do not cover (`git -c` exports
/// `GIT_CONFIG_PARAMETERS` to every child, e.g. under `git rebase -x`).
const AMBIENT_GIT_OVERRIDES: [&str; 9] = [
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_INDEX_FILE",
    "GIT_OBJECT_DIRECTORY",
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_COMMON_DIR",
    "GIT_NAMESPACE",
    "GIT_CONFIG_PARAMETERS",
    "GIT_CONFIG_COUNT",
];

/// A worker workspace root at `<parent>/worker-workspace`. Git may not search
/// above `parent`, so the root's own state is the only state git can report.
pub(super) struct WorkerRepoRoot {
    root: PathBuf,
    ceiling: PathBuf,
}

impl WorkerRepoRoot {
    /// A workspace root that no git repository contains.
    pub(super) fn without_git(parent: &Path) -> Self {
        fs::create_dir_all(parent).expect("create worker root parent");
        let ceiling = fs::canonicalize(parent).expect("canonicalize worker root parent");
        let root = ceiling.join("worker-workspace");
        fs::create_dir_all(root.join("crates/ay")).expect("create worker workspace root");
        for marker in ["Cargo.toml", "crates/ay/Cargo.toml"] {
            fs::write(root.join(marker), "# CHC worker test workspace marker\n")
                .unwrap_or_else(|err| panic!("write worker workspace {marker}: {err}"));
        }
        Self { root, ceiling }
    }

    /// A clean git checkout on `main` holding one commit, and that commit.
    pub(super) fn with_clean_main_commit(parent: &Path) -> (Self, String) {
        let repo = Self::without_git(parent);
        repo.git(&["init", "-q"]);
        repo.git(&["symbolic-ref", "HEAD", "refs/heads/main"]);
        repo.git(&["add", "-A"]);
        repo.git(&["commit", "-q", "--no-verify", "-m", "CHC worker workspace"]);
        let head = repo.git(&["rev-parse", "HEAD"]);
        assert_eq!(head.len(), 40, "fixture HEAD should be a full sha: {head}");
        (repo, head)
    }

    /// An `ay` command that runs from this root with git confined to it.
    pub(super) fn ay_command(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
        self.confine(&mut command);
        // The worker extracts the package archive (the whole `ay` binary) into
        // `$TMPDIR` and never removes it; keep that copy inside the test's
        // temp dir, beside the root rather than in it.
        command.env("TMPDIR", &self.ceiling);
        command
    }

    fn confine(&self, command: &mut Command) {
        command.current_dir(&self.root);
        for variable in AMBIENT_GIT_OVERRIDES {
            command.env_remove(variable);
        }
        command
            .env("GIT_CEILING_DIRECTORIES", &self.ceiling)
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_NOSYSTEM", "1");
    }

    fn git(&self, args: &[&str]) -> String {
        let mut command = Command::new("git");
        self.confine(&mut command);
        let output = command
            .args(args)
            .env("GIT_AUTHOR_NAME", "ay test")
            .env("GIT_AUTHOR_EMAIL", "ay-test@example.invalid")
            .env("GIT_COMMITTER_NAME", "ay test")
            .env("GIT_COMMITTER_EMAIL", "ay-test@example.invalid")
            .output()
            .unwrap_or_else(|err| panic!("spawn git {args:?}: {err}"));
        assert_command_success(&output, &format!("git {args:?}"));
        String::from_utf8_lossy(&output.stdout).trim().to_string()
    }
}

/// Run the package-only worker lane (no solver) from `repo` and parse its report.
fn run_package_only_worker(repo: &WorkerRepoRoot, package: &Path, json: &Path) -> (Output, Value) {
    let output = repo
        .ay_command()
        .args(["submission", "worker", "chc-comp", "run", "--issue", "9692"])
        .args(["--lane", "test-lane", "--tracks", "BV-Lin"])
        .args(["--skip-benchmark-smoke", "--allow-dirty", "--no-gh"])
        .arg("--package")
        .arg(package)
        .arg("--json")
        .arg(json)
        .arg("--report")
        .arg(json.with_extension("md"))
        .output()
        .expect("run CHC worker lane");
    let report = fs::read_to_string(json).expect("worker JSON");
    let report: Value = serde_json::from_str(&report).expect("worker JSON parses");
    (output, report)
}

/// Audit `report` from `repo` under both waivers and return its failing
/// checks, each named by the part of the check name after the report label.
fn waived_audit_failures(repo: &WorkerRepoRoot, report: &Path) -> Vec<(String, String)> {
    let audit_json = report.with_extension("audit.json");
    let output = repo
        .ay_command()
        .args(["submission", "worker", "chc-comp", "audit"])
        .arg(report)
        .args(["--allow-dirty", "--allow-stale-package", "--json"])
        .arg(&audit_json)
        .output()
        .expect("audit CHC worker report");
    let audit = fs::read_to_string(&audit_json).expect("worker audit JSON");
    let audit: Value = serde_json::from_str(&audit).expect("worker audit JSON parses");
    assert_eq!(
        output.status.success(),
        audit["summary"]["audit_ready"] == true,
        "audit exit status must match audit_ready; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    failing_checks(&audit)
        .into_iter()
        .map(|(name, detail)| (name.rsplit(':').next().unwrap_or("").to_string(), detail))
        .collect()
}

fn failing_checks(payload: &Value) -> Vec<(String, String)> {
    payload["checks"]
        .as_array()
        .expect("checks array")
        .iter()
        .filter(|check| check["status"] == "fail")
        .map(|check| {
            let name = check["name"].as_str().unwrap_or("").to_string();
            (name, check["detail"].as_str().unwrap_or("").to_string())
        })
        .collect()
}

/// Negative twin of `submission_worker_chc_comp_run_writes_report_and_audit_accepts`:
/// the same package and flags pass from a git root, while a root with no git
/// HEAD fails the run on `repo:commit` alone. The audit refuses both reports
/// for having no benchmark cases (the smoke is skipped here), and refuses the
/// bare root's report additionally for its missing commit, which neither
/// `--allow-dirty` nor `--allow-stale-package` waives.
#[test]
fn submission_worker_chc_comp_run_fails_closed_without_repo_commit() {
    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("chc-package");
    let package_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "package", "chc", "--output"])
        .arg(&package_dir)
        .args(["--ay-bin", env!("CARGO_BIN_EXE_ay")])
        .output()
        .expect("run ay submission package chc");
    assert_command_success(&package_output, "package chc");

    let (git_root, head) = WorkerRepoRoot::with_clean_main_commit(&temp.path().join("git"));
    let git_json = temp.path().join("git-run.json");
    let (output, report) = run_package_only_worker(&git_root, &package_dir, &git_json);
    assert_command_success(&output, "CHC worker lane from a git root");
    assert_eq!(report["repo"]["commit"], head.as_str());
    let git_failures = failing_checks(&report);
    assert!(
        git_failures.is_empty(),
        "git root failures: {git_failures:?}"
    );

    let bare_root = WorkerRepoRoot::without_git(&temp.path().join("bare"));
    let bare_json = temp.path().join("bare-run.json");
    let (output, report) = run_package_only_worker(&bare_root, &package_dir, &bare_json);
    assert!(
        !output.status.success(),
        "a worker root without a git HEAD must fail the run; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stderr).contains("status=fail"));
    assert_eq!(report["repo"]["commit"], "unavailable");
    let only_repo_commit = [(
        "repo:commit".to_string(),
        "git commit unavailable".to_string(),
    )];
    assert_eq!(failing_checks(&report), only_repo_commit);
    assert_eq!(
        report["blockers"],
        json!(["repo:commit: git commit unavailable"])
    );

    let no_cases = (
        "cases".to_string(),
        "worker report has no benchmark cases".to_string(),
    );
    let missing_commit = ("repo_commit".to_string(), "missing repo commit".to_string());
    assert_eq!(
        waived_audit_failures(&git_root, &git_json),
        [no_cases.clone()]
    );
    assert_eq!(
        waived_audit_failures(&bare_root, &bare_json),
        [missing_commit, no_cases]
    );
}
