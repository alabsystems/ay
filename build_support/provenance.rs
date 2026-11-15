// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Build provenance for the crates that show it: `ay` (CLI version, session
//! markers, feature and stats reports, CHC proof metadata), `ay-dpll` (SMT-LIB
//! `get-info :version`, the revision in capability and native-replay
//! evidence), `ay-pb` (the PB binary) and `ay-ffi` (the C API version). Each
//! build script loads this file as `mod provenance` and calls
//! [`emit_build_provenance`]. Standard library only.
//!
//! WHAT A STAMP CLAIMS. `AY_BUILD_COMMIT` names a commit C. Without `-dirty`,
//! every input of the crate is byte-identical in the working tree and in C,
//! and no untracked file sits among them. With `-dirty`, the inputs were read
//! from a tree based on C that differs from it there. The inputs are described
//! in `provenance_scope.rs`: the crate and the workspace packages it is built
//! from, what their sources embed, and the workspace build files. A change to
//! documentation, reports, scripts, tests or an unrelated crate neither
//! dirties the stamp nor retakes it.
//!
//! WHEN IT IS TAKEN. Cargo reruns a build script only when a path or variable
//! it watches changes, and a rerun recompiles the crate and every crate that
//! depends on it (twelve depend on `ay-dpll`). So a script watches its inputs
//! and nothing else, never `.git/index` and never HEAD, and runs git
//! read-only: `git status` otherwise rewrites the index, which made the next
//! build rerun every script.
//!
//! KEYED ON THE INPUTS, IN EVERY PROFILE. C is HEAD as of the last change to
//! an input. A commit, checkout or reset that leaves every input alone keeps
//! the earlier stamp, which stays true (C's inputs are the ones compiled),
//! instead of recompiling `ay-dpll` and its dependents. A release-profile
//! build once watched HEAD as well, so that C was HEAD exactly; every landing
//! builds a new commit, so its release build legs recompiled those crates
//! whatever the change touched, about 14 minutes a landing
//! (the development design notes; the development design notes DR-48). A build that must
//! name one commit exactly builds it with `AY_SOURCE_GIT_COMMIT`, as an export
//! does, or from a fresh target directory.
//!
//! Without git metadata (a `git archive` export) the commit comes from
//! `AY_SOURCE_GIT_COMMIT` (or `_SHORT`) and `AY_SOURCE_GIT_DIRTY`, else it is
//! `unknown`; set, they override git. Each run records its decision in
//! `$OUT_DIR/ay-build-provenance.txt`, which
//! `crates/ay/tests/group_misc/build_provenance_g9.rs` checks.

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

#[path = "provenance_json.rs"]
pub(crate) mod json;
#[path = "provenance_scope.rs"]
pub(crate) mod scope;

use scope::InputScope;

/// The values a stamping crate compiles in as `AY_BUILD_*`.
pub(crate) struct BuildProvenance {
    pub(crate) build_increment: String,
    pub(crate) commit: String,
    pub(crate) datetime_utc: String,
    pub(crate) stamp: String,
}

/// Variables a stamp reads besides git.
const PROVENANCE_ENV: [&str; 4] = [
    "SOURCE_DATE_EPOCH",
    "AY_SOURCE_GIT_COMMIT",
    "AY_SOURCE_GIT_COMMIT_SHORT",
    "AY_SOURCE_GIT_DIRTY",
];

/// The file each run writes into `OUT_DIR` describing what it decided.
pub(crate) const PROVENANCE_RECORD: &str = "ay-build-provenance.txt";

/// Where the stamped commit came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CommitSource {
    Environment,
    Git,
    Unavailable,
}

impl CommitSource {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::Environment => "environment",
            Self::Git => "git",
            Self::Unavailable => "unavailable",
        }
    }
}

/// What a build script knows about the crate it stamps.
pub(crate) struct StampRequest<'a> {
    pub(crate) package_dir: &'a Path,
    pub(crate) version: &'a str,
    /// The cargo running the build, for `cargo metadata`.
    pub(crate) cargo: &'a Path,
    /// `AY_SOURCE_GIT_COMMIT` (or `_SHORT`), `-dirty` already applied.
    pub(crate) commit_override: Option<String>,
    pub(crate) source_date_epoch: Option<u64>,
}

/// One run's decision: the stamp, and what Cargo must watch to retake it.
pub(crate) struct StampDecision {
    pub(crate) source: CommitSource,
    pub(crate) scope: Option<InputScope>,
    pub(crate) watched: BTreeSet<PathBuf>,
    pub(crate) provenance: BuildProvenance,
}

/// Emit the calling crate's watch list, `AY_BUILD_*` variables and record.
pub(crate) fn emit_build_provenance() -> BuildProvenance {
    for name in PROVENANCE_ENV {
        directive("rerun-if-env-changed", name);
    }
    directive("rerun-if-changed", "build.rs");
    let package_dir =
        env::var_os("CARGO_MANIFEST_DIR").map_or_else(|| PathBuf::from("."), PathBuf::from);
    let version = env::var("CARGO_PKG_VERSION").unwrap_or_else(|_| "unknown".to_string());
    let cargo = env::var_os("CARGO").map_or_else(|| PathBuf::from("cargo"), PathBuf::from);
    let decision = decide_stamp(&StampRequest {
        package_dir: &package_dir,
        version: &version,
        cargo: &cargo,
        commit_override: commit_from_env(),
        source_date_epoch: env::var("SOURCE_DATE_EPOCH")
            .ok()
            .and_then(|value| value.trim().parse().ok()),
    });
    for path in &decision.watched {
        directive("rerun-if-changed", &path.display().to_string());
    }
    if let Some(out_dir) = env::var_os("OUT_DIR") {
        let path = Path::new(&out_dir).join(PROVENANCE_RECORD);
        if let Err(error) = fs::write(&path, decision.record()) {
            directive(
                "warning",
                &format!("cannot write {}: {error}", path.display()),
            );
        }
    }
    let provenance = decision.provenance;
    for (name, value) in [
        ("AY_BUILD_INCREMENT", &provenance.build_increment),
        ("AY_BUILD_COMMIT", &provenance.commit),
        ("AY_BUILD_DATETIME_UTC", &provenance.datetime_utc),
        ("AY_BUILD_STAMP", &provenance.stamp),
    ] {
        directive("rustc-env", &format!("{name}={value}"));
    }
    provenance
}

/// One `cargo:<key>=<value>` line for Cargo.
pub(crate) fn directive(key: &str, value: &str) {
    println!("cargo:{key}={value}");
}

/// Decide the stamp for `request`, and what Cargo must watch to retake it.
pub(crate) fn decide_stamp(request: &StampRequest<'_>) -> StampDecision {
    let repository = Repository::tracking(request.package_dir);
    let head = repository.as_ref().and_then(Repository::head);
    let mut watched = BTreeSet::new();
    let mut scope = None;
    let (source, commit) = match (&request.commit_override, &repository, &head) {
        (Some(commit), _, _) => (CommitSource::Environment, commit.clone()),
        (None, Some(repository), Some(head)) => {
            let inputs = InputScope::for_package(repository, request.package_dir, request.cargo);
            let observation = inputs.observe(repository);
            watched.extend(observation.watched);
            scope = Some(inputs);
            let commit = if observation.clean {
                head.clone()
            } else {
                format!("{head}-dirty")
            };
            (CommitSource::Git, commit)
        }
        _ => (CommitSource::Unavailable, "unknown".to_string()),
    };
    // HEAD's history as of this stamp: retaken with it, when an input changes.
    let build_increment = match (&repository, &head) {
        (Some(repository), Some(head)) => repository
            .text(&["rev-list", "--count", head])
            .unwrap_or_else(|| "0".to_string()),
        _ => "0".to_string(),
    };
    let datetime_utc = request
        .source_date_epoch
        .or_else(current_epoch_seconds)
        .map_or_else(|| "unknown".to_string(), format_unix_timestamp_utc);
    let stamp = format!(
        "{}+build.{build_increment}.{commit}@{datetime_utc}",
        request.version
    );
    StampDecision {
        source,
        scope,
        watched,
        provenance: BuildProvenance {
            build_increment,
            commit,
            datetime_utc,
            stamp,
        },
    }
}

impl StampDecision {
    /// The `OUT_DIR` record: `key=value` lines, pathspecs repository-relative.
    pub(crate) fn record(&self) -> String {
        let mut record = format!(
            "commit-source={}\ncommit={}\n",
            self.source.name(),
            self.provenance.commit,
        );
        if let Some(scope) = &self.scope {
            record.push_str(&format!("scope={}\n", scope.derivation.name()));
            for package in &scope.packages {
                record.push_str(&format!("package={package}\n"));
            }
            for pathspec in &scope.pathspecs {
                record.push_str(&format!("input={pathspec}\n"));
            }
        }
        record
    }
}

fn commit_from_env() -> Option<String> {
    // Each variable is read by name, so the env ledger sees both.
    let commit = [
        env::var("AY_SOURCE_GIT_COMMIT"),
        env::var("AY_SOURCE_GIT_COMMIT_SHORT"),
    ]
    .into_iter()
    .filter_map(Result::ok)
    .map(|value| value.trim().to_string())
    .find(|value| !value.is_empty())?;
    let dirty = env::var("AY_SOURCE_GIT_DIRTY").is_ok_and(|value| {
        matches!(
            value.trim().to_ascii_lowercase().as_str(),
            "1" | "true" | "yes" | "dirty"
        )
    });
    Some(if dirty {
        format!("{commit}-dirty")
    } else {
        commit
    })
}

/// A git work tree, only ever read.
#[derive(Clone, Debug)]
pub(crate) struct Repository {
    /// The work tree's top level, absolute and symlink-free.
    pub(crate) root: PathBuf,
}

impl Repository {
    /// The work tree that tracks the package at `package_dir`. A source tree
    /// unpacked inside some unrelated repository is not tracked by it, so that
    /// repository's HEAD never becomes the crate's stamp.
    pub(crate) fn tracking(package_dir: &Path) -> Option<Self> {
        let toplevel = git_text(package_dir, &["rev-parse", "--show-toplevel"])?;
        let repository = Self {
            root: canonical(Path::new(&toplevel)),
        };
        let manifest = repository.relative(&package_dir.join("Cargo.toml"))?;
        repository
            .text(&["ls-files", "--error-unmatch", "--", &manifest])
            .map(|_| repository)
    }

    /// The full hash of HEAD.
    pub(crate) fn head(&self) -> Option<String> {
        self.text(&["rev-parse", "--verify", "--quiet", "HEAD^{commit}"])
    }

    /// Paths under `pathspecs` that differ from HEAD: modified, staged,
    /// deleted, or untracked and not ignored (an untracked file can be
    /// compiled). `None` if git could not tell.
    pub(crate) fn changes(&self, pathspecs: &[String]) -> Option<Vec<String>> {
        let mut args = vec![
            "status",
            "--porcelain=v1",
            "-z",
            "--untracked-files=all",
            "--",
        ];
        args.extend(pathspecs.iter().map(String::as_str));
        Some(split_nul(&git_stdout(&self.root, &args)?))
    }

    /// Files under `pathspecs`: tracked, and untracked but not ignored.
    pub(crate) fn files(&self, pathspecs: &[String]) -> Option<Vec<String>> {
        let mut args = vec![
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
            "--",
        ];
        args.extend(pathspecs.iter().map(String::as_str));
        Some(split_nul(&git_stdout(&self.root, &args)?))
    }

    /// `path` relative to the root, `/`-separated, if it lies inside it.
    pub(crate) fn relative(&self, path: &Path) -> Option<String> {
        let path = canonical(path);
        let relative = path.strip_prefix(&self.root).ok()?;
        let parts: Vec<&str> = relative
            .components()
            .map(|component| component.as_os_str().to_str())
            .collect::<Option<_>>()?;
        Some(if parts.is_empty() {
            ".".to_string()
        } else {
            parts.join("/")
        })
    }

    /// Trimmed, non-empty stdout of a git command run at the root.
    pub(crate) fn text(&self, args: &[&str]) -> Option<String> {
        git_text(&self.root, args)
    }
}

/// A git command that only reads: no optional index refresh (the write
/// `git status` otherwise makes), pathspecs taken literally, and the
/// repository found from `dir` rather than from an inherited `GIT_DIR`.
pub(crate) fn read_only_git(dir: &Path) -> Command {
    let mut command = Command::new("git");
    command.current_dir(dir).env("GIT_OPTIONAL_LOCKS", "0");
    for name in [
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_COMMON_DIR",
    ] {
        command.env_remove(name);
    }
    command.args(["--no-optional-locks", "--literal-pathspecs"]);
    command
}

fn git_stdout(dir: &Path, args: &[&str]) -> Option<String> {
    let output = read_only_git(dir).args(args).output().ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8(output.stdout).ok()
}

fn git_text(dir: &Path, args: &[&str]) -> Option<String> {
    git_stdout(dir, args)
        .map(|stdout| stdout.trim().to_string())
        .filter(|stdout| !stdout.is_empty())
}

fn split_nul(text: &str) -> Vec<String> {
    text.split('\0')
        .filter(|entry| !entry.is_empty())
        .map(str::to_string)
        .collect()
}

/// `path` absolute, with symlinks resolved as far as it exists and `.`/`..`
/// folded lexically beyond that.
pub(crate) fn canonical(path: &Path) -> PathBuf {
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        env::current_dir().map_or_else(|_| path.to_path_buf(), |dir| dir.join(path))
    };
    let absolute = lexically_normal(&absolute);
    for existing in absolute.ancestors() {
        if let Ok(resolved) = fs::canonicalize(existing) {
            let rest = absolute.strip_prefix(existing).unwrap_or(Path::new(""));
            return if rest.as_os_str().is_empty() {
                resolved
            } else {
                resolved.join(rest)
            };
        }
    }
    absolute
}

/// `path` with `.` and `..` components folded away lexically.
pub(crate) fn lexically_normal(path: &Path) -> PathBuf {
    let mut normal = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                if !normal.pop() {
                    normal.push("..");
                }
            }
            other => normal.push(other),
        }
    }
    normal
}

fn current_epoch_seconds() -> Option<u64> {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .ok()
        .map(|duration| duration.as_secs())
}

pub(crate) fn format_unix_timestamp_utc(epoch_seconds: u64) -> String {
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
