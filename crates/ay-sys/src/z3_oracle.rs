// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ONE resolver for the external `z3` that AY is measured against.
//!
//! z3 is AY's reference oracle: tests, gates and a few CLI commands compare
//! AY's verdicts with z3's. A comparison is only evidence when the program that
//! answered IS z3, and the name `z3` does not say so:
//!
//! * a sandbox or agent terminal can put a stub first on `PATH` under that name.
//!   aterm does, by design: its reroute stub refuses every by-name invocation
//!   (exit 2, empty stdout) because z3 is the oracle AY is measured against. A
//!   caller that spawns `z3` by name then reads that refusal as "z3 answered
//!   nothing", which silently blinds a differential leg or fails it with a
//!   verdict that never came from z3;
//! * AY itself is a z3 drop-in: run under the name `z3` (or with `--z3-mode`) it
//!   prints z3's own `Z3 version ...` banner, so a banner check alone would accept
//!   AY as its own oracle and manufacture agreement.
//!
//! So a z3 is reached BY PATH, and it must PROVE it is z3 before any verdict of
//! it is used:
//!
//! 1. `Z3_PATH`, when set and non-empty, is authoritative. It must name a path
//!    (a bare program name is refused, never looked up on `PATH`), and when that
//!    path fails identity the answer is [`Z3Unavailable::Misconfigured`], never a
//!    fallback to some other z3: the variable is consent to exactly one binary.
//! 2. Otherwise `PATH` is walked the way the aterm reroute stub's own
//!    passthrough walks it: empty and relative entries are skipped, and so is
//!    every directory holding a [`REROUTE_DIR_MARKER`] file; a candidate must be
//!    an executable non-directory, and a file whose second line is
//!    [`REROUTE_STUB_SIGNATURE`] is passed over without ever being executed. The
//!    first remaining candidate that identifies as z3 wins.
//! 3. Identity is two probes, each bounded by [`PROBE_TIMEOUT`]: `--version`
//!    must exit 0 with a first stdout line starting `Z3 version ` (the banner),
//!    AND the negative control `--z3-mode --version` must NOT succeed with a
//!    banner. Real z3 rejects `--z3-mode` as an unknown option; AY consumes it
//!    and prints the banner, which is exactly the impersonation to refuse.
//!
//! The resolved [`Z3Oracle`] carries the absolute path it was reached by, its
//! banner, and every candidate it passed over, so a caller can record WHICH z3
//! answered ([`Z3Oracle::identity`]). [`Z3Oracle::command`] builds a command
//! from that path; nothing here ever spawns `z3` by name.
//!
//! What a caller does when no z3 resolves (skip, fail, report unverified) is
//! the caller's policy, not this module's; tests take theirs from
//! `ay_test_support::z3`.

#![forbid(unsafe_code)]

use std::ffi::{OsStr, OsString};
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

mod identity;
use identity::{is_executable, vet};
pub use identity::{
    is_reroute_stub, parse_banner_version, z3_version_banner, BANNER_PREFIX, PROBE_TIMEOUT,
    REROUTE_STUB_SIGNATURE,
};

/// A directory holding a file of this name is an aterm reroute directory:
/// every program in it is a stub, and the walk skips the whole directory.
pub const REROUTE_DIR_MARKER: &str = ".atpkg-reroute-dir";

/// The environment variable naming the one z3 binary to use. Read here and
/// nowhere else; consumers call [`z3_oracle`].
const Z3_PATH_ENV: &str = "Z3_PATH";

/// The file name a `PATH` walk looks for.
#[cfg(windows)]
const PROGRAM: &str = "z3.exe";
#[cfg(not(windows))]
const PROGRAM: &str = "z3";

/// How the resolved z3 was found.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Z3Source {
    /// `Z3_PATH` named it.
    Z3PathEnv,
    /// The first identified z3 on `PATH`.
    PathSearch,
    /// A caller named this exact path (for example a `--z3 PATH` option).
    Explicit,
}

impl Z3Source {
    fn describe(self) -> &'static str {
        match self {
            Self::Z3PathEnv => "via Z3_PATH",
            Self::PathSearch => "via PATH",
            Self::Explicit => "named explicitly",
        }
    }
}

/// A candidate the resolver did not use, and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassedOver {
    /// The candidate's path.
    pub path: PathBuf,
    /// Why it is not the oracle.
    pub reason: String,
}

impl fmt::Display for PassedOver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} [{}]", self.path.display(), self.reason)
    }
}

/// A z3 that proved its identity, reachable by an absolute path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Z3Oracle {
    path: PathBuf,
    canonical: Option<PathBuf>,
    banner: String,
    source: Z3Source,
    passed_over: Vec<PassedOver>,
}

impl Z3Oracle {
    /// The absolute path the oracle was reached by.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// The first line of its `--version` output, e.g. `Z3 version 4.16.0 - 64 bit`.
    pub fn banner(&self) -> &str {
        &self.banner
    }

    /// How it was found.
    pub fn source(&self) -> Z3Source {
        self.source
    }

    /// The candidates passed over before it (reroute stubs, impostors, ...).
    pub fn passed_over(&self) -> &[PassedOver] {
        &self.passed_over
    }

    /// `(major, minor, patch)` parsed from the banner; a missing patch is 0.
    pub fn version(&self) -> Option<(u32, u32, u32)> {
        parse_banner_version(&self.banner)
    }

    /// A command that runs THIS binary, by its absolute path.
    pub fn command(&self) -> Command {
        Command::new(&self.path)
    }

    /// Banner, path (and where it resolves to), how it was found, and what was
    /// passed over: the line a report prints to say which z3 answered.
    pub fn identity(&self) -> String {
        let mut identity = format!("{} ({}", self.banner, self.path.display());
        if let Some(canonical) = self.canonical.as_ref().filter(|c| **c != self.path) {
            identity.push_str(&format!(" -> {}", canonical.display()));
        }
        identity.push_str(&format!("; {}", self.source.describe()));
        if !self.passed_over.is_empty() {
            let skipped: Vec<String> = self.passed_over.iter().map(ToString::to_string).collect();
            identity.push_str(&format!("; passed over {}", skipped.join(", ")));
        }
        identity.push(')');
        identity
    }
}

impl fmt::Display for Z3Oracle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.identity())
    }
}

/// Why no z3 is available.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Z3Unavailable {
    /// `Z3_PATH` is set but does not name a z3 this resolver accepts. There is
    /// deliberately no fallback: the variable is consent to one binary.
    Misconfigured {
        /// The variable's value.
        value: OsString,
        /// What is wrong with it.
        reason: String,
    },
    /// Nothing on `PATH` identified as z3.
    NotFound {
        /// Every candidate seen and rejected, in `PATH` order.
        passed_over: Vec<PassedOver>,
    },
}

impl Z3Unavailable {
    /// True for a set-but-wrong `Z3_PATH`, which a caller must never treat as
    /// plain absence.
    pub fn is_misconfigured(&self) -> bool {
        matches!(self, Self::Misconfigured { .. })
    }
}

impl fmt::Display for Z3Unavailable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Misconfigured { value, reason } => write!(
                f,
                "{Z3_PATH_ENV}={} is not a usable z3: {reason}",
                value.to_string_lossy()
            ),
            Self::NotFound { passed_over } if passed_over.is_empty() => {
                write!(f, "no {PROGRAM} on PATH")
            }
            Self::NotFound { passed_over } => {
                let seen: Vec<String> = passed_over.iter().map(ToString::to_string).collect();
                write!(
                    f,
                    "no {PROGRAM} on PATH identifies as z3; passed over {}",
                    seen.join(", ")
                )
            }
        }
    }
}

impl std::error::Error for Z3Unavailable {}

/// The process's z3 oracle: `Z3_PATH`, else the first identified z3 on `PATH`.
/// Resolved once per process.
pub fn z3_oracle() -> Result<&'static Z3Oracle, &'static Z3Unavailable> {
    static RESOLVED: OnceLock<Result<Z3Oracle, Z3Unavailable>> = OnceLock::new();
    RESOLVED
        .get_or_init(|| {
            resolve_z3(
                std::env::var_os(Z3_PATH_ENV).as_deref(),
                std::env::var_os("PATH").as_deref(),
            )
        })
        .as_ref()
}

/// The resolution rule over explicit inputs: `z3_path` plays `Z3_PATH` and
/// `path` plays `PATH`. Uncached; [`z3_oracle`] caches it for the process.
pub fn resolve_z3(
    z3_path: Option<&OsStr>,
    path: Option<&OsStr>,
) -> Result<Z3Oracle, Z3Unavailable> {
    match z3_path.filter(|value| !value.is_empty()) {
        Some(value) => resolve_configured(value),
        None => search_path(OsStr::new(PROGRAM), path),
    }
}

/// Resolve a user's spelling of the z3 to use (for example `--z3 VALUE`): the
/// bare name `z3` is [`z3_oracle`] (honouring `Z3_PATH`), anything else is
/// [`resolve_z3_program`] over the process `PATH`.
pub fn resolve_z3_spelling(value: &OsStr) -> Result<Z3Oracle, Z3Unavailable> {
    if value == OsStr::new("z3") || value == OsStr::new(PROGRAM) {
        z3_oracle().cloned().map_err(Clone::clone)
    } else {
        resolve_z3_program(value, std::env::var_os("PATH").as_deref())
    }
}

/// Resolve a caller-supplied z3 spelling (for example a `--z3 VALUE` option):
/// a value with a directory component is that exact file, identity-checked; a
/// bare name is looked up on `path` with the same stub-skipping walk.
pub fn resolve_z3_program(
    program: &OsStr,
    path: Option<&OsStr>,
) -> Result<Z3Oracle, Z3Unavailable> {
    if names_a_path(Path::new(program)) {
        identify_z3(Path::new(program)).map_err(|reason| Z3Unavailable::NotFound {
            passed_over: vec![PassedOver {
                path: PathBuf::from(program),
                reason,
            }],
        })
    } else {
        search_path(program, path)
    }
}

/// Identity-check one explicit path.
pub fn identify_z3(candidate: &Path) -> Result<Z3Oracle, String> {
    let path = std::path::absolute(candidate)
        .map_err(|error| format!("cannot be made absolute: {error}"))?;
    if !is_executable(&path) {
        return Err("is not an executable file".to_string());
    }
    let banner = vet(&path)?;
    Ok(oracle(path, banner, Z3Source::Explicit, Vec::new()))
}

fn resolve_configured(value: &OsStr) -> Result<Z3Oracle, Z3Unavailable> {
    let misconfigured = |reason: String| Z3Unavailable::Misconfigured {
        value: value.to_os_string(),
        reason,
    };
    let configured = Path::new(value);
    if !names_a_path(configured) {
        return Err(misconfigured(format!(
            "it names a program, not a path; {Z3_PATH_ENV} is never looked up on PATH"
        )));
    }
    identify_z3(configured)
        .map(|found| Z3Oracle {
            source: Z3Source::Z3PathEnv,
            ..found
        })
        .map_err(misconfigured)
}

fn search_path(program: &OsStr, path: Option<&OsStr>) -> Result<Z3Oracle, Z3Unavailable> {
    let mut passed_over = Vec::new();
    for candidate in path_candidates(program, path, &mut passed_over) {
        match vet(&candidate) {
            Ok(banner) => return Ok(oracle(candidate, banner, Z3Source::PathSearch, passed_over)),
            Err(reason) => passed_over.push(PassedOver {
                path: candidate,
                reason,
            }),
        }
    }
    Err(Z3Unavailable::NotFound { passed_over })
}

/// Executable `program` files on `path`, in order, after the reroute rules;
/// reroute directories and stub files are recorded in `passed_over`.
fn path_candidates(
    program: &OsStr,
    path: Option<&OsStr>,
    passed_over: &mut Vec<PassedOver>,
) -> Vec<PathBuf> {
    let Some(path) = path else {
        return Vec::new();
    };
    let mut candidates: Vec<PathBuf> = Vec::new();
    for directory in std::env::split_paths(path) {
        if !directory.is_absolute() {
            continue;
        }
        let candidate = directory.join(program);
        if directory.join(REROUTE_DIR_MARKER).is_file() {
            if candidate.exists() {
                passed_over.push(PassedOver {
                    path: candidate,
                    reason: format!("aterm reroute directory ({REROUTE_DIR_MARKER})"),
                });
            }
            continue;
        }
        if !is_executable(&candidate) || candidates.contains(&candidate) {
            continue;
        }
        if is_reroute_stub(&candidate) {
            passed_over.push(PassedOver {
                path: candidate,
                reason: "aterm reroute stub".to_string(),
            });
            continue;
        }
        candidates.push(candidate);
    }
    candidates
}

fn oracle(
    path: PathBuf,
    banner: String,
    source: Z3Source,
    passed_over: Vec<PassedOver>,
) -> Z3Oracle {
    Z3Oracle {
        canonical: std::fs::canonicalize(&path).ok(),
        path,
        banner,
        source,
        passed_over,
    }
}

/// True when `path` has a directory component (so it is a path, not a name).
fn names_a_path(path: &Path) -> bool {
    path.is_absolute()
        || path
            .parent()
            .is_some_and(|parent| !parent.as_os_str().is_empty())
}

#[cfg(test)]
#[path = "z3_oracle_tests.rs"]
mod tests;
