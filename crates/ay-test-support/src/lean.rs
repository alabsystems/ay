// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ONE Lean a test may take a kernel verdict from: the toolchain the
//! repository pins in `lean-toolchain`, run through elan by that name.
//!
//! A test that says "the Lean 4 kernel accepts this proof" is evidence only
//! when the program that answered IS the pinned Lean, and the name `lean` does
//! not say so: a bare `lean` runs whatever `PATH` resolves first. Inside an
//! aterm session that is a reroute stub which runs Trust's `clean` instead
//! (`lean f.lean` becomes `clean check f.lean`), and the ay-sat
//! lean-integration tests failed there with elaboration errors that said
//! nothing about AY.
//!
//! So a Lean is reached through elan, never by name:
//!
//! 1. [`find_toolchain_file`] walks up from the caller's directory (a test
//!    passes `env!("CARGO_MANIFEST_DIR")`) to the nearest `lean-toolchain`,
//!    whose one line names the pin, e.g. `leanprover/lean4:v4.30.0-rc2`.
//! 2. [`locate_elan`] takes `$ELAN_HOME/bin/elan`, else `~/.elan/bin/elan`,
//!    else the first `elan` on `PATH` outside aterm reroute directories that
//!    is not a reroute stub (read, never executed).
//! 3. Every command is `elan run <toolchain> <tool> ...`
//!    ([`PinnedLean::command`]): elan runs the named toolchain's own binary
//!    whatever `PATH` holds, and `run` without `--install` never downloads.
//! 4. [`pinned_lean`] then makes that Lean prove it is the pin: `lean
//!    --version` must print [`expected_banner_prefix`].
//!
//! Every failure is a [`LeanUnavailable`] whose message names the toolchain
//! it tried and the `elan toolchain install` line that provides it. What a
//! test does with one is the caller's policy.

use std::ffi::OsString;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use ay_sys::z3_oracle::{is_reroute_stub, REROUTE_DIR_MARKER};

/// The file that pins a Lean toolchain, as elan and Lake read it.
pub const TOOLCHAIN_FILE: &str = "lean-toolchain";

/// elan's executable name on this platform.
#[cfg(windows)]
const ELAN: &str = "elan.exe";
#[cfg(not(windows))]
const ELAN: &str = "elan";

/// Where elan is looked for: stand-ins for `$ELAN_HOME`, the home directory
/// and `$PATH`, so the rule can be exercised against a fake tree.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ElanSearch {
    /// `$ELAN_HOME`: elan's own install root, when set.
    pub elan_home: Option<OsString>,
    /// The home directory, whose `.elan` is elan's default root.
    pub home: Option<OsString>,
    /// `$PATH`, the last resort.
    pub path: Option<OsString>,
}

impl ElanSearch {
    /// This process's `ELAN_HOME`, home directory and `PATH`.
    pub fn from_process() -> Self {
        Self {
            elan_home: std::env::var_os("ELAN_HOME"),
            home: home_directory(),
            path: std::env::var_os("PATH"),
        }
    }
}

#[cfg(windows)]
fn home_directory() -> Option<OsString> {
    std::env::var_os("USERPROFILE")
}

#[cfg(not(windows))]
fn home_directory() -> Option<OsString> {
    std::env::var_os("HOME")
}

/// The pinned Lean toolchain and the elan that runs it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PinnedLean {
    toolchain: String,
    toolchain_file: PathBuf,
    elan: PathBuf,
}

impl PinnedLean {
    /// The toolchain name, e.g. `leanprover/lean4:v4.30.0-rc2`.
    pub fn toolchain(&self) -> &str {
        &self.toolchain
    }

    /// The `lean-toolchain` file that pinned it.
    pub fn toolchain_file(&self) -> &Path {
        &self.toolchain_file
    }

    /// The absolute path of the elan that runs it.
    pub fn elan(&self) -> &Path {
        &self.elan
    }

    /// `elan run <toolchain> <tool>`; the caller appends the tool's arguments.
    pub fn command(&self, tool: &str) -> Command {
        let mut command = Command::new(&self.elan);
        command.arg("run").arg(&self.toolchain).arg(tool);
        command
    }

    /// `elan run <toolchain> lean`.
    pub fn lean(&self) -> Command {
        self.command("lean")
    }

    /// Run `lean --version` through elan and require the pinned release's
    /// banner; returns that banner line.
    pub fn verify(&self) -> Result<String, LeanUnavailable> {
        let not_the_pin = |detail: String| LeanUnavailable::NotThePin {
            toolchain: self.toolchain.clone(),
            elan: self.elan.clone(),
            detail,
        };
        let probe = format!("`elan run {} lean --version`", self.toolchain);
        let output = self
            .lean()
            .arg("--version")
            .stdin(Stdio::null())
            .output()
            .map_err(|error| not_the_pin(format!("{probe} could not run: {error}")))?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(not_the_pin(format!(
                "{probe} failed ({}): {}",
                output.status,
                first_line(&stderr)
            )));
        }
        let stdout = String::from_utf8_lossy(&output.stdout);
        let banner = first_line(&stdout);
        let expected = expected_banner_prefix(&self.toolchain);
        if !banner.starts_with(&expected) {
            return Err(not_the_pin(format!(
                "{probe} printed {banner:?}, which does not start with {expected:?}"
            )));
        }
        Ok(banner.to_string())
    }

    /// The line a report prints to say which Lean answered.
    pub fn identity(&self) -> String {
        format!(
            "{} via {} (pinned by {})",
            self.toolchain,
            self.elan.display(),
            self.toolchain_file.display()
        )
    }
}

impl fmt::Display for PinnedLean {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.identity())
    }
}

/// Why the pinned Lean cannot be run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeanUnavailable {
    /// No `lean-toolchain` at or above the start directory.
    NoToolchainFile {
        /// Where the upward walk began.
        start: PathBuf,
    },
    /// A `lean-toolchain` that does not name exactly one toolchain.
    BadToolchainFile {
        /// The file.
        file: PathBuf,
        /// What is wrong with it.
        reason: String,
    },
    /// No elan to run the pinned toolchain with.
    NoElan {
        /// The pinned toolchain.
        toolchain: String,
        /// Every candidate looked at and refused, before `PATH`'s.
        looked_at: Vec<PathBuf>,
    },
    /// elan could not run the pinned toolchain's `lean`, or what ran is not it.
    NotThePin {
        /// The pinned toolchain.
        toolchain: String,
        /// The elan that was asked.
        elan: PathBuf,
        /// What happened instead.
        detail: String,
    },
}

impl fmt::Display for LeanUnavailable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoToolchainFile { start } => write!(
                f,
                "no {TOOLCHAIN_FILE} at or above {}, so there is no pinned Lean to run",
                start.display()
            ),
            Self::BadToolchainFile { file, reason } => write!(
                f,
                "{} does not pin one Lean toolchain: {reason}",
                file.display()
            ),
            Self::NoElan {
                toolchain,
                looked_at,
            } => {
                let looked: Vec<String> = looked_at
                    .iter()
                    .map(|path| path.display().to_string())
                    .collect();
                write!(
                    f,
                    "no elan found to run the pinned Lean toolchain {toolchain} \
                     (looked at [{}] and PATH). {}",
                    looked.join(", "),
                    install_hint(toolchain)
                )
            }
            Self::NotThePin {
                toolchain,
                elan,
                detail,
            } => write!(
                f,
                "{} cannot run the pinned Lean toolchain {toolchain}: {detail}. {}",
                elan.display(),
                install_hint(toolchain)
            ),
        }
    }
}

impl std::error::Error for LeanUnavailable {}

/// How to provide `toolchain`: elan, then the named toolchain.
pub fn install_hint(toolchain: &str) -> String {
    format!(
        "Install elan (https://github.com/leanprover/elan), then the toolchain: \
         `elan toolchain install {toolchain}`"
    )
}

/// The start of `lean --version`'s first line for `toolchain`:
/// `Lean (version 4.30.0-rc2,` for the release pin
/// `leanprover/lean4:v4.30.0-rc2`, and the bare `Lean (version ` for a
/// channel pin (`stable`, `nightly-...`) that names no release.
pub fn expected_banner_prefix(toolchain: &str) -> String {
    let release = toolchain
        .rsplit(':')
        .next()
        .and_then(|tag| tag.strip_prefix('v'))
        .filter(|version| version.starts_with(|c: char| c.is_ascii_digit()));
    match release {
        Some(version) => format!("Lean (version {version},"),
        None => "Lean (version ".to_string(),
    }
}

/// The nearest `lean-toolchain` at or above `start`.
pub fn find_toolchain_file(start: &Path) -> Option<PathBuf> {
    start
        .ancestors()
        .map(|directory| directory.join(TOOLCHAIN_FILE))
        .find(|file| file.is_file())
}

/// The toolchain `file` pins: its one non-empty line, which must be a single
/// token.
pub fn read_toolchain(file: &Path) -> Result<String, LeanUnavailable> {
    let bad = |reason: String| LeanUnavailable::BadToolchainFile {
        file: file.to_path_buf(),
        reason,
    };
    let text =
        std::fs::read_to_string(file).map_err(|error| bad(format!("unreadable: {error}")))?;
    let names: Vec<&str> = text.split_whitespace().collect();
    match names.as_slice() {
        [toolchain] => Ok((*toolchain).to_string()),
        [] => Err(bad("it is empty".to_string())),
        _ => Err(bad(format!("it names {} tokens: {names:?}", names.len()))),
    }
}

/// elan: `$ELAN_HOME/bin/elan`, else `<home>/.elan/bin/elan`, else the first
/// executable `elan` on `PATH` outside an aterm reroute directory that is not
/// a reroute stub. Only absolute locations count, and nothing is executed.
/// `Err` lists every existing or expected candidate that was refused.
pub fn locate_elan(search: &ElanSearch) -> Result<PathBuf, Vec<PathBuf>> {
    let mut looked_at = Vec::new();
    let roots = [
        search.elan_home.as_ref().map(PathBuf::from),
        search
            .home
            .as_ref()
            .map(|home| Path::new(home).join(".elan")),
    ];
    for root in roots.into_iter().flatten() {
        let candidate = root.join("bin").join(ELAN);
        if root.is_absolute() && is_runnable_elan(&candidate) {
            return Ok(candidate);
        }
        looked_at.push(candidate);
    }
    let directories = search.path.as_ref().map(std::env::split_paths);
    for directory in directories.into_iter().flatten() {
        let candidate = directory.join(ELAN);
        let rerouted = directory.join(REROUTE_DIR_MARKER).is_file();
        if directory.is_absolute() && !rerouted && is_runnable_elan(&candidate) {
            return Ok(candidate);
        }
        if candidate.exists() {
            looked_at.push(candidate);
        }
    }
    Err(looked_at)
}

/// Resolve without running anything: the pin nearest `start` and the elan
/// that runs it.
pub fn resolve_pinned_lean(
    start: &Path,
    search: &ElanSearch,
) -> Result<PinnedLean, LeanUnavailable> {
    let toolchain_file =
        find_toolchain_file(start).ok_or_else(|| LeanUnavailable::NoToolchainFile {
            start: start.to_path_buf(),
        })?;
    let toolchain = read_toolchain(&toolchain_file)?;
    let elan = locate_elan(search).map_err(|looked_at| LeanUnavailable::NoElan {
        toolchain: toolchain.clone(),
        looked_at,
    })?;
    Ok(PinnedLean {
        toolchain,
        toolchain_file,
        elan,
    })
}

/// The pinned Lean for a test rooted at `start`: resolved from this process's
/// environment, then made to prove it is the pin ([`PinnedLean::verify`]).
pub fn pinned_lean(start: impl AsRef<Path>) -> Result<PinnedLean, LeanUnavailable> {
    let lean = resolve_pinned_lean(start.as_ref(), &ElanSearch::from_process())?;
    lean.verify()?;
    Ok(lean)
}

fn is_runnable_elan(candidate: &Path) -> bool {
    is_executable_file(candidate) && !is_reroute_stub(candidate)
}

fn is_executable_file(path: &Path) -> bool {
    let Ok(metadata) = std::fs::metadata(path) else {
        return false;
    };
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        metadata.is_file() && metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        metadata.is_file()
    }
}

fn first_line(text: &str) -> &str {
    text.lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .unwrap_or_default()
}

#[cfg(test)]
#[path = "lean_tests.rs"]
mod tests;
