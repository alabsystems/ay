// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Exact-source helpers for integration tests that execute workspace binaries.
//!
//! Nested Cargo builds run from immutable snapshots and bind their output to
//! exact workspace bytes, selected external Cargo package trees, Cargo/rustc,
//! configuration, deterministic environment inputs (including an explicit
//! Cargo job cap), and an inventoried set of build tools. Returned executables
//! are frozen and provenance-checked before every execution.
//!
//! This is deliberately not a claim of total platform hermeticity. The running
//! kernel, dynamic loader, dynamic system libraries, and platform SDK contents
//! remain trusted platform inputs. Their selected paths/environment are bound
//! where practical, but their complete transitive runtime behavior is outside
//! this helper's guarantee. Cargo dependencies and their build scripts are also
//! trusted: subprocesses are not OS-sandboxed and can deliberately open other
//! absolute host paths even though ambient home and temporary-directory
//! variables are withheld.

pub mod env;
pub mod veripb;

use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{OsStr, OsString};
use std::fmt::Write as _;
use std::fs as filesystem;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(unix)]
use std::os::unix::ffi::{OsStrExt as _, OsStringExt as _};
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt as _;

/// How a nested binary is bound to the exact source tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceBinding {
    /// Bind the isolated target name to the source identity.
    ///
    /// Use this for binaries without a machine-readable version/provenance
    /// endpoint. Cargo is still invoked on every request.
    IdentityTarget,
    /// Bind the target name to the identity, embed the identity through AY's
    /// build provenance environment, and verify it by executing
    /// `BINARY --version` after the build.
    AyVersion,
    /// Embed and authenticate exact source and build identities through the
    /// binary's machine-readable `--provenance` endpoint.
    ExactProvenance,
}

/// Description of a workspace binary needed by an integration test.
#[derive(Clone, Copy, Debug)]
pub struct WorkspaceBinarySpec<'a> {
    /// Canonicalizable Cargo workspace root.
    pub workspace: &'a Path,
    /// Single-component isolated Cargo target name or prefix.
    pub target_name: &'a str,
    /// Cargo package name.
    pub package: &'a str,
    /// Cargo binary target name.
    pub binary: &'a str,
    /// Cargo features required by the binary.
    pub features: &'a [&'a str],
    /// Exact-source binding strategy.
    pub source_binding: SourceBinding,
}

/// Result of a successful exact-source, inventoried nested workspace build.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BuiltWorkspaceBinary {
    /// Frozen executable copied out of Cargo's mutable target directory.
    artifact_path: PathBuf,
    /// Identity of the exact frozen executable bytes, type, and mode.
    artifact_identity: String,
    /// Environment used for endpoint verification and actual executions.
    execution_environment: BTreeMap<OsString, OsString>,
    /// Endpoint contract required for this executable.
    source_binding: SourceBinding,
    /// Identity of the source used throughout the build.
    pub source_identity: String,
    /// Identity of the sanitized Cargo, compiler, configuration, environment,
    /// and invocation used throughout the build.
    pub build_identity: String,
    /// Isolated Cargo target containing the executable.
    pub target_dir: PathBuf,
    /// Immutable source snapshot from which Cargo built the executable.
    pub snapshot_dir: PathBuf,
}

static UNIQUE_PATH_SEQUENCE: AtomicU64 = AtomicU64::new(0);

const EXACT_PROVENANCE_SCHEMA: &str = "ay-exact-binary-provenance-v1";
const EXACT_PROVENANCE_FLAG: &str = "--provenance";
const CARGO_BUILD_JOBS_ENV: &str = "CARGO_BUILD_JOBS";
const NBCORE_ENV: &str = "NBCORE";
const OOM_GUARD_PARENT_LEASE_ENV: &str = "AY_OOM_GUARD_PARENT_LEASE";
const PARENT_NESTED_CARGO_LOCK_FILE: &str = "ay-test-parent-nested-cargo-v1.lock";

/// Shared isolated target name for exact-source AY CLI integration tests.
pub const AY_CLI_TARGET_NAME: &str = "ay-test-ay-cli";
/// Shared isolated target name for exact-source AY checker integration tests.
pub const AY_CHECKER_TARGET_NAME: &str = "ay-test-checker";

/// Return the isolated Cargo target name for one exact source identity.
///
/// Every binding mode uses an identity-specific directory. Provenance checks
/// alone cannot protect an already-returned executable path from a concurrent
/// build of changed source overwriting that same path after verification.
pub fn source_bound_target_name(target_name: &str, source_identity: &str) -> String {
    assert!(
        !source_identity.is_empty(),
        "source identity must not be empty"
    );
    format!("{target_name}-{source_identity}")
}

/// Return the isolated Cargo target name for exact source and build inputs.
///
/// Source identity alone is insufficient: Cargo can otherwise reuse or
/// overwrite the same executable across compiler, configuration, environment,
/// or feature changes.
pub fn build_bound_target_name(
    target_name: &str,
    source_identity: &str,
    build_identity: &str,
) -> String {
    assert!(
        !build_identity.is_empty(),
        "build identity must not be empty"
    );
    format!(
        "{}-{build_identity}",
        source_bound_target_name(target_name, source_identity)
    )
}

fn canonicalize_existing_parent(path: PathBuf) -> PathBuf {
    if let Ok(canonical) = path.canonicalize() {
        return canonical;
    }
    let Some(name) = path.file_name() else {
        return path;
    };
    path.parent()
        .and_then(|parent| parent.canonicalize().ok())
        .map_or(path.clone(), |parent| parent.join(name))
}

fn cargo_target_root_from(workspace: &Path, configured: Option<&OsStr>) -> PathBuf {
    let configured = configured.filter(|value| !value.is_empty());
    let Some(configured) = configured else {
        return canonicalize_existing_parent(workspace.join("target"));
    };
    let path = PathBuf::from(configured);
    let configured_root = if path.is_absolute() {
        path
    } else {
        workspace.join(path)
    };
    let configured_root = canonicalize_existing_parent(configured_root);
    let mut hasher = Sha256::new();
    hash_component(
        &mut hasher,
        b"schema",
        b"ay-test-target-workspace-namespace-v1",
    );
    hash_os_component(&mut hasher, b"workspace", workspace.as_os_str());
    configured_root
        .join("ay-test-workspaces-v1")
        .join(finish_source_identity(hasher))
}

/// Select the writable outer Cargo target root for test build artifacts.
///
/// An explicit `CARGO_TARGET_DIR` controls only artifact storage. Exact-source
/// nested builds still receive a sanitized environment and an explicit,
/// source-and-build-bound `--target-dir` below this root. Relative overrides
/// are resolved against the canonical workspace.
#[must_use]
pub fn cargo_target_root(workspace: &Path) -> PathBuf {
    let workspace = workspace
        .canonicalize()
        .unwrap_or_else(|_| workspace.to_path_buf());
    cargo_target_root_from(&workspace, std::env::var_os("CARGO_TARGET_DIR").as_deref())
}

fn prepare_selected_cargo_target_root(target_root: PathBuf) -> PathBuf {
    let parent = target_root
        .parent()
        .expect("Cargo target root should have a parent");
    filesystem::create_dir_all(parent).unwrap_or_else(|error| {
        panic!(
            "failed to create Cargo target namespace {}: {error}",
            parent.display()
        )
    });
    for directory in [parent, target_root.as_path()] {
        filesystem::create_dir_all(directory).unwrap_or_else(|error| {
            panic!(
                "failed to create Cargo target directory {}: {error}",
                directory.display()
            )
        });
        let metadata = filesystem::symlink_metadata(directory).unwrap_or_else(|error| {
            panic!(
                "failed to inspect Cargo target directory {}: {error}",
                directory.display()
            )
        });
        assert!(
            metadata.is_dir() && !metadata.file_type().is_symlink(),
            "Cargo target directory is not a real directory: {}",
            directory.display()
        );
    }
    target_root
        .canonicalize()
        .expect("Cargo target root should be canonicalizable")
}

fn prepare_cargo_target_root(workspace: &Path) -> PathBuf {
    prepare_selected_cargo_target_root(cargo_target_root(workspace))
}

fn isolated_cargo_target_dir_for_outer_in(
    target_root: &Path,
    target_name: &str,
    outer_exe: Option<&Path>,
) -> PathBuf {
    let primary = canonicalize_existing_parent(target_root.join(target_name));
    let outer_exe = outer_exe.map(|path| canonicalize_existing_parent(path.to_path_buf()));
    if outer_exe
        .as_deref()
        .is_some_and(|executable| executable.starts_with(&primary))
    {
        return canonicalize_existing_parent(
            target_root.join(format!("{target_name}-nested-{}", std::process::id())),
        );
    }
    primary
}

/// Select an isolated nested Cargo target without sharing the outer test
/// process's target lock. `target_name` must be one path component.
pub fn isolated_cargo_target_dir_for_outer(
    workspace: &Path,
    target_name: &str,
    outer_exe: Option<&Path>,
) -> PathBuf {
    assert!(
        !target_name.is_empty()
            && Path::new(target_name).components().count() == 1
            && Path::new(target_name)
                .file_name()
                .is_some_and(|name| name == target_name),
        "isolated Cargo target name must be one non-empty path component"
    );
    let target_root = cargo_target_root(workspace);
    isolated_cargo_target_dir_for_outer_in(&target_root, target_name, outer_exe)
}

/// Select an isolated nested Cargo target for the current executable.
pub fn isolated_cargo_target_dir(workspace: &Path, target_name: &str) -> PathBuf {
    let outer_exe = std::env::current_exe().ok();
    isolated_cargo_target_dir_for_outer(workspace, target_name, outer_exe.as_deref())
}

/// Return the host binary path inside an explicit Cargo target directory.
pub fn cargo_binary_path(target_dir: &Path, binary: &str) -> PathBuf {
    target_dir
        .join("debug")
        .join(format!("{binary}{}", std::env::consts::EXE_SUFFIX))
}

/// Normalize a PATH to existing canonical absolute directories.
///
/// Empty or relative components are rejected instead of being interpreted
/// relative to a mutable current directory. Nonexistent absolute components
/// are omitted so they cannot appear later and silently change tool choice.
fn normalized_absolute_path(path: Option<&OsStr>) -> OsString {
    let path = path.expect("PATH is required to select exact build tools");
    let mut directories = Vec::new();
    let mut seen = BTreeSet::new();
    for directory in std::env::split_paths(path) {
        assert!(
            !directory.as_os_str().is_empty(),
            "PATH contains an empty, current-directory-relative component"
        );
        assert!(
            directory.is_absolute(),
            "PATH contains relative component {}",
            directory.display()
        );
        if !directory.is_dir() {
            continue;
        }
        let canonical = directory.canonicalize().unwrap_or_else(|error| {
            panic!(
                "failed to canonicalize PATH directory {}: {error}",
                directory.display()
            )
        });
        if seen.insert(canonical.clone()) {
            directories.push(canonical);
        }
    }
    assert!(
        !directories.is_empty(),
        "PATH has no existing absolute directories"
    );
    std::env::join_paths(directories).expect("canonical PATH should be joinable")
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct GitContext {
    executable: PathBuf,
    environment: BTreeMap<OsString, OsString>,
    identity: String,
}

fn git_null_device() -> &'static str {
    if cfg!(windows) {
        "NUL"
    } else {
        "/dev/null"
    }
}

fn git_environment() -> BTreeMap<OsString, OsString> {
    let mut environment = environment_subset(&["SYSTEMROOT", "WINDIR"]);
    environment.insert("GIT_CONFIG_GLOBAL".into(), git_null_device().into());
    environment.insert("GIT_CONFIG_NOSYSTEM".into(), "1".into());
    environment.insert("GIT_CONFIG_SYSTEM".into(), git_null_device().into());
    environment.insert("GIT_OPTIONAL_LOCKS".into(), "0".into());
    environment.insert("GIT_TERMINAL_PROMPT".into(), "0".into());
    environment
}

fn git_tool_identity(
    executable: &Path,
    environment: &BTreeMap<OsString, OsString>,
    workspace: &Path,
) -> String {
    let version = checked_tool_output(executable, &["--version"], workspace, environment);
    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-git-tool-v1");
    hash_file_input(&mut hasher, b"git", executable);
    hash_component(&mut hasher, b"git-version", &version);
    hash_environment(&mut hasher, environment);
    finish_source_identity(hasher)
}

impl GitContext {
    fn resolve(workspace: &Path) -> Self {
        // Git is necessarily part of the source-discovery trust boundary.
        // Resolve it once, clear ambient GIT_* overrides, and bind its absolute
        // executable bytes plus version to the resulting source identity.
        let path = normalized_absolute_path(std::env::var_os("PATH").as_deref());
        let executable = resolve_program(OsStr::new("git"), Some(&path));
        let environment = git_environment();
        let identity = git_tool_identity(&executable, &environment, workspace);
        Self {
            executable,
            environment,
            identity,
        }
    }

    fn assert_unchanged(&self, workspace: &Path) {
        let actual = git_tool_identity(&self.executable, &self.environment, workspace);
        assert_eq!(
            actual, self.identity,
            "Git executable changed while computing exact workspace source identity"
        );
    }
}

fn git_output_with(context: &GitContext, workspace: &Path, args: &[&str]) -> Vec<u8> {
    let output = Command::new(&context.executable)
        .args(["--literal-pathspecs", "-c"])
        .arg(format!("core.excludesFile={}", git_null_device()))
        .args(args)
        .current_dir(workspace)
        .env_clear()
        .envs(&context.environment)
        .output()
        .unwrap_or_else(|error| panic!("failed to run git {args:?}: {error}"));
    assert!(
        output.status.success(),
        "{} {args:?} failed with status {}: {}",
        context.executable.display(),
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

fn hash_component(hasher: &mut Sha256, label: &[u8], value: &[u8]) {
    hasher.update((label.len() as u64).to_le_bytes());
    hasher.update(label);
    hasher.update((value.len() as u64).to_le_bytes());
    hasher.update(value);
}

fn finish_source_identity(hasher: Sha256) -> String {
    let digest = hasher.finalize();
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        write!(&mut hex, "{byte:02x}").expect("writing to String cannot fail");
    }
    format!("source-sha256-{hex}")
}

fn git_paths(context: &GitContext, workspace: &Path, args: &[&str]) -> Vec<Vec<u8>> {
    let output = git_output_with(context, workspace, args);
    let mut paths = output
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
        .map(<[u8]>::to_vec)
        .collect::<Vec<_>>();
    paths.sort_unstable();
    paths.dedup();
    paths
}

#[derive(Debug, Eq, PartialEq)]
struct GitTrackedEntry {
    path: Vec<u8>,
    index_mode: Vec<u8>,
}

fn git_tracked_entries(context: &GitContext, workspace: &Path) -> Vec<GitTrackedEntry> {
    let output = git_output_with(context, workspace, &["ls-files", "-z", "--stage"]);
    let mut entries = output
        .split(|byte| *byte == 0)
        .filter(|entry| !entry.is_empty())
        .map(|entry| {
            let tab = entry
                .iter()
                .position(|byte| *byte == b'\t')
                .unwrap_or_else(|| panic!("malformed git ls-files --stage entry: {entry:?}"));
            let metadata = entry[..tab].split(|byte| *byte == b' ').collect::<Vec<_>>();
            assert_eq!(
                metadata.len(),
                3,
                "malformed git ls-files --stage metadata: {:?}",
                &entry[..tab]
            );
            assert_eq!(
                metadata[2],
                b"0",
                "unmerged index entry cannot identify one exact worktree source: {:?}",
                &entry[tab + 1..]
            );
            GitTrackedEntry {
                path: entry[tab + 1..].to_vec(),
                index_mode: metadata[0].to_vec(),
            }
        })
        .collect::<Vec<_>>();
    entries.sort_unstable_by(|left, right| left.path.cmp(&right.path));
    assert!(
        entries.windows(2).all(|pair| pair[0].path != pair[1].path),
        "duplicate tracked paths cannot identify one exact worktree source"
    );
    entries
}

#[cfg(unix)]
fn path_component_from_git_bytes(path: &[u8]) -> OsString {
    OsString::from_vec(path.to_vec())
}

#[cfg(not(unix))]
fn path_component_from_git_bytes(path: &[u8]) -> OsString {
    String::from_utf8(path.to_vec())
        .unwrap_or_else(|error| {
            panic!("non-UTF-8 Git path is unsupported on this platform: {error}")
        })
        .into()
}

#[cfg(unix)]
fn os_str_identity_bytes(value: &OsStr) -> Vec<u8> {
    value.as_bytes().to_vec()
}

#[cfg(windows)]
fn os_str_identity_bytes(value: &OsStr) -> Vec<u8> {
    use std::os::windows::ffi::OsStrExt as _;

    value
        .encode_wide()
        .flat_map(u16::to_le_bytes)
        .collect::<Vec<_>>()
}

#[cfg(not(any(unix, windows)))]
fn os_str_identity_bytes(value: &OsStr) -> Vec<u8> {
    value.to_string_lossy().as_bytes().to_vec()
}

#[cfg(unix)]
fn permission_identity_bytes(metadata: &std::fs::Metadata) -> Vec<u8> {
    metadata.permissions().mode().to_le_bytes().to_vec()
}

#[cfg(not(unix))]
fn permission_identity_bytes(metadata: &std::fs::Metadata) -> Vec<u8> {
    vec![u8::from(metadata.permissions().readonly())]
}

fn hash_worktree_entry(
    hasher: &mut Sha256,
    workspace: &Path,
    scope: &[u8],
    relative_bytes: &[u8],
    tracked_index_mode: Option<&[u8]>,
) {
    hash_component(hasher, b"entry-scope", scope);
    hash_component(hasher, b"entry-path", relative_bytes);
    if let Some(index_mode) = tracked_index_mode {
        hash_component(hasher, b"entry-index-mode", index_mode);
    }

    let relative = PathBuf::from(path_component_from_git_bytes(relative_bytes));
    let path = workspace.join(&relative);
    let metadata = match std::fs::symlink_metadata(&path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            assert_ne!(
                tracked_index_mode,
                Some(b"160000".as_slice()),
                "tracked gitlink {} is uninitialized",
                path.display()
            );
            hash_component(hasher, b"entry-kind", b"missing");
            return;
        }
        Err(error) => panic!("failed to inspect {}: {error}", path.display()),
    };
    hash_component(hasher, b"entry-mode", &permission_identity_bytes(&metadata));

    let file_type = metadata.file_type();
    if file_type.is_symlink() {
        hash_component(hasher, b"entry-kind", b"symlink");
        let target = std::fs::read_link(&path)
            .unwrap_or_else(|error| panic!("failed to read link {}: {error}", path.display()));
        hash_component(
            hasher,
            b"entry-link-target",
            &os_str_identity_bytes(target.as_os_str()),
        );
    } else if file_type.is_file() {
        hash_component(hasher, b"entry-kind", b"file");
        let contents = std::fs::read(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        hash_component(hasher, b"entry-contents", &contents);
    } else if file_type.is_dir() {
        assert_eq!(
            tracked_index_mode,
            Some(b"160000".as_slice()),
            "tracked non-gitlink unexpectedly became directory: {}",
            path.display()
        );
        // Gitlinks are the only directories Git tracks. Bind the nested
        // repository's actual worktree too, not merely the superproject's
        // recorded commit, so dirty submodule source cannot reuse a binary.
        hash_component(hasher, b"entry-kind", b"directory");
        let nested_identity = workspace_source_identity(&path);
        hash_component(hasher, b"entry-nested-worktree", nested_identity.as_bytes());
    } else {
        hash_component(hasher, b"entry-kind", b"other");
    }
}

/// Build a deterministic identity from a Git HEAD, serialized tracked state,
/// and `(path, contents)` pairs for non-ignored untracked files.
///
/// This lower-level constructor is useful for tests and path planning. Real
/// workspace identities use [`workspace_source_identity`] so index flags
/// cannot hide worktree changes.
pub fn source_identity_from_parts(
    head: &[u8],
    tracked_state: &[u8],
    untracked: &[(Vec<u8>, Vec<u8>)],
) -> String {
    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-source-v2");
    hash_component(&mut hasher, b"head", head);
    hash_component(&mut hasher, b"tracked-state", tracked_state);
    let mut untracked = untracked.iter().collect::<Vec<_>>();
    untracked.sort_unstable_by(|left, right| left.0.cmp(&right.0));
    for (relative, contents) in untracked {
        hash_component(&mut hasher, b"entry-scope", b"untracked");
        hash_component(&mut hasher, b"entry-path", relative);
        hash_component(&mut hasher, b"entry-contents", contents);
    }
    finish_source_identity(hasher)
}

/// Bind a nested test build to the exact checked-out source, including
/// every tracked worktree entry and every non-ignored untracked entry.
///
/// Tracked paths are read from the filesystem rather than represented by
/// `git diff`: `assume-unchanged` and `skip-worktree` index flags are allowed
/// to suppress diffs but must never make a stale test binary look current.
pub fn workspace_source_identity(workspace: &Path) -> String {
    let workspace = workspace
        .canonicalize()
        .expect("workspace root should be canonicalizable");
    let git = GitContext::resolve(&workspace);
    let git_toplevel = git_output_with(&git, &workspace, &["rev-parse", "--show-toplevel"]);
    let git_toplevel = std::str::from_utf8(&git_toplevel)
        .expect("Git top-level path should be UTF-8")
        .trim_end();
    let git_toplevel = Path::new(git_toplevel)
        .canonicalize()
        .expect("Git top-level path should be canonicalizable");
    assert_eq!(
        git_toplevel, workspace,
        "requested workspace is not its repository's Git top level"
    );

    let head = git_output_with(&git, &workspace, &["rev-parse", "--verify", "HEAD"]);
    let tracked_entries = git_tracked_entries(&git, &workspace);
    let untracked_paths = git_paths(
        &git,
        &workspace,
        &["ls-files", "-z", "--others", "--exclude-standard"],
    );

    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-worktree-v3");
    hash_component(&mut hasher, b"git-tool", git.identity.as_bytes());
    hash_component(&mut hasher, b"head", &head);
    for entry in tracked_entries {
        hash_worktree_entry(
            &mut hasher,
            &workspace,
            b"tracked",
            &entry.path,
            Some(&entry.index_mode),
        );
    }
    for relative in untracked_paths {
        hash_worktree_entry(&mut hasher, &workspace, b"untracked", &relative, None);
    }
    git.assert_unchanged(&workspace);
    finish_source_identity(hasher)
}

/// Fail closed if the workspace changed while an exact-source operation ran.
pub fn assert_workspace_source_identity(workspace: &Path, expected: &str, operation: &str) {
    let actual = workspace_source_identity(workspace);
    assert_eq!(
        actual, expected,
        "workspace source changed during {operation}; refusing an ambiguously sourced binary"
    );
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceSnapshot {
    root: PathBuf,
    source_identity: String,
    manifest_identity: String,
}

fn checked_relative_git_path(path: &[u8]) -> PathBuf {
    let relative = PathBuf::from(path_component_from_git_bytes(path));
    assert!(
        !relative.as_os_str().is_empty() && !relative.is_absolute(),
        "Git returned a non-relative source path: {}",
        relative.display()
    );
    assert!(
        relative.components().all(|component| matches!(
            component,
            std::path::Component::Normal(_) | std::path::Component::CurDir
        )),
        "Git returned an escaping source path: {}",
        relative.display()
    );
    relative
}

fn ensure_snapshot_parent(root: &Path, destination: &Path) {
    let parent = destination
        .parent()
        .expect("snapshot entry should have a parent");
    let relative = parent
        .strip_prefix(root)
        .expect("snapshot destination must remain under its root");
    let mut current = root.to_path_buf();
    for component in relative.components() {
        current.push(component);
        match filesystem::symlink_metadata(&current) {
            Ok(metadata) => assert!(
                metadata.is_dir() && !metadata.file_type().is_symlink(),
                "snapshot parent is not a real directory: {}",
                current.display()
            ),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                filesystem::create_dir(&current).unwrap_or_else(|create_error| {
                    panic!(
                        "failed to create snapshot directory {}: {create_error}",
                        current.display()
                    )
                });
            }
            Err(error) => panic!(
                "failed to inspect snapshot directory {}: {error}",
                current.display()
            ),
        }
    }
}

#[cfg(unix)]
fn create_snapshot_symlink(target: &Path, destination: &Path, _source: &Path) {
    std::os::unix::fs::symlink(target, destination).unwrap_or_else(|error| {
        panic!(
            "failed to create snapshot symlink {} -> {}: {error}",
            destination.display(),
            target.display()
        )
    });
}

#[cfg(windows)]
fn create_snapshot_symlink(target: &Path, destination: &Path, source: &Path) {
    let result = if source.is_dir() {
        std::os::windows::fs::symlink_dir(target, destination)
    } else {
        std::os::windows::fs::symlink_file(target, destination)
    };
    result.unwrap_or_else(|error| {
        panic!(
            "failed to create snapshot symlink {} -> {}: {error}",
            destination.display(),
            target.display()
        )
    });
}

#[cfg(not(any(unix, windows)))]
fn create_snapshot_symlink(_target: &Path, destination: &Path, _source: &Path) {
    panic!(
        "source snapshots do not support symlinks on this platform: {}",
        destination.display()
    );
}

fn copy_snapshot_file(source: &Path, destination: &Path, metadata: &filesystem::Metadata) {
    let contents = filesystem::read(source)
        .unwrap_or_else(|error| panic!("failed to read source {}: {error}", source.display()));
    filesystem::write(destination, contents).unwrap_or_else(|error| {
        panic!(
            "failed to write source snapshot {}: {error}",
            destination.display()
        )
    });
    filesystem::set_permissions(destination, metadata.permissions()).unwrap_or_else(|error| {
        panic!(
            "failed to preserve source mode on {}: {error}",
            destination.display()
        )
    });
}

fn copy_repository_to_snapshot(
    repository: &Path,
    snapshot_root: &Path,
    destination_prefix: &Path,
    enumerator: &mut Sha256,
) {
    let repository = repository
        .canonicalize()
        .expect("source repository should be canonicalizable");
    let git = GitContext::resolve(&repository);
    let git_toplevel = git_output_with(&git, &repository, &["rev-parse", "--show-toplevel"]);
    let git_toplevel = std::str::from_utf8(&git_toplevel)
        .expect("Git top-level path should be UTF-8")
        .trim_end();
    let git_toplevel = Path::new(git_toplevel)
        .canonicalize()
        .expect("Git top-level path should be canonicalizable");
    assert_eq!(
        git_toplevel, repository,
        "snapshot source is not its repository's Git top level"
    );

    let head = git_output_with(&git, &repository, &["rev-parse", "--verify", "HEAD"]);
    hash_os_component(
        enumerator,
        b"repository-prefix",
        destination_prefix.as_os_str(),
    );
    hash_component(enumerator, b"git-tool", git.identity.as_bytes());
    hash_component(enumerator, b"head", &head);

    let tracked_entries = git_tracked_entries(&git, &repository);
    let untracked_paths = git_paths(
        &git,
        &repository,
        &["ls-files", "-z", "--others", "--exclude-standard"],
    );

    for (scope, relative_bytes, index_mode) in tracked_entries
        .iter()
        .map(|entry| {
            (
                b"tracked".as_slice(),
                entry.path.as_slice(),
                Some(entry.index_mode.as_slice()),
            )
        })
        .chain(
            untracked_paths
                .iter()
                .map(|path| (b"untracked".as_slice(), path.as_slice(), None)),
        )
    {
        hash_component(enumerator, b"entry-scope", scope);
        hash_component(enumerator, b"entry-path", relative_bytes);
        if let Some(mode) = index_mode {
            hash_component(enumerator, b"entry-index-mode", mode);
        }

        let relative = checked_relative_git_path(relative_bytes);
        let source = repository.join(&relative);
        let destination_relative = destination_prefix.join(&relative);
        let destination = snapshot_root.join(&destination_relative);
        let metadata = match filesystem::symlink_metadata(&source) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                assert_ne!(
                    index_mode,
                    Some(b"160000".as_slice()),
                    "tracked gitlink {} is uninitialized",
                    source.display()
                );
                hash_component(enumerator, b"entry-kind", b"missing");
                continue;
            }
            Err(error) => panic!("failed to inspect source {}: {error}", source.display()),
        };
        ensure_snapshot_parent(snapshot_root, &destination);

        let file_type = metadata.file_type();
        if file_type.is_symlink() {
            hash_component(enumerator, b"entry-kind", b"symlink");
            let target = filesystem::read_link(&source).unwrap_or_else(|error| {
                panic!("failed to read source link {}: {error}", source.display())
            });
            create_snapshot_symlink(&target, &destination, &source);
        } else if file_type.is_file() {
            hash_component(enumerator, b"entry-kind", b"file");
            copy_snapshot_file(&source, &destination, &metadata);
        } else if file_type.is_dir() {
            assert_eq!(
                index_mode,
                Some(b"160000".as_slice()),
                "source directory is not a tracked gitlink: {}",
                source.display()
            );
            hash_component(enumerator, b"entry-kind", b"gitlink");
            filesystem::create_dir(&destination).unwrap_or_else(|error| {
                panic!(
                    "failed to create gitlink snapshot directory {}: {error}",
                    destination.display()
                )
            });
            copy_repository_to_snapshot(&source, snapshot_root, &destination_relative, enumerator);
        } else {
            panic!(
                "unsupported special source entry {} cannot enter an exact snapshot",
                source.display()
            );
        }
    }
    git.assert_unchanged(&repository);
}

fn snapshot_paths(root: &Path) -> Vec<PathBuf> {
    fn visit(root: &Path, directory: &Path, paths: &mut Vec<PathBuf>) {
        let entries = filesystem::read_dir(directory)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", directory.display()));
        for entry in entries {
            let entry = entry.unwrap_or_else(|error| {
                panic!(
                    "failed to read entry under {}: {error}",
                    directory.display()
                )
            });
            let path = entry.path();
            let metadata = filesystem::symlink_metadata(&path)
                .unwrap_or_else(|error| panic!("failed to inspect {}: {error}", path.display()));
            paths.push(path.clone());
            if metadata.is_dir() && !metadata.file_type().is_symlink() {
                visit(root, &path, paths);
            }
        }
    }

    let mut paths = Vec::new();
    visit(root, root, &mut paths);
    paths.sort_unstable_by(|left, right| {
        os_str_identity_bytes(
            left.strip_prefix(root)
                .expect("snapshot entry should be under root")
                .as_os_str(),
        )
        .cmp(&os_str_identity_bytes(
            right
                .strip_prefix(root)
                .expect("snapshot entry should be under root")
                .as_os_str(),
        ))
    });
    paths
}

fn symlink_target_stays_within_snapshot(root: &Path, link: &Path, target: &Path) -> bool {
    if target.is_absolute() {
        return false;
    }
    let mut components = link
        .parent()
        .and_then(|parent| parent.strip_prefix(root).ok())
        .into_iter()
        .flat_map(Path::components)
        .filter_map(|component| match component {
            std::path::Component::Normal(value) => Some(value.to_owned()),
            std::path::Component::CurDir => None,
            _ => None,
        })
        .collect::<Vec<_>>();
    for component in target.components() {
        match component {
            std::path::Component::Normal(value) => components.push(value.to_owned()),
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                if components.pop().is_none() {
                    return false;
                }
            }
            std::path::Component::RootDir | std::path::Component::Prefix(_) => return false,
        }
    }
    true
}

fn assert_snapshot_symlinks_are_internal(root: &Path) {
    let canonical_root = root
        .canonicalize()
        .expect("snapshot root should be canonicalizable");
    for path in snapshot_paths(root) {
        let metadata = filesystem::symlink_metadata(&path)
            .unwrap_or_else(|error| panic!("failed to inspect {}: {error}", path.display()));
        if !metadata.file_type().is_symlink() {
            continue;
        }
        let target = filesystem::read_link(&path)
            .unwrap_or_else(|error| panic!("failed to read link {}: {error}", path.display()));
        assert!(
            symlink_target_stays_within_snapshot(root, &path, &target),
            "snapshot symlink escapes its source boundary: {} -> {}",
            path.display(),
            target.display()
        );
        if let Ok(resolved) = path.canonicalize() {
            assert!(
                resolved.starts_with(&canonical_root),
                "snapshot symlink resolves outside its source boundary: {} -> {}",
                path.display(),
                resolved.display()
            );
        }
    }
}

fn freeze_snapshot_tree(root: &Path) {
    let mut paths = snapshot_paths(root);
    paths.sort_unstable_by_key(|path| std::cmp::Reverse(path.components().count()));
    paths.push(root.to_path_buf());
    for path in paths {
        let metadata = filesystem::symlink_metadata(&path)
            .unwrap_or_else(|error| panic!("failed to inspect {}: {error}", path.display()));
        if metadata.file_type().is_symlink() {
            continue;
        }
        let mut permissions = metadata.permissions();
        #[cfg(unix)]
        permissions.set_mode(permissions.mode() & !0o222);
        #[cfg(not(unix))]
        permissions.set_readonly(true);
        filesystem::set_permissions(&path, permissions).unwrap_or_else(|error| {
            panic!(
                "failed to freeze snapshot entry {}: {error}",
                path.display()
            )
        });
    }
}

fn assert_snapshot_tree_is_frozen(root: &Path) {
    for path in std::iter::once(root.to_path_buf()).chain(snapshot_paths(root)) {
        let metadata = filesystem::symlink_metadata(&path)
            .unwrap_or_else(|error| panic!("failed to inspect {}: {error}", path.display()));
        if metadata.file_type().is_symlink() {
            continue;
        }
        #[cfg(unix)]
        assert_eq!(
            metadata.permissions().mode() & 0o222,
            0,
            "published source snapshot is writable: {}",
            path.display()
        );
        #[cfg(not(unix))]
        assert!(
            metadata.permissions().readonly(),
            "published source snapshot is writable: {}",
            path.display()
        );
    }
}

fn snapshot_manifest_identity(root: &Path) -> String {
    let metadata = filesystem::symlink_metadata(root)
        .unwrap_or_else(|error| panic!("failed to inspect snapshot {}: {error}", root.display()));
    assert!(
        metadata.is_dir() && !metadata.file_type().is_symlink(),
        "source snapshot root is not a real directory: {}",
        root.display()
    );
    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-snapshot-manifest-v1");
    hash_component(
        &mut hasher,
        b"root-mode",
        &permission_identity_bytes(&metadata),
    );
    for path in snapshot_paths(root) {
        let relative = path
            .strip_prefix(root)
            .expect("snapshot entry should be under root");
        hash_os_component(&mut hasher, b"entry-path", relative.as_os_str());
        let metadata = filesystem::symlink_metadata(&path)
            .unwrap_or_else(|error| panic!("failed to inspect {}: {error}", path.display()));
        hash_component(
            &mut hasher,
            b"entry-mode",
            &permission_identity_bytes(&metadata),
        );
        let file_type = metadata.file_type();
        if file_type.is_symlink() {
            hash_component(&mut hasher, b"entry-kind", b"symlink");
            let target = filesystem::read_link(&path).unwrap_or_else(|error| {
                panic!("failed to read snapshot link {}: {error}", path.display())
            });
            hash_os_component(&mut hasher, b"entry-link-target", target.as_os_str());
        } else if file_type.is_file() {
            hash_component(&mut hasher, b"entry-kind", b"file");
            let contents = filesystem::read(&path).unwrap_or_else(|error| {
                panic!("failed to read snapshot file {}: {error}", path.display())
            });
            hash_component(&mut hasher, b"entry-contents", &contents);
        } else if file_type.is_dir() {
            hash_component(&mut hasher, b"entry-kind", b"directory");
        } else {
            panic!(
                "published source snapshot contains special entry {}",
                path.display()
            );
        }
    }
    finish_source_identity(hasher)
}

fn make_tree_writable(root: &Path) {
    let mut paths = snapshot_paths(root);
    paths.push(root.to_path_buf());
    for path in paths {
        let Ok(metadata) = filesystem::symlink_metadata(&path) else {
            continue;
        };
        if metadata.file_type().is_symlink() {
            continue;
        }
        let mut permissions = metadata.permissions();
        #[cfg(unix)]
        permissions.set_mode(permissions.mode() | 0o700);
        #[cfg(not(unix))]
        permissions.set_readonly(false);
        let _ = filesystem::set_permissions(path, permissions);
    }
}

fn remove_snapshot_staging(root: &Path) {
    if filesystem::symlink_metadata(root).is_err() {
        return;
    }
    make_tree_writable(root);
    filesystem::remove_dir_all(root)
        .unwrap_or_else(|error| panic!("failed to remove snapshot staging tree: {error}"));
}

struct SnapshotStagingGuard {
    root: PathBuf,
}

impl Drop for SnapshotStagingGuard {
    fn drop(&mut self) {
        if filesystem::symlink_metadata(&self.root).is_err() {
            return;
        }
        // Cleanup runs on both success (where rename made the staging path
        // disappear) and unwind. It must never double-panic while preserving
        // the original fail-closed snapshot error.
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            make_tree_writable(&self.root);
        }));
        let _ = filesystem::remove_dir_all(&self.root);
    }
}

fn source_snapshot_store(workspace: &Path) -> PathBuf {
    let temp = std::env::temp_dir()
        .canonicalize()
        .expect("temporary directory should be canonicalizable");
    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-snapshot-workspace-v1");
    hash_os_component(&mut hasher, b"workspace", workspace.as_os_str());
    let workspace_key = finish_source_identity(hasher);
    let base = temp
        .join("ay-test-support-source-snapshots-v1")
        .join(workspace_key);
    filesystem::create_dir_all(&base).unwrap_or_else(|error| {
        panic!(
            "failed to create source snapshot store {}: {error}",
            base.display()
        )
    });
    let metadata = filesystem::symlink_metadata(&base)
        .unwrap_or_else(|error| panic!("failed to inspect {}: {error}", base.display()));
    assert!(
        metadata.is_dir() && !metadata.file_type().is_symlink(),
        "source snapshot store is not a real directory: {}",
        base.display()
    );
    base
}

fn create_workspace_source_snapshot(workspace: &Path) -> SourceSnapshot {
    create_workspace_source_snapshot_with_hook(workspace, || {})
}

fn create_workspace_source_snapshot_with_hook(
    workspace: &Path,
    after_copy: impl FnOnce(),
) -> SourceSnapshot {
    let workspace = workspace
        .canonicalize()
        .expect("workspace root should be canonicalizable");
    let live_source_identity = workspace_source_identity(&workspace);
    let store = source_snapshot_store(&workspace);
    let sequence = UNIQUE_PATH_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let staging = store.join(format!(".staging-{}-{sequence}", std::process::id()));
    filesystem::create_dir(&staging).unwrap_or_else(|error| {
        panic!(
            "failed to create source snapshot staging tree {}: {error}",
            staging.display()
        )
    });
    let _staging_guard = SnapshotStagingGuard {
        root: staging.clone(),
    };

    let mut enumerator = Sha256::new();
    hash_component(
        &mut enumerator,
        b"schema",
        b"ay-test-git-snapshot-enumerator-v1",
    );
    copy_repository_to_snapshot(&workspace, &staging, Path::new(""), &mut enumerator);
    after_copy();
    assert_workspace_source_identity(
        &workspace,
        &live_source_identity,
        "immutable source snapshot capture",
    );
    let enumerator_identity = finish_source_identity(enumerator);
    assert_snapshot_symlinks_are_internal(&staging);
    freeze_snapshot_tree(&staging);
    assert_snapshot_tree_is_frozen(&staging);
    let manifest_identity = snapshot_manifest_identity(&staging);

    let mut identity = Sha256::new();
    hash_component(&mut identity, b"schema", b"ay-test-source-snapshot-v1");
    hash_component(
        &mut identity,
        b"stable-live-workspace",
        live_source_identity.as_bytes(),
    );
    hash_component(
        &mut identity,
        b"git-enumerator",
        enumerator_identity.as_bytes(),
    );
    hash_component(
        &mut identity,
        b"staged-manifest",
        manifest_identity.as_bytes(),
    );
    let source_identity = finish_source_identity(identity);
    let published = store.join(&source_identity);

    match filesystem::symlink_metadata(&published) {
        Ok(metadata) => {
            assert!(
                metadata.is_dir() && !metadata.file_type().is_symlink(),
                "preexisting content-addressed snapshot is not a real directory: {}",
                published.display()
            );
            assert_snapshot_symlinks_are_internal(&published);
            assert_snapshot_tree_is_frozen(&published);
            assert_eq!(
                snapshot_manifest_identity(&published),
                manifest_identity,
                "preexisting content-addressed snapshot failed exact manifest verification"
            );
            remove_snapshot_staging(&staging);
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            if let Err(rename_error) = filesystem::rename(&staging, &published) {
                if filesystem::symlink_metadata(&published).is_ok() {
                    assert_snapshot_symlinks_are_internal(&published);
                    assert_snapshot_tree_is_frozen(&published);
                    assert_eq!(
                        snapshot_manifest_identity(&published),
                        manifest_identity,
                        "racing content-addressed snapshot publication disagreed"
                    );
                    remove_snapshot_staging(&staging);
                } else {
                    panic!(
                        "failed to publish source snapshot {}: {rename_error}",
                        published.display()
                    );
                }
            }
        }
        Err(error) => panic!(
            "failed to inspect source snapshot destination {}: {error}",
            published.display()
        ),
    }

    let snapshot = SourceSnapshot {
        root: published,
        source_identity,
        manifest_identity,
    };
    snapshot.assert_unchanged("snapshot publication");
    snapshot
}

impl SourceSnapshot {
    fn assert_unchanged(&self, operation: &str) {
        assert_snapshot_symlinks_are_internal(&self.root);
        assert_snapshot_tree_is_frozen(&self.root);
        assert_eq!(
            snapshot_manifest_identity(&self.root),
            self.manifest_identity,
            "immutable source snapshot changed during {operation}"
        );
    }
}

const BUILD_ENV_PASSTHROUGH: &[&str] = &[
    "COMSPEC",
    "DEVELOPER_DIR",
    "MACOSX_DEPLOYMENT_TARGET",
    "PATH",
    "PATHEXT",
    "SDKROOT",
    "SYSTEMROOT",
];

const TOOL_SELECTION_ENV_PASSTHROUGH: &[&str] = &[
    "HOME",
    "PATH",
    "RUSTUP_HOME",
    "RUSTUP_TOOLCHAIN",
    "TEMP",
    "TMP",
    "TMPDIR",
    "USERPROFILE",
];

#[derive(Clone, Debug, Eq, PartialEq)]
struct InventoriedBuildContext {
    cargo: PathBuf,
    rustc: PathBuf,
    cargo_scheduling: NestedCargoScheduling,
    environment: BTreeMap<OsString, OsString>,
    execution_environment: BTreeMap<OsString, OsString>,
    identity: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NestedCargoScheduling {
    CargoDefault,
    ExplicitPerInvocation { jobs: usize },
    ParentEnvelopeSerialized { jobs: usize },
}

impl NestedCargoScheduling {
    fn jobs(self) -> Option<usize> {
        match self {
            Self::CargoDefault => None,
            Self::ExplicitPerInvocation { jobs } | Self::ParentEnvelopeSerialized { jobs } => {
                Some(jobs)
            }
        }
    }

    fn serializes_parent_envelope(self) -> bool {
        matches!(self, Self::ParentEnvelopeSerialized { .. })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PairedToolchain {
    cargo: PathBuf,
    rustc: PathBuf,
    sysroot: PathBuf,
    host: String,
}

fn finish_build_identity(hasher: Sha256) -> String {
    let digest = hasher.finalize();
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        write!(&mut hex, "{byte:02x}").expect("writing to String cannot fail");
    }
    format!("build-sha256-{hex}")
}

fn native_target_fingerprint(target_cpus: &[u8], native_cfg: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-rustc-native-target-v1");
    for (scope, output) in [
        (b"target-cpus".as_slice(), target_cpus),
        (b"cfg", native_cfg),
    ] {
        let mut lines = output
            .split(|byte| *byte == b'\n')
            .map(|line| line.strip_suffix(b"\r").unwrap_or(line))
            .filter(|line| !line.is_empty())
            .collect::<Vec<_>>();
        lines.sort_unstable();
        lines.dedup();
        for line in lines {
            hash_component(&mut hasher, scope, line);
        }
    }
    let digest = hasher.finalize();
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        write!(&mut hex, "{byte:02x}").expect("writing to String cannot fail");
    }
    format!("native-target-sha256-{hex}")
}

fn hash_os_component(hasher: &mut Sha256, label: &[u8], value: &OsStr) {
    hash_component(hasher, label, &os_str_identity_bytes(value));
}

fn normalize_input_path(workspace: &Path, path: PathBuf) -> PathBuf {
    let absolute = if path.is_absolute() {
        path
    } else {
        workspace.join(path)
    };
    canonicalize_existing_parent(absolute)
}

fn cargo_home(workspace: &Path) -> PathBuf {
    if let Some(configured) = std::env::var_os("CARGO_HOME").filter(|value| !value.is_empty()) {
        return normalize_input_path(workspace, configured.into());
    }
    let home = std::env::var_os("HOME")
        .or_else(|| std::env::var_os("USERPROFILE"))
        .expect("HOME or USERPROFILE is required to locate Cargo's cache");
    normalize_input_path(workspace, PathBuf::from(home).join(".cargo"))
}

fn environment_subset(names: &[&str]) -> BTreeMap<OsString, OsString> {
    names
        .iter()
        .filter_map(|name| std::env::var_os(name).map(|value| ((*name).into(), value)))
        .collect()
}

fn sanitized_build_environment_from(
    ambient: impl IntoIterator<Item = (OsString, OsString)>,
    cargo_home: &Path,
    rustc: &Path,
) -> BTreeMap<OsString, OsString> {
    let allowed = BUILD_ENV_PASSTHROUGH
        .iter()
        .map(OsStr::new)
        .collect::<BTreeSet<_>>();
    let mut environment = ambient
        .into_iter()
        .filter(|(name, _)| allowed.contains(name.as_os_str()))
        .collect::<BTreeMap<_, _>>();
    environment.insert("CARGO_HOME".into(), cargo_home.as_os_str().to_owned());
    environment.insert("CARGO_INCREMENTAL".into(), "0".into());
    environment.insert("CARGO_NET_OFFLINE".into(), "true".into());
    environment.insert("CARGO_TERM_COLOR".into(), "never".into());
    environment.insert("RUSTC".into(), rustc.as_os_str().to_owned());
    environment.insert("SOURCE_DATE_EPOCH".into(), "1".into());
    if let Some(path) = environment.get(OsStr::new("PATH")).cloned() {
        environment.insert("PATH".into(), normalized_absolute_path(Some(&path)));
    }
    environment
}

fn ambient_value<'a>(ambient: &'a [(OsString, OsString)], name: &str) -> Option<&'a OsStr> {
    ambient
        .iter()
        .find_map(|(key, value)| (key == OsStr::new(name)).then_some(value.as_os_str()))
}

fn positive_job_count(name: &str, value: &OsStr) -> usize {
    let value = value
        .to_str()
        .unwrap_or_else(|| panic!("{name} must be a positive UTF-8 integer"));
    let jobs = value
        .parse::<usize>()
        .unwrap_or_else(|_| panic!("{name} must be a positive integer, got {value:?}"));
    assert!(jobs > 0, "{name} must be positive");
    jobs
}

fn nested_cargo_scheduling_from_ambient(ambient: &[(OsString, OsString)]) -> NestedCargoScheduling {
    let configured = ambient_value(ambient, CARGO_BUILD_JOBS_ENV)
        .map(|value| positive_job_count(CARGO_BUILD_JOBS_ENV, value));
    let Some(parent_lease) = ambient_value(ambient, OOM_GUARD_PARENT_LEASE_ENV) else {
        return configured.map_or(NestedCargoScheduling::CargoDefault, |jobs| {
            NestedCargoScheduling::ExplicitPerInvocation { jobs }
        });
    };
    assert_eq!(
        parent_lease.to_str(),
        Some("1"),
        "{OOM_GUARD_PARENT_LEASE_ENV} must be exactly 1 when present"
    );
    let jobs = configured.unwrap_or_else(|| {
        panic!("{CARGO_BUILD_JOBS_ENV} is required under the parent OOM-guard lease")
    });
    let nbcore = ambient_value(ambient, NBCORE_ENV)
        .unwrap_or_else(|| panic!("{NBCORE_ENV} is required under the parent OOM-guard lease"));
    let nbcore = positive_job_count(NBCORE_ENV, nbcore);
    assert_eq!(
        jobs, nbcore,
        "{CARGO_BUILD_JOBS_ENV}={jobs} does not match {NBCORE_ENV}={nbcore}"
    );
    NestedCargoScheduling::ParentEnvelopeSerialized { jobs }
}

fn current_nested_cargo_scheduling() -> NestedCargoScheduling {
    nested_cargo_scheduling_from_ambient(&std::env::vars_os().collect::<Vec<_>>())
}

fn parent_nested_cargo_lock_path(target_root: &Path) -> PathBuf {
    target_root.join(PARENT_NESTED_CARGO_LOCK_FILE)
}

struct ParentNestedCargoLock {
    path: PathBuf,
    file: filesystem::File,
}

impl Drop for ParentNestedCargoLock {
    fn drop(&mut self) {
        if let Err(error) = self.file.unlock() {
            if std::thread::panicking() {
                eprintln!(
                    "[ay tests] failed to release parent nested-Cargo lock {} while unwinding: {error}",
                    self.path.display()
                );
            } else {
                panic!(
                    "failed to release parent nested-Cargo lock {}: {error}",
                    self.path.display()
                );
            }
        }
    }
}

fn assert_parent_nested_cargo_lock_file(path: &Path, file: &filesystem::File) {
    let path_metadata = filesystem::symlink_metadata(path).unwrap_or_else(|error| {
        panic!(
            "failed to inspect parent nested-Cargo lock {}: {error}",
            path.display()
        )
    });
    assert!(
        path_metadata.is_file() && !path_metadata.file_type().is_symlink(),
        "parent nested-Cargo lock is not a real file: {}",
        path.display()
    );
    let file_metadata = file.metadata().unwrap_or_else(|error| {
        panic!(
            "failed to inspect open parent nested-Cargo lock {}: {error}",
            path.display()
        )
    });
    assert!(
        file_metadata.is_file(),
        "open parent nested-Cargo lock is not a file: {}",
        path.display()
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;

        assert_eq!(
            (path_metadata.dev(), path_metadata.ino()),
            (file_metadata.dev(), file_metadata.ino()),
            "parent nested-Cargo lock path changed while opening: {}",
            path.display()
        );
        assert_eq!(
            file_metadata.nlink(),
            1,
            "parent nested-Cargo lock has unexpected hard links: {}",
            path.display()
        );
    }
}

fn open_parent_nested_cargo_lock(target_root: &Path) -> filesystem::File {
    let path = parent_nested_cargo_lock_path(target_root);
    match filesystem::symlink_metadata(&path) {
        Ok(metadata) => assert!(
            metadata.is_file() && !metadata.file_type().is_symlink(),
            "parent nested-Cargo lock is not a real file: {}",
            path.display()
        ),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => panic!(
            "failed to inspect parent nested-Cargo lock {}: {error}",
            path.display()
        ),
    }
    let file = filesystem::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(&path)
        .unwrap_or_else(|error| {
            panic!(
                "failed to open parent nested-Cargo lock {}: {error}",
                path.display()
            )
        });
    assert_parent_nested_cargo_lock_file(&path, &file);
    file
}

fn acquire_parent_nested_cargo_lock(target_root: &Path) -> ParentNestedCargoLock {
    let path = parent_nested_cargo_lock_path(target_root);
    let file = open_parent_nested_cargo_lock(target_root);
    file.lock().unwrap_or_else(|error| {
        panic!(
            "failed to acquire parent nested-Cargo lock {}: {error}",
            path.display()
        )
    });
    assert_parent_nested_cargo_lock_file(&path, &file);
    ParentNestedCargoLock { path, file }
}

fn run_with_environment(
    program: &Path,
    args: &[&str],
    current_dir: &Path,
    environment: &BTreeMap<OsString, OsString>,
) -> Output {
    let mut command = Command::new(program);
    command
        .args(args)
        .current_dir(current_dir)
        .env_clear()
        .envs(environment);
    command
        .output()
        .unwrap_or_else(|error| panic!("failed to run {} {args:?}: {error}", program.display()))
}

fn checked_tool_output(
    program: &Path,
    args: &[&str],
    current_dir: &Path,
    environment: &BTreeMap<OsString, OsString>,
) -> Vec<u8> {
    let output = run_with_environment(program, args, current_dir, environment);
    assert!(
        output.status.success(),
        "{} {args:?} failed with status {}: {}",
        program.display(),
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

fn absolute_program_path_preserving_final_symlink(path: &Path) -> PathBuf {
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .expect("current directory should be available")
            .join(path)
    };
    let name = absolute
        .file_name()
        .unwrap_or_else(|| panic!("program path has no filename: {}", absolute.display()));
    let parent = absolute
        .parent()
        .expect("program path with a filename should have a parent")
        .canonicalize()
        .unwrap_or_else(|error| {
            panic!(
                "failed to resolve program directory {}: {error}",
                absolute.display()
            )
        });
    parent.join(name)
}

fn resolve_program(program: &OsStr, path: Option<&OsStr>) -> PathBuf {
    let requested = Path::new(program);
    if requested.is_absolute()
        || requested
            .parent()
            .is_some_and(|parent| !parent.as_os_str().is_empty())
    {
        let resolved = absolute_program_path_preserving_final_symlink(requested);
        assert!(
            resolved.is_file(),
            "resolved program is not a file: {}",
            resolved.display()
        );
        return resolved;
    }

    let path = path.unwrap_or_default();
    for directory in std::env::split_paths(path) {
        let candidate = directory.join(requested);
        if candidate.is_file() {
            return absolute_program_path_preserving_final_symlink(&candidate);
        }
        if !std::env::consts::EXE_SUFFIX.is_empty() {
            let candidate = directory.join(format!(
                "{}{}",
                requested.to_string_lossy(),
                std::env::consts::EXE_SUFFIX
            ));
            if candidate.is_file() {
                return absolute_program_path_preserving_final_symlink(&candidate);
            }
        }
    }
    panic!(
        "could not resolve {} in PATH {:?}",
        program.display(),
        path.to_string_lossy()
    );
}

fn resolve_paired_toolchain(workspace: &Path) -> PairedToolchain {
    let mut selection_environment = environment_subset(TOOL_SELECTION_ENV_PASSTHROUGH);
    let normalized_path = normalized_absolute_path(
        selection_environment
            .get(OsStr::new("PATH"))
            .map(OsString::as_os_str),
    );
    selection_environment.insert("PATH".into(), normalized_path);
    let rustc_seed = resolve_program(
        OsStr::new("rustc"),
        selection_environment
            .get(OsStr::new("PATH"))
            .map(OsString::as_os_str),
    );
    let sysroot = checked_tool_output(
        &rustc_seed,
        &["--print", "sysroot"],
        workspace,
        &selection_environment,
    );
    let sysroot = std::str::from_utf8(&sysroot)
        .expect("rustc sysroot should be UTF-8")
        .trim_end();
    let sysroot = Path::new(sysroot)
        .canonicalize()
        .expect("rustc sysroot should be canonicalizable");
    let verbose = checked_tool_output(&rustc_seed, &["-vV"], workspace, &selection_environment);
    let verbose = std::str::from_utf8(&verbose).expect("rustc -vV should be UTF-8");
    let host = verbose
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .filter(|host| !host.is_empty())
        .expect("rustc -vV should report a host triple")
        .to_owned();
    let rustc = sysroot
        .join("bin")
        .join(format!("rustc{}", std::env::consts::EXE_SUFFIX));
    assert!(
        rustc.is_file(),
        "selected sysroot should contain rustc at {}",
        rustc.display()
    );
    let cargo = sysroot
        .join("bin")
        .join(format!("cargo{}", std::env::consts::EXE_SUFFIX));
    assert!(
        cargo.is_file(),
        "selected sysroot should contain its paired cargo at {}",
        cargo.display()
    );
    PairedToolchain {
        cargo,
        rustc,
        sysroot,
        host,
    }
}

fn hash_file_input(hasher: &mut Sha256, scope: &[u8], path: &Path) -> Vec<u8> {
    hash_component(hasher, b"file-scope", scope);
    hash_os_component(hasher, b"file-path", path.as_os_str());
    let link_metadata = std::fs::symlink_metadata(path)
        .unwrap_or_else(|error| panic!("failed to inspect {}: {error}", path.display()));
    hash_component(
        hasher,
        b"file-link-mode",
        &permission_identity_bytes(&link_metadata),
    );
    if link_metadata.file_type().is_symlink() {
        let target = std::fs::read_link(path)
            .unwrap_or_else(|error| panic!("failed to read link {}: {error}", path.display()));
        hash_os_component(hasher, b"file-link-target", target.as_os_str());
    } else {
        assert!(
            link_metadata.is_file(),
            "semantic build input is not a regular file: {}",
            path.display()
        );
    }
    let canonical = path
        .canonicalize()
        .unwrap_or_else(|error| panic!("failed to resolve {}: {error}", path.display()));
    hash_os_component(hasher, b"file-canonical-path", canonical.as_os_str());
    let metadata = std::fs::metadata(&canonical)
        .unwrap_or_else(|error| panic!("failed to inspect {}: {error}", canonical.display()));
    assert!(
        metadata.is_file(),
        "semantic build input does not resolve to a regular file: {}",
        path.display()
    );
    hash_component(hasher, b"file-mode", &permission_identity_bytes(&metadata));
    let contents = std::fs::read(&canonical)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", canonical.display()));
    hash_component(hasher, b"file-contents", &contents);
    contents
}

fn hash_directory_tree(hasher: &mut Sha256, scope: &[u8], root: &Path) {
    let root = root
        .canonicalize()
        .unwrap_or_else(|error| panic!("failed to resolve {}: {error}", root.display()));
    hash_component(hasher, b"tree-scope", scope);
    hash_os_component(hasher, b"tree-root", root.as_os_str());
    for path in snapshot_paths(&root) {
        let relative = path
            .strip_prefix(&root)
            .expect("tree entry should remain under its root");
        hash_os_component(hasher, b"tree-entry", relative.as_os_str());
        let metadata = filesystem::symlink_metadata(&path)
            .unwrap_or_else(|error| panic!("failed to inspect {}: {error}", path.display()));
        hash_component(
            hasher,
            b"tree-entry-mode",
            &permission_identity_bytes(&metadata),
        );
        let file_type = metadata.file_type();
        if file_type.is_symlink() {
            hash_component(hasher, b"tree-entry-kind", b"symlink");
            let target = filesystem::read_link(&path)
                .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
            hash_os_component(hasher, b"tree-entry-link", target.as_os_str());
            let canonical = path.canonicalize().unwrap_or_else(|error| {
                panic!(
                    "selected build input symlink is dangling {}: {error}",
                    path.display()
                )
            });
            assert!(
                canonical.is_file(),
                "selected build input symlink does not resolve to a file: {}",
                path.display()
            );
            hash_os_component(hasher, b"tree-entry-canonical", canonical.as_os_str());
            let contents = filesystem::read(&canonical).unwrap_or_else(|error| {
                panic!(
                    "failed to read selected build input {}: {error}",
                    canonical.display()
                )
            });
            hash_component(hasher, b"tree-entry-contents", &contents);
        } else if file_type.is_file() {
            hash_component(hasher, b"tree-entry-kind", b"file");
            let contents = filesystem::read(&path).unwrap_or_else(|error| {
                panic!(
                    "failed to read selected build input {}: {error}",
                    path.display()
                )
            });
            hash_component(hasher, b"tree-entry-contents", &contents);
        } else if file_type.is_dir() {
            hash_component(hasher, b"tree-entry-kind", b"directory");
        } else {
            panic!(
                "selected build-input tree contains special file {}",
                path.display()
            );
        }
    }
}

fn sysroot_library_identity(toolchain: &PairedToolchain) -> String {
    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-rust-sysroot-v1");
    hash_os_component(&mut hasher, b"sysroot", toolchain.sysroot.as_os_str());
    hash_component(&mut hasher, b"host", toolchain.host.as_bytes());

    let host_library = toolchain
        .sysroot
        .join("lib")
        .join("rustlib")
        .join(&toolchain.host)
        .join("lib");
    hash_directory_tree(&mut hasher, b"host-rustlib", &host_library);

    let root_library = toolchain.sysroot.join("lib");
    let mut runtime_libraries = filesystem::read_dir(&root_library)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", root_library.display()))
        .map(|entry| {
            entry
                .unwrap_or_else(|error| {
                    panic!("failed to read {} entry: {error}", root_library.display())
                })
                .path()
        })
        .filter(|path| {
            path.file_name()
                .and_then(OsStr::to_str)
                .is_some_and(|name| name.starts_with("librustc") || name.starts_with("libLLVM"))
        })
        .collect::<Vec<_>>();
    runtime_libraries.sort_unstable();
    for path in runtime_libraries {
        hash_file_input(&mut hasher, b"rustc-runtime-library", &path);
    }

    let rustlib = root_library.join("rustlib");
    for name in [
        "components".to_owned(),
        "multirust-channel-manifest.toml".to_owned(),
        format!("manifest-rustc-{}", toolchain.host),
        format!("manifest-rust-std-{}", toolchain.host),
    ] {
        let path = rustlib.join(name);
        if path.is_file() {
            hash_file_input(&mut hasher, b"rustup-component-manifest", &path);
        }
    }
    finish_build_identity(hasher)
}

fn resolve_optional_program(program: &str, path: &OsStr) -> Option<PathBuf> {
    let requested = Path::new(program);
    for directory in std::env::split_paths(path) {
        let candidate = directory.join(requested);
        if candidate.is_file() {
            return Some(absolute_program_path_preserving_final_symlink(&candidate));
        }
        if !std::env::consts::EXE_SUFFIX.is_empty() {
            let candidate = directory.join(format!("{program}{}", std::env::consts::EXE_SUFFIX));
            if candidate.is_file() {
                return Some(absolute_program_path_preserving_final_symlink(&candidate));
            }
        }
    }
    None
}

fn selected_external_build_tools() -> BTreeMap<String, PathBuf> {
    let path = normalized_absolute_path(std::env::var_os("PATH").as_deref());
    #[cfg(windows)]
    let required = ["git", "cl", "lib"];
    #[cfg(not(windows))]
    let required = ["git", "cc", "c++", "ar", "ranlib"];
    let mut tools = BTreeMap::new();
    for name in required {
        tools.insert(
            name.to_owned(),
            resolve_program(OsStr::new(name), Some(&path)),
        );
    }
    for name in [
        // GCC invokes the system assembler by name. Omitting it from the
        // hermetic PATH makes otherwise inventoried isolated builds fail at
        // native dependencies such as `psm` even though `cc` itself is fixed.
        "as",
        "bash",
        "clang",
        "clang++",
        "cmake",
        "ld",
        "llvm-ar",
        "llvm-ranlib",
        "make",
        "nm",
        "perl",
        "pkg-config",
        "python3",
        "sh",
        "strip",
        "xcrun",
    ] {
        if let Some(path) = resolve_optional_program(name, &path) {
            tools.insert(name.to_owned(), path);
        }
    }
    tools
}

fn tool_set_identity(tools: &BTreeMap<String, PathBuf>) -> String {
    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-external-tools-v1");
    for (name, path) in tools {
        hash_component(&mut hasher, b"tool-name", name.as_bytes());
        hash_file_input(&mut hasher, b"tool-executable", path);
    }
    finish_build_identity(hasher)
}

#[cfg(unix)]
fn publish_tool_link(target: &Path, destination: &Path) {
    std::os::unix::fs::symlink(target, destination).unwrap_or_else(|error| {
        panic!(
            "failed to publish selected build tool {} -> {}: {error}",
            destination.display(),
            target.display()
        )
    });
}

#[cfg(windows)]
fn publish_tool_link(target: &Path, destination: &Path) {
    std::os::windows::fs::symlink_file(target, destination).unwrap_or_else(|error| {
        panic!(
            "failed to publish selected build tool {} -> {}: {error}",
            destination.display(),
            target.display()
        )
    });
}

#[cfg(not(any(unix, windows)))]
fn publish_tool_link(target: &Path, destination: &Path) {
    filesystem::copy(target, destination).unwrap_or_else(|error| {
        panic!(
            "failed to copy selected build tool {} -> {}: {error}",
            destination.display(),
            target.display()
        )
    });
}

fn assert_tool_path_matches(path: &Path, tools: &BTreeMap<String, PathBuf>) {
    let metadata = filesystem::symlink_metadata(path)
        .unwrap_or_else(|error| panic!("failed to inspect tool PATH {}: {error}", path.display()));
    assert!(
        metadata.is_dir() && !metadata.file_type().is_symlink(),
        "selected tool PATH is not a real directory: {}",
        path.display()
    );
    let mut names = filesystem::read_dir(path)
        .unwrap_or_else(|error| panic!("failed to read tool PATH {}: {error}", path.display()))
        .map(|entry| {
            entry
                .unwrap_or_else(|error| {
                    panic!("failed to read tool PATH {}: {error}", path.display())
                })
                .file_name()
        })
        .collect::<Vec<_>>();
    names.sort_unstable();
    let mut expected = tools.keys().map(OsString::from).collect::<Vec<_>>();
    expected.sort_unstable();
    assert_eq!(names, expected, "selected tool PATH inventory changed");
    for (name, target) in tools {
        let link = path.join(name);
        let actual = link.canonicalize().unwrap_or_else(|error| {
            panic!(
                "failed to resolve selected tool {}: {error}",
                link.display()
            )
        });
        let expected = target.canonicalize().unwrap_or_else(|error| {
            panic!(
                "failed to resolve selected tool {}: {error}",
                target.display()
            )
        });
        assert_eq!(actual, expected, "selected tool link changed: {name}");
    }
}

fn publish_tool_path(tools: &BTreeMap<String, PathBuf>) -> PathBuf {
    let identity = tool_set_identity(tools);
    let temp = std::env::temp_dir()
        .canonicalize()
        .expect("temporary directory should be canonicalizable");
    let base = temp.join("ay-test-support-tool-path-v1");
    filesystem::create_dir_all(&base).unwrap_or_else(|error| {
        panic!(
            "failed to create selected tool store {}: {error}",
            base.display()
        )
    });
    let published = base.join(identity);
    if filesystem::symlink_metadata(&published).is_ok() {
        assert_tool_path_matches(&published, tools);
        return published;
    }
    let sequence = UNIQUE_PATH_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let staging = base.join(format!(".staging-{}-{sequence}", std::process::id()));
    filesystem::create_dir(&staging).unwrap_or_else(|error| {
        panic!(
            "failed to create selected tool staging {}: {error}",
            staging.display()
        )
    });
    for (name, target) in tools {
        assert_eq!(
            Path::new(name).components().count(),
            1,
            "selected tool name must be one path component"
        );
        publish_tool_link(target, &staging.join(name));
    }
    let mut permissions = filesystem::metadata(&staging)
        .expect("selected tool staging should exist")
        .permissions();
    #[cfg(unix)]
    permissions.set_mode(permissions.mode() & !0o222);
    #[cfg(not(unix))]
    permissions.set_readonly(true);
    filesystem::set_permissions(&staging, permissions)
        .expect("selected tool staging should become read-only");
    if let Err(error) = filesystem::rename(&staging, &published) {
        if filesystem::symlink_metadata(&published).is_ok() {
            make_tree_writable(&staging);
            filesystem::remove_dir_all(&staging)
                .expect("racing selected tool staging should be removable");
        } else {
            panic!("failed to publish selected tool PATH: {error}");
        }
    }
    assert_tool_path_matches(&published, tools);
    published
}

fn cargo_dependency_source_identity(
    build_workspace: &Path,
    spec: WorkspaceBinarySpec<'_>,
    cargo_home: &Path,
    cargo: &Path,
    host: &str,
    environment: &BTreeMap<OsString, OsString>,
) -> String {
    let mut command = Command::new(cargo);
    command
        .current_dir(build_workspace)
        .env_clear()
        .envs(environment)
        .args([
            "metadata",
            "--locked",
            "--offline",
            "--format-version",
            "1",
            "--filter-platform",
            host,
        ]);
    if !spec.features.is_empty() {
        command.arg("--features").arg(
            spec.features
                .iter()
                .map(|feature| format!("{}/{feature}", spec.package))
                .collect::<Vec<_>>()
                .join(","),
        );
    }
    let output = command.output().unwrap_or_else(|error| {
        panic!(
            "failed to inventory Cargo dependencies for {}: {error}",
            spec.package
        )
    });
    assert!(
        output.status.success(),
        "Cargo dependency inventory for {} failed with status {}:\n{}{}",
        spec.package,
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let metadata: serde_json::Value = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("Cargo metadata was not valid JSON: {error}"));
    let packages = metadata["packages"]
        .as_array()
        .expect("Cargo metadata packages should be an array");
    let workspace_members = metadata["workspace_members"]
        .as_array()
        .expect("Cargo metadata workspace_members should be an array")
        .iter()
        .map(|member| {
            member
                .as_str()
                .expect("Cargo workspace member ID should be a string")
                .to_owned()
        })
        .collect::<BTreeSet<_>>();

    let selected_package_names = if shared_checker_artifact_group(spec) {
        BTreeSet::from(["ay-drat-check", "ay-lrat-check"])
    } else {
        BTreeSet::from([spec.package])
    };
    let mut package_by_id = BTreeMap::new();
    let mut selected = Vec::new();
    for package in packages {
        let id = package["id"]
            .as_str()
            .expect("Cargo package ID should be a string")
            .to_owned();
        if workspace_members.contains(&id)
            && package["name"]
                .as_str()
                .is_some_and(|name| selected_package_names.contains(name))
        {
            selected.push(id.clone());
        }
        package_by_id.insert(id, package);
    }
    assert_eq!(
        selected.len(),
        selected_package_names.len(),
        "selected Cargo package set {selected_package_names:?} must identify exactly one workspace member per name"
    );

    let nodes = metadata["resolve"]["nodes"]
        .as_array()
        .expect("Cargo metadata resolve.nodes should be an array");
    let mut dependencies_by_id = BTreeMap::<String, Vec<String>>::new();
    for node in nodes {
        let id = node["id"]
            .as_str()
            .expect("Cargo resolve node ID should be a string")
            .to_owned();
        let dependencies = node["deps"]
            .as_array()
            .expect("Cargo resolve deps should be an array")
            .iter()
            .map(|dependency| {
                dependency["pkg"]
                    .as_str()
                    .expect("Cargo dependency package ID should be a string")
                    .to_owned()
            })
            .collect::<Vec<_>>();
        dependencies_by_id.insert(id, dependencies);
    }

    let mut closure = BTreeSet::new();
    let mut pending = selected;
    while let Some(id) = pending.pop() {
        if !closure.insert(id.clone()) {
            continue;
        }
        if let Some(dependencies) = dependencies_by_id.get(&id) {
            pending.extend(dependencies.iter().cloned());
        }
    }

    let build_workspace = build_workspace
        .canonicalize()
        .expect("build workspace should be canonicalizable");
    let cargo_home = cargo_home
        .canonicalize()
        .expect("Cargo home should be canonicalizable");
    let mut hasher = Sha256::new();
    hash_component(
        &mut hasher,
        b"schema",
        b"ay-test-cargo-dependency-sources-v1",
    );
    for package in selected_package_names {
        hash_component(&mut hasher, b"selected-package", package.as_bytes());
    }
    for id in closure {
        let package = package_by_id
            .get(&id)
            .unwrap_or_else(|| panic!("Cargo resolve referenced unknown package {id}"));
        let manifest = PathBuf::from(
            package["manifest_path"]
                .as_str()
                .expect("Cargo package manifest_path should be a string"),
        );
        let package_root = manifest
            .parent()
            .expect("Cargo package manifest should have a parent");
        assert!(
            package_root.is_absolute(),
            "Cargo reported a relative package source root: {} ({id})",
            package_root.display()
        );
        if package_root.starts_with(&build_workspace) {
            assert!(
                path_is_inside_real_tree(&build_workspace, package_root),
                "workspace Cargo package source traverses a symlink: {} ({id})",
                package_root.display()
            );
            continue;
        }
        assert!(
            package_root.starts_with(&cargo_home),
            "external Cargo package source is outside the inventoried Cargo home: {} ({id})",
            package_root.display()
        );
        assert!(
            path_is_inside_real_tree(&cargo_home, package_root),
            "external Cargo package source traverses a symlink: {} ({id})",
            package_root.display()
        );
        let canonical_root = package_root.canonicalize().unwrap_or_else(|error| {
            panic!(
                "failed to resolve Cargo package source {}: {error}",
                package_root.display()
            )
        });
        assert!(
            canonical_root.starts_with(&cargo_home),
            "external Cargo package source is outside the inventoried Cargo home: {} ({id})",
            canonical_root.display()
        );
        assert_snapshot_symlinks_are_internal(&canonical_root);
        let tree_identity = snapshot_manifest_identity(&canonical_root);
        hash_component(&mut hasher, b"package-id", id.as_bytes());
        hash_component(
            &mut hasher,
            b"package-source",
            package["source"].as_str().unwrap_or("path").as_bytes(),
        );
        hash_os_component(&mut hasher, b"package-root", canonical_root.as_os_str());
        hash_component(&mut hasher, b"package-tree", tree_identity.as_bytes());
    }
    finish_build_identity(hasher)
}

fn cargo_config_paths(workspace: &Path, cargo_home: &Path) -> Vec<PathBuf> {
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

fn git_path_status(
    context: &GitContext,
    workspace: &Path,
    args: &[&str],
    path: &Path,
) -> std::process::ExitStatus {
    Command::new(&context.executable)
        .args(["--literal-pathspecs", "-c"])
        .arg(format!("core.excludesFile={}", git_null_device()))
        .args(args)
        .arg(path)
        .current_dir(workspace)
        .env_clear()
        .envs(&context.environment)
        .output()
        .unwrap_or_else(|error| panic!("failed to run git {args:?}: {error}"))
        .status
}

fn cargo_config_is_source_bound(context: &GitContext, workspace: &Path, path: &Path) -> bool {
    if !path.starts_with(workspace) {
        return false;
    }
    let relative = path
        .strip_prefix(workspace)
        .expect("workspace prefix was checked");
    let mut component_path = workspace.to_path_buf();
    for component in relative.components() {
        component_path.push(component);
        let metadata = std::fs::symlink_metadata(&component_path).unwrap_or_else(|error| {
            panic!(
                "failed to inspect Cargo config component {}: {error}",
                component_path.display()
            )
        });
        if metadata.file_type().is_symlink() {
            return false;
        }
    }
    let canonical = path.canonicalize().unwrap_or_else(|error| {
        panic!("failed to resolve Cargo config {}: {error}", path.display())
    });
    if !canonical.starts_with(workspace) {
        return false;
    }
    if git_path_status(
        context,
        workspace,
        &["ls-files", "--error-unmatch", "--"],
        relative,
    )
    .success()
    {
        return true;
    }
    let ignored = git_path_status(
        context,
        workspace,
        &["check-ignore", "--quiet", "--"],
        relative,
    );
    match ignored.code() {
        Some(0) => false,
        Some(1) => true,
        _ => panic!(
            "git check-ignore failed while classifying Cargo config {}",
            path.display()
        ),
    }
}

fn reject_unbound_semantic_cargo_config(path: &Path, parsed: &toml::Value) {
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
            || (key == "build"
                && value.as_table().is_some_and(|t| {
                    t.keys()
                        .all(|k| matches!(k.as_str(), "rustc-wrapper" | "incremental"))
                }));
        assert!(
            nonsemantic,
            "Cargo config {} is outside exact source identity but sets semantic key {key:?}; move it into the workspace or remove the override",
            path.display()
        );
    }
}

fn cargo_configuration_identity(workspace: &Path, cargo_home: &Path) -> String {
    let workspace = workspace
        .canonicalize()
        .expect("workspace root should be canonicalizable");
    let cargo_home = canonicalize_existing_parent(cargo_home.to_path_buf());
    let git = GitContext::resolve(&workspace);
    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-cargo-config-v1");
    hash_os_component(&mut hasher, b"workspace", workspace.as_os_str());
    hash_os_component(&mut hasher, b"cargo-home", cargo_home.as_os_str());
    for path in cargo_config_paths(&workspace, &cargo_home) {
        let source_bound = cargo_config_is_source_bound(&git, &workspace, &path);
        hash_component(
            &mut hasher,
            b"config-source-bound",
            &[u8::from(source_bound)],
        );
        let contents = hash_file_input(&mut hasher, b"cargo-config", &path);
        let contents = std::str::from_utf8(&contents).unwrap_or_else(|error| {
            panic!("Cargo config {} is not UTF-8: {error}", path.display())
        });
        let parsed = contents.parse::<toml::Value>().unwrap_or_else(|error| {
            panic!("failed to parse Cargo config {}: {error}", path.display())
        });
        if !source_bound {
            reject_unbound_semantic_cargo_config(&path, &parsed);
        }
    }
    git.assert_unchanged(&workspace);
    finish_build_identity(hasher)
}

fn path_is_inside_real_tree(root: &Path, path: &Path) -> bool {
    if !path.starts_with(root) {
        return false;
    }
    let relative = path.strip_prefix(root).expect("tree prefix was checked");
    let mut component_path = root.to_path_buf();
    for component in relative.components() {
        component_path.push(component);
        let metadata = filesystem::symlink_metadata(&component_path).unwrap_or_else(|error| {
            panic!(
                "failed to inspect semantic input component {}: {error}",
                component_path.display()
            )
        });
        if metadata.file_type().is_symlink() {
            return false;
        }
    }
    path.canonicalize()
        .is_ok_and(|canonical| canonical.starts_with(root))
}

fn snapshot_cargo_configuration_identity(snapshot: &Path, cargo_home: &Path) -> String {
    let snapshot = snapshot
        .canonicalize()
        .expect("source snapshot should be canonicalizable");
    let cargo_home = canonicalize_existing_parent(cargo_home.to_path_buf());
    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-snapshot-cargo-config-v1");
    hash_os_component(&mut hasher, b"snapshot", snapshot.as_os_str());
    hash_os_component(&mut hasher, b"cargo-home", cargo_home.as_os_str());
    for path in cargo_config_paths(&snapshot, &cargo_home) {
        let source_bound = path_is_inside_real_tree(&snapshot, &path);
        hash_component(
            &mut hasher,
            b"config-source-bound",
            &[u8::from(source_bound)],
        );
        let contents = hash_file_input(&mut hasher, b"cargo-config", &path);
        let contents = std::str::from_utf8(&contents).unwrap_or_else(|error| {
            panic!("Cargo config {} is not UTF-8: {error}", path.display())
        });
        let parsed = contents.parse::<toml::Value>().unwrap_or_else(|error| {
            panic!("failed to parse Cargo config {}: {error}", path.display())
        });
        if !source_bound {
            reject_unbound_semantic_cargo_config(&path, &parsed);
        }
    }
    finish_build_identity(hasher)
}

fn hash_environment(hasher: &mut Sha256, environment: &BTreeMap<OsString, OsString>) {
    for (name, value) in environment {
        hash_os_component(hasher, b"environment-name", name);
        hash_os_component(hasher, b"environment-value", value);
    }
}

fn shared_checker_artifact_group(spec: WorkspaceBinarySpec<'_>) -> bool {
    spec.target_name == AY_CHECKER_TARGET_NAME
        && spec.features.is_empty()
        && spec.source_binding == SourceBinding::ExactProvenance
        && matches!(
            (spec.package, spec.binary),
            ("ay-lrat-check", "ay-lrat-check") | ("ay-drat-check", "ay-drat-check")
        )
}

fn workspace_invocation_identity(
    spec: WorkspaceBinarySpec<'_>,
    cargo_scheduling: NestedCargoScheduling,
) -> String {
    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-cargo-invocation-v2");
    if shared_checker_artifact_group(spec) {
        // These two whitelisted packages have distinct output filenames and
        // identical feature/binding requirements. Their build context binds
        // the union of both dependency closures, so sharing one target is
        // collision-free and avoids recompiling common dependencies.
        hash_component(
            &mut hasher,
            b"artifact-group",
            b"ay-distinct-standalone-checkers-v1",
        );
    } else {
        hash_component(&mut hasher, b"package", spec.package.as_bytes());
        hash_component(&mut hasher, b"binary", spec.binary.as_bytes());
    }
    let mut features = spec.features.to_vec();
    features.sort_unstable();
    features.dedup();
    for feature in features {
        hash_component(&mut hasher, b"feature", feature.as_bytes());
    }
    hash_component(
        &mut hasher,
        b"source-binding",
        match spec.source_binding {
            SourceBinding::IdentityTarget => b"identity-target",
            SourceBinding::AyVersion => b"ay-version",
            SourceBinding::ExactProvenance => b"exact-provenance",
        },
    );
    match cargo_scheduling {
        NestedCargoScheduling::CargoDefault => {
            hash_component(&mut hasher, b"cargo-jobs-mode", b"cargo-default");
        }
        NestedCargoScheduling::ExplicitPerInvocation { jobs } => {
            hash_component(&mut hasher, b"cargo-jobs-mode", b"explicit-per-invocation");
            hash_component(&mut hasher, b"cargo-jobs", jobs.to_string().as_bytes());
        }
        NestedCargoScheduling::ParentEnvelopeSerialized { jobs } => {
            hash_component(
                &mut hasher,
                b"cargo-jobs-mode",
                b"parent-envelope-serialized-v1",
            );
            hash_component(&mut hasher, b"cargo-jobs", jobs.to_string().as_bytes());
        }
    }
    finish_build_identity(hasher)
}

fn nested_cargo_build_arguments(
    spec: WorkspaceBinarySpec<'_>,
    target_dir: &Path,
    cargo_scheduling: NestedCargoScheduling,
) -> Vec<OsString> {
    let mut arguments = vec![OsString::from("build")];
    if let Some(jobs) = cargo_scheduling.jobs() {
        arguments.push("--jobs".into());
        arguments.push(jobs.to_string().into());
    }
    arguments.extend(
        [
            "--locked",
            "--offline",
            "-p",
            spec.package,
            "--bin",
            spec.binary,
            "--target-dir",
        ]
        .into_iter()
        .map(OsString::from),
    );
    arguments.push(target_dir.as_os_str().to_owned());
    if !spec.features.is_empty() {
        arguments.push("--features".into());
        arguments.push(spec.features.join(",").into());
    }
    arguments
}

fn inventoried_build_context(
    build_workspace: &Path,
    source_workspace: &Path,
    target_root: &Path,
    spec: WorkspaceBinarySpec<'_>,
    source_identity: &str,
) -> InventoriedBuildContext {
    let cargo_home = cargo_home(source_workspace);
    let toolchain = resolve_paired_toolchain(build_workspace);
    let tools = selected_external_build_tools();
    let tool_path = publish_tool_path(&tools);
    let tool_identity = tool_set_identity(&tools);
    let ambient = std::env::vars_os().collect::<Vec<_>>();
    let cargo_scheduling = nested_cargo_scheduling_from_ambient(&ambient);
    let mut environment = sanitized_build_environment_from(ambient, &cargo_home, &toolchain.rustc);
    environment.insert("PATH".into(), tool_path.as_os_str().to_owned());

    #[cfg(not(windows))]
    {
        let cc = tools.get("cc").expect("selected tool set must contain cc");
        let cxx = tools
            .get("c++")
            .expect("selected tool set must contain c++");
        let ar = tools.get("ar").expect("selected tool set must contain ar");
        let ranlib = tools
            .get("ranlib")
            .expect("selected tool set must contain ranlib");
        environment.insert("CC".into(), cc.as_os_str().to_owned());
        environment.insert("CXX".into(), cxx.as_os_str().to_owned());
        environment.insert("AR".into(), ar.as_os_str().to_owned());
        environment.insert("RANLIB".into(), ranlib.as_os_str().to_owned());
        let cargo_linker = format!(
            "CARGO_TARGET_{}_LINKER",
            toolchain.host.to_ascii_uppercase().replace(['-', '.'], "_")
        );
        environment.insert(cargo_linker.into(), cc.as_os_str().to_owned());
    }
    #[cfg(windows)]
    {
        let linker = tools.get("cl").expect("selected tool set must contain cl");
        let librarian = tools
            .get("lib")
            .expect("selected tool set must contain lib");
        environment.insert("CC".into(), linker.as_os_str().to_owned());
        environment.insert("CXX".into(), linker.as_os_str().to_owned());
        environment.insert("AR".into(), librarian.as_os_str().to_owned());
        let cargo_linker = format!(
            "CARGO_TARGET_{}_LINKER",
            toolchain.host.to_ascii_uppercase().replace(['-', '.'], "_")
        );
        environment.insert(cargo_linker.into(), linker.as_os_str().to_owned());
    }

    let execution_environment = environment_subset(&["SYSTEMROOT", "WINDIR"]);
    let cargo_version =
        checked_tool_output(&toolchain.cargo, &["-Vv"], build_workspace, &environment);
    let rustc_version =
        checked_tool_output(&toolchain.rustc, &["-Vv"], build_workspace, &environment);
    let target_cpus = checked_tool_output(
        &toolchain.rustc,
        &["--print", "target-cpus"],
        build_workspace,
        &environment,
    );
    let native_cfg = checked_tool_output(
        &toolchain.rustc,
        &["--print", "cfg", "-C", "target-cpu=native"],
        build_workspace,
        &environment,
    );
    let native_target = native_target_fingerprint(&target_cpus, &native_cfg);
    // This validation preserves the policy that ignored or external live
    // configs may not supply semantic build inputs. Cargo itself runs from the
    // out-of-tree snapshot and therefore cannot observe live workspace config.
    let source_config_policy = cargo_configuration_identity(source_workspace, &cargo_home);
    let config_identity = snapshot_cargo_configuration_identity(build_workspace, &cargo_home);
    let sysroot_identity = sysroot_library_identity(&toolchain);
    let dependency_identity = cargo_dependency_source_identity(
        build_workspace,
        spec,
        &cargo_home,
        &toolchain.cargo,
        &toolchain.host,
        &environment,
    );

    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-build-v4");
    hash_os_component(&mut hasher, b"build-workspace", build_workspace.as_os_str());
    hash_os_component(
        &mut hasher,
        b"source-workspace",
        source_workspace.as_os_str(),
    );
    hash_os_component(&mut hasher, b"cargo-target-root", target_root.as_os_str());
    hash_component(&mut hasher, b"source-identity", source_identity.as_bytes());
    hash_file_input(&mut hasher, b"cargo", &toolchain.cargo);
    hash_component(&mut hasher, b"cargo-version", &cargo_version);
    hash_file_input(&mut hasher, b"rustc", &toolchain.rustc);
    hash_component(&mut hasher, b"rustc-version", &rustc_version);
    hash_component(&mut hasher, b"rust-sysroot", sysroot_identity.as_bytes());
    hash_component(
        &mut hasher,
        b"external-build-tools",
        tool_identity.as_bytes(),
    );
    hash_component(
        &mut hasher,
        b"cargo-dependency-sources",
        dependency_identity.as_bytes(),
    );
    hash_component(
        &mut hasher,
        b"rustc-native-target",
        native_target.as_bytes(),
    );
    hash_component(
        &mut hasher,
        b"cargo-configuration",
        config_identity.as_bytes(),
    );
    hash_component(
        &mut hasher,
        b"source-cargo-config-policy",
        source_config_policy.as_bytes(),
    );
    hash_environment(&mut hasher, &environment);
    let invocation_identity = workspace_invocation_identity(spec, cargo_scheduling);
    hash_component(
        &mut hasher,
        b"cargo-invocation",
        invocation_identity.as_bytes(),
    );

    InventoriedBuildContext {
        cargo: toolchain.cargo,
        rustc: toolchain.rustc,
        cargo_scheduling,
        environment,
        execution_environment,
        identity: finish_build_identity(hasher),
    }
}

fn assert_inventoried_build_context(
    build_workspace: &Path,
    source_workspace: &Path,
    target_root: &Path,
    spec: WorkspaceBinarySpec<'_>,
    source_identity: &str,
    expected: &InventoriedBuildContext,
    operation: &str,
) {
    let actual = inventoried_build_context(
        build_workspace,
        source_workspace,
        target_root,
        spec,
        source_identity,
    );
    assert_eq!(
        &actual, expected,
        "semantic build inputs changed during {operation}; refusing an ambiguously built binary"
    );
}

/// Return whether AY's UTF-8 `--version` output carries `source_identity`.
pub fn ay_version_has_source_identity(version_stdout: &[u8], source_identity: &str) -> bool {
    let Ok(version) = std::str::from_utf8(version_stdout) else {
        return false;
    };
    version.contains(&format!(".{source_identity}@"))
}

fn expected_exact_provenance(source_identity: &str, build_identity: &str) -> String {
    assert!(
        source_identity
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-'),
        "source identity is not JSON-token safe"
    );
    assert!(
        build_identity
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-'),
        "build identity is not JSON-token safe"
    );
    format!(
        "{{\"schema\":\"{EXACT_PROVENANCE_SCHEMA}\",\"source_identity\":\"{source_identity}\",\"build_identity\":\"{build_identity}\"}}\n"
    )
}

fn frozen_artifact_identity(path: &Path) -> String {
    let metadata = filesystem::symlink_metadata(path)
        .unwrap_or_else(|error| panic!("failed to inspect artifact {}: {error}", path.display()));
    assert!(
        metadata.is_file() && !metadata.file_type().is_symlink(),
        "exact executable artifact is not a real file: {}",
        path.display()
    );
    #[cfg(unix)]
    assert_eq!(
        metadata.permissions().mode() & 0o222,
        0,
        "exact executable artifact is writable: {}",
        path.display()
    );
    #[cfg(not(unix))]
    assert!(
        metadata.permissions().readonly(),
        "exact executable artifact is writable: {}",
        path.display()
    );
    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", b"ay-test-frozen-artifact-v1");
    hash_component(
        &mut hasher,
        b"artifact-mode",
        &permission_identity_bytes(&metadata),
    );
    let contents = filesystem::read(path)
        .unwrap_or_else(|error| panic!("failed to read artifact {}: {error}", path.display()));
    hash_component(&mut hasher, b"artifact-contents", &contents);
    finish_build_identity(hasher)
}

fn publish_frozen_artifact(
    target_root: &Path,
    binary_path: &Path,
    binary: &str,
    source_identity: &str,
    build_identity: &str,
) -> (PathBuf, String) {
    filesystem::create_dir_all(target_root).unwrap_or_else(|error| {
        panic!(
            "failed to create target root {}: {error}",
            target_root.display()
        )
    });
    let target_root = target_root
        .canonicalize()
        .expect("target root should be canonicalizable");
    let artifact_dir = target_root
        .join("ay-test-frozen-artifacts-v1")
        .join(source_identity)
        .join(build_identity);
    filesystem::create_dir_all(&artifact_dir).unwrap_or_else(|error| {
        panic!(
            "failed to create frozen artifact directory {}: {error}",
            artifact_dir.display()
        )
    });
    let metadata = filesystem::symlink_metadata(&artifact_dir).unwrap_or_else(|error| {
        panic!(
            "failed to inspect artifact directory {}: {error}",
            artifact_dir.display()
        )
    });
    assert!(
        metadata.is_dir() && !metadata.file_type().is_symlink(),
        "frozen artifact directory is not a real directory: {}",
        artifact_dir.display()
    );

    let sequence = UNIQUE_PATH_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let staging = artifact_dir.join(format!(
        ".{binary}.staging-{}-{sequence}",
        std::process::id()
    ));
    let contents = filesystem::read(binary_path).unwrap_or_else(|error| {
        panic!(
            "failed to read Cargo artifact {}: {error}",
            binary_path.display()
        )
    });
    filesystem::write(&staging, contents).unwrap_or_else(|error| {
        panic!(
            "failed to stage frozen artifact {}: {error}",
            staging.display()
        )
    });
    let source_mode = filesystem::metadata(binary_path)
        .unwrap_or_else(|error| panic!("failed to inspect {}: {error}", binary_path.display()))
        .permissions();
    filesystem::set_permissions(&staging, source_mode).unwrap_or_else(|error| {
        panic!(
            "failed to preserve artifact mode on {}: {error}",
            staging.display()
        )
    });
    let mut permissions = filesystem::metadata(&staging)
        .expect("staged artifact should exist")
        .permissions();
    #[cfg(unix)]
    permissions.set_mode(permissions.mode() & !0o222);
    #[cfg(not(unix))]
    permissions.set_readonly(true);
    filesystem::set_permissions(&staging, permissions)
        .expect("staged artifact should become read-only");
    let artifact_identity = frozen_artifact_identity(&staging);
    let published = artifact_dir.join(format!(
        "{binary}-{artifact_identity}{}",
        std::env::consts::EXE_SUFFIX
    ));
    match filesystem::symlink_metadata(&published) {
        Ok(metadata) => {
            assert!(
                metadata.is_file() && !metadata.file_type().is_symlink(),
                "preexisting frozen artifact is not a real file: {}",
                published.display()
            );
            assert_eq!(
                frozen_artifact_identity(&published),
                artifact_identity,
                "preexisting frozen artifact failed content verification"
            );
            let mut staging_permissions = filesystem::metadata(&staging)
                .expect("staged artifact should exist")
                .permissions();
            #[cfg(unix)]
            staging_permissions.set_mode(staging_permissions.mode() | 0o600);
            #[cfg(not(unix))]
            staging_permissions.set_readonly(false);
            filesystem::set_permissions(&staging, staging_permissions)
                .expect("staged artifact should become removable");
            filesystem::remove_file(&staging).expect("staged artifact should be removable");
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            if let Err(rename_error) = filesystem::rename(&staging, &published) {
                if filesystem::symlink_metadata(&published).is_ok() {
                    assert_eq!(
                        frozen_artifact_identity(&published),
                        artifact_identity,
                        "racing frozen artifact publication disagreed"
                    );
                    let mut staging_permissions = filesystem::metadata(&staging)
                        .expect("staged artifact should exist")
                        .permissions();
                    #[cfg(unix)]
                    staging_permissions.set_mode(staging_permissions.mode() | 0o600);
                    #[cfg(not(unix))]
                    staging_permissions.set_readonly(false);
                    filesystem::set_permissions(&staging, staging_permissions)
                        .expect("staged artifact should become removable");
                    filesystem::remove_file(&staging)
                        .expect("racing staged artifact should be removable");
                } else {
                    panic!("failed to publish frozen executable artifact: {rename_error}");
                }
            }
        }
        Err(error) => panic!(
            "failed to inspect frozen artifact destination {}: {error}",
            published.display()
        ),
    }
    assert_eq!(
        frozen_artifact_identity(&published),
        artifact_identity,
        "published frozen artifact changed"
    );
    (published, artifact_identity)
}

impl BuiltWorkspaceBinary {
    fn assert_ready_for_execution(&self) {
        assert_eq!(
            frozen_artifact_identity(&self.artifact_path),
            self.artifact_identity,
            "exact executable artifact changed after it was built"
        );
        match self.source_binding {
            SourceBinding::IdentityTarget => {}
            SourceBinding::AyVersion => {
                let mut command = Command::new(&self.artifact_path);
                command
                    .arg("--version")
                    .env_clear()
                    .envs(&self.execution_environment);
                let output = command.output().unwrap_or_else(|error| {
                    panic!(
                        "failed to verify exact executable {}: {error}",
                        self.artifact_path.display()
                    )
                });
                assert!(
                    output.status.success()
                        && ay_version_has_source_identity(&output.stdout, &self.source_identity),
                    "{} failed exact source version verification: status={} stdout={} stderr={}",
                    self.artifact_path.display(),
                    output.status,
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
            }
            SourceBinding::ExactProvenance => {
                let mut command = Command::new(&self.artifact_path);
                command
                    .arg(EXACT_PROVENANCE_FLAG)
                    .env_clear()
                    .envs(&self.execution_environment);
                let output = command.output().unwrap_or_else(|error| {
                    panic!(
                        "failed to verify exact executable provenance {}: {error}",
                        self.artifact_path.display()
                    )
                });
                assert!(
                    output.status.success(),
                    "{} provenance endpoint failed with status {}: {}",
                    self.artifact_path.display(),
                    output.status,
                    String::from_utf8_lossy(&output.stderr)
                );
                let expected =
                    expected_exact_provenance(&self.source_identity, &self.build_identity);
                assert_eq!(
                    output.stdout,
                    expected.as_bytes(),
                    "{} returned mismatched exact provenance",
                    self.artifact_path.display()
                );
                assert!(
                    output.stderr.is_empty(),
                    "{} provenance endpoint wrote unexpected stderr: {}",
                    self.artifact_path.display(),
                    String::from_utf8_lossy(&output.stderr)
                );
            }
        }
        assert_eq!(
            frozen_artifact_identity(&self.artifact_path),
            self.artifact_identity,
            "exact executable artifact changed during provenance verification"
        );
    }

    /// Create a sanitized command after revalidating the frozen executable's
    /// content and exact machine-readable provenance.
    ///
    /// The returned command has no ambient environment or PATH. Callers may
    /// add explicit arguments, stdio, or narrowly required environment values.
    #[must_use]
    pub fn command(&self) -> Command {
        self.assert_ready_for_execution();
        let mut command = Command::new(&self.artifact_path);
        command.env_clear().envs(&self.execution_environment);
        command
    }

    /// Format the frozen executable path for diagnostics.
    ///
    /// Path privacy is API discipline, not a sealed capability: formatted
    /// output and [`Command::get_program`] can reveal the path. In-repository
    /// callers must execute through [`Self::command`] so revalidation runs.
    pub fn artifact_display(&self) -> impl std::fmt::Display + '_ {
        self.artifact_path.display()
    }
}

/// Build from an immutable exact-workspace snapshot with inventoried Cargo
/// dependency and build-tool provenance.
///
/// The platform kernel, loader, dynamic system libraries, and SDK internals
/// remain platform TCB inputs; this function does not claim total hermeticity.
pub fn build_workspace_binary(spec: WorkspaceBinarySpec<'_>) -> BuiltWorkspaceBinary {
    let workspace = spec
        .workspace
        .canonicalize()
        .expect("workspace root should be canonicalizable");
    let snapshot = create_workspace_source_snapshot(&workspace);
    build_workspace_binary_from_snapshot(spec, workspace, snapshot)
}

fn build_workspace_binary_from_snapshot(
    spec: WorkspaceBinarySpec<'_>,
    workspace: PathBuf,
    snapshot: SourceSnapshot,
) -> BuiltWorkspaceBinary {
    let source_identity = snapshot.source_identity.clone();
    let target_root = prepare_cargo_target_root(&workspace);
    let expected_cargo_scheduling = current_nested_cargo_scheduling();
    let parent_nested_cargo_lock = expected_cargo_scheduling
        .serializes_parent_envelope()
        .then(|| acquire_parent_nested_cargo_lock(&target_root));
    let build_context = inventoried_build_context(
        &snapshot.root,
        &workspace,
        &target_root,
        spec,
        &source_identity,
    );
    assert_eq!(
        build_context.cargo_scheduling, expected_cargo_scheduling,
        "nested Cargo scheduling environment changed while acquiring the parent-envelope lock"
    );
    let build_identity = build_context.identity.clone();
    let target_name = build_bound_target_name(spec.target_name, &source_identity, &build_identity);
    let outer_exe = std::env::current_exe().ok();
    let target_dir =
        isolated_cargo_target_dir_for_outer_in(&target_root, &target_name, outer_exe.as_deref());
    let binary_path = cargo_binary_path(&target_dir, spec.binary);

    eprintln!(
        "[ay tests] building {}/{} from {source_identity} with {build_identity} in isolated target {}",
        spec.package,
        spec.binary,
        target_dir.display()
    );
    let mut command = Command::new(&build_context.cargo);
    command
        .current_dir(&snapshot.root)
        .env_clear()
        .envs(&build_context.environment)
        .args(nested_cargo_build_arguments(
            spec,
            &target_dir,
            build_context.cargo_scheduling,
        ));
    if matches!(
        spec.source_binding,
        SourceBinding::AyVersion | SourceBinding::ExactProvenance
    ) {
        command
            .env("AY_SOURCE_GIT_COMMIT", &source_identity)
            .env("AY_SOURCE_GIT_DIRTY", "false");
    }
    if spec.source_binding == SourceBinding::ExactProvenance {
        command
            .env("AY_TEST_SOURCE_IDENTITY", &source_identity)
            .env("AY_TEST_BUILD_IDENTITY", &build_identity);
    }
    let output = command.output().unwrap_or_else(|error| {
        panic!(
            "failed to build {}/{} from {source_identity}: {error}",
            spec.package, spec.binary
        )
    });
    assert!(
        output.status.success(),
        "isolated cargo build for {}/{} failed with status {}:\n{}{}",
        spec.package,
        spec.binary,
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    snapshot.assert_unchanged(&format!(
        "isolated cargo build for {}/{}",
        spec.package, spec.binary
    ));
    assert_inventoried_build_context(
        &snapshot.root,
        &workspace,
        &target_root,
        spec,
        &source_identity,
        &build_context,
        &format!("isolated cargo build for {}/{}", spec.package, spec.binary),
    );
    drop(parent_nested_cargo_lock);
    assert!(
        binary_path.is_file(),
        "isolated cargo build did not produce {}",
        binary_path.display()
    );

    let (artifact_path, artifact_identity) = publish_frozen_artifact(
        &target_root,
        &binary_path,
        spec.binary,
        &source_identity,
        &build_identity,
    );
    let built = BuiltWorkspaceBinary {
        artifact_path,
        artifact_identity,
        execution_environment: build_context.execution_environment,
        source_binding: spec.source_binding,
        source_identity,
        build_identity,
        target_dir,
        snapshot_dir: snapshot.root,
    };
    built.assert_ready_for_execution();
    built
}

/// Build and provenance-check the exact-source AY CLI.
pub fn build_ay_cli(workspace: &Path) -> BuiltWorkspaceBinary {
    build_workspace_binary(WorkspaceBinarySpec {
        workspace,
        target_name: AY_CLI_TARGET_NAME,
        package: "ay",
        binary: "ay",
        features: &["cli"],
        source_binding: SourceBinding::ExactProvenance,
    })
}

/// Build the exact-source standalone AY LRAT checker.
pub fn build_ay_lrat_checker(workspace: &Path) -> BuiltWorkspaceBinary {
    build_workspace_binary(WorkspaceBinarySpec {
        workspace,
        target_name: AY_CHECKER_TARGET_NAME,
        package: "ay-lrat-check",
        binary: "ay-lrat-check",
        features: &[],
        source_binding: SourceBinding::ExactProvenance,
    })
}

/// Build the exact-source standalone AY DRAT checker.
pub fn build_ay_drat_checker(workspace: &Path) -> BuiltWorkspaceBinary {
    build_workspace_binary(WorkspaceBinarySpec {
        workspace,
        target_name: AY_CHECKER_TARGET_NAME,
        package: "ay-drat-check",
        binary: "ay-drat-check",
        features: &[],
        source_binding: SourceBinding::ExactProvenance,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(not(windows))]
    #[test]
    fn selected_tool_path_includes_the_system_assembler_when_available() {
        let ambient = normalized_absolute_path(std::env::var_os("PATH").as_deref());
        if resolve_optional_program("as", &ambient).is_some() {
            assert!(
                selected_external_build_tools().contains_key("as"),
                "an inventoried cc must be able to invoke its PATH-selected assembler"
            );
        }
    }

    fn run_git(workspace: &Path, args: &[&str]) {
        let output = Command::new("git")
            .args(args)
            .current_dir(workspace)
            .output()
            .unwrap_or_else(|error| panic!("failed to run git {args:?}: {error}"));
        assert!(
            output.status.success(),
            "git {args:?} failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    fn empty_repository() -> tempfile::TempDir {
        let repository = tempfile::tempdir().expect("temporary Git repository");
        run_git(repository.path(), &["init", "--quiet"]);
        run_git(repository.path(), &["config", "user.name", "AY Tests"]);
        run_git(
            repository.path(),
            &["config", "user.email", "ay-tests@example.invalid"],
        );
        repository
    }

    fn assert_index_flag_cannot_hide_tracked_content(flag: &str) {
        let repository = empty_repository();
        let tracked = repository.path().join("tracked.txt");
        std::fs::write(&tracked, b"original\n").expect("write tracked fixture");
        run_git(repository.path(), &["add", "tracked.txt"]);
        run_git(repository.path(), &["commit", "--quiet", "-m", "fixture"]);

        let original = workspace_source_identity(repository.path());
        run_git(repository.path(), &["update-index", flag, "tracked.txt"]);
        std::fs::write(&tracked, b"changed behind the index flag\n")
            .expect("change index-flagged tracked fixture");

        let diff_status = Command::new("git")
            .args(["diff", "--quiet", "HEAD", "--", "tracked.txt"])
            .current_dir(repository.path())
            .status()
            .expect("run git diff");
        assert!(
            diff_status.success(),
            "fixture must demonstrate that git diff suppressed the change"
        );
        let changed = workspace_source_identity(repository.path());
        assert_ne!(
            changed, original,
            "actual tracked bytes must affect identity despite {flag}"
        );
    }

    #[test]
    fn source_identity_detects_assume_unchanged_tracked_content() {
        assert_index_flag_cannot_hide_tracked_content("--assume-unchanged");
    }

    #[test]
    fn source_identity_detects_skip_worktree_tracked_content() {
        assert_index_flag_cannot_hide_tracked_content("--skip-worktree");
    }

    #[test]
    fn source_identity_parts_sort_untracked_entries() {
        let forward = vec![
            (b"a".to_vec(), b"one".to_vec()),
            (b"b".to_vec(), b"two".to_vec()),
        ];
        let reverse = forward.iter().rev().cloned().collect::<Vec<_>>();
        assert_eq!(
            source_identity_from_parts(b"head", b"tracked", &forward),
            source_identity_from_parts(b"head", b"tracked", &reverse),
            "caller enumeration order must not affect source identity"
        );
    }

    #[test]
    fn build_target_binds_source_and_semantic_build_inputs() {
        assert_eq!(
            build_bound_target_name("exact", "source-one", "build-one"),
            "exact-source-one-build-one"
        );
        assert_ne!(
            build_bound_target_name("exact", "source-one", "build-one"),
            build_bound_target_name("exact", "source-one", "build-two")
        );
    }

    #[test]
    fn cargo_target_root_honors_outer_storage_without_changing_fallback() {
        let workspace = tempfile::tempdir().expect("temporary workspace");
        let workspace = workspace.path().canonicalize().unwrap();
        assert_eq!(
            cargo_target_root_from(&workspace, None),
            workspace.join("target")
        );
        assert_eq!(
            cargo_target_root_from(&workspace, Some(OsStr::new(""))),
            workspace.join("target"),
            "an empty override must preserve the existing fallback"
        );

        let absolute = tempfile::tempdir().expect("absolute target root");
        let configured = cargo_target_root_from(&workspace, Some(absolute.path().as_os_str()));
        assert_eq!(
            configured,
            cargo_target_root_from(&workspace, Some(absolute.path().as_os_str())),
            "one workspace must select a stable shared target namespace"
        );
        assert!(
            configured.starts_with(
                absolute
                    .path()
                    .canonicalize()
                    .unwrap()
                    .join("ay-test-workspaces-v1")
            ),
            "configured target must remain below the explicit storage root"
        );
        assert!(
            cargo_target_root_from(&workspace, Some(OsStr::new("outer-target")))
                .starts_with(workspace.join("outer-target/ay-test-workspaces-v1"))
        );

        let other_workspace = tempfile::tempdir().expect("other temporary workspace");
        assert_ne!(
            configured,
            cargo_target_root_from(
                &other_workspace.path().canonicalize().unwrap(),
                Some(absolute.path().as_os_str())
            ),
            "shared outer storage must retain worktree isolation"
        );
    }

    #[test]
    fn configured_target_root_preserves_nested_lock_avoidance() {
        let target_root = tempfile::tempdir().expect("temporary target root");
        let primary = isolated_cargo_target_dir_for_outer_in(target_root.path(), "exact", None);
        assert_eq!(
            primary,
            target_root
                .path()
                .canonicalize()
                .expect("temporary target root should be canonicalizable")
                .join("exact"),
            "target identity must use the canonical root even when macOS exposes /var via /private/var"
        );

        let outer_exe = primary.join("debug/deps/running-test");
        let nested =
            isolated_cargo_target_dir_for_outer_in(target_root.path(), "exact", Some(&outer_exe));
        assert_ne!(nested, primary);
        assert_eq!(
            nested.file_name().and_then(OsStr::to_str),
            Some(format!("exact-nested-{}", std::process::id()).as_str())
        );
    }

    #[cfg(unix)]
    #[test]
    fn configured_target_root_rejects_symlinked_managed_namespace() {
        use std::os::unix::fs::symlink;

        let base = tempfile::tempdir().expect("temporary configured root");
        let redirect = tempfile::tempdir().expect("temporary redirect");
        let namespace = base.path().join("ay-test-workspaces-v1");
        symlink(redirect.path(), &namespace).expect("create namespace symlink");
        let selected = namespace.join("workspace-key");
        assert!(
            std::panic::catch_unwind(|| prepare_selected_cargo_target_root(selected)).is_err(),
            "managed target namespace symlinks must fail closed"
        );
    }

    #[test]
    fn only_distinct_whitelisted_checkers_share_an_invocation_target() {
        let lrat = WorkspaceBinarySpec {
            workspace: Path::new("."),
            target_name: AY_CHECKER_TARGET_NAME,
            package: "ay-lrat-check",
            binary: "ay-lrat-check",
            features: &[],
            source_binding: SourceBinding::ExactProvenance,
        };
        let drat = WorkspaceBinarySpec {
            workspace: Path::new("."),
            target_name: AY_CHECKER_TARGET_NAME,
            package: "ay-drat-check",
            binary: "ay-drat-check",
            features: &[],
            source_binding: SourceBinding::ExactProvenance,
        };
        let colliding_other_package = WorkspaceBinarySpec {
            workspace: Path::new("."),
            target_name: AY_CHECKER_TARGET_NAME,
            package: "other-package",
            binary: "ay-lrat-check",
            features: &[],
            source_binding: SourceBinding::ExactProvenance,
        };

        let parent_scheduling = NestedCargoScheduling::ParentEnvelopeSerialized { jobs: 3 };
        let lrat_identity = workspace_invocation_identity(lrat, parent_scheduling);
        let drat_identity = workspace_invocation_identity(drat, parent_scheduling);
        let other_identity =
            workspace_invocation_identity(colliding_other_package, parent_scheduling);
        assert_eq!(
            lrat_identity, drat_identity,
            "the distinct standalone checker outputs should reuse compiled dependencies"
        );
        assert_ne!(
            lrat_identity, other_identity,
            "generic or colliding output specs must retain package/binary isolation"
        );
        assert_eq!(
            build_bound_target_name("checker", "source", &lrat_identity),
            build_bound_target_name("checker", "source", &drat_identity)
        );
        assert_ne!(
            build_bound_target_name("checker", "source", &lrat_identity),
            build_bound_target_name("checker", "source", &other_identity)
        );
        assert_ne!(
            lrat_identity,
            workspace_invocation_identity(
                lrat,
                NestedCargoScheduling::ParentEnvelopeSerialized { jobs: 2 }
            ),
            "Cargo exposes its job count to build scripts, so the cap is an artifact input"
        );
        assert_ne!(
            lrat_identity,
            workspace_invocation_identity(lrat, NestedCargoScheduling::CargoDefault),
            "an explicit cap and Cargo's host-dependent default must not share provenance"
        );
        assert_ne!(
            lrat_identity,
            workspace_invocation_identity(
                lrat,
                NestedCargoScheduling::ExplicitPerInvocation { jobs: 3 }
            ),
            "serialized parent-envelope scheduling must be explicit in provenance"
        );
    }

    #[test]
    fn nested_cargo_job_cap_is_strict_and_parent_authenticated() {
        fn environment(entries: &[(&str, &str)]) -> Vec<(OsString, OsString)> {
            entries
                .iter()
                .map(|(name, value)| (OsString::from(name), OsString::from(value)))
                .collect()
        }

        assert_eq!(
            nested_cargo_scheduling_from_ambient(&[]),
            NestedCargoScheduling::CargoDefault
        );
        assert_eq!(
            nested_cargo_scheduling_from_ambient(&environment(&[(CARGO_BUILD_JOBS_ENV, "3")])),
            NestedCargoScheduling::ExplicitPerInvocation { jobs: 3 }
        );
        assert_eq!(
            nested_cargo_scheduling_from_ambient(&environment(&[
                (OOM_GUARD_PARENT_LEASE_ENV, "1"),
                (CARGO_BUILD_JOBS_ENV, "3"),
                (NBCORE_ENV, "3"),
            ])),
            NestedCargoScheduling::ParentEnvelopeSerialized { jobs: 3 }
        );

        for entries in [
            vec![(CARGO_BUILD_JOBS_ENV, "")],
            vec![(CARGO_BUILD_JOBS_ENV, "0")],
            vec![(CARGO_BUILD_JOBS_ENV, "-1")],
            vec![(CARGO_BUILD_JOBS_ENV, "many")],
            vec![(OOM_GUARD_PARENT_LEASE_ENV, "0")],
            vec![(OOM_GUARD_PARENT_LEASE_ENV, "1")],
            vec![
                (OOM_GUARD_PARENT_LEASE_ENV, "1"),
                (CARGO_BUILD_JOBS_ENV, "3"),
            ],
            vec![
                (OOM_GUARD_PARENT_LEASE_ENV, "1"),
                (CARGO_BUILD_JOBS_ENV, "3"),
                (NBCORE_ENV, "2"),
            ],
        ] {
            assert!(
                std::panic::catch_unwind(|| {
                    nested_cargo_scheduling_from_ambient(&environment(&entries))
                })
                .is_err(),
                "invalid nested Cargo resource environment must fail closed: {entries:?}"
            );
        }
    }

    #[test]
    fn nested_cargo_command_explicitly_applies_validated_job_cap() {
        let spec = WorkspaceBinarySpec {
            workspace: Path::new("."),
            target_name: "exact",
            package: "example-package",
            binary: "example-binary",
            features: &["one", "two"],
            source_binding: SourceBinding::IdentityTarget,
        };
        let capped = nested_cargo_build_arguments(
            spec,
            Path::new("exact-target"),
            NestedCargoScheduling::ParentEnvelopeSerialized { jobs: 3 },
        );
        assert_eq!(
            capped,
            [
                "build",
                "--jobs",
                "3",
                "--locked",
                "--offline",
                "-p",
                "example-package",
                "--bin",
                "example-binary",
                "--target-dir",
                "exact-target",
                "--features",
                "one,two",
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );

        let uncapped = nested_cargo_build_arguments(
            spec,
            Path::new("exact-target"),
            NestedCargoScheduling::CargoDefault,
        );
        assert!(
            !uncapped
                .iter()
                .any(|argument| argument == OsStr::new("--jobs")),
            "ordinary tests without a configured cap retain Cargo's default"
        );
    }

    #[test]
    fn parent_nested_cargo_lock_excludes_a_second_file_handle() {
        let target_root = tempfile::tempdir().expect("temporary target root");
        let expected_path = target_root.path().join(PARENT_NESTED_CARGO_LOCK_FILE);
        assert_eq!(
            parent_nested_cargo_lock_path(target_root.path()),
            expected_path
        );

        let first = acquire_parent_nested_cargo_lock(target_root.path());
        let second = open_parent_nested_cargo_lock(target_root.path());
        let error = second
            .try_lock()
            .expect_err("a second nested Cargo handle must not enter the parent envelope");
        assert!(
            matches!(error, filesystem::TryLockError::WouldBlock),
            "lock contention must fail nonblockingly: {error}"
        );

        drop(first);
        second
            .try_lock()
            .expect("dropping the first handle must release the nested Cargo lock");
    }

    #[test]
    fn native_target_fingerprint_is_order_independent_and_cpu_sensitive() {
        let first = native_target_fingerprint(
            b"cpu-b\nnative currently cpu-a\ncpu-a\n",
            b"target_feature=\"b\"\ntarget_arch=\"example\"\ntarget_feature=\"a\"\n",
        );
        let reordered = native_target_fingerprint(
            b"cpu-a\ncpu-b\nnative currently cpu-a\n",
            b"target_feature=\"a\"\ntarget_feature=\"b\"\ntarget_arch=\"example\"\n",
        );
        let other_cpu = native_target_fingerprint(
            b"cpu-a\ncpu-b\nnative currently cpu-b\n",
            b"target_feature=\"a\"\ntarget_feature=\"b\"\ntarget_arch=\"example\"\n",
        );
        assert_eq!(first, reordered, "rustc output order must not matter");
        assert_ne!(
            first, other_cpu,
            "the CPU selected by target-cpu=native must bind the build target"
        );
    }

    #[test]
    fn sanitized_build_environment_removes_ambient_compiler_overrides() {
        let path_dir = tempfile::tempdir().expect("temporary PATH directory");
        let ambient = [
            (OsString::from("HOME"), OsString::from("/home/test")),
            (
                OsString::from("USERPROFILE"),
                OsString::from("C:\\Users\\test"),
            ),
            (OsString::from("TEMP"), OsString::from("/ambient/temp")),
            (OsString::from("TMP"), OsString::from("/ambient/tmp")),
            (OsString::from("TMPDIR"), OsString::from("/ambient/tmpdir")),
            (
                OsString::from("PATH"),
                path_dir.path().as_os_str().to_owned(),
            ),
            (OsString::from("RUSTC"), OsString::from("fake-rustc")),
            (
                OsString::from("RUSTC_WRAPPER"),
                OsString::from("fake-wrapper"),
            ),
            (
                OsString::from("RUSTC_WORKSPACE_WRAPPER"),
                OsString::from("fake-workspace-wrapper"),
            ),
            (OsString::from("RUSTFLAGS"), OsString::from("--cfg=fake")),
            (
                OsString::from("CARGO_ENCODED_RUSTFLAGS"),
                OsString::from("--cfg=fake"),
            ),
            (
                OsString::from("CARGO_TARGET_DIR"),
                OsString::from("/fake/target"),
            ),
            (
                OsString::from("CARGO_BUILD_TARGET"),
                OsString::from("fake-target"),
            ),
            (
                OsString::from("CARGO_PROFILE_DEV_OPT_LEVEL"),
                OsString::from("3"),
            ),
            (OsString::from(CARGO_BUILD_JOBS_ENV), OsString::from("3")),
            (
                OsString::from(OOM_GUARD_PARENT_LEASE_ENV),
                OsString::from("1"),
            ),
            (OsString::from(NBCORE_ENV), OsString::from("3")),
        ];
        let environment = sanitized_build_environment_from(
            ambient,
            Path::new("/exact/cargo-home"),
            Path::new("/exact/rustc"),
        );

        assert_eq!(
            environment.get(OsStr::new("RUSTC")),
            Some(&OsString::from("/exact/rustc"))
        );
        assert_eq!(
            environment.get(OsStr::new("CARGO_HOME")),
            Some(&OsString::from("/exact/cargo-home"))
        );
        assert_eq!(
            environment.get(OsStr::new("PATH")),
            Some(&path_dir.path().canonicalize().unwrap().into_os_string())
        );
        assert_eq!(
            environment.get(OsStr::new("SOURCE_DATE_EPOCH")),
            Some(&OsString::from("1"))
        );
        assert_eq!(
            environment.get(OsStr::new("CARGO_INCREMENTAL")),
            Some(&OsString::from("0"))
        );
        for removed in [
            "HOME",
            "USERPROFILE",
            "TEMP",
            "TMP",
            "TMPDIR",
            "RUSTC_WRAPPER",
            "RUSTC_WORKSPACE_WRAPPER",
            "RUSTFLAGS",
            "CARGO_ENCODED_RUSTFLAGS",
            "CARGO_TARGET_DIR",
            "CARGO_BUILD_TARGET",
            "CARGO_PROFILE_DEV_OPT_LEVEL",
            CARGO_BUILD_JOBS_ENV,
            OOM_GUARD_PARENT_LEASE_ENV,
            NBCORE_ENV,
        ] {
            assert!(
                !environment.contains_key(OsStr::new(removed)),
                "ambient override {removed} must not reach nested Cargo"
            );
        }
    }

    #[test]
    fn ignored_cargo_config_cannot_supply_a_compiler_wrapper() {
        let repository = empty_repository();
        std::fs::write(
            repository.path().join(".gitignore"),
            b".cargo/config.toml\n",
        )
        .expect("write ignore fixture");
        std::fs::write(repository.path().join("Cargo.toml"), b"[workspace]\n")
            .expect("write workspace fixture");
        run_git(repository.path(), &["add", ".gitignore", "Cargo.toml"]);
        run_git(repository.path(), &["commit", "--quiet", "-m", "fixture"]);
        std::fs::create_dir(repository.path().join(".cargo"))
            .expect("create ignored Cargo config directory");
        std::fs::write(
            repository.path().join(".cargo/config.toml"),
            b"[build]\nrustc-wrapper = 'fake-wrapper'\n",
        )
        .expect("write ignored Cargo config");
        let cargo_home = tempfile::tempdir().expect("temporary Cargo home");

        assert!(
            std::panic::catch_unwind(|| {
                cargo_configuration_identity(repository.path(), cargo_home.path())
            })
            .is_err(),
            "an ignored config must not inject a wrapper outside source identity"
        );
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_cargo_directory_cannot_supply_a_compiler_wrapper() {
        use std::os::unix::fs::symlink;

        let repository = empty_repository();
        std::fs::write(repository.path().join("Cargo.toml"), b"[workspace]\n")
            .expect("write workspace fixture");
        run_git(repository.path(), &["add", "Cargo.toml"]);
        run_git(repository.path(), &["commit", "--quiet", "-m", "fixture"]);

        let external = tempfile::tempdir().expect("external Cargo config directory");
        std::fs::write(
            external.path().join("config.toml"),
            b"[build]\nrustc-wrapper = 'fake-wrapper'\n",
        )
        .expect("write external Cargo config");
        symlink(external.path(), repository.path().join(".cargo"))
            .expect("symlink workspace Cargo config directory");
        let cargo_home = tempfile::tempdir().expect("temporary Cargo home");

        assert!(
            std::panic::catch_unwind(|| {
                cargo_configuration_identity(repository.path(), cargo_home.path())
            })
            .is_err(),
            "a config reached through a symlinked parent must not enter the source trust boundary"
        );
    }

    #[test]
    fn external_cargo_config_content_changes_build_identity() {
        let repository = empty_repository();
        std::fs::write(repository.path().join("Cargo.toml"), b"[workspace]\n")
            .expect("write workspace fixture");
        run_git(repository.path(), &["add", "Cargo.toml"]);
        run_git(repository.path(), &["commit", "--quiet", "-m", "fixture"]);
        let cargo_home = tempfile::tempdir().expect("temporary Cargo home");
        let config = cargo_home.path().join("config.toml");
        std::fs::write(&config, b"[net]\noffline = true\n").expect("write external Cargo config");
        let first = cargo_configuration_identity(repository.path(), cargo_home.path());
        std::fs::write(&config, b"[net]\noffline = false\n").expect("change external Cargo config");
        let second = cargo_configuration_identity(repository.path(), cargo_home.path());
        assert_ne!(
            first, second,
            "every external Cargo config byte must bind the build target"
        );
    }

    #[test]
    fn tool_binary_content_changes_build_identity() {
        let directory = tempfile::tempdir().expect("temporary tool directory");
        let tool = directory.path().join("cargo");
        std::fs::write(&tool, b"first tool bytes\n").expect("write tool fixture");
        let mut first = Sha256::new();
        hash_component(&mut first, b"schema", b"tool-test");
        hash_file_input(&mut first, b"cargo", &tool);
        let first = finish_build_identity(first);

        std::fs::write(&tool, b"second tool bytes\n").expect("change tool fixture");
        let mut second = Sha256::new();
        hash_component(&mut second, b"schema", b"tool-test");
        hash_file_input(&mut second, b"cargo", &tool);
        let second = finish_build_identity(second);

        assert_ne!(
            first, second,
            "compiler and Cargo bytes must bind the build target"
        );
    }

    #[cfg(unix)]
    #[test]
    fn path_selected_git_is_resolved_and_bound_by_content() {
        use std::os::unix::fs::PermissionsExt as _;

        let repository = empty_repository();
        let directory = tempfile::tempdir().expect("temporary Git tool directory");
        let git = directory.path().join("git");
        std::fs::write(&git, b"#!/bin/sh\necho 'git version fake-one'\n")
            .expect("write fake Git fixture");
        let mut permissions = std::fs::metadata(&git)
            .expect("fake Git metadata")
            .permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&git, permissions).expect("make fake Git executable");

        let path = std::env::join_paths([directory.path()]).expect("fake Git PATH");
        let resolved = resolve_program(OsStr::new("git"), Some(&path));
        assert!(resolved.is_absolute(), "Git must be resolved before use");
        let environment = git_environment();
        let first = git_tool_identity(&resolved, &environment, repository.path());

        std::fs::write(&git, b"#!/bin/sh\necho 'git version fake-two'\n")
            .expect("change fake Git fixture");
        let second = git_tool_identity(&resolved, &environment, repository.path());
        assert_ne!(
            first, second,
            "a PATH-selected Git executable must be part of source provenance"
        );
        for removed in ["GIT_DIR", "GIT_INDEX_FILE", "GIT_WORK_TREE", "HOME"] {
            assert!(
                !environment.contains_key(OsStr::new(removed)),
                "ambient Git override {removed} must not reach source discovery"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn program_resolution_preserves_rustup_style_proxy_basename() {
        use std::os::unix::fs::symlink;

        let directory = tempfile::tempdir().expect("temporary proxy directory");
        let dispatcher = directory.path().join("dispatcher");
        std::fs::write(&dispatcher, b"dispatcher bytes\n").expect("write dispatcher fixture");
        symlink("dispatcher", directory.path().join("rustc"))
            .expect("create rustc-style proxy symlink");
        let path = std::env::join_paths([directory.path()]).expect("proxy PATH");

        let resolved = resolve_program(OsStr::new("rustc"), Some(&path));
        assert_eq!(resolved.file_name(), Some(OsStr::new("rustc")));
        assert!(
            std::fs::symlink_metadata(&resolved)
                .expect("resolved proxy metadata")
                .file_type()
                .is_symlink(),
            "final symlink must be preserved so dispatchers see argv[0]=rustc"
        );
    }

    fn repository_with_gitlink(create_worktree_directory: bool) -> tempfile::TempDir {
        let repository = empty_repository();
        std::fs::write(repository.path().join("root.txt"), b"root\n")
            .expect("write superproject fixture");
        run_git(repository.path(), &["add", "root.txt"]);
        run_git(
            repository.path(),
            &["commit", "--quiet", "-m", "superproject fixture"],
        );
        let git = GitContext::resolve(repository.path());
        let head = String::from_utf8(git_output_with(
            &git,
            repository.path(),
            &["rev-parse", "--verify", "HEAD"],
        ))
        .expect("fixture HEAD should be UTF-8");
        git.assert_unchanged(repository.path());
        run_git(
            repository.path(),
            &[
                "update-index",
                "--add",
                "--cacheinfo",
                "160000",
                head.trim_end(),
                "nested",
            ],
        );
        if create_worktree_directory {
            std::fs::create_dir(repository.path().join("nested"))
                .expect("create misdirected gitlink directory");
        }
        repository
    }

    #[test]
    fn source_identity_rejects_uninitialized_gitlink() {
        let repository = repository_with_gitlink(false);
        assert!(
            std::panic::catch_unwind(|| workspace_source_identity(repository.path())).is_err(),
            "missing gitlink worktree must fail closed"
        );
    }

    #[test]
    fn source_identity_rejects_gitlink_that_discovers_superproject() {
        let repository = repository_with_gitlink(true);
        assert!(
            std::panic::catch_unwind(|| workspace_source_identity(repository.path())).is_err(),
            "gitlink directory without its own repository must not inherit the superproject"
        );
    }

    #[cfg(unix)]
    #[test]
    fn source_identity_binds_tracked_executable_mode() {
        use std::os::unix::fs::PermissionsExt as _;

        let repository = empty_repository();
        let tracked = repository.path().join("script.sh");
        std::fs::write(&tracked, b"#!/bin/sh\nexit 0\n").expect("write tracked script");
        run_git(repository.path(), &["add", "script.sh"]);
        run_git(repository.path(), &["commit", "--quiet", "-m", "fixture"]);

        let original = workspace_source_identity(repository.path());
        let mut permissions = std::fs::metadata(&tracked)
            .expect("tracked script metadata")
            .permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&tracked, permissions).expect("make tracked script executable");
        let executable = workspace_source_identity(repository.path());
        assert_ne!(executable, original, "tracked mode must affect identity");
    }

    #[cfg(unix)]
    #[test]
    fn source_identity_binds_tracked_symlink_target() {
        use std::os::unix::fs::symlink;

        let repository = empty_repository();
        std::fs::write(repository.path().join("target-a"), b"same\n").expect("write target-a");
        std::fs::write(repository.path().join("target-b"), b"same\n").expect("write target-b");
        let link = repository.path().join("tracked-link");
        symlink("target-a", &link).expect("create tracked symlink");
        run_git(
            repository.path(),
            &["add", "target-a", "target-b", "tracked-link"],
        );
        run_git(repository.path(), &["commit", "--quiet", "-m", "fixture"]);

        let original = workspace_source_identity(repository.path());
        std::fs::remove_file(&link).expect("remove tracked symlink");
        symlink("target-b", &link).expect("retarget tracked symlink");
        let retargeted = workspace_source_identity(repository.path());
        assert_ne!(
            retargeted, original,
            "tracked symlink target must affect identity"
        );
    }

    #[cfg(unix)]
    #[test]
    fn source_snapshot_is_exact_frozen_content_addressed_and_mode_preserving() {
        use std::os::unix::fs::PermissionsExt as _;

        let repository = empty_repository();
        let script = repository.path().join("script.sh");
        std::fs::write(&script, b"#!/bin/sh\nexit 0\n").expect("write script fixture");
        let mut permissions = std::fs::metadata(&script).unwrap().permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&script, permissions).unwrap();
        std::fs::write(repository.path().join("Cargo.toml"), b"[workspace]\n")
            .expect("write workspace fixture");
        run_git(repository.path(), &["add", "script.sh", "Cargo.toml"]);
        run_git(repository.path(), &["commit", "--quiet", "-m", "fixture"]);
        std::fs::write(
            repository.path().join("untracked.txt"),
            b"untracked exact bytes\n",
        )
        .expect("write untracked fixture");

        let first = create_workspace_source_snapshot(repository.path());
        assert!(!first.root.starts_with(repository.path()));
        assert_eq!(
            std::fs::read(first.root.join("untracked.txt")).unwrap(),
            b"untracked exact bytes\n"
        );
        let snapshot_mode = std::fs::metadata(first.root.join("script.sh"))
            .unwrap()
            .permissions()
            .mode();
        assert_ne!(snapshot_mode & 0o111, 0, "executable bits must survive");
        assert_eq!(snapshot_mode & 0o222, 0, "snapshot must be read-only");

        let reused = create_workspace_source_snapshot(repository.path());
        assert_eq!(reused, first, "identical source must reuse exact snapshot");

        std::fs::write(
            repository.path().join("untracked.txt"),
            b"changed exact bytes\n",
        )
        .expect("change untracked fixture");
        let changed = create_workspace_source_snapshot(repository.path());
        assert_ne!(changed.source_identity, first.source_identity);
        assert_ne!(changed.root, first.root);
    }

    #[test]
    fn source_snapshot_binds_head_even_when_tree_bytes_are_unchanged() {
        let repository = empty_repository();
        std::fs::write(repository.path().join("Cargo.toml"), b"[workspace]\n")
            .expect("write workspace fixture");
        run_git(repository.path(), &["add", "Cargo.toml"]);
        run_git(repository.path(), &["commit", "--quiet", "-m", "fixture"]);
        let first = create_workspace_source_snapshot(repository.path());
        run_git(
            repository.path(),
            &["commit", "--quiet", "--allow-empty", "-m", "new head"],
        );
        let second = create_workspace_source_snapshot(repository.path());
        assert_eq!(first.manifest_identity, second.manifest_identity);
        assert_ne!(first.source_identity, second.source_identity);
    }

    fn snapshot_generation_repository() -> tempfile::TempDir {
        let repository = empty_repository();
        std::fs::write(repository.path().join("Cargo.toml"), b"[workspace]\n")
            .expect("write tracked workspace fixture");
        run_git(repository.path(), &["add", "Cargo.toml"]);
        run_git(repository.path(), &["commit", "--quiet", "-m", "fixture"]);
        repository
    }

    fn assert_snapshot_staging_was_cleaned(repository: &Path) {
        let workspace = repository.canonicalize().unwrap();
        let store = source_snapshot_store(&workspace);
        let staging = filesystem::read_dir(store)
            .unwrap()
            .filter_map(Result::ok)
            .map(|entry| entry.file_name())
            .filter(|name| name.to_string_lossy().starts_with(".staging-"))
            .collect::<Vec<_>>();
        assert!(
            staging.is_empty(),
            "failed snapshot captures must clean staging trees: {staging:?}"
        );
    }

    #[test]
    fn source_snapshot_rejects_tracked_change_during_capture() {
        let repository = snapshot_generation_repository();
        let tracked = repository.path().join("Cargo.toml");
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            create_workspace_source_snapshot_with_hook(repository.path(), || {
                std::fs::write(&tracked, b"[workspace]\n# changed during capture\n")
                    .expect("mutate tracked fixture during capture");
            })
        }));
        assert!(
            result.is_err(),
            "a tracked source generation change must abort snapshot publication"
        );
        assert_snapshot_staging_was_cleaned(repository.path());
    }

    #[test]
    fn source_snapshot_rejects_untracked_change_during_capture() {
        let repository = snapshot_generation_repository();
        let untracked = repository.path().join("appeared-during-capture.txt");
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            create_workspace_source_snapshot_with_hook(repository.path(), || {
                std::fs::write(&untracked, b"new untracked source\n")
                    .expect("create untracked fixture during capture");
            })
        }));
        assert!(
            result.is_err(),
            "an untracked source generation change must abort snapshot publication"
        );
        assert_snapshot_staging_was_cleaned(repository.path());
    }

    #[cfg(unix)]
    #[test]
    fn source_snapshot_rejects_outward_symlinks() {
        use std::os::unix::fs::symlink;

        let repository = empty_repository();
        std::fs::write(repository.path().join("Cargo.toml"), b"[workspace]\n")
            .expect("write workspace fixture");
        symlink("../../outside", repository.path().join("escape"))
            .expect("create escaping source link");
        run_git(repository.path(), &["add", "Cargo.toml", "escape"]);
        run_git(repository.path(), &["commit", "--quiet", "-m", "fixture"]);
        assert!(
            std::panic::catch_unwind(|| create_workspace_source_snapshot(repository.path()))
                .is_err(),
            "a snapshot must never preserve a source link escaping its boundary"
        );
    }

    #[cfg(unix)]
    #[test]
    fn preexisting_snapshot_is_reverified_and_tampering_fails_closed() {
        use std::os::unix::fs::PermissionsExt as _;

        let repository = empty_repository();
        std::fs::write(repository.path().join("Cargo.toml"), b"[workspace]\n")
            .expect("write workspace fixture");
        run_git(repository.path(), &["add", "Cargo.toml"]);
        run_git(repository.path(), &["commit", "--quiet", "-m", "fixture"]);
        let snapshot = create_workspace_source_snapshot(repository.path());
        let file = snapshot.root.join("Cargo.toml");
        let mut permissions = std::fs::metadata(&file).unwrap().permissions();
        permissions.set_mode(0o644);
        std::fs::set_permissions(&file, permissions).unwrap();
        std::fs::write(&file, b"[workspace]\n# tampered\n").unwrap();
        assert!(
            std::panic::catch_unwind(|| create_workspace_source_snapshot(repository.path()))
                .is_err(),
            "a preexisting content-addressed tree must be fully reverified"
        );
    }

    #[test]
    fn normalized_path_rejects_relative_and_empty_components() {
        let relative = std::env::join_paths([Path::new("relative")]).unwrap();
        assert!(std::panic::catch_unwind(|| normalized_absolute_path(Some(&relative))).is_err());
        let empty = OsString::from(if cfg!(windows) { ";" } else { ":" });
        assert!(std::panic::catch_unwind(|| normalized_absolute_path(Some(&empty))).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn command_revalidates_exact_provenance_and_artifact_bytes() {
        use std::os::unix::fs::PermissionsExt as _;

        let directory = tempfile::tempdir().expect("temporary exact binary directory");
        let artifact = directory.path().join("exact-binary");
        let source = "source-sha256-test";
        let build = "build-sha256-test";
        let expected = expected_exact_provenance(source, build);
        std::fs::write(
            &artifact,
            format!(
                "#!/bin/sh\nprintf '%b' '{}'\n",
                expected.replace('\n', "\\n")
            ),
        )
        .unwrap();
        let mut permissions = std::fs::metadata(&artifact).unwrap().permissions();
        permissions.set_mode(0o555);
        std::fs::set_permissions(&artifact, permissions).unwrap();
        let built = BuiltWorkspaceBinary {
            artifact_identity: frozen_artifact_identity(&artifact),
            artifact_path: artifact.clone(),
            execution_environment: BTreeMap::new(),
            source_binding: SourceBinding::ExactProvenance,
            source_identity: source.to_owned(),
            build_identity: build.to_owned(),
            target_dir: directory.path().join("target"),
            snapshot_dir: directory.path().join("snapshot"),
        };
        assert!(built
            .command()
            .arg("ignored")
            .output()
            .unwrap()
            .status
            .success());

        let mut permissions = std::fs::metadata(&artifact).unwrap().permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&artifact, permissions).unwrap();
        std::fs::write(&artifact, b"#!/bin/sh\nexit 0\n").unwrap();
        assert!(
            std::panic::catch_unwind(|| drop(built.command())).is_err(),
            "post-return artifact mutation must fail before execution"
        );
    }

    #[test]
    fn cargo_build_runs_from_snapshot_and_returns_only_frozen_command() {
        let repository = empty_repository();
        std::fs::create_dir(repository.path().join("src")).unwrap();
        std::fs::write(
            repository.path().join("Cargo.toml"),
            b"[package]\nname = 'snapshot-fixture'\nversion = '0.1.0'\nedition = '2021'\n",
        )
        .unwrap();
        std::fs::write(
            repository.path().join("Cargo.lock"),
            b"# This file is automatically @generated by Cargo.\n# It is not intended for manual editing.\nversion = 4\n\n[[package]]\nname = \"snapshot-fixture\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        std::fs::write(
            repository.path().join("src/main.rs"),
            b"fn main() { println!(\"snapshot-ok\"); }\n",
        )
        .unwrap();
        std::fs::write(repository.path().join(".gitignore"), b"target/\n").unwrap();
        run_git(repository.path(), &["add", "."]);
        run_git(repository.path(), &["commit", "--quiet", "-m", "fixture"]);

        let spec = WorkspaceBinarySpec {
            workspace: repository.path(),
            target_name: "snapshot-cargo-test",
            package: "snapshot-fixture",
            binary: "snapshot-fixture",
            features: &[],
            source_binding: SourceBinding::IdentityTarget,
        };
        let snapshot = create_workspace_source_snapshot(repository.path());
        std::fs::write(
            repository.path().join("src/main.rs"),
            b"fn main() { println!(\"live-worktree-wrong\"); }\n",
        )
        .expect("mutate live worktree after snapshot capture");
        let built = build_workspace_binary_from_snapshot(
            spec,
            repository.path().canonicalize().unwrap(),
            snapshot.clone(),
        );
        assert_eq!(built.source_identity, snapshot.source_identity);
        assert!(!built.snapshot_dir.starts_with(repository.path()));
        let output = built.command().output().expect("run frozen fixture");
        assert!(output.status.success());
        assert_eq!(output.stdout, b"snapshot-ok\n");
        assert!(output.stderr.is_empty());
    }
}
