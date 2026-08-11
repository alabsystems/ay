// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Faithful, per-check DIMACS export for bit-vector certificate consumers.
//!
//! A dump is a certificate input, not a best-effort debug trace.  Every
//! top-level `check-sat` owns a serialized export transaction, clears the
//! preceding artifact, and accepts only a file installed by that transaction's
//! canonical writer.  Nested checks run normally but cannot clear or overwrite
//! their owner's artifact.  Missing, stale, concurrent, or unwritable output is
//! an execution error, so no verdict can authorize the wrong certificate input.

use std::cell::{Cell, RefCell};
use std::fs::{File, Metadata, OpenOptions};
use std::io::{self, BufWriter, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, MutexGuard, TryLockError};

use ay_core::{CnfClause, TermId, TermStore};
use ay_sat::Literal as SatLiteral;
use sha2::{Digest, Sha256};

use crate::executor_types::{ExecutorError, Result};

static BV_CNF_DUMP_FILE_ID: AtomicU64 = AtomicU64::new(0);
static BV_CNF_DUMP_GENERATION: AtomicU64 = AtomicU64::new(1);

fn reserve_generation(counter: &AtomicU64) -> Option<u64> {
    let mut generation = counter.load(Ordering::Relaxed);
    loop {
        let next = generation.checked_add(1)?;
        match counter.compare_exchange_weak(generation, next, Ordering::Relaxed, Ordering::Relaxed)
        {
            Ok(_) => return Some(generation),
            Err(observed) => generation = observed,
        }
    }
}
static BV_CNF_DUMP_LOCK: Mutex<()> = Mutex::new(());

#[derive(Default)]
struct ThreadTransactionState {
    depth: usize,
    suppression_depth: usize,
    generation: u64,
    cnf_path: Option<String>,
    drat_path: Option<String>,
    written_artifact: Option<(u64, ArtifactSeal)>,
    drat_artifact: Option<DratArtifactState>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ArtifactSeal {
    identity: FileIdentity,
    len: u64,
    sha256: [u8; 32],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FileIdentity {
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
    #[cfg(windows)]
    volume: u32,
    #[cfg(windows)]
    index: u64,
}

#[derive(Clone, Copy, Debug)]
struct DratArtifactState {
    generation: u64,
    identity: FileIdentity,
    seal: Option<ArtifactSeal>,
}

/// Open descriptor retained independently of the SAT proof writer so the
/// completed DRAT can be synced and authenticated without reopening a
/// potentially replaced destination.
pub(in crate::executor) struct BvDratArtifact {
    path: PathBuf,
    file: File,
    identity: FileIdentity,
    generation: u64,
}

thread_local! {
    static THREAD_TRANSACTION: RefCell<ThreadTransactionState> =
        RefCell::new(ThreadTransactionState::default());
    /// Whether the `--self-check` BV DRAT self-cert temp paths are live for the
    /// current solve on this thread. Set only around an eligible top-level
    /// pure-QF_BV `(check-sat)` (see `Executor::maybe_arm_bv_drat_self_cert`).
    /// When false, [`configured_path`]/[`configured_drat_path`] never expose the
    /// self-cert temp files, so no user-facing `--dump-bv-cnf` machinery and no
    /// non-BV / probe / optimization path can ever see them.
    static SELF_CERT_ARMED: Cell<bool> = const { Cell::new(false) };
}

/// RAII guard that disarms the self-cert export on drop, restoring the previous
/// state (so a nested arm never clears an outer one).
pub(in crate::executor) struct SelfCertArm {
    prev: bool,
}

impl Drop for SelfCertArm {
    fn drop(&mut self) {
        SELF_CERT_ARMED.with(|armed| armed.set(self.prev));
    }
}

/// Arm the `--self-check` BV DRAT self-cert export for the current solve scope.
pub(in crate::executor) fn arm_self_cert() -> SelfCertArm {
    let prev = SELF_CERT_ARMED.with(|armed| armed.replace(true));
    SelfCertArm { prev }
}

/// Whether the self-cert export is armed on this thread.
pub(in crate::executor) fn self_cert_armed() -> bool {
    SELF_CERT_ARMED.with(Cell::get)
}

/// How a checked artifact can be reached for platform identity queries.
///
/// Windows exposes neither the file identity nor the hard-link count through
/// `Metadata` on stable (the accessors sit behind the perpetually unstable
/// `windows_by_handle` feature, rust-lang/rust#63010), so the source is threaded
/// through to `GetFileInformationByHandle` instead of read off the metadata.
#[derive(Clone, Copy)]
#[cfg_attr(not(windows), allow(dead_code))]
enum ArtifactFileRef<'a> {
    Handle(&'a File),
    Path(&'a Path),
}

#[cfg(windows)]
impl ArtifactFileRef<'_> {
    fn windows_info(self) -> io::Result<ay_sys::windows_fs::WindowsFileInfo> {
        match self {
            Self::Handle(file) => ay_sys::windows_fs::file_info(file),
            Self::Path(path) => ay_sys::windows_fs::file_info_no_follow(path),
        }
    }
}

fn validate_regular_artifact_metadata(
    metadata: &Metadata,
    source: ArtifactFileRef<'_>,
) -> io::Result<()> {
    if !metadata.file_type().is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "artifact path is not a regular file",
        ));
    }
    #[cfg(unix)]
    {
        let _ = source;
        use std::os::unix::fs::MetadataExt;
        if metadata.nlink() != 1 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "artifact file has multiple hard links",
            ));
        }
    }
    #[cfg(windows)]
    {
        if metadata.file_type().is_symlink() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "artifact path is a symbolic link",
            ));
        }
        if source.windows_info()?.number_of_links != 1 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "artifact file has multiple hard links",
            ));
        }
    }
    #[cfg(not(any(unix, windows)))]
    {
        let _ = source;
    }
    Ok(())
}

#[cfg(unix)]
fn file_identity(metadata: &Metadata, source: ArtifactFileRef<'_>) -> io::Result<FileIdentity> {
    let _ = source;
    use std::os::unix::fs::MetadataExt;
    Ok(FileIdentity {
        device: metadata.dev(),
        inode: metadata.ino(),
    })
}

#[cfg(windows)]
fn file_identity(metadata: &Metadata, source: ArtifactFileRef<'_>) -> io::Result<FileIdentity> {
    let _ = metadata;
    let info = source.windows_info()?;
    Ok(FileIdentity {
        volume: info.volume_serial_number,
        index: info.file_index,
    })
}

#[cfg(not(any(unix, windows)))]
fn file_identity(_metadata: &Metadata, _source: ArtifactFileRef<'_>) -> io::Result<FileIdentity> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "artifact identity checks are unsupported on this platform",
    ))
}

fn configure_no_follow(options: &mut OpenOptions) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    #[cfg(windows)]
    {
        use std::os::windows::fs::OpenOptionsExt;
        const FILE_FLAG_OPEN_REPARSE_POINT: u32 = 0x0020_0000;
        options.custom_flags(FILE_FLAG_OPEN_REPARSE_POINT);
    }
}

fn reject_unsafe_artifact_leaf(path: &Path, allow_missing: bool) -> io::Result<()> {
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_symlink() => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "artifact path is a symbolic link",
        )),
        Ok(metadata) if !metadata.file_type().is_file() => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "artifact path is not a regular file",
        )),
        Ok(metadata) => validate_regular_artifact_metadata(&metadata, ArtifactFileRef::Path(path)),
        Err(error) if allow_missing && error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error),
    }
}

fn open_regular_file_no_follow(path: &Path) -> io::Result<(File, FileIdentity)> {
    reject_unsafe_artifact_leaf(path, false)?;
    let mut options = OpenOptions::new();
    options.read(true);
    configure_no_follow(&mut options);
    let file = options.open(path)?;
    let metadata = file.metadata()?;
    validate_regular_artifact_metadata(&metadata, ArtifactFileRef::Handle(&file))?;
    let identity = file_identity(&metadata, ArtifactFileRef::Handle(&file))?;
    Ok((file, identity))
}

fn create_new_regular_file_no_follow(path: &Path) -> io::Result<(File, FileIdentity)> {
    reject_unsafe_artifact_leaf(path, true)?;
    let mut options = OpenOptions::new();
    options.read(true).write(true).create_new(true);
    configure_no_follow(&mut options);
    let file = options.open(path)?;
    let metadata = file.metadata()?;
    validate_regular_artifact_metadata(&metadata, ArtifactFileRef::Handle(&file))?;
    let identity = file_identity(&metadata, ArtifactFileRef::Handle(&file))?;
    Ok((file, identity))
}

fn path_has_identity(path: &Path, expected: FileIdentity) -> io::Result<bool> {
    match open_regular_file_no_follow(path) {
        Ok((_file, actual)) => Ok(actual == expected),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error),
    }
}

/// Identity check used only while unwinding the brief two-link state created
/// by no-replace CNF publication. It still rejects symlinks/non-regular files,
/// but permits the exact retained inode to have both temporary and final names.
fn path_has_identity_allow_multiple_links(path: &Path, expected: FileIdentity) -> io::Result<bool> {
    match std::fs::symlink_metadata(path) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(false),
        Err(error) => return Err(error),
        Ok(metadata) if metadata.file_type().is_symlink() => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "artifact cleanup path is a symbolic link",
            ));
        }
        Ok(metadata) if !metadata.file_type().is_file() => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "artifact cleanup path is not a regular file",
            ));
        }
        Ok(_) => {}
    }
    let mut options = OpenOptions::new();
    options.read(true);
    configure_no_follow(&mut options);
    let file = options.open(path)?;
    let metadata = file.metadata()?;
    if !metadata.file_type().is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "opened artifact cleanup path is not a regular file",
        ));
    }
    Ok(file_identity(&metadata, ArtifactFileRef::Handle(&file))? == expected)
}

fn remove_file_link_if_owned(path: &Path, expected: FileIdentity) -> io::Result<bool> {
    if path_has_identity_allow_multiple_links(path, expected)? {
        std::fs::remove_file(path)?;
        Ok(true)
    } else {
        Ok(false)
    }
}

fn remove_file_if_owned(path: &Path, expected: FileIdentity) -> io::Result<bool> {
    if path_has_identity(path, expected)? {
        std::fs::remove_file(path)?;
        Ok(true)
    } else {
        Ok(false)
    }
}

fn clear_stale_artifact(path: &Path) -> io::Result<()> {
    clear_stale_artifact_with_hook(path, || {})
}

fn clear_stale_artifact_with_hook(path: &Path, before_remove: impl FnOnce()) -> io::Result<()> {
    let (_retained, identity) = match open_regular_file_no_follow(path) {
        Ok(opened) => opened,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
    };
    before_remove();
    if remove_file_if_owned(path, identity)? {
        Ok(())
    } else {
        Err(io::Error::other(
            "artifact destination was replaced before stale-file cleanup",
        ))
    }
}

fn sync_parent_directory(path: &Path) -> io::Result<()> {
    #[cfg(unix)]
    {
        let parent = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        File::open(parent)?.sync_all()?;
    }
    Ok(())
}

/// Scoped suppression for semantic validation re-solves that are subordinate
/// to an already-completed user decision.
///
/// This is thread-local deliberately: suppressing one thread must never allow
/// an independent concurrent caller to return a verdict without its requested
/// artifact.
pub(in crate::executor) struct InternalExportSuppression;

impl Drop for InternalExportSuppression {
    fn drop(&mut self) {
        THREAD_TRANSACTION.with(|state| {
            let mut state = state.borrow_mut();
            state.suppression_depth = state
                .suppression_depth
                .checked_sub(1)
                .expect("BV CNF export suppression depth underflow");
        });
    }
}

/// Disable BV CNF export for nested semantic validation on this thread.
pub(in crate::executor) fn suppress_internal_export() -> InternalExportSuppression {
    THREAD_TRANSACTION.with(|state| {
        let mut state = state.borrow_mut();
        state.suppression_depth = state
            .suppression_depth
            .checked_add(1)
            .expect("BV CNF export suppression depth overflow");
    });
    InternalExportSuppression
}

/// RAII ownership of one check's export transaction.
///
/// An unfinished top-level transaction removes its CNF and DRAT destinations
/// on drop. This also covers solver errors and unwinding panics after a partial
/// solve.
pub(in crate::executor) struct CheckTransaction {
    active: bool,
    owner: bool,
    generation: u64,
    completed: bool,
    cnf_path: Option<PathBuf>,
    drat_path: Option<PathBuf>,
    _cross_process_locks: Vec<CrossProcessLock>,
    _process_lock: Option<MutexGuard<'static, ()>>,
}

impl CheckTransaction {
    fn disabled() -> Self {
        Self {
            active: false,
            owner: false,
            generation: 0,
            completed: true,
            cnf_path: None,
            drat_path: None,
            _cross_process_locks: Vec::new(),
            _process_lock: None,
        }
    }
}

struct CrossProcessLock {
    _path: PathBuf,
    _file: File,
}

impl Drop for CrossProcessLock {
    fn drop(&mut self) {
        // Release eagerly instead of relying only on descriptor close. This is
        // observably important to a same-process successor on platforms where
        // an immediately preceding failed nonblocking acquisition can delay
        // close-based lock release.
        let _ = self._file.unlock();
    }
}

/// Resolve the parent directory once and retain the resulting physical target
/// for the entire export transaction. All later cleanup, create, rename, seal,
/// and lock operations use this path, so swapping a symlink in the caller's
/// lexical parent cannot redirect only part of a CNF/DRAT transaction.
fn resolve_export_target(path: &str) -> Result<PathBuf> {
    let target = Path::new(path);
    let file_name = target.file_name().ok_or_else(|| {
        ExecutorError::ArtifactExport(format!("BV CNF dump path '{path}' has no file name"))
    })?;
    reject_unsafe_artifact_leaf(target, true)
        .map_err(|error| export_error(path, "validate export destination for", error))?;
    let parent = target
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let canonical_parent = std::fs::canonicalize(parent)
        .map_err(|error| export_error(path, "resolve physical parent directory for", error))?;
    let resolved = canonical_parent.join(file_name);
    reject_unsafe_artifact_leaf(&resolved, true)
        .map_err(|error| export_error(path, "validate resolved export destination for", error))?;
    Ok(resolved)
}

fn resolved_target_string(path: &str) -> Result<String> {
    resolve_export_target(path)?
        .into_os_string()
        .into_string()
        .map_err(|path| {
            ExecutorError::ArtifactExport(format!(
                "resolved BV export target '{}' is not valid UTF-8",
                PathBuf::from(path).display()
            ))
        })
}

fn lock_path_for_resolved_target(target: &Path) -> Result<PathBuf> {
    let file_name = target.file_name().ok_or_else(|| {
        ExecutorError::ArtifactExport(format!(
            "resolved BV export path '{}' has no file name",
            target.display()
        ))
    })?;
    let parent = target.parent().ok_or_else(|| {
        ExecutorError::ArtifactExport(format!(
            "resolved BV export path '{}' has no parent",
            target.display()
        ))
    })?;
    Ok(parent.join(format!(".{}.ay-bv-cnf.lock", file_name.to_string_lossy())))
}

fn cross_process_lock_path(path: &str) -> Result<PathBuf> {
    lock_path_for_resolved_target(&resolve_export_target(path)?)
}

#[cfg(test)]
fn acquire_cross_process_lock(path: &str, generation: u64) -> Result<CrossProcessLock> {
    let lock_path = cross_process_lock_path(path)?;
    acquire_cross_process_lock_at(path, lock_path, generation)
}

fn acquire_cross_process_lock_at(
    path: &str,
    lock_path: PathBuf,
    generation: u64,
) -> Result<CrossProcessLock> {
    let mut file = open_coordination_file_no_follow(&lock_path).map_err(|error| {
        export_error(
            path,
            "acquire cross-process export lock for",
            format!("{}: {error}", lock_path.display()),
        )
    })?;
    file.try_lock().map_err(|error| {
        export_error(
            path,
            "acquire cross-process export lock for",
            format!("{}: {error}", lock_path.display()),
        )
    })?;
    file.set_len(0)
        .and_then(|()| writeln!(file, "pid={} generation={generation}", std::process::id()))
        .and_then(|()| file.sync_all())
        .map_err(|error| export_error(path, "initialize cross-process export lock for", error))?;
    Ok(CrossProcessLock {
        _path: lock_path,
        _file: file,
    })
}

/// Open the persistent coordination file without following a final-component
/// symlink. The generation stamp is rewritten only after the OS lock is held,
/// so following an attacker- or accident-created symlink here would otherwise
/// truncate an unrelated referent in `set_len(0)`.
fn open_coordination_file_no_follow(path: &Path) -> io::Result<File> {
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_symlink() => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "coordination path is a symbolic link",
            ));
        }
        Ok(metadata) if !metadata.file_type().is_file() => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "coordination path is not a regular file",
            ));
        }
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }

    let mut options = OpenOptions::new();
    options
        .read(true)
        .write(true)
        .create(true)
        // Existing contents (a stale generation stamp) must survive until the
        // lock is held, so explicitly do not truncate during open.
        .truncate(false);

    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        // O_NONBLOCK also prevents a final-component FIFO introduced between
        // the metadata check and open from hanging this diagnostic path. The
        // opened descriptor is type-checked below before any lock/write.
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    #[cfg(windows)]
    {
        use std::os::windows::fs::OpenOptionsExt;
        // FILE_FLAG_OPEN_REPARSE_POINT: open the link itself so it can be
        // inspected and rejected instead of following it to a referent.
        const FILE_FLAG_OPEN_REPARSE_POINT: u32 = 0x0020_0000;
        options.custom_flags(FILE_FLAG_OPEN_REPARSE_POINT);
    }
    #[cfg(not(any(unix, windows)))]
    if std::fs::symlink_metadata(path).is_ok_and(|meta| meta.file_type().is_symlink()) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "coordination path is a symbolic link",
        ));
    }

    let file = options.open(path)?;

    let metadata = file.metadata()?;
    if !metadata.file_type().is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "opened coordination path is not a regular file",
        ));
    }

    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if metadata.nlink() != 1 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "coordination file has multiple hard links",
            ));
        }
    }

    #[cfg(windows)]
    if metadata.file_type().is_symlink() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "coordination path is a symbolic link",
        ));
    }
    #[cfg(not(any(unix, windows)))]
    if std::fs::symlink_metadata(path).is_ok_and(|meta| meta.file_type().is_symlink()) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "coordination path became a symbolic link while opening",
        ));
    }

    Ok(file)
}

/// Acquire every destination lock for one CNF/DRAT transaction.
///
/// The DRAT is a first-class certificate output, so serializing only the CNF
/// destination would still allow two processes with different CNF paths and a
/// shared proof path to truncate or remove each other's proof. Sort the derived
/// lock paths before the nonblocking acquisitions so swapped CNF/DRAT targets
/// have one deterministic order. Exact lock-path aliases fail closed instead
/// of attempting to lock the same OS file twice.
fn acquire_transaction_locks(
    cnf_path: &str,
    drat_path: Option<&str>,
    generation: u64,
) -> Result<Vec<CrossProcessLock>> {
    let mut requests = vec![(cnf_path, cross_process_lock_path(cnf_path)?)];
    if let Some(drat_path) = drat_path {
        let drat_lock_path = cross_process_lock_path(drat_path)?;
        if drat_lock_path == requests[0].1 {
            return Err(ExecutorError::ArtifactExport(format!(
                "BV CNF and DRAT destinations resolve to the same coordination lock '{}'",
                drat_lock_path.display()
            )));
        }
        requests.push((drat_path, drat_lock_path));
    }
    requests.sort_unstable_by(|left, right| left.1.cmp(&right.1));

    let mut locks = Vec::with_capacity(requests.len());
    for (target, lock_path) in requests {
        locks.push(acquire_cross_process_lock_at(
            target, lock_path, generation,
        )?);
    }
    Ok(locks)
}

impl Drop for CheckTransaction {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        THREAD_TRANSACTION.with(|state| {
            let mut state = state.borrow_mut();
            debug_assert!(state.depth > 0, "BV CNF transaction depth underflow");
            state.depth = state.depth.saturating_sub(1);
            if self.owner {
                debug_assert_eq!(
                    state.depth, 0,
                    "top-level BV CNF owner dropped while nested"
                );
                debug_assert_eq!(state.generation, self.generation);
                if !self.completed {
                    if let (Some(path), Some((generation, expected_seal))) =
                        (self.cnf_path.as_deref(), state.written_artifact)
                    {
                        if generation == self.generation {
                            let current_is_owned = seal_file(path, Some(expected_seal.len))
                                .is_ok_and(|actual_seal| actual_seal == expected_seal);
                            if current_is_owned {
                                let _ = remove_file_if_owned(path, expected_seal.identity);
                            }
                        }
                    }
                    // The DRAT stream is written directly to its destination,
                    // so any error or unwind before `finish_check` otherwise
                    // leaves a partial proof that can be mistaken for this
                    // transaction's certificate. The owner holds both export
                    // locks until after this cleanup; nested transactions must
                    // never remove their owner's proof.
                    if let (Some(path), Some(drat)) =
                        (self.drat_path.as_deref(), state.drat_artifact)
                    {
                        if drat.generation == self.generation {
                            let _ = remove_file_if_owned(path, drat.identity);
                        }
                    }
                }
                state.generation = 0;
                state.cnf_path = None;
                state.drat_path = None;
                state.written_artifact = None;
                state.drat_artifact = None;
            }
        });
        // `_process_lock` is released after the transaction state is cleared.
    }
}

fn configured_path() -> Option<&'static str> {
    let config = ay_core::trace_config();
    // An explicit user `--dump-bv-cnf` always owns the export. Otherwise, the
    // `--self-check` self-cert temp CNF is exposed ONLY while the self-cert arm
    // is set (an eligible top-level pure-QF_BV check-sat).
    config.dump_bv_cnf_path.as_deref().or_else(|| {
        self_cert_armed()
            .then_some(config.bv_drat_self_cert_cnf_path.as_deref())
            .flatten()
    })
}

/// The configured single-invocation BV DRAT proof path, if any.
fn configured_drat_path() -> Option<&'static str> {
    let config = ay_core::trace_config();
    config.bv_drat_path.as_deref().or_else(|| {
        self_cert_armed()
            .then_some(config.bv_drat_self_cert_drat_path.as_deref())
            .flatten()
    })
}

fn active_cnf_path() -> Result<String> {
    THREAD_TRANSACTION
        .with(|state| {
            let state = state.borrow();
            (state.depth == 1 && state.generation != 0)
                .then(|| state.cnf_path.clone())
                .flatten()
        })
        .ok_or_else(|| {
            ExecutorError::ArtifactExport(
                "BV CNF writer has no resolved top-level transaction target".to_string(),
            )
        })
}

fn active_drat_path() -> Option<String> {
    THREAD_TRANSACTION.with(|state| {
        let state = state.borrow();
        (state.depth == 1 && state.generation != 0)
            .then(|| state.drat_path.clone())
            .flatten()
    })
}

/// Whether a BV CNF artifact was requested for this process.
pub(in crate::executor) fn requested() -> bool {
    configured_path().is_some()
        && THREAD_TRANSACTION.with(|state| state.borrow().suppression_depth == 0)
}

/// Whether the current solve is the top-level owner that may emit the artifact.
///
/// Nested model-completion/cross-check solves intentionally see `false`: their
/// formula is not the user's decision query and must not replace its CNF.
pub(in crate::executor) fn enabled() -> bool {
    requested()
        && THREAD_TRANSACTION.with(|state| {
            let state = state.borrow();
            state.depth == 1 && state.generation != 0
        })
}

/// The DRAT proof target `(path, binary)` for the current top-level BV export,
/// or `None` when no DRAT was requested or this is not the owning check.
///
/// Coupled to the CNF-export owner gate ([`enabled`]): a DRAT is only ever
/// emitted from the same top-level, non-suppressed check that owns the CNF
/// artifact, so a nested model-completion or cross-check solve can never write
/// a proof. `bv_drat_path` is itself only populated by the CLI when
/// `--dump-bv-cnf` is set, so the CNF export's fail-closed pure-QF_BV gate is
/// the single point that keeps a DRAT from being emitted for a non-bit-blastable
/// logic.
pub(in crate::executor) fn bv_drat_target() -> Option<(String, bool)> {
    if !enabled() {
        return None;
    }
    // origin's refactor reads the resolved, in-transaction DRAT target rather
    // than the raw config path. The `--self-check` self-cert path still flows
    // here: when the self-cert arm is set, `prepare_for_check` resolves the
    // self-cert DRAT via `configured_drat_path()` and stores it in the
    // transaction state, so `active_drat_path()` returns it for this check. The
    // self-cert DRAT is text (`bv_drat_binary` is unset absent an explicit user
    // `--proof X.drat`), which is what AY's native checker consumes.
    let config = ay_core::trace_config();
    active_drat_path().map(|path| (path, config.bv_drat_binary))
}

/// Write the empty-clause DRAT record for a trivial-false conjunction.
///
/// The companion CNF is the bare empty clause (`p cnf 0 1` / `0`), which is
/// already UNSAT; an explicit text `0` line or binary `a\0` record makes the
/// empty-clause derivation explicit so drat-trim reports `s VERIFIED`.
fn install_trivial_false_drat(drat_path: &str, binary: bool) -> Result<()> {
    let (mut file, artifact) = create_bv_drat(drat_path)?;
    let result = (|| {
        // Binary DRAT records start with an addition marker and terminate the
        // literal sequence with zero. Therefore the empty addition is exactly
        // `a\0`; text DRAT spells the same clause as `0\n`.
        file.write_all(if binary { b"a\0" } else { b"0\n" })?;
        file.flush()?;
        drop(file);
        finalize_drat_artifact(artifact)
            .map(|_| ())
            .map_err(|error| io::Error::other(format!("finalize trivial-false DRAT: {error}")))
    })();
    if let Err(error) = result {
        return Err(export_error(
            drat_path,
            "write trivial-false DRAT for",
            error,
        ));
    }
    Ok(())
}

/// Create the current transaction's DRAT destination without following or
/// truncating a path planted after the transaction's stale-file cleanup.
/// `create_new` turns that clear/create window into a fail-closed error.
pub(in crate::executor) fn create_bv_drat(path: &str) -> Result<(File, BvDratArtifact)> {
    let generation = current_generation()?;
    let target = PathBuf::from(path);
    let (writer_file, identity) = create_new_regular_file_no_follow(&target)
        .map_err(|error| export_error(path, "create DRAT output for", error))?;
    let retained = writer_file.try_clone().map_err(|error| {
        let _ = remove_file_if_owned(&target, identity);
        export_error(path, "retain DRAT descriptor for", error)
    })?;
    THREAD_TRANSACTION.with(|state| {
        let mut state = state.borrow_mut();
        debug_assert_eq!(state.generation, generation);
        debug_assert_eq!(state.depth, 1);
        state.drat_artifact = Some(DratArtifactState {
            generation,
            identity,
            seal: None,
        });
    });
    Ok((
        writer_file,
        BvDratArtifact {
            path: target,
            file: retained,
            identity,
            generation,
        },
    ))
}

fn finalize_drat_artifact(mut artifact: BvDratArtifact) -> Result<ArtifactSeal> {
    let path = artifact.path.to_string_lossy();
    artifact
        .file
        .sync_all()
        .map_err(|error| export_error(&path, "sync DRAT proof for", error))?;
    let seal = seal_open_file(&mut artifact.file, None)
        .map_err(|error| export_error(&path, "seal DRAT proof for", error))?;
    if seal.len == 0 {
        return Err(export_error(
            &path,
            "seal DRAT proof for",
            "the proof file is empty",
        ));
    }
    if !path_has_identity(&artifact.path, artifact.identity)
        .map_err(|error| export_error(&path, "verify DRAT identity for", error))?
    {
        return Err(export_error(
            &path,
            "verify DRAT identity for",
            "the destination was replaced while the proof was being written",
        ));
    }
    let installed = seal_file(&artifact.path, Some(seal.len))
        .map_err(|error| export_error(&path, "verify sealed DRAT contents for", error))?;
    if installed != seal {
        return Err(export_error(
            &path,
            "verify sealed DRAT contents for",
            "the destination content differs from the retained writer descriptor",
        ));
    }
    sync_parent_directory(&artifact.path)
        .map_err(|error| export_error(&path, "sync DRAT parent directory for", error))?;
    THREAD_TRANSACTION.with(|state| {
        let mut state = state.borrow_mut();
        match state.drat_artifact.as_mut() {
            Some(record)
                if record.generation == artifact.generation
                    && record.identity == artifact.identity =>
            {
                record.seal = Some(seal);
            }
            _ => debug_assert!(
                false,
                "DRAT artifact transaction state changed unexpectedly"
            ),
        }
    });
    Ok(seal)
}

/// Finalize the single-invocation BV DRAT proof.
///
/// On UNSAT the live proof stream (already terminated by the empty clause the
/// SAT solver emits when it declares UNSAT) is flushed and its writer's I/O
/// health is checked: a truncated proof aborts the check rather than leaving an
/// uncheckable certificate. On SAT/Unknown the scratch DRAT is removed so no
/// verdict is ever accompanied by a non-refuting "proof".
pub(in crate::executor) fn finish_bv_drat(
    proof: Option<ay_sat::ProofOutput>,
    artifact: BvDratArtifact,
    unsat: bool,
) -> Result<()> {
    let path = artifact.path.to_string_lossy().into_owned();
    if unsat {
        let mut proof = proof.ok_or_else(|| {
            export_error(
                &path,
                "finalize DRAT proof for",
                "the SAT solver retained no proof writer",
            )
        })?;
        proof
            .flush()
            .map_err(|error| export_error(&path, "flush DRAT proof for", error))?;
        if proof.has_io_error() {
            return Err(export_error(
                &path,
                "write DRAT proof for",
                "the proof stream reported an I/O error and may be truncated",
            ));
        }
        // Dropping the writer closes the file with all buffered bytes flushed.
        drop(proof);
        finalize_drat_artifact(artifact)?;
    } else {
        drop(proof);
        remove_file_if_owned(&artifact.path, artifact.identity).map_err(|error| {
            export_error(&path, "remove the non-UNSAT DRAT scratch file for", error)
        })?;
        sync_parent_directory(&artifact.path).map_err(|error| {
            export_error(
                &path,
                "sync the non-UNSAT DRAT removal directory for",
                error,
            )
        })?;
        THREAD_TRANSACTION.with(|state| {
            let mut state = state.borrow_mut();
            if state
                .drat_artifact
                .is_some_and(|record| record.identity == artifact.identity)
            {
                state.drat_artifact = None;
            }
        });
    }
    Ok(())
}

fn export_error(path: &str, action: &str, error: impl std::fmt::Display) -> ExecutorError {
    ExecutorError::ArtifactExport(format!(
        "cannot {action} BV CNF dump target '{path}': {error}"
    ))
}

/// Begin one certificate-export transaction.
///
/// Top-level transactions use a process-wide `try_lock`: independent solvers
/// targeting the singleton configured path are rejected instead of racing (or
/// deadlocking a parallel parent waiting for its worker).  Reentrant checks on
/// the owner thread are tracked as nested and do not touch the artifact.
pub(in crate::executor) fn prepare_for_check() -> Result<CheckTransaction> {
    if !requested() {
        return Ok(CheckTransaction::disabled());
    }
    let Some(path) = configured_path() else {
        return Ok(CheckTransaction::disabled());
    };

    if let Some(generation) = THREAD_TRANSACTION.with(|state| {
        let mut state = state.borrow_mut();
        if state.depth == 0 {
            None
        } else {
            state.depth += 1;
            Some(state.generation)
        }
    }) {
        return Ok(CheckTransaction {
            active: true,
            owner: false,
            generation,
            completed: true,
            cnf_path: None,
            drat_path: None,
            _cross_process_locks: Vec::new(),
            _process_lock: None,
        });
    }

    let process_lock = match BV_CNF_DUMP_LOCK.try_lock() {
        Ok(guard) => guard,
        Err(TryLockError::WouldBlock) => {
            return Err(ExecutorError::ArtifactExport(
                "concurrent BV CNF export is unsupported for the single configured target"
                    .to_string(),
            ));
        }
        Err(TryLockError::Poisoned(error)) => {
            return Err(ExecutorError::ArtifactExport(format!(
                "BV CNF export transaction lock is poisoned: {error}"
            )));
        }
    };

    // Preserve `try_update`'s return contract: reserve `current + 1` while
    // returning the previous value as this transaction's generation.  The CAS
    // helper keeps that contract on the older toolchain used by model-checker-consumer.
    let generation = reserve_generation(&BV_CNF_DUMP_GENERATION).ok_or_else(|| {
        ExecutorError::ArtifactExport(
            "BV CNF export generation counter exhausted the u64 domain".to_string(),
        )
    })?;
    // Resolve both destinations before acquiring either lock and retain these
    // physical paths until the transaction drops. Never return to the caller's
    // lexical path after this point.
    let resolved_path = resolved_target_string(path)?;
    let resolved_drat_path = configured_drat_path()
        .map(resolved_target_string)
        .transpose()?;
    let cross_process_locks =
        acquire_transaction_locks(&resolved_path, resolved_drat_path.as_deref(), generation)?;

    clear_stale_artifact(Path::new(&resolved_path))
        .map_err(|error| export_error(&resolved_path, "clear", error))?;

    // Clear any stale DRAT companion so a prior run's proof can never be mistaken
    // for this check's certificate. The DRAT is (re)written only on this check's
    // own UNSAT; a SAT/Unknown verdict must leave no proof file behind.
    if let Some(drat_path) = resolved_drat_path.as_deref() {
        clear_stale_artifact(Path::new(drat_path))
            .map_err(|error| export_error(drat_path, "clear DRAT companion", error))?;
    }

    THREAD_TRANSACTION.with(|state| {
        let mut state = state.borrow_mut();
        debug_assert_eq!(state.depth, 0);
        state.depth = 1;
        state.generation = generation;
        state.cnf_path = Some(resolved_path.clone());
        state.drat_path = resolved_drat_path.clone();
        state.written_artifact = None;
        state.drat_artifact = None;
    });
    Ok(CheckTransaction {
        active: true,
        owner: true,
        generation,
        completed: false,
        cnf_path: Some(PathBuf::from(&resolved_path)),
        drat_path: resolved_drat_path.map(PathBuf::from),
        _cross_process_locks: cross_process_locks,
        _process_lock: Some(process_lock),
    })
}

fn seal_open_file(file: &mut File, expected_len: Option<u64>) -> io::Result<ArtifactSeal> {
    let before = file.metadata()?;
    validate_regular_artifact_metadata(&before, ArtifactFileRef::Handle(file))?;
    let identity = file_identity(&before, ArtifactFileRef::Handle(file))?;
    let len = before.len();
    if let Some(expected) = expected_len {
        if expected != len {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("artifact length changed (expected {expected} bytes, found {len})"),
            ));
        }
    }
    let read_limit = len.checked_add(1).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            "artifact length cannot be bounded for sealing",
        )
    })?;
    file.seek(SeekFrom::Start(0))?;
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 16 * 1024];
    let mut bytes_read = 0u64;
    {
        let mut bounded = file.take(read_limit);
        loop {
            let read = bounded.read(&mut buffer)?;
            if read == 0 {
                break;
            }
            bytes_read = bytes_read.checked_add(read as u64).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    "artifact byte count overflowed while sealing",
                )
            })?;
            hasher.update(&buffer[..read]);
        }
    }
    if bytes_read != len {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("artifact changed while sealing (expected {len} bytes, read {bytes_read})"),
        ));
    }
    let after = file.metadata()?;
    validate_regular_artifact_metadata(&after, ArtifactFileRef::Handle(file))?;
    if file_identity(&after, ArtifactFileRef::Handle(file))? != identity || after.len() != len {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "artifact identity or length changed while sealing",
        ));
    }
    Ok(ArtifactSeal {
        identity,
        len,
        sha256: hasher.finalize().into(),
    })
}

fn seal_file(path: &Path, expected_len: Option<u64>) -> io::Result<ArtifactSeal> {
    let (mut file, identity) = open_regular_file_no_follow(path)?;
    let seal = seal_open_file(&mut file, expected_len)?;
    if !path_has_identity(path, identity)? {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "artifact destination was replaced while sealing",
        ));
    }
    Ok(seal)
}

/// Install a file through a same-directory temporary without replacing a leaf
/// planted after transaction cleanup. A hard link atomically creates the final
/// name only when absent; unlinking the temporary then restores the required
/// single-link artifact before identity validation and parent-directory sync.
fn atomic_write<F>(path: &str, write_contents: F) -> io::Result<ArtifactSeal>
where
    F: FnOnce(&mut BufWriter<File>) -> io::Result<()>,
{
    atomic_write_with_hook(path, write_contents, || {})
}

fn atomic_write_with_hook<F, H>(
    path: &str,
    write_contents: F,
    before_publish: H,
) -> io::Result<ArtifactSeal>
where
    F: FnOnce(&mut BufWriter<File>) -> io::Result<()>,
    H: FnOnce(),
{
    let target = Path::new(path);
    let file_name = target.file_name().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "BV CNF dump path has no file name",
        )
    })?;
    let parent = target
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));

    let mut temporary_file = None;
    for _ in 0..128 {
        let id = BV_CNF_DUMP_FILE_ID.fetch_add(1, Ordering::Relaxed);
        let candidate = parent.join(format!(
            ".{}.ay-bv-cnf-{}-{id}.tmp",
            file_name.to_string_lossy(),
            std::process::id()
        ));
        match create_new_regular_file_no_follow(&candidate) {
            Ok((file, identity)) => {
                temporary_file = Some((candidate, file, identity));
                break;
            }
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    let (temporary, file, identity) = temporary_file.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::AlreadyExists,
            "exhausted 128 unique BV CNF temporary-file attempts",
        )
    })?;

    let mut installed = false;
    let result = (|| {
        let mut writer = BufWriter::new(file);
        write_contents(&mut writer)?;
        writer.flush()?;
        writer.get_ref().sync_all()?;
        let seal = seal_open_file(writer.get_mut(), None)?;
        drop(writer);

        before_publish();
        std::fs::hard_link(&temporary, target)?;
        installed = true;
        std::fs::remove_file(&temporary)?;
        if !path_has_identity(target, identity)? {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "installed BV CNF destination does not retain the temporary file identity",
            ));
        }
        let installed_seal = seal_file(target, Some(seal.len))?;
        if installed_seal != seal {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "installed BV CNF destination differs from the sealed temporary file",
            ));
        }
        sync_parent_directory(target)?;
        Ok(seal)
    })();
    if result.is_err() {
        // `installed` documents whether a two-link state may exist. The
        // identity-aware helper is safe in both states and refuses replacement
        // files, so clean both names unconditionally.
        let _ = installed;
        let _ = remove_file_link_if_owned(target, identity);
        let _ = remove_file_link_if_owned(&temporary, identity);
    }
    result
}

fn install<F>(path: &str, write_contents: F) -> Result<ArtifactSeal>
where
    F: FnOnce(&mut BufWriter<File>) -> io::Result<()>,
{
    match atomic_write(path, write_contents) {
        Ok(seal) => Ok(seal),
        Err(error) => Err(export_error(path, "write", error)),
    }
}

fn current_generation() -> Result<u64> {
    THREAD_TRANSACTION
        .with(|state| {
            let state = state.borrow();
            (state.depth == 1 && state.generation != 0).then_some(state.generation)
        })
        .ok_or_else(|| {
            ExecutorError::ArtifactExport(
                "BV CNF writer was invoked without a top-level export transaction".to_string(),
            )
        })
}

fn mark_written(generation: u64, seal: ArtifactSeal) {
    THREAD_TRANSACTION.with(|state| {
        let mut state = state.borrow_mut();
        debug_assert_eq!(state.generation, generation);
        debug_assert_eq!(state.depth, 1);
        state.written_artifact = Some((generation, seal));
    });
}

/// The provenance marker a consumer uses to prove this CNF came from the solver
/// invocation it launched.
///
/// ⚑ Uses the ROOT pid, not `std::process::id()`. `ay_sys::govern::arm` re-execs
/// this image under `taskpolicy` so the jetsam memlimit binds the real binary,
/// so by the time the writer runs the live pid need NOT be the pid the caller
/// spawned. Emitting the live pid made external-codegen's `c ay export pid <PID>`
/// binding unsatisfiable: it compared against the pid it launched and saw a
/// different number. `root_pid()` falls back to the live pid when nothing
/// re-exec'd, which is precisely when they coincide.
fn generation_marker(generation: u64) -> String {
    format!(
        "c ay export pid {} generation {generation}",
        ay_sys::govern::root_pid()
    )
}

fn sat_literal_to_dimacs(literal: SatLiteral) -> Result<i32> {
    let zero_based = literal.variable().id();
    let one_based = zero_based.checked_add(1).ok_or_else(|| {
        ExecutorError::ArtifactExport(format!(
            "SAT variable {zero_based} overflows DIMACS one-based numbering"
        ))
    })?;
    let variable = i32::try_from(one_based).map_err(|_| {
        ExecutorError::ArtifactExport(format!(
            "SAT variable {zero_based} exceeds the DIMACS i32 domain"
        ))
    })?;
    Ok(if literal.is_positive() {
        variable
    } else {
        -variable
    })
}

fn assumption_literals_to_dimacs(assumptions: &[SatLiteral], total_vars: u32) -> Result<Vec<i32>> {
    let literals = assumptions
        .iter()
        .copied()
        .map(sat_literal_to_dimacs)
        .collect::<Result<Vec<_>>>()?;
    if let Some(&literal) = literals
        .iter()
        .find(|literal| literal.unsigned_abs() > total_vars)
    {
        return Err(ExecutorError::ArtifactExport(format!(
            "assumption literal {literal} lies outside declared variable range 1..={total_vars}"
        )));
    }
    Ok(literals)
}

/// Export the exact conjunction solved for one pure QF_BV decision query.
///
/// `clauses` is the fully assembled eager bit-blast.  `assumptions` are
/// materialized as unit clauses because `solve_with_assumptions(assumptions)`
/// is satisfiability-equivalent to solving that augmented clause set.  Delayed
/// internalization and the persistent incremental route are disabled while
/// export is enabled, so no post-write semantic refinement can be omitted.
pub(in crate::executor) fn write_formula(
    clauses: &[CnfClause],
    total_vars: u32,
    assumptions: &[SatLiteral],
) -> Result<()> {
    if !enabled() {
        return Ok(());
    }
    let path = active_cnf_path()?;
    let generation = current_generation()?;
    if total_vars > i32::MAX as u32 {
        return Err(ExecutorError::ArtifactExport(format!(
            "BV CNF has {total_vars} variables, exceeding the DIMACS i32 domain"
        )));
    }
    let assumption_literals = assumption_literals_to_dimacs(assumptions, total_vars)?;
    let clause_count = clauses
        .len()
        .checked_add(assumption_literals.len())
        .ok_or_else(|| {
            ExecutorError::ArtifactExport(
                "BV CNF clause count overflows the platform usize domain".to_string(),
            )
        })?;

    let seal = install(&path, |writer| {
        writeln!(writer, "{}", generation_marker(generation))?;
        writeln!(writer, "c ay bit-blasted QF_BV CNF (--dump-bv-cnf)")?;
        writeln!(
            writer,
            "c complete eager encoding of the current check-sat query"
        )?;
        writeln!(writer, "p cnf {total_vars} {clause_count}")?;
        for clause in clauses {
            for &literal in clause.literals() {
                if literal == 0 || literal.unsigned_abs() > total_vars {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "CNF literal {literal} lies outside declared variable range 1..={total_vars}"
                        ),
                    ));
                }
                write!(writer, "{literal} ")?;
            }
            writeln!(writer, "0")?;
        }
        for literal in &assumption_literals {
            writeln!(writer, "{literal} 0")?;
        }
        Ok(())
    })?;
    mark_written(generation, seal);
    tracing::info!(
        path,
        generation,
        vars = total_vars,
        clauses = clause_count,
        assumption_units = assumptions.len(),
        "faithful bit-blasted BV DIMACS written"
    );
    Ok(())
}

/// Return the value of a conjunction made only from literal `true`/`false`
/// roots, or `None` for any non-literal formula.
pub(in crate::executor) fn trivial_conjunction(
    terms: &TermStore,
    roots: &[TermId],
) -> Option<bool> {
    if roots.iter().any(|&root| root == terms.false_term()) {
        Some(false)
    } else if roots.iter().all(|&root| root == terms.true_term()) {
        Some(true)
    } else {
        None
    }
}

fn artifact_has_generation(path: &str, generation: u64) -> Result<bool> {
    let target = Path::new(path);
    let (file, identity) = match open_regular_file_no_follow(target) {
        Ok(opened) => opened,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(false),
        Err(error) => return Err(export_error(path, "inspect", error)),
    };
    let mut prefix = Vec::with_capacity(256);
    file.take(256)
        .read_to_end(&mut prefix)
        .map_err(|error| export_error(path, "inspect", error))?;
    if !path_has_identity(target, identity)
        .map_err(|error| export_error(path, "verify identity while inspecting", error))?
    {
        return Ok(false);
    }
    let first_line = prefix
        .split(|byte| *byte == b'\n')
        .next()
        .unwrap_or_default();
    Ok(first_line == generation_marker(generation).as_bytes())
}

fn install_trivial(path: &str, generation: u64, value: bool) -> Result<()> {
    let seal = install(path, |writer| {
        writeln!(writer, "{}", generation_marker(generation))?;
        if value {
            writeln!(writer, "c ay canonical true CNF (--dump-bv-cnf)")?;
            writeln!(writer, "p cnf 0 0")?;
        } else {
            writeln!(writer, "c ay canonical false CNF (--dump-bv-cnf)")?;
            writeln!(writer, "p cnf 0 1")?;
            writeln!(writer, "0")?;
        }
        Ok(())
    })?;
    mark_written(generation, seal);
    Ok(())
}

fn verify_drat_for_finish(path: &str, generation: u64) -> Result<()> {
    let record = THREAD_TRANSACTION.with(|state| state.borrow().drat_artifact);
    let Some(record) = record else {
        return match std::fs::symlink_metadata(path) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
            Ok(_) => Err(export_error(
                path,
                "verify absent non-UNSAT DRAT output for",
                "an unowned destination appeared during the export transaction",
            )),
            Err(error) => Err(export_error(
                path,
                "verify absent non-UNSAT DRAT output for",
                error,
            )),
        };
    };
    if record.generation != generation {
        return Err(export_error(
            path,
            "verify DRAT generation for",
            format!(
                "recorded generation {} does not match current generation {generation}",
                record.generation
            ),
        ));
    }
    let expected = record.seal.ok_or_else(|| {
        export_error(
            path,
            "verify completed DRAT output for",
            "the retained proof descriptor was never sealed",
        )
    })?;
    if !path_has_identity(Path::new(path), record.identity)
        .map_err(|error| export_error(path, "verify DRAT identity for", error))?
    {
        return Err(export_error(
            path,
            "verify DRAT identity for",
            "the destination was removed or replaced after finalization",
        ));
    }
    let actual = seal_file(Path::new(path), Some(expected.len))
        .map_err(|error| export_error(path, "verify sealed DRAT contents of", error))?;
    if actual != expected {
        return Err(export_error(
            path,
            "verify sealed DRAT contents of",
            "the proof changed after finalization",
        ));
    }
    Ok(())
}

/// Complete one decision query's export transaction.
///
/// Literal `true`/`false` formulas can terminate before theory dispatch and get
/// canonical CNFs.  Non-literal early simplifications never synthesize a file
/// from the solver verdict: they must have gone through the faithful writer or
/// the check fails before its verdict is returned.
pub(in crate::executor) fn finish_check(
    mut transaction: CheckTransaction,
    terms: &TermStore,
    roots: &[TermId],
) -> Result<()> {
    if !transaction.active {
        transaction.completed = true;
        return Ok(());
    }
    if !transaction.owner {
        transaction.completed = true;
        return Ok(());
    }

    let path = transaction.cnf_path.as_deref().ok_or_else(|| {
        ExecutorError::ArtifactExport(
            "active BV CNF export transaction has no resolved target".to_string(),
        )
    })?;
    let path_text = path.to_string_lossy();
    let generation = transaction.generation;
    let mut written = THREAD_TRANSACTION.with(|state| {
        let state = state.borrow();
        (state.depth == 1 && state.generation == generation)
            .then_some(state.written_artifact)
            .flatten()
            .and_then(|(written_generation, seal)| {
                (written_generation == generation).then_some(seal)
            })
    });
    if written.is_none() {
        if let Some(value) = trivial_conjunction(terms, roots) {
            install_trivial(&path_text, generation, value)?;
            // A trivial-false conjunction is decided before bit-blasting, so the
            // SAT solver (and its live DRAT stream) never ran. Its canonical CNF
            // is the bare empty clause, so a one-line empty-clause DRAT is a
            // complete drat-trim-checkable refutation of it. A trivial-true
            // conjunction is SAT and gets no proof.
            if !value {
                if let Some((drat_path, binary)) = bv_drat_target() {
                    install_trivial_false_drat(&drat_path, binary)?;
                }
            }
            written = THREAD_TRANSACTION.with(|state| {
                state
                    .borrow()
                    .written_artifact
                    .and_then(|(written_generation, seal)| {
                        (written_generation == generation).then_some(seal)
                    })
            });
        } else {
            return Err(ExecutorError::ArtifactExport(format!(
                "BV CNF export generation {generation} produced no artifact for the current check at '{}'",
                path.display()
            )));
        }
    }

    if !artifact_has_generation(&path_text, generation)? {
        return Err(ExecutorError::ArtifactExport(format!(
            "BV CNF artifact at '{}' was not produced by current export generation {generation}",
            path.display()
        )));
    }
    let expected_seal = written.ok_or_else(|| {
        ExecutorError::ArtifactExport(format!(
            "BV CNF export generation {generation} did not record an artifact seal for '{}'",
            path.display()
        ))
    })?;
    let actual_seal = seal_file(path, Some(expected_seal.len))
        .map_err(|error| export_error(&path_text, "verify sealed contents of", error))?;
    if actual_seal != expected_seal {
        return Err(ExecutorError::ArtifactExport(format!(
            "BV CNF artifact at '{}' changed after generation {generation} installed it (expected {} bytes, found {} bytes; file identity or SHA-256 content seal differs)",
            path.display(),
            expected_seal.len,
            actual_seal.len
        )));
    }
    if let Some(drat_path) = transaction.drat_path.as_deref() {
        verify_drat_for_finish(&drat_path.to_string_lossy(), generation)?;
    }
    transaction.completed = true;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_sat::Variable as SatVariable;

    #[test]
    fn generation_reservation_advances_and_fails_closed_at_exhaustion() {
        let counter = AtomicU64::new(41);
        assert_eq!(reserve_generation(&counter), Some(41));
        assert_eq!(counter.load(Ordering::Relaxed), 42);

        counter.store(u64::MAX, Ordering::Relaxed);
        assert_eq!(reserve_generation(&counter), None);
        assert_eq!(counter.load(Ordering::Relaxed), u64::MAX);
    }

    fn set_test_transaction(generation: u64) {
        THREAD_TRANSACTION.with(|state| {
            let mut state = state.borrow_mut();
            *state = ThreadTransactionState::default();
            state.depth = 1;
            state.generation = generation;
        });
    }

    fn clear_test_transaction() {
        THREAD_TRANSACTION.with(|state| *state.borrow_mut() = ThreadTransactionState::default());
    }

    #[test]
    fn trivial_false_drat_respects_text_and_binary_encoding() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        for (name, binary, expected) in [
            ("proof.drat", false, b"0\n".as_slice()),
            ("proof.dratb", true, b"a\0".as_slice()),
        ] {
            let path = temp.path().join(name);
            let path_str = path.to_str().expect("temporary path is UTF-8");
            set_test_transaction(1);
            install_trivial_false_drat(path_str, binary).expect("write trivial-false DRAT");
            assert_eq!(
                std::fs::read(&path).expect("read trivial-false DRAT"),
                expected
            );
            std::fs::remove_file(&path).expect("remove trivial-false DRAT");
            clear_test_transaction();
        }
    }

    #[test]
    fn incomplete_owner_transaction_removes_drat_scratch() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let cnf_path = temp.path().join("formula.cnf");
        let drat_path = temp.path().join("partial.dratb");
        std::fs::write(&drat_path, b"a").expect("write partial DRAT scratch");

        const GENERATION: u64 = 73;
        let cnf = cnf_path.to_str().expect("temporary path is UTF-8");
        let drat = drat_path.to_str().expect("temporary path is UTF-8");
        let locks = acquire_transaction_locks(cnf, Some(drat), GENERATION)
            .expect("acquire both transaction locks");
        let (_owned_file, drat_identity) =
            open_regular_file_no_follow(&drat_path).expect("inspect owned DRAT scratch");
        assert!(
            acquire_transaction_locks(drat, Some(cnf), GENERATION + 1).is_err(),
            "an incomplete owner must hold both destination locks through cleanup"
        );
        THREAD_TRANSACTION.with(|state| {
            let mut state = state.borrow_mut();
            assert_eq!(state.depth, 0);
            state.depth = 1;
            state.generation = GENERATION;
            state.written_artifact = None;
            state.drat_artifact = Some(DratArtifactState {
                generation: GENERATION,
                identity: drat_identity,
                seal: None,
            });
        });
        drop(CheckTransaction {
            active: true,
            owner: true,
            generation: GENERATION,
            completed: false,
            cnf_path: Some(cnf_path.clone()),
            drat_path: Some(drat_path.clone()),
            _cross_process_locks: locks,
            _process_lock: None,
        });

        assert!(
            !drat_path.exists(),
            "an errored transaction must not leave a partial DRAT certificate"
        );
        drop(
            acquire_transaction_locks(drat, Some(cnf), GENERATION + 2)
                .expect("owner drop must release both destination locks"),
        );
        THREAD_TRANSACTION.with(|state| {
            let state = state.borrow();
            assert_eq!(state.depth, 0);
            assert_eq!(state.generation, 0);
            assert!(state.written_artifact.is_none());
            assert!(state.drat_artifact.is_none());
        });
    }

    #[test]
    fn dimacs_conversion_rejects_unrepresentable_variable() {
        let literal = SatLiteral::positive(SatVariable::new(i32::MAX as u32));
        assert!(matches!(
            sat_literal_to_dimacs(literal),
            Err(ExecutorError::ArtifactExport(_))
        ));
    }

    #[test]
    fn assumption_must_fit_declared_header_range() {
        let literal = SatLiteral::positive(SatVariable::new(3));
        assert!(matches!(
            assumption_literals_to_dimacs(&[literal], 3),
            Err(ExecutorError::ArtifactExport(_))
        ));
        assert_eq!(assumption_literals_to_dimacs(&[literal], 4).unwrap(), [4]);
    }

    #[test]
    fn stale_lock_file_is_reusable_but_live_lock_is_exclusive() {
        static TEST_ID: AtomicU64 = AtomicU64::new(0);
        let id = TEST_ID.fetch_add(1, Ordering::Relaxed);
        let target = std::env::temp_dir().join(format!(
            "ay-bv-cnf-lock-test-{}-{id}.cnf",
            std::process::id()
        ));
        let path = target.to_str().expect("temporary path is UTF-8");
        let lock_path = cross_process_lock_path(path).expect("derive lock path");
        std::fs::write(&lock_path, "stale marker without an OS lock\n")
            .expect("precreate stale lock file");

        let first = acquire_cross_process_lock(path, 11).expect("first lock acquisition");
        assert!(matches!(
            acquire_cross_process_lock(path, 12),
            Err(ExecutorError::ArtifactExport(_))
        ));
        drop(first);
        let second = acquire_cross_process_lock(path, 13).expect("lock released on drop");
        drop(second);
        let _ = std::fs::remove_file(target);
        let _ = std::fs::remove_file(lock_path);
    }

    #[test]
    fn canonical_and_dotdot_aliases_share_one_cross_process_lock() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let directory = temp.path().join("exports");
        std::fs::create_dir(&directory).expect("create export directory");
        let canonical = directory.join("formula.cnf");
        let alias = directory.join("..").join("exports").join("formula.cnf");
        let canonical = canonical.to_str().expect("temporary path is UTF-8");
        let alias = alias.to_str().expect("temporary path is UTF-8");

        assert_eq!(
            cross_process_lock_path(canonical).unwrap(),
            cross_process_lock_path(alias).unwrap(),
            "lexical aliases must derive one coordination-file identity"
        );
        let first = acquire_cross_process_lock(canonical, 31).expect("acquire canonical lock");
        assert!(
            acquire_cross_process_lock(alias, 32).is_err(),
            "alias acquisition must conflict while canonical lock is live"
        );
        #[cfg(unix)]
        {
            let symlinked_directory = temp.path().join("exports-link");
            std::os::unix::fs::symlink(&directory, &symlinked_directory)
                .expect("create directory symlink");
            let symlinked = symlinked_directory.join("formula.cnf");
            let symlinked = symlinked.to_str().expect("temporary path is UTF-8");
            assert_eq!(
                cross_process_lock_path(canonical).unwrap(),
                cross_process_lock_path(symlinked).unwrap()
            );
            assert!(
                acquire_cross_process_lock(symlinked, 32).is_err(),
                "symlinked-parent acquisition must conflict with canonical lock"
            );
        }
        drop(first);
        drop(acquire_cross_process_lock(alias, 33).expect("lock released for alias successor"));
    }

    #[test]
    #[cfg(unix)]
    fn resolved_cnf_and_drat_targets_survive_parent_symlink_swap() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let first_parent = temp.path().join("first");
        let second_parent = temp.path().join("second");
        let parent_link = temp.path().join("current");
        std::fs::create_dir(&first_parent).expect("create first export directory");
        std::fs::create_dir(&second_parent).expect("create second export directory");
        std::os::unix::fs::symlink(&first_parent, &parent_link)
            .expect("point export parent at first directory");

        let lexical_cnf = parent_link.join("formula.cnf");
        let lexical_drat = parent_link.join("proof.drat");
        let resolved_cnf = resolved_target_string(lexical_cnf.to_str().expect("UTF-8 path"))
            .expect("resolve CNF target");
        let resolved_drat = resolved_target_string(lexical_drat.to_str().expect("UTF-8 path"))
            .expect("resolve DRAT target");
        let retained_cnf_lock = cross_process_lock_path(&resolved_cnf).expect("derive CNF lock");
        let retained_drat_lock = cross_process_lock_path(&resolved_drat).expect("derive DRAT lock");

        std::fs::remove_file(&parent_link).expect("remove first parent link");
        std::os::unix::fs::symlink(&second_parent, &parent_link)
            .expect("redirect lexical export parent");

        atomic_write(&resolved_cnf, |writer| writer.write_all(b"p cnf 0 0\n"))
            .expect("write retained CNF target");
        set_test_transaction(90);
        let (mut proof, artifact) = create_bv_drat(&resolved_drat).expect("create retained DRAT");
        proof.write_all(b"0\n").expect("write retained DRAT");
        proof.flush().expect("flush retained DRAT");
        drop(proof);
        finalize_drat_artifact(artifact).expect("seal retained DRAT");

        assert_eq!(
            std::fs::read(first_parent.join("formula.cnf")).expect("read retained CNF"),
            b"p cnf 0 0\n"
        );
        assert_eq!(
            std::fs::read(first_parent.join("proof.drat")).expect("read retained DRAT"),
            b"0\n"
        );
        assert!(!second_parent.join("formula.cnf").exists());
        assert!(!second_parent.join("proof.drat").exists());
        // The production path canonicalizes the export parent (the hardening
        // under test), so the expected side must be canonicalized too: on
        // macOS the default TMPDIR sits behind the /var -> /private/var
        // symlink and the lexical `first_parent` differs from the physical
        // path the lock is actually derived from.
        let canonical_first_parent =
            std::fs::canonicalize(&first_parent).expect("canonicalize retained export parent");
        assert_eq!(
            retained_cnf_lock,
            canonical_first_parent.join(".formula.cnf.ay-bv-cnf.lock")
        );
        assert_eq!(
            retained_drat_lock,
            canonical_first_parent.join(".proof.drat.ay-bv-cnf.lock")
        );
        clear_test_transaction();
    }

    #[test]
    #[cfg(unix)]
    fn existing_leaf_symlink_is_rejected_before_lock_or_cleanup() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let canonical = temp.path().join("formula.cnf");
        let symlink = temp.path().join("proof.drat");
        std::fs::write(&canonical, b"stale artifact").expect("create referent");
        std::os::unix::fs::symlink(&canonical, &symlink).expect("create leaf symlink");
        let symlink = symlink.to_str().expect("temporary path is UTF-8");

        assert!(
            cross_process_lock_path(symlink).is_err(),
            "a leaf symlink must fail before a lock path is derived"
        );
        assert_eq!(
            std::fs::read(&canonical).expect("read symlink referent"),
            b"stale artifact",
            "rejected target resolution must not touch the referent"
        );
    }

    #[test]
    #[cfg(unix)]
    fn symlink_coordination_file_is_rejected_without_touching_referent() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let export = temp.path().join("formula.cnf");
        let export = export.to_str().expect("temporary path is UTF-8");
        let lock_path = cross_process_lock_path(export).expect("derive lock path");
        let unrelated = temp.path().join("unrelated.txt");
        const SENTINEL: &[u8] = b"must remain unchanged\n";
        std::fs::write(&unrelated, SENTINEL).expect("write unrelated referent");
        std::os::unix::fs::symlink(&unrelated, &lock_path)
            .expect("replace coordination file with symlink");

        assert!(
            acquire_cross_process_lock(export, 51).is_err(),
            "a symlink coordination file must fail closed"
        );
        assert_eq!(
            std::fs::read(&unrelated).expect("read unrelated referent"),
            SENTINEL,
            "failed lock acquisition must not truncate or stamp the symlink referent"
        );
    }

    #[test]
    #[cfg(unix)]
    fn hard_link_coordination_file_is_rejected_without_touching_referent() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let export = temp.path().join("formula.cnf");
        let export = export.to_str().expect("temporary path is UTF-8");
        let lock_path = cross_process_lock_path(export).expect("derive lock path");
        let unrelated = temp.path().join("unrelated.txt");
        const SENTINEL: &[u8] = b"hard-link referent must remain unchanged\n";
        std::fs::write(&unrelated, SENTINEL).expect("write unrelated referent");
        std::fs::hard_link(&unrelated, &lock_path)
            .expect("hard-link unrelated file at coordination path");

        assert!(
            acquire_cross_process_lock(export, 52).is_err(),
            "a multiply-linked coordination file must fail closed"
        );
        assert_eq!(
            std::fs::read(&unrelated).expect("read unrelated referent"),
            SENTINEL,
            "failed lock acquisition must not truncate or stamp a hard-link referent"
        );
    }

    #[test]
    fn non_regular_coordination_file_is_rejected() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let export = temp.path().join("formula.cnf");
        let export = export.to_str().expect("temporary path is UTF-8");
        let lock_path = cross_process_lock_path(export).expect("derive lock path");
        std::fs::create_dir(&lock_path).expect("create non-regular coordination path");

        assert!(
            acquire_cross_process_lock(export, 53).is_err(),
            "directories, FIFOs, devices, and other non-regular lock paths must fail closed"
        );
    }

    #[test]
    fn transaction_locks_cover_shared_drat_target_in_deterministic_order() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let cnf_path = temp.path().join("formula.cnf");
        let drat_path = temp.path().join("proof.drat");
        let cnf = cnf_path.to_str().expect("temporary path is UTF-8");
        let drat = drat_path.to_str().expect("temporary path is UTF-8");

        let first = acquire_transaction_locks(cnf, Some(drat), 21)
            .expect("acquire CNF and DRAT transaction locks");
        assert_eq!(first.len(), 2);
        assert!(
            acquire_transaction_locks(drat, Some(cnf), 22).is_err(),
            "swapping CNF and DRAT targets must still conflict, not race"
        );

        drop(first);
        let second = acquire_transaction_locks(drat, Some(cnf), 23)
            .expect("both destination locks must be released together");
        assert_eq!(second.len(), 2);
    }

    #[test]
    #[cfg(unix)]
    fn artifact_readers_reject_symlinks_hard_links_and_fifos() {
        use std::process::Command;

        let temp = tempfile::tempdir().expect("create temporary directory");
        let sentinel = temp.path().join("sentinel");
        std::fs::write(&sentinel, b"unchanged").expect("write sentinel");

        let symlink = temp.path().join("artifact-symlink");
        std::os::unix::fs::symlink(&sentinel, &symlink).expect("create symlink");
        assert!(seal_file(&symlink, None).is_err());

        let hard_link = temp.path().join("artifact-hard-link");
        std::fs::hard_link(&sentinel, &hard_link).expect("create hard link");
        assert!(seal_file(&hard_link, None).is_err());

        let fifo = temp.path().join("artifact-fifo");
        let status = Command::new("mkfifo")
            .arg(&fifo)
            .status()
            .expect("invoke mkfifo");
        assert!(status.success(), "mkfifo must create the test FIFO");
        assert!(seal_file(&fifo, None).is_err());

        assert_eq!(
            std::fs::read(&sentinel).expect("read sentinel"),
            b"unchanged"
        );
    }

    #[test]
    #[cfg(unix)]
    fn drat_create_new_does_not_follow_replanted_symlink() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let sentinel = temp.path().join("sentinel");
        let drat = temp.path().join("proof.drat");
        std::fs::write(&sentinel, b"must not be truncated").expect("write sentinel");
        std::os::unix::fs::symlink(&sentinel, &drat).expect("plant DRAT symlink");
        set_test_transaction(91);

        assert!(create_bv_drat(drat.to_str().expect("UTF-8 path")).is_err());
        assert_eq!(
            std::fs::read(&sentinel).expect("read sentinel"),
            b"must not be truncated"
        );
        clear_test_transaction();
    }

    #[test]
    #[cfg(unix)]
    fn stale_cleanup_does_not_delete_a_replaced_leaf() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let target = temp.path().join("formula.cnf");
        std::fs::write(&target, b"stale").expect("write stale artifact");

        let result = clear_stale_artifact_with_hook(&target, || {
            std::fs::remove_file(&target).expect("unlink stale artifact");
            std::fs::write(&target, b"replacement").expect("plant replacement artifact");
        });
        assert!(
            result.is_err(),
            "replacement must fail stale cleanup closed"
        );
        assert_eq!(
            std::fs::read(&target).expect("read replacement"),
            b"replacement",
            "identity-aware cleanup must not delete the replacement"
        );
    }

    #[test]
    #[cfg(unix)]
    fn cnf_publication_refuses_a_leaf_planted_after_temporary_write() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let target = temp.path().join("formula.cnf");
        let target_text = target.to_str().expect("UTF-8 path");

        let result = atomic_write_with_hook(
            target_text,
            |writer| writer.write_all(b"p cnf 0 0\n"),
            || std::fs::write(&target, b"planted").expect("plant final destination"),
        );
        assert!(result.is_err(), "no-replace publication must fail closed");
        assert_eq!(
            std::fs::read(&target).expect("read planted destination"),
            b"planted",
            "failed publication must not replace or delete the planted leaf"
        );
        let temporary_files = std::fs::read_dir(temp.path())
            .expect("list temporary directory")
            .filter_map(|entry| entry.ok())
            .filter(|entry| entry.file_name().to_string_lossy().ends_with(".tmp"))
            .count();
        assert_eq!(temporary_files, 0, "failed publication leaked a temporary");
    }

    #[test]
    #[cfg(unix)]
    fn drat_finalization_rejects_destination_replacement() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let drat = temp.path().join("proof.drat");
        set_test_transaction(92);
        let (mut writer, artifact) =
            create_bv_drat(drat.to_str().expect("UTF-8 path")).expect("create DRAT");
        writer.write_all(b"0\n").expect("write proof");
        writer.flush().expect("flush proof");
        drop(writer);

        std::fs::remove_file(&drat).expect("unlink owned destination");
        // Replant byte-identical content: identity, not merely a content hash,
        // must bind the proof to the descriptor the SAT writer actually used.
        std::fs::write(&drat, b"0\n").expect("plant replacement");
        assert!(finalize_drat_artifact(artifact).is_err());
        assert_eq!(std::fs::read(&drat).expect("read replacement"), b"0\n");
        clear_test_transaction();
    }

    #[test]
    #[cfg(unix)]
    fn incomplete_transaction_does_not_delete_replacement_file() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let drat = temp.path().join("proof.drat");
        std::fs::write(&drat, b"partial").expect("write owned scratch");
        let (_file, identity) = open_regular_file_no_follow(&drat).expect("inspect owned scratch");
        const GENERATION: u64 = 93;
        set_test_transaction(GENERATION);
        THREAD_TRANSACTION.with(|state| {
            state.borrow_mut().drat_artifact = Some(DratArtifactState {
                generation: GENERATION,
                identity,
                seal: None,
            });
        });
        std::fs::remove_file(&drat).expect("unlink owned scratch");
        std::fs::write(&drat, b"replacement").expect("plant replacement");

        drop(CheckTransaction {
            active: true,
            owner: true,
            generation: GENERATION,
            completed: false,
            cnf_path: None,
            drat_path: Some(drat.clone()),
            _cross_process_locks: Vec::new(),
            _process_lock: None,
        });
        assert_eq!(
            std::fs::read(&drat).expect("read replacement"),
            b"replacement"
        );
        clear_test_transaction();
    }

    #[test]
    fn seal_rejects_a_length_outside_the_recorded_envelope() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let artifact = temp.path().join("formula.cnf");
        std::fs::write(&artifact, b"1234").expect("write artifact");
        assert!(seal_file(&artifact, Some(3)).is_err());
        assert!(seal_file(&artifact, Some(5)).is_err());
        assert_eq!(seal_file(&artifact, Some(4)).expect("exact seal").len, 4);
    }

    #[test]
    #[cfg(unix)]
    fn seal_binds_byte_identical_content_to_the_original_file_identity() {
        let temp = tempfile::tempdir().expect("create temporary directory");
        let artifact = temp.path().join("formula.cnf");
        std::fs::write(&artifact, b"same bytes").expect("write original");
        // Retain the original inode so the filesystem cannot immediately
        // recycle its number for the replacement and make this regression
        // nondeterministic.
        let (original_descriptor, _) =
            open_regular_file_no_follow(&artifact).expect("retain original descriptor");
        let original = seal_file(&artifact, None).expect("seal original");

        std::fs::remove_file(&artifact).expect("unlink original");
        std::fs::write(&artifact, b"same bytes").expect("write replacement");
        let replacement = seal_file(&artifact, None).expect("seal replacement");
        assert_ne!(original, replacement);
        drop(original_descriptor);
    }
}
