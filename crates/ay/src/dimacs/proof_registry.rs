// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub(crate) type Sha256Digest = [u8; 32];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ProofFileIdentity {
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
    #[cfg(windows)]
    volume_serial_number: u32,
    #[cfg(windows)]
    file_index: u64,
    #[cfg(not(any(unix, windows)))]
    created: Option<std::time::SystemTime>,
}

impl ProofFileIdentity {
    /// Identity of the file behind an open descriptor.
    ///
    /// Windows has no stable `Metadata` accessor for file identity (the
    /// `windows_by_handle` feature is unstable, rust-lang/rust#63010), so the
    /// exact `(volume serial, file index)` pair — the analogue of unix
    /// `(dev, ino)` — is read through the handle instead of approximated by a
    /// creation timestamp.
    fn from_file(file: &File) -> io::Result<Self> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            let metadata = file.metadata()?;
            Ok(Self {
                device: metadata.dev(),
                inode: metadata.ino(),
            })
        }
        #[cfg(windows)]
        {
            let info = ay_sys::windows_fs::file_info(file)?;
            Ok(Self {
                volume_serial_number: info.volume_serial_number,
                file_index: info.file_index,
            })
        }
        #[cfg(not(any(unix, windows)))]
        {
            Ok(Self {
                created: file.metadata()?.created().ok(),
            })
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PublishedDimacsProof {
    identity: ProofFileIdentity,
    len: u64,
    sha256: Sha256Digest,
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
const DIMACS_PROOF_STAGING_ATTEMPTS: u64 = 128;
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
const DIMACS_PROOF_STAGING_PREFIX: &str = ".ay-dimacs-proof-";
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
static DIMACS_PROOF_STAGING_NONCE: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OwnedDimacsProofLocation {
    Anonymous,
    Staged,
    Public,
    Removed,
}

struct OwnedDimacsProof {
    descriptor: File,
    identity: ProofFileIdentity,
    staging_path: Option<PathBuf>,
    location: OwnedDimacsProofLocation,
    write_failed: Arc<AtomicBool>,
    published: Option<PublishedDimacsProof>,
    status_reservation: Option<DimacsProofStatusReservation>,
    invalidation: DimacsPublicationInvalidation,
    /// What an exit that cannot take this registry's lock can reach.
    custody: Arc<DimacsProofCustody>,
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
struct DimacsProofStatusReservation {
    proof_path: PathBuf,
    status_path: PathBuf,
    lock_path: PathBuf,
    lock_descriptor: File,
    lock_identity: ProofFileIdentity,
    /// Reachable by an exit wherever the run holds the reservation
    /// (status_custody.rs).
    custody: Arc<DimacsStatusCustody>,
}

#[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
struct DimacsProofStatusReservation;

struct RetainedDimacsPublication {
    descriptor: File,
    path: PathBuf,
    identity: ProofFileIdentity,
    len: u64,
    sha256: Sha256Digest,
    label: &'static str,
    invalidation: DimacsPublicationInvalidation,
    recheck: DimacsPublicationRecheck,
}

#[derive(Clone, Copy)]
enum DimacsPublicationInvalidation {
    Empty,
    Proof { binary: bool },
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InjectedDimacsProofCreateFailure {
    Identity,
    Clone,
}

#[cfg(test)]
std::thread_local! {
    #[cfg(any(target_os = "linux", target_os = "macos", windows))]
    static INJECTED_DIMACS_PROOF_CREATE_FAILURE:
        std::cell::Cell<Option<InjectedDimacsProofCreateFailure>> = const { std::cell::Cell::new(None) };
    #[cfg(any(target_os = "linux", target_os = "macos", windows))]
    static INJECTED_DIMACS_PROOF_CLEANUP_FAILURE:
        std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    #[cfg(any(target_os = "linux", target_os = "macos", windows))]
    static INJECTED_DIMACS_PROOF_CLEANUP_REPLACEMENT:
        std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    #[cfg(target_os = "linux")]
    static INJECTED_OPTIONAL_DIMACS_WRITER_FAILURE:
        std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    #[cfg(any(target_os = "linux", target_os = "macos", windows))]
    static INJECTED_DIMACS_STATUS_LOCK_IDENTITY_FAILURE:
        std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    #[cfg(target_os = "linux")]
    static INJECTED_ANONYMOUS_DIMACS_STAGING_ERROR:
        std::cell::Cell<Option<i32>> = const { std::cell::Cell::new(None) };
    #[cfg(any(target_os = "linux", target_os = "macos", windows))]
    static INJECTED_DIMACS_RENAME_NOREPLACE_ERROR:
        std::cell::Cell<Option<i32>> = const { std::cell::Cell::new(None) };
}

#[cfg(all(test, target_os = "linux"))]
fn inject_dimacs_proof_identity_failure_once() {
    INJECTED_DIMACS_PROOF_CREATE_FAILURE.with(|failure| {
        failure.set(Some(InjectedDimacsProofCreateFailure::Identity));
    });
}

#[cfg(all(test, target_os = "linux"))]
fn inject_dimacs_proof_clone_failure_once() {
    INJECTED_DIMACS_PROOF_CREATE_FAILURE.with(|failure| {
        failure.set(Some(InjectedDimacsProofCreateFailure::Clone));
    });
}

#[cfg(all(test, target_os = "linux"))]
fn inject_dimacs_proof_cleanup_failure_once() {
    INJECTED_DIMACS_PROOF_CLEANUP_FAILURE.with(|failure| failure.set(true));
}

#[cfg(all(test, target_os = "linux"))]
fn inject_dimacs_proof_cleanup_replacement_once() {
    INJECTED_DIMACS_PROOF_CLEANUP_REPLACEMENT.with(|replacement| replacement.set(true));
}

#[cfg(all(test, target_os = "linux"))]
fn inject_optional_dimacs_writer_failure_once() {
    INJECTED_OPTIONAL_DIMACS_WRITER_FAILURE.with(|failure| failure.set(true));
}

#[cfg(all(test, target_os = "linux"))]
fn inject_dimacs_status_lock_identity_failure_once() {
    INJECTED_DIMACS_STATUS_LOCK_IDENTITY_FAILURE.with(|failure| failure.set(true));
}

#[cfg(all(test, target_os = "linux"))]
fn inject_anonymous_dimacs_staging_error_once(raw_os_error: i32) {
    INJECTED_ANONYMOUS_DIMACS_STAGING_ERROR.with(|error| error.set(Some(raw_os_error)));
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
fn inject_dimacs_rename_noreplace_error_once(raw_os_error: i32) {
    INJECTED_DIMACS_RENAME_NOREPLACE_ERROR.with(|error| error.set(Some(raw_os_error)));
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
fn take_injected_dimacs_proof_create_failure(expected: InjectedDimacsProofCreateFailure) -> bool {
    INJECTED_DIMACS_PROOF_CREATE_FAILURE.with(|failure| {
        if failure.get() == Some(expected) {
            failure.set(None);
            true
        } else {
            false
        }
    })
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
fn take_injected_dimacs_proof_cleanup_failure() -> bool {
    INJECTED_DIMACS_PROOF_CLEANUP_FAILURE.with(|failure| failure.replace(false))
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
fn take_injected_dimacs_proof_cleanup_replacement() -> bool {
    INJECTED_DIMACS_PROOF_CLEANUP_REPLACEMENT.with(|replacement| replacement.replace(false))
}

#[cfg(all(test, target_os = "linux"))]
fn take_injected_optional_dimacs_writer_failure() -> bool {
    INJECTED_OPTIONAL_DIMACS_WRITER_FAILURE.with(|failure| failure.replace(false))
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
fn take_injected_dimacs_status_lock_identity_failure() -> bool {
    INJECTED_DIMACS_STATUS_LOCK_IDENTITY_FAILURE.with(|failure| failure.replace(false))
}

#[cfg(all(test, target_os = "linux"))]
fn take_injected_anonymous_dimacs_staging_error() -> Option<i32> {
    INJECTED_ANONYMOUS_DIMACS_STAGING_ERROR.with(|error| error.replace(None))
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
fn take_injected_dimacs_rename_noreplace_error() -> Option<i32> {
    INJECTED_DIMACS_RENAME_NOREPLACE_ERROR.with(|error| error.replace(None))
}

fn owned_dimacs_proofs() -> &'static Mutex<HashMap<PathBuf, OwnedDimacsProof>> {
    static OWNED: OnceLock<Mutex<HashMap<PathBuf, OwnedDimacsProof>>> = OnceLock::new();
    OWNED.get_or_init(|| Mutex::new(HashMap::new()))
}

fn dimacs_proof_registry_error() -> io::Error {
    io::Error::other("DIMACS proof ownership registry is poisoned")
}

fn resolved_dimacs_proof_path(path: &str) -> io::Result<PathBuf> {
    crate::run::resolve_artifact_target(Path::new(path))
}

/// Arm the process-exit sweep that releases unpublished proof transactions.
///
/// Called once, when the first status transaction is reserved or proof
/// generation is registered — before its status lock or staging file exists on
/// disk, where the registry, a `static` that runs no destructor, or a status
/// custody will be its only owner. Registration is deliberately
/// lazy: a run that never reserves a proof target has nothing to release and
/// pays nothing.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn arm_abandoned_dimacs_proof_sweep() {
    static ARMED: OnceLock<()> = OnceLock::new();
    ARMED.get_or_init(|| {
        if !ay_sys::at_process_exit(sweep_abandoned_dimacs_proof_transactions) {
            safe_eprintln!(
                "c Warning: could not arm the DIMACS proof staging sweep; an abnormal exit will strand its staging file"
            );
        }
    });
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
extern "C" fn sweep_abandoned_dimacs_proof_transactions() {
    discard_abandoned_dimacs_proof_transactions();
    // What the registry could not reach, or never held (status_custody.rs).
    // A current marker goes stale only with the proofs of an unanswered run.
    settle_open_dimacs_status_custodies(crate::run_claimed_unanswered());
}

/// Filename prefix every staging entry reserved by THIS process carries.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn abandoned_dimacs_proof_owner_prefix() -> String {
    format!("{DIMACS_PROOF_STAGING_PREFIX}{}-", std::process::id())
}

/// Whether this entry still owns a named staging file that THIS process
/// reserved.
///
/// The producing PID is re-read from the staging file name rather than trusted
/// from the registry: `ay` supervises every solve behind a `fork()`, and the
/// child inherits a byte-for-byte copy of this map. Only the process whose PID
/// names the stage may remove it — otherwise a parent could unlink the stage
/// its live solve child is still writing.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn owns_abandoned_dimacs_proof_stage(state: &OwnedDimacsProof, owner_prefix: &str) -> bool {
    state.location == OwnedDimacsProofLocation::Staged
        && state
            .staging_path
            .as_deref()
            .and_then(Path::file_name)
            .and_then(std::ffi::OsStr::to_str)
            .is_some_and(|name| name.starts_with(owner_prefix))
}

/// Whether this entry is a transaction the process is about to abandon: no seal
/// was ever recorded, and it still holds a status lock or a staging file of its
/// own. A sealed generation fails the first test and is therefore never a
/// candidate for removal.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn is_abandoned_dimacs_proof_transaction(state: &OwnedDimacsProof, owner_prefix: &str) -> bool {
    state.published.is_none()
        && (state.status_reservation.is_some()
            || owns_abandoned_dimacs_proof_stage(state, owner_prefix))
}

/// Discard the named staging file of an abandoned proof generation.
///
/// Deliberately NOT the quarantine dance [`cleanup_owned_dimacs_proof_state`]
/// performs. That one guards a PUBLIC pathname another process may legitimately
/// own, and pays for the guarantee with a round trip through a private
/// directory beside the target. A staging pathname is private to this process —
/// `create_named_dimacs_staging_file` reserved it with `O_EXCL` under this PID
/// and a nonce that is never reused — so authenticating the visible inode
/// against the descriptor this run still holds is the whole guarantee here, and
/// the exit path leaves nothing behind.
///
/// The bytes are destroyed through the descriptor BEFORE the unlink, so an
/// abandoned multi-gigabyte stage is reclaimed even when the unlink itself
/// fails.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn discard_abandoned_dimacs_proof_stage(state: &mut OwnedDimacsProof) -> io::Result<()> {
    let Some(staging_path) = state.staging_path.as_deref() else {
        return Ok(());
    };
    let visible = match open_dimacs_regular_file(staging_path) {
        Ok(visible) => visible,
        // An unanswered exit already reclaimed and unlinked it through its
        // custody, without this registry's lock.
        Err(error) if error.kind() == io::ErrorKind::NotFound && state.custody.is_abandoned() => {
            state.staging_path = None;
            state.location = OwnedDimacsProofLocation::Removed;
            return Ok(());
        }
        Err(error) => return Err(error),
    };
    let visible_identity = regular_file_identity(&visible, staging_path)?;
    drop(visible);
    if visible_identity != state.identity {
        return Err(io::Error::other(format!(
            "abandoned DIMACS proof staging path '{}' no longer names this run's generation; it was preserved",
            staging_path.display()
        )));
    }
    invalidate_dimacs_descriptor(&state.descriptor, state.invalidation)?;
    std::fs::remove_file(staging_path)?;
    state.staging_path = None;
    state.location = OwnedDimacsProofLocation::Removed;
    Ok(())
}

/// Release every proof transaction this process opened and never settled.
///
/// A proof generation lives between `create_owned_dimacs_proof_file_with_status`
/// (which reserves a `.ay-status.lock` transaction for a synthesized default and
/// a `.ay-dimacs-proof-<pid>-<nonce>.stage` sibling of the proof target) and
/// `seal_owned_dimacs_proof` (which renames the stage onto the target). In
/// between, both artifacts are reachable only through this registry — and the
/// registry is a `static`, which runs no destructor, in a process that ends
/// through `process::exit` on every timeout, SIGTERM, memory abort and fatal
/// CLI error. Nothing unlinked them: a sweep of this repository's benchmark tree
/// on 2026-08-27 found 86 stranded stages holding 40.1 GB, the oldest from
/// 7 August, plus two stranded status locks — and a stranded lock is worse than
/// wasted space, because `create_dimacs_status_reservation` fails closed on it
/// and poisons that proof path for every later run.
///
/// A sealed proof can never be removed here:
///
///  * an entry with a recorded seal is skipped outright;
///  * only a generation still in [`OwnedDimacsProofLocation::Staged`] is
///    unlinked, and publication clears that state under the same lock this
///    holds, in the same critical section as the rename;
///  * the pathname unlinked is the staging name, never the proof target, and
///    after publication that name no longer exists at all — the rename consumed
///    it, so a sweep that observes a torn registry finds nothing to remove; and
///  * the unlink is authenticated against the retained descriptor, so a stage
///    replaced by an unrelated object is preserved and reported.
///
/// `try_lock`, never `lock`: the exiting thread may itself hold the registry
/// lock — a certification failure exits from inside it — and a solver thread
/// may hold it across a whole-proof hash. Blocking here would hang the process
/// instead of leaking a file, which is far worse. Losing the race leaves the
/// old behaviour for that one entry.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn discard_abandoned_dimacs_proof_transactions() {
    let Ok(mut owned) = owned_dimacs_proofs().try_lock() else {
        return;
    };
    let owner_prefix = abandoned_dimacs_proof_owner_prefix();
    let abandoned: Vec<PathBuf> = owned
        .iter()
        .filter(|(_, state)| is_abandoned_dimacs_proof_transaction(state, &owner_prefix))
        .map(|(resolved, _)| resolved.clone())
        .collect();
    for resolved in abandoned {
        let Some(state) = owned.get_mut(&resolved) else {
            continue;
        };
        // The reserved status transaction settles as `stale-not-current`: the
        // run ended without a certificate, which is exactly what that marker
        // states, and publishing it releases the lock pathname.
        let status = match state.status_reservation.take() {
            // An unanswered exit already settled it stale-not-current.
            Some(reservation) if reservation.custody.settled_by_exit() => Ok(()),
            Some(reservation) => {
                publish_reserved_dimacs_proof_status(reservation, "stale-not-current", None)
                    .map(drop)
            }
            None => Ok(()),
        };
        let stage = discard_abandoned_dimacs_proof_stage(state);
        if let Err(error) = &stage {
            safe_eprintln!(
                "c Warning: failed to discard abandoned DIMACS proof staging for {}: {error}",
                resolved.display()
            );
        }
        if let Err(error) = &status {
            safe_eprintln!(
                "c Warning: failed to settle the abandoned DIMACS proof status transaction for {}: {error}",
                resolved.display()
            );
        }
        // Retain the entry — and with it the authoritative descriptor — when
        // either half failed, matching `remove_owned_dimacs_proof`.
        if stage.is_ok() && status.is_ok() {
            owned.remove(&resolved);
        }
    }
}

fn owned_dimacs_proof_write_failure_flag(path: &str) -> io::Result<Arc<AtomicBool>> {
    let resolved = resolved_dimacs_proof_path(path)?;
    owned_dimacs_proofs()
        .lock()
        .map_err(|_| dimacs_proof_registry_error())?
        .get(&resolved)
        .map(|state| Arc::clone(&state.write_failed))
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                format!(
                    "no active DIMACS proof writer exists for '{}'",
                    resolved.display()
                ),
            )
        })
}

/// Regression cover for the abandoned-transaction sweep (#68): AY stranded 86
/// staging files holding 40.1 GB, plus two status locks, because the registry is
/// a `static` and every abnormal exit runs `process::exit`.
///
/// Each case drives the ONE registry entry it created rather than
/// [`discard_abandoned_dimacs_proof_transactions`], which sweeps the whole
/// process: the test harness runs these in parallel with the rest of the DIMACS
/// suite, and a process-wide sweep would remove the unsealed proofs those tests
/// are still holding.
#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
mod abandoned_staging_sweep_tests {
    use super::*;

    /// Reserve a proof target that is backed by a NAMED staging file on every
    /// platform. Linux prefers an anonymous `O_TMPFILE` inode, which has no
    /// pathname and therefore nothing to strand, so the fallback is forced
    /// there with the documented "filesystem cannot stage anonymously" errno.
    fn reserve_named_stage(path: &str) -> File {
        #[cfg(target_os = "linux")]
        inject_anonymous_dimacs_staging_error_once(nix::libc::EOPNOTSUPP);
        create_owned_dimacs_proof_file(path).expect("reserve proof")
    }

    fn staging_entries(parent: &Path) -> Vec<PathBuf> {
        std::fs::read_dir(parent)
            .expect("read proof parent")
            .map(|entry| entry.expect("read proof parent entry").path())
            .filter(|path| {
                path.file_name()
                    .and_then(std::ffi::OsStr::to_str)
                    .is_some_and(|name| name.starts_with(DIMACS_PROOF_STAGING_PREFIX))
            })
            .collect()
    }

    /// Apply the sweep to exactly one registered proof target, reporting
    /// whether it was selected as abandoned.
    fn sweep_one(path: &str) -> bool {
        let resolved = resolved_dimacs_proof_path(path).expect("resolve proof target");
        let mut owned = owned_dimacs_proofs().lock().expect("registry lock");
        let state = owned.get_mut(&resolved).expect("registered proof");
        if !is_abandoned_dimacs_proof_transaction(state, &abandoned_dimacs_proof_owner_prefix()) {
            return false;
        }
        discard_abandoned_dimacs_proof_stage(state).expect("discard abandoned stage");
        owned.remove(&resolved);
        true
    }

    #[test]
    fn sweep_discards_the_stage_of_an_abandoned_proof() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("abandoned.drat");
        let path_text = path.to_str().expect("UTF-8 path");
        let mut proof = reserve_named_stage(path_text);
        Write::write_all(&mut proof, b"0\n").expect("write proof");
        Write::flush(&mut proof).expect("flush proof");
        assert_eq!(
            staging_entries(dir.path()).len(),
            1,
            "an unsealed proof must be staged under a private sibling name"
        );

        assert!(sweep_one(path_text), "an unsealed stage is abandoned");
        assert!(
            staging_entries(dir.path()).is_empty(),
            "the sweep must leave no staging residue beside the proof target"
        );
        assert!(!path.exists(), "the sweep must never publish the stage");
    }

    #[test]
    fn sweep_preserves_a_sealed_proof() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("sealed.drat");
        let path_text = path.to_str().expect("UTF-8 path");
        let mut proof = reserve_named_stage(path_text);
        Write::write_all(&mut proof, b"0\n").expect("write proof");
        drop(proof);
        let sealed = seal_owned_dimacs_proof(path_text).expect("seal proof");

        assert!(
            !sweep_one(path_text),
            "a sealed proof is never an abandoned transaction"
        );
        assert_eq!(
            std::fs::read(&path).expect("read published proof"),
            b"0\n",
            "the published proof must survive the exit sweep byte for byte"
        );
        assert_eq!(
            read_published_dimacs_proof(path_text, sealed.sha256).expect("authenticated read"),
            b"0\n"
        );
        assert!(
            staging_entries(dir.path()).is_empty(),
            "publication consumed the staging name"
        );
        remove_owned_dimacs_proof(path_text).expect("release the sealed proof");
    }
}
