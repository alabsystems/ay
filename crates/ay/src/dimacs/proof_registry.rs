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
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
struct DimacsProofStatusReservation {
    proof_path: PathBuf,
    status_path: PathBuf,
    lock_path: PathBuf,
    lock_descriptor: File,
    lock_identity: ProofFileIdentity,
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

#[cfg(test)]
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

#[cfg(all(test, target_os = "linux"))]
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

#[cfg(test)]
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
