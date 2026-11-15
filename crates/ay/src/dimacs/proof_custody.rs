// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Custody of one proof generation, reachable from any thread without the
/// registry lock.
///
/// A run that ends without an answer must not leave its proof behind, and the
/// registry alone cannot promise that: the thread that ends a timed-out run is
/// a watchdog, while the main thread may hold the registry lock for tens of
/// seconds as it seals and re-hashes a large proof. Measured on 166e1e5a
/// (2026-09-13): the solve answered UNSAT at 248.2 s, its 2.73 GB proof was
/// published at the target at 248.3 s, and `s UNSATISFIABLE` followed only at
/// 295.3 s. A run whose budget ended inside those 47 s printed `s UNKNOWN` from
/// the watchdog and left the whole proof at the target.
///
/// Custody is the part of a generation such an exit can act on: its target and
/// staging names, its inode identity, a descriptor of its own, and one state
/// that the seal and the exit settle by compare-and-swap:
///
///  * open: being written, and the seal may still publish it;
///  * publishing: the seal is renaming or linking it onto the target;
///  * published: it is at the target;
///  * abandoned: the run will not answer with it. The seal refuses to publish
///    it, its writer drops buffered bytes unwritten and writes nothing more,
///    and the exit reclaims its bytes and removes its names.
struct DimacsProofCustody {
    state: std::sync::atomic::AtomicU8,
    target: PathBuf,
    staging_path: Option<PathBuf>,
    identity: ProofFileIdentity,
    /// Owned by the custody alone, so an exit can reclaim the bytes whatever
    /// name the inode has, and so its number is never reused while the
    /// custody is reachable.
    descriptor: File,
    /// The process that created the generation. `ay` supervises solves behind
    /// `fork()`, and a child inherits this list; only the creator settles it.
    owner_pid: u32,
    /// Whether this generation is published on the competition fast path
    /// (`dimacs_fast_publication`): its writer hashes the proof as it writes,
    /// and the seal and the verdict gates never read the proof back.
    fast_publication: bool,
    /// The writer's digest, recorded once when a live writer is dropped.
    streamed: OnceLock<StreamedDimacsProofDigest>,
}

/// The SHA-256 of every byte a fast-publication writer put in its proof, taken
/// as the bytes were written (proof_writer.rs), so the seal needs no read-back.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct StreamedDimacsProofDigest {
    len: u64,
    sha256: Sha256Digest,
}

/// How a retained publication is re-checked between authorization and verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DimacsPublicationRecheck {
    /// Re-hash the retained descriptor and the visible path.
    Bytes,
    /// Check identity, link count and length only, on both. For a fast-
    /// publication proof, where no in-process consumer reads the proof's bytes
    /// (see `dimacs_fast_publication`).
    Identity,
}

const DIMACS_PROOF_CUSTODY_OPEN: u8 = 0;
const DIMACS_PROOF_CUSTODY_PUBLISHING: u8 = 1;
const DIMACS_PROOF_CUSTODY_PUBLISHED: u8 = 2;
const DIMACS_PROOF_CUSTODY_ABANDONED: u8 = 3;

/// How long an abandoning exit waits for a publication already in flight. A
/// publication is one rename or link system call; the bound only covers a
/// descheduled sealing thread.
const DIMACS_PROOF_PUBLICATION_WAIT: std::time::Duration = std::time::Duration::from_secs(2);

impl DimacsProofCustody {
    fn new(
        target: PathBuf,
        staging_path: Option<PathBuf>,
        identity: ProofFileIdentity,
        descriptor: File,
        fast_publication: bool,
    ) -> Self {
        Self {
            state: std::sync::atomic::AtomicU8::new(DIMACS_PROOF_CUSTODY_OPEN),
            target,
            staging_path,
            identity,
            descriptor,
            owner_pid: std::process::id(),
            fast_publication,
            streamed: OnceLock::new(),
        }
    }

    /// Record the digest a live writer took of every byte it wrote. A digest
    /// in an abandoned custody is inert: publication is decided by the
    /// compare-and-swap in the seal, never by the digest.
    fn record_streamed_digest(&self, digest: StreamedDimacsProofDigest) {
        let recorded = self.streamed.set(digest);
        debug_assert!(recorded.is_ok(), "a generation has one writer");
    }

    /// The writer's digest, when this is a fast-publication generation whose
    /// writer finished cleanly; `None` sends the seal back to a read-back hash.
    fn streamed_digest(&self) -> Option<StreamedDimacsProofDigest> {
        self.fast_publication
            .then(|| self.streamed.get().copied())
            .flatten()
    }

    fn is_abandoned(&self) -> bool {
        self.state.load(Ordering::SeqCst) == DIMACS_PROOF_CUSTODY_ABANDONED
    }

    /// Claim the right to put this generation at its target, immediately
    /// before the rename or link. Fails once the generation is abandoned, so no
    /// publication can follow an unanswered exit's discard.
    fn begin_publication(&self) -> io::Result<()> {
        match self.state.compare_exchange(
            DIMACS_PROOF_CUSTODY_OPEN,
            DIMACS_PROOF_CUSTODY_PUBLISHING,
            Ordering::SeqCst,
            Ordering::SeqCst,
        ) {
            Ok(_) => Ok(()),
            Err(DIMACS_PROOF_CUSTODY_ABANDONED) => Err(io::Error::other(format!(
                "DIMACS proof output '{}' was abandoned by an unanswered exit and is not published",
                self.target.display()
            ))),
            Err(state) => Err(io::Error::other(format!(
                "DIMACS proof output '{}' is not open for publication (custody state {state})",
                self.target.display()
            ))),
        }
    }

    /// Record the outcome of the rename or link `begin_publication` claimed.
    /// Only the sealing thread leaves the publishing state: an abandoning exit
    /// waits for it.
    fn end_publication(&self, published: bool) {
        let outcome = if published {
            DIMACS_PROOF_CUSTODY_PUBLISHED
        } else {
            DIMACS_PROOF_CUSTODY_OPEN
        };
        let settled = self.state.compare_exchange(
            DIMACS_PROOF_CUSTODY_PUBLISHING,
            outcome,
            Ordering::SeqCst,
            Ordering::SeqCst,
        );
        debug_assert!(settled.is_ok(), "only the seal leaves the publishing state");
    }

    /// Mark the generation abandoned, waiting out a publication in flight.
    /// Returns false only when a publication outlasted the wait; the caller
    /// then discards on a best-effort basis.
    fn abandon(&self) -> bool {
        self.abandon_within(DIMACS_PROOF_PUBLICATION_WAIT)
    }

    fn abandon_within(&self, wait: std::time::Duration) -> bool {
        let deadline = std::time::Instant::now() + wait;
        loop {
            match self.state.load(Ordering::SeqCst) {
                DIMACS_PROOF_CUSTODY_ABANDONED => return true,
                DIMACS_PROOF_CUSTODY_PUBLISHING => {
                    if std::time::Instant::now() >= deadline {
                        return false;
                    }
                    std::thread::sleep(std::time::Duration::from_millis(1));
                }
                state => {
                    if self
                        .state
                        .compare_exchange(
                            state,
                            DIMACS_PROOF_CUSTODY_ABANDONED,
                            Ordering::SeqCst,
                            Ordering::SeqCst,
                        )
                        .is_ok()
                    {
                        return true;
                    }
                }
            }
        }
    }

    /// Reclaim an abandoned generation's bytes and remove every name it has,
    /// without the registry lock. Truncation comes first, through the
    /// custody's own descriptor, so the bytes are gone whatever name the inode
    /// has, including one a concurrent cleanup is moving; the names follow,
    /// the private stage before the public target.
    #[cfg(any(target_os = "linux", target_os = "macos", windows))]
    fn discard(&self) -> io::Result<()> {
        let truncated = self.descriptor.set_len(0);
        let stage = match self.staging_path.as_deref() {
            Some(stage) => remove_private_dimacs_custody_name(stage, self.identity),
            None => Ok(()),
        };
        let target = remove_public_dimacs_custody_name(&self.target, self.identity);
        truncated.and(stage).and(target)
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
    fn discard(&self) -> io::Result<()> {
        self.descriptor.set_len(0)
    }
}

fn dimacs_proof_custodies() -> &'static Mutex<Vec<Arc<DimacsProofCustody>>> {
    static CUSTODIES: OnceLock<Mutex<Vec<Arc<DimacsProofCustody>>>> = OnceLock::new();
    CUSTODIES.get_or_init(|| Mutex::new(Vec::new()))
}

/// Held only to push, remove, or copy the list, never across I/O, so a watchdog
/// never waits behind a seal; a poisoned list is still consistent.
fn locked_dimacs_proof_custodies() -> std::sync::MutexGuard<'static, Vec<Arc<DimacsProofCustody>>> {
    dimacs_proof_custodies()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// Give a new generation its custody and register it. Registered before the
/// claim check, so an unanswered exit that claims the run later sees it; one
/// that claimed it earlier may have missed it, so it is abandoned and discarded
/// here and can never be published.
fn register_dimacs_proof_custody(
    target: PathBuf,
    staging_path: Option<PathBuf>,
    identity: ProofFileIdentity,
    descriptor: File,
    fast_publication: bool,
) -> Arc<DimacsProofCustody> {
    let custody = Arc::new(DimacsProofCustody::new(
        target,
        staging_path,
        identity,
        descriptor,
        fast_publication,
    ));
    locked_dimacs_proof_custodies().push(Arc::clone(&custody));
    remember_dimacs_proof_custody_for_memory_ceiling(&custody);
    if crate::run_claimed_unanswered() {
        custody.abandon();
        let _ = custody.discard();
    }
    custody
}

/// Forget a settled generation, closing the custody's descriptor once no exit
/// in progress still holds it.
fn release_dimacs_proof_custody(custody: &Arc<DimacsProofCustody>) {
    locked_dimacs_proof_custodies().retain(|held| !Arc::ptr_eq(held, custody));
}

fn owned_dimacs_proof_custody(path: &str) -> io::Result<Arc<DimacsProofCustody>> {
    let resolved = resolved_dimacs_proof_path(path)?;
    owned_dimacs_proofs()
        .lock()
        .map_err(|_| dimacs_proof_registry_error())?
        .get(&resolved)
        .map(|state| Arc::clone(&state.custody))
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                format!(
                    "no active DIMACS proof generation exists for '{}'",
                    resolved.display()
                ),
            )
        })
}

/// Whether the proof at `path` was sealed under its writer's streamed digest,
/// with no read-back: the competition fast publication (stats key
/// `sat.proof_digest_streamed`).
fn dimacs_proof_sealed_from_stream(path: &str) -> bool {
    let Ok(resolved) = resolved_dimacs_proof_path(path) else {
        return false;
    };
    let Ok(owned) = owned_dimacs_proofs().lock() else {
        return false;
    };
    owned.get(&resolved).is_some_and(|state| {
        match (state.published, state.custody.streamed_digest()) {
            (Some(published), Some(streamed)) => {
                published.sha256 == streamed.sha256 && published.len == streamed.len
            }
            _ => false,
        }
    })
}

/// Discard the proof generation at the configured path for a solve that will
/// not answer with it, on the main thread.
///
/// The generation is abandoned before the writer is dropped, so the writer
/// discards its buffered bytes instead of flushing them into a proof that is
/// about to go; its bytes and names are then reclaimed through its custody,
/// which leaves nothing beside the target, and the registry entry is settled.
fn discard_owned_dimacs_proof(solver: Option<&mut SatSolver>, proof_config: Option<&ProofConfig>) {
    let custody = proof_config.and_then(|proof| owned_dimacs_proof_custody(&proof.path).ok());
    if let Some(custody) = &custody {
        custody.abandon();
    }
    if let Some(solver) = solver {
        drop(solver.take_proof_writer());
    }
    if let Some(custody) = &custody {
        if let Err(error) = custody.discard() {
            safe_eprintln!(
                "c Warning: failed to discard the DIMACS proof {} of a solve that did not answer UNSAT: {error}",
                custody.target.display()
            );
        }
    }
    cleanup_dimacs_non_unsat_proof_paths(proof_config);
}

/// Discard every proof generation this process still holds, for an exit that
/// ends the run without an answer: the timeout, memory and termination
/// watchdogs, and every main-thread exit that prints no decisive verdict.
///
/// Never takes the registry lock, which the main thread may hold for tens of
/// seconds while it seals and re-hashes a large proof. The caller must have
/// claimed the run as unanswered first (`crate::claim_unanswered_outcome`),
/// so no decisive verdict can still publish one of these proofs.
///
/// The status custodies settle first. The run publishes its
/// `current-same-run` marker before it claims its verdict, so an exit can
/// meet a marker that names a proof it is about to discard, published or
/// still being published: the exit waits that publication out and rewrites
/// the marker `stale-not-current` before the proof goes, so no current
/// marker stands beside a discarded proof. Only a publication on another
/// thread that outlasts the wait can still rename its marker after the
/// proof is gone; the process-exit sweep revokes that marker if the
/// publication has finished by then.
pub(crate) fn discard_unanswered_dimacs_proofs() {
    discard_unanswered_dimacs_proofs_among(
        || locked_dimacs_status_custodies().clone(),
        || locked_dimacs_proof_custodies().clone(),
        DIMACS_PROOF_PUBLICATION_WAIT,
    );
}

/// [`discard_unanswered_dimacs_proofs`] over the status and proof custodies
/// the two lists yield, waiting at most `wait` for each status publication
/// in flight on another thread.
fn discard_unanswered_dimacs_proofs_among(
    statuses: impl FnOnce() -> Vec<Arc<DimacsStatusCustody>>,
    proofs: impl FnOnce() -> Vec<Arc<DimacsProofCustody>>,
    wait: std::time::Duration,
) {
    settle_dimacs_status_custodies_among(statuses, true, wait);
    let owner = std::process::id();
    for custody in proofs().iter().filter(|custody| custody.owner_pid == owner) {
        if !custody.abandon() {
            safe_eprintln!(
                "c Warning: DIMACS proof {} was still being published when the run ended unanswered; discarding it anyway",
                custody.target.display()
            );
        }
        if let Err(error) = custody.discard() {
            safe_eprintln!(
                "c Warning: failed to discard the DIMACS proof {} of an unanswered run: {error}",
                custody.target.display()
            );
        }
    }
}

/// Every proof generation's custody, for the allocator's hard memory ceiling,
/// which settles the run from inside the global allocator (2026-09-13). The
/// registry cannot serve there: its lock is held across allocations, so the
/// thread that breached may hold it. This table's lock never is. Its slots are
/// a fixed array of `Weak`, and nothing is allocated while the lock is held, so
/// no thread can breach inside it; the settling thread never waits on a thread
/// a breach has parked. A `Weak` keeps no descriptor open: a generation that
/// has ended upgrades to nothing, and its slot is reused.
const DIMACS_PROOF_CEILING_SLOTS: usize = 64;
type DimacsProofCeilingSlots =
    [Option<std::sync::Weak<DimacsProofCustody>>; DIMACS_PROOF_CEILING_SLOTS];
static DIMACS_PROOF_CEILING_CUSTODIES: Mutex<DimacsProofCeilingSlots> =
    Mutex::new([const { None }; DIMACS_PROOF_CEILING_SLOTS]);

fn remember_dimacs_proof_custody_for_memory_ceiling(custody: &Arc<DimacsProofCustody>) {
    let weak = Arc::downgrade(custody);
    let remembered = {
        let mut slots = DIMACS_PROOF_CEILING_CUSTODIES
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // Replacing a dead `Weak` may free its block; freeing never breaches.
        match slots
            .iter_mut()
            .find(|slot| slot.as_ref().is_none_or(|held| held.strong_count() == 0))
        {
            Some(slot) => {
                *slot = Some(weak);
                true
            }
            None => false,
        }
    };
    if !remembered {
        safe_eprintln!(
            "c Warning: more than {DIMACS_PROOF_CEILING_SLOTS} DIMACS proof generations are live; if the allocator's memory ceiling ends the run, it will not discard {}",
            custody.target.display()
        );
    }
}

/// Discard every proof generation this process still holds, for the
/// allocator's hard memory ceiling, exactly as [`discard_unanswered_dimacs_proofs`]
/// does for every other exit that ends the run without an answer: each is
/// abandoned, waiting out a publication in flight, then its bytes are
/// reclaimed and its names removed. Only the custody list differs: this reads
/// the ceiling's own table, since the breaching thread may hold the registry
/// lock. Returns how many generations it discarded and how many bytes they held.
///
/// Runs inside the global allocator on the settling thread
/// (`ay_sys::set_hard_memory_ceiling_settlement`): it holds no lock while it
/// allocates, and writes through `ay_sys::write_stderr_unlocked` only.
pub(crate) fn discard_dimacs_proofs_at_memory_ceiling() -> (usize, u64) {
    // A current marker goes stale before its proof goes, as in
    // `discard_unanswered_dimacs_proofs`.
    settle_dimacs_status_custodies_at_memory_ceiling();
    // Cloning a `Weak` only counts a reference: nothing allocates under the lock.
    let held: DimacsProofCeilingSlots = DIMACS_PROOF_CEILING_CUSTODIES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clone();
    let owner = std::process::id();
    let (mut discarded, mut bytes) = (0, 0);
    for custody in held.iter().flatten().filter_map(std::sync::Weak::upgrade) {
        if custody.owner_pid != owner {
            continue;
        }
        if !custody.abandon() {
            ay_sys::write_stderr_unlocked(
                b"c Warning: a DIMACS proof was still being published when the memory ceiling ended the run; discarding it anyway\n",
            );
        }
        let len = custody
            .descriptor
            .metadata()
            .map_or(0, |metadata| metadata.len());
        match custody.discard() {
            Ok(()) => {
                discarded += 1;
                bytes += len;
            }
            Err(_) => ay_sys::write_stderr_unlocked(
                b"c Warning: failed to discard a DIMACS proof of the run the memory ceiling ended\n",
            ),
        }
    }
    (discarded, bytes)
}
