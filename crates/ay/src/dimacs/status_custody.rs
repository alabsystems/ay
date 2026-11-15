// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Custody of one synthesized-default status reservation, reachable from any
/// thread without the registry lock.
///
/// A synthesized-default DIMACS proof reserves its status transaction before
/// anything else: `<proof>.ay-status.lock`, created with `O_EXCL`
/// (`create_dimacs_status_reservation`), which the run's publication rewrites
/// and renames onto `<proof>.ay-status`. Until the proof file exists, the
/// reservation lives only in a local variable, and afterwards only in the
/// registry, which an exit can take only with `try_lock`. An exit in either
/// window left the lock behind: every later run on that path then reports a
/// live transaction where none exists ("synthesized-default proof status
/// transaction ... is already active"). The `stale-not-current` marker an
/// exit leaves instead is the honest end state of every unanswered run; a
/// later run still declines to overwrite it, as after any unanswered run. MEASURED 2026-10-08 on 8a0e18584 under CPU contention:
/// `ay --quiet --memory 1 -T:20` on a two-clause CNF left
/// `t.cnf.drat.ay-status.lock` in 87 of 96 runs, and a pigeonhole instance at
/// `--memory 16` in 41 of 48. strace shows the lock created, then the memory
/// watchdog's `exit_group`, with no proof file in between.
///
/// The custody is registered once the lock carries its transaction header,
/// with a descriptor and an identity of its own. An exit that ends the run
/// unanswered, and the process-exit sweep, settle every custody still open
/// exactly as the registry sweep settles a registered reservation:
/// `stale-not-current`. The run's own publication or removal claims the
/// custody first, so the run and an exit never both write the marker:
///
///  * open: the run may still publish or remove the reservation;
///  * settling: the run is publishing or removing it;
///  * settled: the run published or removed it;
///  * current: the run published `current-same-run`, which names its proof.
///    An unanswered exit discards that proof, so it still settles the
///    marker, rewriting it `stale-not-current`: the run publishes the marker
///    before it claims its verdict, and no current marker may stand beside a
///    discarded proof;
///  * abandoned: an exit settled it, and the run may no longer publish it.
struct DimacsStatusCustody {
    state: std::sync::atomic::AtomicU8,
    lock_path: PathBuf,
    status_path: PathBuf,
    identity: ProofFileIdentity,
    /// Owned by the custody alone, so an exit can rewrite the marker without
    /// the reservation, wherever the run holds it.
    descriptor: File,
    /// The process that reserved the transaction. A forked child inherits
    /// the custody list and the process-exit sweep; only the creator settles.
    owner_pid: u32,
}

/// A claim on a status custody's settlement (`claim_settling`), held on the
/// thread that took it.
struct DimacsStatusSettlingClaim<'a> {
    custody: &'a DimacsStatusCustody,
    finished: bool,
    /// The claim this thread held before this one (`SETTLING_HERE`).
    enclosing: usize,
    /// Never sent to another thread, which `SETTLING_HERE` would not know.
    _thread: std::marker::PhantomData<*const ()>,
}

impl DimacsStatusSettlingClaim<'_> {
    /// Record the outcome of what the claim covered.
    fn finish(self, settled: bool) {
        self.end(if settled {
            DIMACS_STATUS_CUSTODY_SETTLED
        } else {
            DIMACS_STATUS_CUSTODY_OPEN
        });
    }

    /// The claim published `current-same-run`.
    fn finish_current(self) {
        self.end(DIMACS_STATUS_CUSTODY_CURRENT);
    }

    fn end(mut self, outcome: u8) {
        self.finished = true;
        self.custody.leave_settling(outcome);
        leave_dimacs_status_settling_here(self.enclosing);
    }
}

impl Drop for DimacsStatusSettlingClaim<'_> {
    fn drop(&mut self) {
        if !self.finished {
            self.custody.leave_settling(DIMACS_STATUS_CUSTODY_OPEN);
            leave_dimacs_status_settling_here(self.enclosing);
        }
    }
}

const DIMACS_STATUS_CUSTODY_OPEN: u8 = 0;
const DIMACS_STATUS_CUSTODY_SETTLING: u8 = 1;
const DIMACS_STATUS_CUSTODY_SETTLED: u8 = 2;
const DIMACS_STATUS_CUSTODY_ABANDONED: u8 = 3;
const DIMACS_STATUS_CUSTODY_CURRENT: u8 = 4;

impl DimacsStatusCustody {
    /// Claim the right to publish or remove the reservation. Fails once an
    /// exit has settled it, so no marker can follow an unanswered exit's.
    fn begin_settling(&self) -> io::Result<()> {
        match self.state.compare_exchange(
            DIMACS_STATUS_CUSTODY_OPEN,
            DIMACS_STATUS_CUSTODY_SETTLING,
            Ordering::SeqCst,
            Ordering::SeqCst,
        ) {
            Ok(_) => Ok(()),
            Err(DIMACS_STATUS_CUSTODY_ABANDONED) => Err(io::Error::other(format!(
                "DIMACS proof status transaction '{}' was settled stale-not-current by an unanswered exit",
                self.lock_path.display()
            ))),
            Err(state) => Err(io::Error::other(format!(
                "DIMACS proof status transaction '{}' is not open (custody state {state})",
                self.lock_path.display()
            ))),
        }
    }

    /// Record the outcome of what `begin_settling` claimed. A failed
    /// publication leaves the lock in place, so the custody reopens and an
    /// exit can still settle it. An exit on the claiming thread itself (the
    /// allocator's memory ceiling) may have taken the claim over: the custody
    /// is then abandoned, and stays so.
    fn leave_settling(&self, outcome: u8) {
        let left = self.state.compare_exchange(
            DIMACS_STATUS_CUSTODY_SETTLING,
            outcome,
            Ordering::SeqCst,
            Ordering::SeqCst,
        );
        debug_assert!(
            matches!(left, Ok(_) | Err(DIMACS_STATUS_CUSTODY_ABANDONED)),
            "only the run, or an exit on the claiming thread, leaves the settling state"
        );
    }

    /// [`Self::begin_settling`], released on drop: a panic between the claim
    /// and its outcome reopens the custody instead of leaving every exit to
    /// wait out the settling state.
    fn claim_settling(&self) -> io::Result<DimacsStatusSettlingClaim<'_>> {
        self.begin_settling()?;
        Ok(DimacsStatusSettlingClaim {
            custody: self,
            finished: false,
            enclosing: enter_dimacs_status_settling_here(self.address()),
            _thread: std::marker::PhantomData,
        })
    }

    /// This custody's address, which names it in `SETTLING_HERE`.
    fn address(&self) -> usize {
        std::ptr::from_ref(self).addr()
    }

    /// Whether an exit may still have to settle the custody: open, being
    /// settled, or holding a current marker an unanswered exit revokes.
    fn is_live(&self) -> bool {
        matches!(
            self.state.load(Ordering::SeqCst),
            DIMACS_STATUS_CUSTODY_OPEN
                | DIMACS_STATUS_CUSTODY_SETTLING
                | DIMACS_STATUS_CUSTODY_CURRENT
        )
    }

    fn settled_by_exit(&self) -> bool {
        self.state.load(Ordering::SeqCst) == DIMACS_STATUS_CUSTODY_ABANDONED
    }

    /// Settle the reservation `stale-not-current` for an exit, waiting out a
    /// publication in flight on another thread. With `revoke_current` (the
    /// exit discards this run's proofs), a `current-same-run` marker the run
    /// published is rewritten `stale-not-current` too. `Ok` also when nothing
    /// is left to settle.
    fn settle_at_exit(&self, revoke_current: bool) -> io::Result<()> {
        self.settle_at_exit_within(DIMACS_PROOF_PUBLICATION_WAIT, revoke_current)
    }

    fn settle_at_exit_within(
        &self,
        wait: std::time::Duration,
        revoke_current: bool,
    ) -> io::Result<()> {
        let deadline = std::time::Instant::now() + wait;
        loop {
            let state = self.state.load(Ordering::SeqCst);
            match state {
                DIMACS_STATUS_CUSTODY_SETTLED | DIMACS_STATUS_CUSTODY_ABANDONED => return Ok(()),
                DIMACS_STATUS_CUSTODY_CURRENT if !revoke_current => return Ok(()),
                // A claim this thread holds is never waited on: the memory
                // ceiling settles on the thread that crossed it, inside the
                // claim, and the claimed publication never resumes. The exit
                // takes the claim over below instead of spending the wait.
                DIMACS_STATUS_CUSTODY_SETTLING if !dimacs_status_settling_here(self.address()) => {
                    if std::time::Instant::now() >= deadline {
                        return Err(io::Error::other(format!(
                            "DIMACS proof status transaction '{}' was still being published when the run ended",
                            self.lock_path.display()
                        )));
                    }
                    std::thread::sleep(std::time::Duration::from_millis(1));
                }
                _ => {
                    if self
                        .state
                        .compare_exchange(
                            state,
                            DIMACS_STATUS_CUSTODY_ABANDONED,
                            Ordering::SeqCst,
                            Ordering::SeqCst,
                        )
                        .is_ok()
                    {
                        return self.publish_stale();
                    }
                }
            }
        }
    }

    /// Rewrite this run's lock as the `stale-not-current` marker and rename
    /// it into place, as `publish_reserved_dimacs_proof_status` does. A lock
    /// that is gone, or that is no longer this run's inode, is left alone,
    /// and the marker is settled instead if it is this run's inode
    /// ([`Self::revoke_published_marker`]); a lock whose marker already
    /// exists is removed. MEASURED: the main thread of a memout run
    /// re-reserves to mark its proof stale after the exit has settled the
    /// first reservation, and that second lock stranded the path beside the
    /// first marker in 71 of 96 runs.
    #[cfg(any(target_os = "linux", target_os = "macos", windows))]
    fn publish_stale(&self) -> io::Result<()> {
        match self.names_this_transaction(&self.lock_path) {
            Ok(true) => {}
            Ok(false) => return self.revoke_published_marker(),
            Err(error) => return self.revoke_published_marker().and(Err(error)),
        }
        let content = dimacs_proof_status_content("stale-not-current", None);
        // The rewrite truncates the lock first: a rewrite that fails (a full
        // disk, on the storage exit) would strand an empty lock, so it is
        // removed instead.
        if let Err(error) = rewrite_reserved_dimacs_proof_status(
            &self.descriptor,
            &self.lock_path,
            self.identity,
            content.as_bytes(),
        ) {
            return remove_public_dimacs_custody_name(&self.lock_path, self.identity).map_err(
                |removal| {
                    io::Error::other(format!("{error}; removing the lock also failed: {removal}"))
                },
            );
        }
        match rename_dimacs_noreplace(&self.lock_path, &self.status_path) {
            Ok(()) => Ok(()),
            // A marker is already in place (this run's own earlier
            // settlement, or an earlier run's): it is never clobbered, and
            // this transaction's lock must not strand the path either.
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                remove_public_dimacs_custody_name(&self.lock_path, self.identity)
            }
            Err(error) => Err(error),
        }
    }

    /// Whether `path` names this transaction's inode.
    #[cfg(any(target_os = "linux", target_os = "macos", windows))]
    fn names_this_transaction(&self, path: &Path) -> io::Result<bool> {
        match open_dimacs_regular_file(path) {
            Ok(visible) => Ok(regular_single_link_identity(&visible, path)
                .is_ok_and(|identity| identity == self.identity)),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
            Err(error) => Err(error),
        }
    }

    /// The run renamed the lock onto the marker before this exit settled the
    /// custody: a `current-same-run` publication, a publication that failed
    /// after its rename, or one this thread was making when the memory
    /// ceiling stopped it. The marker is rewritten `stale-not-current` in
    /// place, or removed if that rewrite fails, so no current marker is left
    /// for a proof the exit discards. A marker that is gone, or that is no
    /// longer this run's inode, is left alone.
    #[cfg(any(target_os = "linux", target_os = "macos", windows))]
    fn revoke_published_marker(&self) -> io::Result<()> {
        if !self.names_this_transaction(&self.status_path)? {
            return Ok(());
        }
        let content = dimacs_proof_status_content("stale-not-current", None);
        rewrite_reserved_dimacs_proof_status(
            &self.descriptor,
            &self.status_path,
            self.identity,
            content.as_bytes(),
        )
        .or_else(|error| {
            remove_public_dimacs_custody_name(&self.status_path, self.identity).map_err(|removal| {
                io::Error::other(format!(
                    "{error}; removing the marker also failed: {removal}"
                ))
            })
        })
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
    fn publish_stale(&self) -> io::Result<()> {
        Ok(())
    }
}

fn dimacs_status_custodies() -> &'static Mutex<Vec<Arc<DimacsStatusCustody>>> {
    static CUSTODIES: OnceLock<Mutex<Vec<Arc<DimacsStatusCustody>>>> = OnceLock::new();
    CUSTODIES.get_or_init(|| Mutex::new(Vec::new()))
}

/// Held only to push, prune, or copy the list, never across I/O.
fn locked_dimacs_status_custodies() -> std::sync::MutexGuard<'static, Vec<Arc<DimacsStatusCustody>>>
{
    dimacs_status_custodies()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// The status custodies for the allocator's hard memory ceiling, which
/// settles the run from inside the global allocator and so may not allocate
/// under a lock (as `DIMACS_PROOF_CEILING_CUSTODIES`).
const DIMACS_STATUS_CEILING_SLOTS: usize = 16;
type DimacsStatusCeilingSlots =
    [Option<std::sync::Weak<DimacsStatusCustody>>; DIMACS_STATUS_CEILING_SLOTS];
static DIMACS_STATUS_CEILING_CUSTODIES: Mutex<DimacsStatusCeilingSlots> =
    Mutex::new([const { None }; DIMACS_STATUS_CEILING_SLOTS]);

/// Give a new reservation its custody and register it, before the lock
/// leaves the function that created it. A run an unanswered exit already
/// claimed settles it at once: that exit may have missed it.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn register_dimacs_status_custody(
    lock_path: PathBuf,
    status_path: PathBuf,
    identity: ProofFileIdentity,
    descriptor: File,
) -> Arc<DimacsStatusCustody> {
    let custody = Arc::new(DimacsStatusCustody {
        state: std::sync::atomic::AtomicU8::new(DIMACS_STATUS_CUSTODY_OPEN),
        lock_path,
        status_path,
        identity,
        descriptor,
        owner_pid: std::process::id(),
    });
    {
        let mut held = locked_dimacs_status_custodies();
        held.retain(|held| held.is_live());
        held.push(Arc::clone(&custody));
    }
    remember_dimacs_status_custody_for_memory_ceiling(&custody);
    if crate::run_claimed_unanswered() {
        let _ = custody.settle_at_exit(true);
    }
    custody
}

/// Register the custody of the lock `create_dimacs_status_reservation` just
/// wrote, with a descriptor of its own. On failure the lock is removed, as on
/// every other failure of that function.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn register_reserved_dimacs_status_custody(
    lock_path: &Path,
    status_path: &Path,
    lock_descriptor: &File,
    lock_identity: ProofFileIdentity,
) -> io::Result<Arc<DimacsStatusCustody>> {
    let descriptor = lock_descriptor.try_clone().map_err(|error| {
        status_transaction_error(
            error,
            remove_authenticated_visible_file(
                lock_path,
                lock_descriptor,
                lock_identity,
                "DIMACS proof status transaction lock",
                DimacsPublicationInvalidation::Empty,
            ),
            "DIMACS proof status transaction lock",
        )
    })?;
    Ok(register_dimacs_status_custody(
        lock_path.to_path_buf(),
        status_path.to_path_buf(),
        lock_identity,
        descriptor,
    ))
}

fn remember_dimacs_status_custody_for_memory_ceiling(custody: &Arc<DimacsStatusCustody>) {
    let weak = Arc::downgrade(custody);
    let remembered = {
        let mut slots = DIMACS_STATUS_CEILING_CUSTODIES
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        match slots.iter_mut().find(|slot| {
            slot.as_ref()
                .and_then(std::sync::Weak::upgrade)
                .is_none_or(|held| !held.is_live())
        }) {
            Some(slot) => {
                *slot = Some(weak);
                true
            }
            None => false,
        }
    };
    if !remembered {
        safe_eprintln!(
            "c Warning: more than {DIMACS_STATUS_CEILING_SLOTS} DIMACS proof status transactions are open; if the allocator's memory ceiling ends the run, it will not settle {}",
            custody.lock_path.display()
        );
    }
}

/// Settle every status custody this process still holds open, for an exit
/// that ends the run unanswered and for the process-exit sweep.
/// `revoke_current`: the run ended unanswered, so its proofs are discarded
/// and a `current-same-run` marker it published goes stale with them; the
/// process-exit sweep of a run that printed its verdict leaves that marker.
/// Either way a publication that failed after its rename reopened its
/// custody, and the marker it left, which authorizes nothing, is rewritten
/// `stale-not-current`.
fn settle_open_dimacs_status_custodies(revoke_current: bool) {
    settle_dimacs_status_custodies_among(
        || locked_dimacs_status_custodies().clone(),
        revoke_current,
        DIMACS_PROOF_PUBLICATION_WAIT,
    );
}

/// [`settle_open_dimacs_status_custodies`] over the custodies `custodies`
/// yields, waiting at most `wait` for each publication in flight on another
/// thread.
fn settle_dimacs_status_custodies_among(
    custodies: impl FnOnce() -> Vec<Arc<DimacsStatusCustody>>,
    revoke_current: bool,
    wait: std::time::Duration,
) {
    // Waited out first, so a reservation still being created is registered
    // before the list is read.
    let reserving =
        (!wait_out_dimacs_status_reservations(DIMACS_PROOF_PUBLICATION_WAIT)).then(|| {
            "a DIMACS proof status transaction was still being reserved when the run ended"
                .to_string()
        });
    let owner = std::process::id();
    let custodies = custodies();
    let failures = custodies
        .iter()
        .filter(|custody| custody.owner_pid == owner)
        .filter_map(|custody| {
            custody.settle_at_exit_within(wait, revoke_current).err().map(|error| {
                format!(
                    "failed to settle the DIMACS proof status transaction {} of an unanswered run: {error}",
                    custody.lock_path.display()
                )
            })
        });
    for warning in reserving.into_iter().chain(failures) {
        safe_eprintln!("c Warning: {warning}");
    }
}

/// [`settle_open_dimacs_status_custodies`] for the allocator's hard memory
/// ceiling, which ends the run unanswered: it reads the ceiling's own table,
/// holds no lock while it allocates, and writes through
/// `ay_sys::write_stderr_unlocked` only.
fn settle_dimacs_status_custodies_at_memory_ceiling() {
    if !wait_out_dimacs_status_reservations(DIMACS_PROOF_PUBLICATION_WAIT) {
        ay_sys::write_stderr_unlocked(
            b"c Warning: a DIMACS proof status transaction was still being reserved when the memory ceiling ended the run\n",
        );
    }
    let held: DimacsStatusCeilingSlots = DIMACS_STATUS_CEILING_CUSTODIES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clone();
    let owner = std::process::id();
    for custody in held.iter().flatten().filter_map(std::sync::Weak::upgrade) {
        if custody.owner_pid == owner && custody.settle_at_exit(true).is_err() {
            ay_sys::write_stderr_unlocked(
                b"c Warning: failed to settle a DIMACS proof status transaction of the run the memory ceiling ended\n",
            );
        }
    }
}
