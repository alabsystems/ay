// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! What a breach of the hard allocation ceiling does before the process leaves
//! (2026-09-13). The breach leaves through `_exit`, which runs no `atexit`
//! handler and no destructor, so anything a run must not leave behind — a
//! partial proof above all — is released here or not at all. The standalone
//! `ay` registers a settlement that ends the run like every other exit that
//! does not answer.

use std::cell::Cell;
use std::sync::atomic::{AtomicPtr, Ordering};

use super::{write_fd, STDERR_FD};

/// How a breach of the hard allocation ceiling leaves, as the settlement
/// registered with [`set_hard_memory_ceiling_settlement`] decides.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CeilingSettlement {
    /// Write the armed verdict and leave with the armed status.
    ArmedVerdict,
    /// Write the armed verdict but leave with this status: the verdict
    /// answers the current query, and an earlier query's decisive answer
    /// already on stdout keeps the run from reading as failed.
    ArmedVerdictWithStatus(i32),
    /// Write nothing and leave with this status: another exit owns the verdict.
    Silent(i32),
}

/// What settles the run before a breach leaves; null when nothing registered
/// one. Holds a `fn(i32) -> CeilingSettlement`.
pub(crate) static SETTLEMENT: AtomicPtr<()> = AtomicPtr::new(std::ptr::null_mut());

thread_local! {
    /// Set on the one thread that is settling a breach. Its allocations are not
    /// refused: the settlement is bounded, and refusing them would re-enter the
    /// breach from inside it.
    pub(crate) static SETTLING: Cell<bool> = const { Cell::new(false) };
}

/// Register what a breach does before the process leaves. The standalone `ay`
/// settles the run like every other exit that does not answer: it claims the
/// run and discards the proofs an unanswered run must not leave.
///
/// `settle` runs on the breaching thread, inside the global allocator, with
/// every other thread still live. That thread may allocate past the ceiling,
/// and a breach on any other thread parks until the process ends. `settle`
/// must not take a lock another thread may hold, write through
/// `std::io::stdout` or `stderr` (use [`write_stderr_unlocked`]), or panic; a
/// panic is caught and the armed verdict is written. It receives the armed
/// exit status.
pub fn set_hard_memory_ceiling_settlement(settle: fn(i32) -> CeilingSettlement) {
    SETTLEMENT.store(settle as *mut (), Ordering::SeqCst);
}

/// Write `bytes` to stderr through a raw `write(2)`, without the standard
/// library's stderr lock, which a thread parked by a breach may hold.
pub fn write_stderr_unlocked(bytes: &[u8]) {
    write_fd(STDERR_FD, bytes);
}

/// Whether this thread is settling a breach. Reached only past the ceiling.
#[cold]
pub(crate) fn settling_here() -> bool {
    SETTLING.try_with(Cell::get).unwrap_or(false)
}

/// Run the registered settlement, if any, on this thread, which it exempts
/// from the ceiling. A settlement that panics must not unwind out of the
/// allocator, so its panic is caught and the armed verdict is written.
pub(crate) fn settle(armed_exit_code: i32) -> CeilingSettlement {
    let settle = SETTLEMENT.load(Ordering::SeqCst);
    if settle.is_null() {
        return CeilingSettlement::ArmedVerdict;
    }
    // SAFETY: `set_hard_memory_ceiling_settlement` is the only writer and
    // stores a `fn(i32) -> CeilingSettlement` cast to a data pointer; function
    // pointers and data pointers have the same size on every supported target.
    let settle = unsafe { std::mem::transmute::<*mut (), fn(i32) -> CeilingSettlement>(settle) };
    let _ = SETTLING.try_with(|settling| settling.set(true));
    std::panic::catch_unwind(|| settle(armed_exit_code)).unwrap_or(CeilingSettlement::ArmedVerdict)
}

/// Park a thread that breached after another one: the settling thread ends
/// the process. Sleeping allocates nothing and takes no lock.
pub(crate) fn park_until_the_process_ends() -> ! {
    loop {
        std::thread::sleep(std::time::Duration::from_secs(3600));
    }
}
