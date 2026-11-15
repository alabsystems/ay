// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Status reservations some thread is creating or settling right now
// (status_custody.rs), and which of them the current thread holds.

/// Status reservations being created right now: from just before the lock's
/// `O_EXCL` open until its custody is registered. A memory watchdog fires as
/// soon as the process is over its limit, which at `--memory 1` is at
/// startup, inside this window: strace showed the lock opened and the
/// process gone before its transaction header was written. An exit waits the
/// window out before it settles.
static DIMACS_STATUS_RESERVING: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

/// Held across `create_dimacs_status_reservation`.
struct DimacsStatusReserving;

thread_local! {
    /// Whether this thread is inside `create_dimacs_status_reservation`. The
    /// allocator's memory ceiling settles on the thread that crossed it,
    /// which may be this one: waiting on its own reservation would only
    /// spend the whole wait.
    static RESERVING_HERE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The status custody whose settling claim this thread holds, by
    /// address (0: none). The memory ceiling may cross inside the claim, in
    /// `publish_claimed_dimacs_proof_status`, which allocates: waiting on its
    /// own claim spent the exit's whole wait, and that publication never
    /// resumes.
    static SETTLING_HERE: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl DimacsStatusReserving {
    fn enter() -> Self {
        RESERVING_HERE.with(|here| here.set(true));
        DIMACS_STATUS_RESERVING.fetch_add(1, Ordering::SeqCst);
        Self
    }
}

impl Drop for DimacsStatusReserving {
    fn drop(&mut self) {
        DIMACS_STATUS_RESERVING.fetch_sub(1, Ordering::SeqCst);
        RESERVING_HERE.with(|here| here.set(false));
    }
}

/// Wait, at most `wait`, until no status reservation is being created.
/// False when one outlasted the wait, e.g. on a thread the allocator parked.
fn wait_out_dimacs_status_reservations(wait: std::time::Duration) -> bool {
    if RESERVING_HERE.with(std::cell::Cell::get) {
        return false;
    }
    let deadline = std::time::Instant::now() + wait;
    while DIMACS_STATUS_RESERVING.load(Ordering::SeqCst) != 0 {
        if std::time::Instant::now() >= deadline {
            return false;
        }
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
    true
}

/// Record that this thread holds the settling claim on the custody at
/// `custody`. Returns the claim it encloses, which
/// [`leave_dimacs_status_settling_here`] restores.
fn enter_dimacs_status_settling_here(custody: usize) -> usize {
    SETTLING_HERE.with(|here| here.replace(custody))
}

fn leave_dimacs_status_settling_here(enclosing: usize) {
    SETTLING_HERE.with(|here| here.set(enclosing));
}

/// Whether this thread holds the settling claim on the custody at `custody`.
fn dimacs_status_settling_here(custody: usize) -> bool {
    SETTLING_HERE.with(std::cell::Cell::get) == custody
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
thread_local! {
    /// A pause the next status publication on this thread takes after its
    /// rewrite and before its rename (status_custody_tests.rs).
    static INJECTED_DIMACS_STATUS_PUBLICATION_PAUSE: std::cell::RefCell<Option<Box<dyn FnOnce()>>> =
        const { std::cell::RefCell::new(None) };
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
fn inject_dimacs_status_publication_pause_once(pause: impl FnOnce() + 'static) {
    INJECTED_DIMACS_STATUS_PUBLICATION_PAUSE
        .with(|slot| *slot.borrow_mut() = Some(Box::new(pause)));
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
fn run_injected_dimacs_status_publication_pause() {
    let pause = INJECTED_DIMACS_STATUS_PUBLICATION_PAUSE.with(|slot| slot.borrow_mut().take());
    if let Some(pause) = pause {
        pause();
    }
}
