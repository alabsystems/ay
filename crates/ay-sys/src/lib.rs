// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Low-level system interfaces for AY.
//!
//! This crate provides safe wrappers around OS-specific system calls for memory
//! measurement. It is the only crate in the ay workspace that permits `unsafe`
//! code, keeping FFI boundaries minimal and auditable.
//!
//! ## Why this crate exists
//!
//! All other ay crates use `#![forbid(unsafe_code)]`. Memory measurement
//! requires FFI calls (`getrusage`, `sysctlbyname`, `sysconf`), so the unsafe
//! code is isolated here behind safe public APIs.

use std::alloc::{GlobalAlloc, Layout};
#[cfg(unix)]
pub mod supervisor;
pub mod time;

use std::sync::atomic::{AtomicUsize, Ordering};

/// Process-wide memory limit in bytes. 0 = no limit.
static PROCESS_MEMORY_LIMIT: AtomicUsize = AtomicUsize::new(0);

/// Live bytes currently allocated through [`CountingAllocator`], summed across
/// all threads. 0 when no counting allocator is installed.
///
/// This is the **instantaneous** heap signal: it is incremented on every
/// `alloc`/`realloc`-grow and decremented on every `dealloc`/`realloc`-shrink,
/// so it reflects a bulk allocation the moment it happens — before the OS's RSS
/// (`getrusage`, which we read via [`current_rss_bytes`]) catches up, and before
/// an OOM-killer can fire. Two relaxed atomics per allocation, no syscalls, no
/// polling. See [`CountingAllocator`].
static LIVE_BYTES: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    /// Test-only per-thread override forcing [`process_memory_exceeded`] to
    /// return `true` on the current thread. Production never sets this. It lets a
    /// test exercise the memory-exit paths without flipping the *process-global*
    /// `PROCESS_MEMORY_LIMIT`, which — when the test runs in parallel with others
    /// — would otherwise make every concurrent solve on other threads abort
    /// spuriously (a flaky-test source). Mirrors the project's thread-local
    /// spawn-failure test hook.
    static FORCE_PROCESS_MEMORY_EXCEEDED: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

/// Test-only: force (or clear) [`process_memory_exceeded`] on the current thread.
///
/// Thread-local by design so a test cannot leak the forced state into other
/// threads' solves running concurrently.
#[doc(hidden)]
pub fn force_process_memory_exceeded_for_testing(force: bool) {
    FORCE_PROCESS_MEMORY_EXCEEDED.with(|cell| cell.set(force));
}

/// Set the process-wide memory limit in bytes.
///
/// All subsequent calls to [`process_memory_exceeded`] will check against this
/// limit. Set to 0 to disable the limit.
///
/// Intended to be called once from `main()`.
pub fn set_process_memory_limit(bytes: usize) {
    PROCESS_MEMORY_LIMIT.store(bytes, Ordering::SeqCst);
}

/// Get the current process-wide memory limit in bytes. 0 = no limit.
pub fn get_process_memory_limit() -> usize {
    PROCESS_MEMORY_LIMIT.load(Ordering::Relaxed)
}

/// Check if the process has exceeded its memory limit.
///
/// Returns `false` if no limit is set (limit == 0) or if measurement fails.
/// This is cheap to call (single syscall, no subprocess).
///
/// Two signals are consulted against the same limit, and the process is
/// considered over-budget if **either** trips:
///
/// 1. **Live heap bytes** ([`current_live_bytes`]): exact and instantaneous
///    when a [`CountingAllocator`] is installed (the `ay` binary installs one).
///    A single bulk allocation (e.g. a 40 GB `Vec`/`Box`) is reflected the
///    moment it lands — this is the signal that the OOM-causing burst trips
///    *before* `getrusage` peak RSS catches up. 0 when no counting allocator
///    is installed (library consumers), in which case only signal 2 applies.
/// 2. **Peak RSS** ([`current_rss_bytes`]): the OS's view via `getrusage`.
///    Always available, but lags fast allocation bursts.
///
/// Both fire at 95% of the limit to leave headroom for graceful cleanup.
pub fn process_memory_exceeded() -> bool {
    process_memory_exceeded_at_percent(95)
}

/// Check whether current memory usage exceeds the given **percentage** of the
/// process memory limit.
///
/// Identical to [`process_memory_exceeded`] (which uses 95%) except the trip
/// threshold is configurable. The lower thresholds are used as *predictive*
/// backpressure before a known about-to-happen bulk allocation: e.g. cloning a
/// large incremental SAT solver roughly doubles its resident footprint, so a
/// caller that is already past ~half the budget would breach the limit by
/// cloning. Declining that clone (returning `Unknown` / the best incumbent) is
/// sound — it only ends the search early, never fabricates a verdict — and trips
/// *before* the breach instead of relying on the lagging post-allocation guard.
///
/// Returns `false` when no limit is set (`limit == 0`) so it is a strict no-op
/// for library consumers and uncapped runs.
#[must_use]
pub fn process_memory_exceeded_at_percent(percent: usize) -> bool {
    if percent >= 95 && FORCE_PROCESS_MEMORY_EXCEEDED.with(std::cell::Cell::get) {
        // The test-only force hook represents a true >=95% (real) breach; honor
        // it for the production threshold but not for the lower predictive ones,
        // so a forced "exceeded" still exercises the hard-limit code paths.
        return true;
    }
    let limit = PROCESS_MEMORY_LIMIT.load(Ordering::Relaxed);
    if limit == 0 {
        return false;
    }
    // Trigger at `percent`% of limit (95% for the hard guard; lower for
    // pre-allocation backpressure) to leave headroom for graceful cleanup.
    let threshold = limit.saturating_mul(percent) / 100;
    // Signal 1: live heap bytes — exact, instantaneous, no syscall. Catches a
    // bulk allocation burst before the OS RSS reading reflects it.
    let live = current_live_bytes();
    if live > threshold {
        return true;
    }
    // Signal 2: CURRENT physical footprint — the preferred OS signal.
    // macOS: `task_info` phys_footprint (resident + compressed + swapped, the
    // jetsam metric — the only signal that sees compressor-backed growth,
    // which is how a 263 GB runaway hid behind a ~16 GB RSS reading);
    // Linux: current resident from /proc/self/statm. Both are LIVE ledgers
    // that decrease when memory is freed, which is essential in a LONG-LIVED
    // host (a compiler verifying many functions, a test harness running
    // thousands of cases): a peak-based reading would latch the first
    // high-water mark forever and permanently degrade every later solve to
    // Unknown after one hungry-but-cancelled attempt.
    let footprint = current_footprint_bytes();
    if footprint > 0 {
        return footprint > threshold;
    }
    // Signal 3 (fallback, platforms with no footprint API): peak RSS via
    // `getrusage`. Conservative — never under-reports, but as a PEAK it can
    // over-trip long after a past high-water mark; acceptable only as the
    // last-resort signal.
    let rss = current_rss_bytes();
    rss > 0 && rss > threshold
}

/// Syscall-free subset of [`process_memory_exceeded_at_percent`]: consults ONLY
/// the instantaneous live-heap signal (signal 1 — a single relaxed atomic load),
/// never the `getrusage`/`task_info` footprint syscall.
///
/// Intended as a per-call pre-check on a hot `should_stop` path: a steadily
/// growing heap (e.g. permanent objective-bound rows accreting in the optimize
/// loop) trips this promptly, without paying a syscall on every call and without
/// waiting for a coarse strided full poll. Returns `false` when no limit is set
/// (`limit == 0`) or no counting allocator is installed (`live == 0`), so it is a
/// strict no-op for library consumers and uncapped runs.
///
/// This is only the live-heap signal, so callers should keep the full
/// [`process_memory_exceeded`] as a strided backstop — it also sees RSS /
/// compressor-backed footprint growth that the allocator counter cannot.
#[must_use]
pub fn live_bytes_exceeded_at_percent(percent: usize) -> bool {
    if percent >= 95 && FORCE_PROCESS_MEMORY_EXCEEDED.with(std::cell::Cell::get) {
        // Mirror the test-only force hook honored by the full guard for >=95%.
        return true;
    }
    let limit = PROCESS_MEMORY_LIMIT.load(Ordering::Relaxed);
    if limit == 0 {
        return false;
    }
    let threshold = limit.saturating_mul(percent) / 100;
    current_live_bytes() > threshold
}

/// Current live heap bytes tracked by [`CountingAllocator`].
///
/// Returns 0 when no counting allocator is installed (e.g. library consumers
/// that keep their own allocator). Single relaxed atomic load.
#[must_use]
pub fn current_live_bytes() -> usize {
    LIVE_BYTES.load(Ordering::Relaxed)
}

/// Add to the live-bytes counter. Internal to [`CountingAllocator`]; exposed
/// `#[doc(hidden)]` only so the wiring is testable without performing real
/// allocations.
#[doc(hidden)]
#[inline]
pub fn add_live_bytes(bytes: usize) {
    LIVE_BYTES.fetch_add(bytes, Ordering::Relaxed);
}

/// Subtract from the live-bytes counter. Saturating: a counter underflow would
/// otherwise wrap to a huge value and spuriously trip the limit. Internal to
/// [`CountingAllocator`]; see [`add_live_bytes`].
#[doc(hidden)]
#[inline]
pub fn sub_live_bytes(bytes: usize) {
    // `fetch_sub` wraps on underflow; clamp at zero instead. The CAS loop runs
    // only in the (impossible-under-correct-pairing) underflow case, so the
    // common path is one relaxed `fetch_sub`.
    let prev = LIVE_BYTES.fetch_sub(bytes, Ordering::Relaxed);
    if prev < bytes {
        // Underflowed past zero — restore to a non-negative floor.
        LIVE_BYTES.fetch_add(bytes - prev, Ordering::Relaxed);
    }
}

/// A `#[global_allocator]` wrapper that maintains [`LIVE_BYTES`], the exact
/// count of live heap bytes, while delegating every allocation to an inner
/// allocator `A`.
///
/// # Why
///
/// Process memory limits enforced via peak RSS (`getrusage`) lag fast
/// allocation bursts: a single 40 GB `Vec`/`Box`/`alloc::alloc` can land — and
/// the kernel OOM-killer can fire — in the gap between two RSS samples. By
/// hooking the global allocator we observe the burst *synchronously*, the
/// instant the bytes are committed, with no syscall and no polling. The solver
/// then trips its existing cancellation at the next checkpoint and returns
/// `Unknown` instead of panicking the machine. This is the binary's allocator
/// only; library consumers keep their own allocator and `LIVE_BYTES` stays 0.
///
/// # Overhead
///
/// Two relaxed atomics per allocation (one on alloc, one on dealloc); none on
/// the read side beyond a single relaxed load in [`process_memory_exceeded`],
/// which already ran at every solver checkpoint. No syscalls, no locks.
///
/// # Soundness
///
/// The accounting only *observes* — it never changes which pointer the inner
/// allocator returns, so it cannot affect a solve's logical result. Its only
/// effect is to make `process_memory_exceeded()` return `true` sooner, which
/// drives the solver to `Unknown` (never a wrong SAT/UNSAT).
#[derive(Debug, Default, Clone, Copy)]
pub struct CountingAllocator<A> {
    /// The real allocator that performs the work (e.g. `mimalloc::MiMalloc`).
    pub inner: A,
}

impl<A> CountingAllocator<A> {
    /// Wrap an inner allocator.
    pub const fn new(inner: A) -> Self {
        Self { inner }
    }
}

/// One-time latch guarding the mimalloc `arena_reserve` peak-RSS trim so it runs on
/// the FIRST allocation only.
#[cfg(feature = "mimalloc-arena-trim")]
static ARENA_TRIM_DONE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Peak-RSS trim: zero mimalloc's `arena_reserve` on the VERY FIRST allocation —
/// which is the first mimalloc use, before any arena has been reserved — so the
/// whole process (and, via copy-on-write, any child the fork-before-threads solve
/// supervisor forks from it) reserves and commits OS pages at segment granularity
/// instead of inside the default 1 GiB arena, whose looser commit granularity runs
/// peak RSS well above the live heap (measured ~1.7x on a churn-heavy proof solve).
///
/// This is the ONLY point early enough: mimalloc reserves its first arena on the
/// first `malloc`, which happens during runtime startup BEFORE `main`, so a runtime
/// `mi_option_set` from `main` (let alone from a post-`fork` child) is already too
/// late — it only resizes FUTURE arenas, and a working set that fits in the first
/// 1 GiB arena never triggers one. Setting it here, ahead of the first inner
/// allocation, makes the first arena itself small. This replaces the old
/// re-exec-child `MIMALLOC_ARENA_RESERVE=0` env injection, which the fork model
/// cannot use (a forked child inherits the parent's already-initialized allocator).
///
/// Soundness-neutral: an allocator arena-sizing knob only changes WHERE bytes land,
/// never which pointer is returned or any solve verdict. An explicit user
/// `MIMALLOC_ARENA_RESERVE` always wins (checked allocation-free via `getenv`, so
/// mimalloc's own env read applies instead). Self-validating against mimalloc enum
/// drift: only acts when the option currently reads as a GiB-scale reserve
/// (mimalloc's 1 GiB 64-bit default), confirming the ordinal still names
/// `arena_reserve`; otherwise a no-op, so a future enum reorder forfeits only the
/// trim and never sets a wrong option. No-op unless the `mimalloc-arena-trim`
/// feature is on (only the final `ay` binary links mimalloc).
#[cfg(feature = "mimalloc-arena-trim")]
#[inline]
fn ensure_arena_reserve_trimmed() {
    use std::sync::atomic::Ordering;
    // Fast path: after the first allocation this is a single relaxed load.
    if ARENA_TRIM_DONE.load(Ordering::Relaxed) {
        return;
    }
    if ARENA_TRIM_DONE.swap(true, Ordering::Relaxed) {
        return;
    }
    // v3 `mi_option_t` ordinal for `mi_option_arena_reserve`, verified against the
    // linked libmimalloc-sys 0.1.49 vendored v3 header (cross-checked: the same enum
    // count yields `_mi_option_last == 47`, matching the crate's binding).
    const MI_OPTION_ARENA_RESERVE: libc::c_int = 23;
    extern "C" {
        fn mi_option_get_size(option: libc::c_int) -> usize;
        fn mi_option_set(option: libc::c_int, value: libc::c_long);
        fn getenv(name: *const libc::c_char) -> *mut libc::c_char;
    }
    // SAFETY: `getenv` reads `environ` and returns a borrowed pointer (no
    // allocation, so no re-entry into this allocator); `mi_option_get_size` /
    // `mi_option_set` are mimalloc's documented option API (present because the
    // final binary statically links mimalloc under this feature) and perform no
    // allocation. `c"..."` is a valid NUL-terminated C string.
    unsafe {
        // Respect an explicit user setting: mimalloc reads MIMALLOC_ARENA_RESERVE
        // from the env at its first arena reservation (after this hook), so if the
        // user set it we leave the option untouched and let that env read win.
        if !getenv(c"MIMALLOC_ARENA_RESERVE".as_ptr()).is_null() {
            return;
        }
        if mi_option_get_size(MI_OPTION_ARENA_RESERVE) >= 64 * 1024 * 1024 {
            mi_option_set(MI_OPTION_ARENA_RESERVE, 0);
        }
    }
}

/// No-op when mimalloc is not the linked allocator (feature off): other consumers
/// of [`CountingAllocator`] must not reference mimalloc symbols and pay nothing.
#[cfg(not(feature = "mimalloc-arena-trim"))]
#[inline(always)]
fn ensure_arena_reserve_trimmed() {}

// SAFETY: All four methods forward verbatim to `self.inner`, which upholds the
// `GlobalAlloc` contract by assumption. The only added work is updating the
// `LIVE_BYTES` atomic with the exact `layout.size()` / `new_size` that the
// inner allocator just (de)committed; this performs no allocation and touches
// only a `'static` atomic, so it introduces no new safety obligations and does
// not alter the returned pointers.
unsafe impl<A: GlobalAlloc> GlobalAlloc for CountingAllocator<A> {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // Peak-RSS trim: zero mimalloc's arena_reserve on the first allocation,
        // before any arena is reserved (see `ensure_arena_reserve_trimmed`).
        ensure_arena_reserve_trimmed();
        // SAFETY: forwarded unchanged; caller upholds `alloc`'s contract.
        let ptr = unsafe { self.inner.alloc(layout) };
        if !ptr.is_null() {
            add_live_bytes(layout.size());
        }
        ptr
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // Peak-RSS trim on the first allocation (see `ensure_arena_reserve_trimmed`).
        ensure_arena_reserve_trimmed();
        // SAFETY: forwarded unchanged; caller upholds `alloc_zeroed`'s contract.
        let ptr = unsafe { self.inner.alloc_zeroed(layout) };
        if !ptr.is_null() {
            add_live_bytes(layout.size());
        }
        ptr
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: forwarded unchanged; caller upholds `dealloc`'s contract
        // (`ptr` came from this allocator with this `layout`).
        unsafe { self.inner.dealloc(ptr, layout) };
        sub_live_bytes(layout.size());
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: forwarded unchanged; caller upholds `realloc`'s contract.
        let new_ptr = unsafe { self.inner.realloc(ptr, layout, new_size) };
        if !new_ptr.is_null() {
            // Adjust by the signed delta. On grow, add; on shrink, subtract.
            let old_size = layout.size();
            if new_size >= old_size {
                add_live_bytes(new_size - old_size);
            } else {
                sub_live_bytes(old_size - new_size);
            }
        }
        // On failure the original block is unchanged, so the counter is correct
        // as-is (no adjustment needed).
        new_ptr
    }
}

/// Returns the peak resident set size (RSS) of this process in bytes.
///
/// Uses `getrusage(RUSAGE_SELF)` — a single syscall with no subprocess
/// overhead. Returns peak RSS, which closely tracks current RSS for a
/// continuously-growing process (Rust's allocator does not aggressively
/// return memory to the OS).
///
/// Returns 0 if measurement fails or on unsupported platforms.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub fn current_rss_bytes() -> usize {
    // SAFETY: `libc::rusage` is a plain old data struct and zero-init is valid
    // before passing it to `getrusage`, which fills all output fields.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    // SAFETY: `usage` points to valid writable memory for the duration of the call.
    let ret = unsafe { libc::getrusage(libc::RUSAGE_SELF, &raw mut usage) };
    if ret != 0 {
        return 0;
    }
    // macOS: ru_maxrss is in bytes.
    // Linux: ru_maxrss is in kilobytes.
    #[cfg(target_os = "macos")]
    {
        usage.ru_maxrss as usize
    }
    #[cfg(target_os = "linux")]
    {
        (usage.ru_maxrss as usize) * 1024
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub fn current_rss_bytes() -> usize {
    0
}

/// Returns the process's physical memory footprint in bytes: resident pages
/// PLUS compressor-backed and swapped pages (`phys_footprint` from
/// `task_info(TASK_VM_INFO)` — the same accounting jetsam uses).
///
/// This is the signal that keeps rising when the macOS VM compressor squeezes
/// a runaway process whose RSS has plateaued; see Signal 3 in
/// [`process_memory_exceeded_at_percent`]. Cheap (one Mach call, no
/// allocation). Returns 0 on failure or on platforms without a footprint API.
#[cfg(target_os = "macos")]
#[must_use]
pub fn current_footprint_bytes() -> usize {
    // Hand-declared subset of <mach/task_info.h>'s task_vm_info: the fields up
    // to and including `phys_footprint` (mach_vm_size_t / integer_t are fixed
    // width, so the offsets are stable ABI). Declaring the prefix only keeps
    // this dependency-free; TASK_VM_INFO returns at most `count` integers.
    #[repr(C)]
    struct TaskVmInfoPrefix {
        virtual_size: u64,
        region_count: i32,
        page_size: i32,
        resident_size: u64,
        resident_size_peak: u64,
        device: u64,
        device_peak: u64,
        internal: u64,
        internal_peak: u64,
        external: u64,
        external_peak: u64,
        reusable: u64,
        reusable_peak: u64,
        purgeable_volatile_pmap: u64,
        purgeable_volatile_resident: u64,
        purgeable_volatile_virtual: u64,
        compressed: u64,
        compressed_peak: u64,
        compressed_lifetime: u64,
        phys_footprint: u64,
    }
    const TASK_VM_INFO: u32 = 22;
    // Count is in units of natural_t (u32) words.
    let mut count = (size_of::<TaskVmInfoPrefix>() / size_of::<u32>()) as u32;
    let mut info = std::mem::MaybeUninit::<TaskVmInfoPrefix>::zeroed();
    unsafe extern "C" {
        fn mach_task_self() -> u32;
        fn task_info(task: u32, flavor: u32, info: *mut u32, count: *mut u32) -> i32;
    }
    // SAFETY: `info` points to owned writable memory sized for `count` words;
    // task_info writes at most `count` natural_t words and updates `count`.
    let kr = unsafe {
        task_info(
            mach_task_self(),
            TASK_VM_INFO,
            info.as_mut_ptr().cast::<u32>(),
            &raw mut count,
        )
    };
    let full_words = (size_of::<TaskVmInfoPrefix>() / size_of::<u32>()) as u32;
    if kr != 0 || count < full_words {
        // Call failed, or the kernel returned a truncated struct that does not
        // reach phys_footprint (pre-10.9 ABI) — no footprint signal.
        return 0;
    }
    // SAFETY: kr == KERN_SUCCESS and count covers the full prefix, so every
    // field up to phys_footprint was written.
    let info = unsafe { info.assume_init() };
    info.phys_footprint as usize
}

/// Linux: current resident set from `/proc/self/statm` (field 2, pages).
/// There is no compressor on Linux, so current RSS IS the footprint analog —
/// and unlike `ru_maxrss` it decreases when memory is freed, avoiding the
/// permanent high-water latch (see `process_memory_exceeded_at_percent`).
#[cfg(target_os = "linux")]
#[must_use]
pub fn current_footprint_bytes() -> usize {
    let Ok(statm) = std::fs::read_to_string("/proc/self/statm") else {
        return 0;
    };
    let Some(resident_pages) = statm.split_whitespace().nth(1) else {
        return 0;
    };
    let Ok(pages) = resident_pages.parse::<usize>() else {
        return 0;
    };
    // SAFETY: sysconf(_SC_PAGESIZE) is async-signal-safe and has no
    // preconditions; a failure returns -1, mapped to the universal 4 KiB.
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    let page = if page > 0 { page as usize } else { 4096 };
    pages.saturating_mul(page)
}

/// Other platforms: no footprint API; peak RSS is the only (fallback) signal.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
#[must_use]
pub fn current_footprint_bytes() -> usize {
    0
}

/// Returns the total physical memory of the system in bytes.
///
/// Returns 0 if detection fails or on unsupported platforms.
#[cfg(target_os = "macos")]
pub fn physical_memory_bytes() -> usize {
    let mut size: u64 = 0;
    let mut len = size_of::<u64>();
    let name = c"hw.memsize";
    // SAFETY: `name.as_ptr()` is a valid null-terminated C string literal.
    // `size` and `len` are owned stack locals with exclusive mutable access
    // here, and their layouts match the `u64` / `size_t` expected by
    // `sysctlbyname` on macOS. The new-value pointer is null and newlen is 0,
    // matching the read-only usage documented in sysctl(3).
    let ret = unsafe {
        libc::sysctlbyname(
            name.as_ptr(),
            std::ptr::addr_of_mut!(size).cast::<libc::c_void>(),
            &raw mut len,
            std::ptr::null_mut(),
            0,
        )
    };
    if ret == 0 {
        size as usize
    } else {
        0
    }
}

/// Linux: host RAM (`_SC_PHYS_PAGES`) clamped to the process's cgroup memory
/// limit when one is set. Competition/cluster and container runs typically
/// enforce a cgroup ceiling far below host RAM; anchoring to host RAM alone
/// would place every derived limit and watermark above the point where the
/// kernel OOM-kills the process (a crash, never a graceful `Unknown`).
#[cfg(target_os = "linux")]
pub fn physical_memory_bytes() -> usize {
    // SAFETY: `sysconf` takes a valid sysconf name constant defined in
    // `<unistd.h>`; `_SC_PHYS_PAGES` is a read-only query with no pointer
    // parameters and returns `-1` on failure (handled below).
    let pages = unsafe { libc::sysconf(libc::_SC_PHYS_PAGES) };
    // SAFETY: Same as above — `_SC_PAGE_SIZE` is a read-only sysconf query.
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGE_SIZE) };
    let host_ram = if pages > 0 && page_size > 0 {
        (pages as usize) * (page_size as usize)
    } else {
        0
    };
    effective_physical_memory_from(host_ram, cgroup_memory_limit_bytes())
}

/// Reads the process's cgroup memory ceiling, if any.
///
/// Checks cgroup v2 (`/sys/fs/cgroup/memory.max`) and cgroup v1
/// (`/sys/fs/cgroup/memory/memory.limit_in_bytes`); on hybrid hierarchies
/// where both report a real limit, the tighter one wins. Inside a container
/// or a competition cgroup these files (via the cgroup namespace mount) carry
/// the limit the kernel actually enforces; on an unconfined host they are
/// absent (the v2 root has no `memory.max`) or hold the "unlimited" sentinel,
/// and `None` is returned.
#[cfg(target_os = "linux")]
fn cgroup_memory_limit_bytes() -> Option<usize> {
    let read_limit = |path: &str| {
        std::fs::read_to_string(path)
            .ok()
            .and_then(|contents| parse_cgroup_memory_limit(&contents))
    };
    let v2 = read_limit("/sys/fs/cgroup/memory.max");
    let v1 = read_limit("/sys/fs/cgroup/memory/memory.limit_in_bytes");
    match (v2, v1) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

/// Parse the contents of a cgroup memory-limit file into an effective byte
/// ceiling. Pure so the policy is testable on every platform.
///
/// Handles both hierarchies:
/// - cgroup v2 `memory.max`: a byte count, or the literal `max` (no limit).
/// - cgroup v1 `memory.limit_in_bytes`: always numeric; "no limit" is a huge
///   sentinel (`PAGE_COUNTER_MAX * PAGE_SIZE`, i.e. `i64::MAX` rounded down
///   to a page multiple). Anything at or above `i64::MAX / 2` cannot be a
///   real ceiling and is treated as that sentinel.
///
/// Returns `None` when the contents denote "no limit" or carry no usable
/// information (empty, non-numeric, zero — a zero ceiling could not be
/// running this code, and propagating 0 would read as "detection failed" and
/// *disable* the internal limit, which is fail-open). Values beyond
/// `usize::MAX` (32-bit targets) exceed the address space and are likewise
/// treated as unlimited.
#[cfg_attr(not(target_os = "linux"), allow(dead_code))]
pub(crate) fn parse_cgroup_memory_limit(contents: &str) -> Option<usize> {
    /// cgroup v1 "unlimited" floor: `i64::MAX / 2` (expressed shift-wise to
    /// avoid a sign-losing cast). Real limits are far below; the kernel
    /// sentinel (~`i64::MAX`) is far above.
    const V1_UNLIMITED_FLOOR: u64 = (u64::MAX >> 1) / 2;
    let bytes: u64 = contents.trim().parse().ok()?;
    if bytes == 0 || bytes >= V1_UNLIMITED_FLOOR {
        return None;
    }
    usize::try_from(bytes).ok()
}

/// Pure core of the Linux [`physical_memory_bytes`] clamp: the effective
/// memory ceiling given host RAM and an optional cgroup limit.
///
/// Takes the MINIMUM of the two — the kernel OOM-kills at the cgroup ceiling
/// regardless of host RAM. When host detection fails (0) but a cgroup limit
/// is known, the cgroup limit is the ceiling (fail-closed: a real bound beats
/// "unknown"). No cgroup limit falls back to host RAM.
#[cfg_attr(not(target_os = "linux"), allow(dead_code))]
pub(crate) fn effective_physical_memory_from(
    host_ram: usize,
    cgroup_limit: Option<usize>,
) -> usize {
    match cgroup_limit {
        Some(limit) if host_ram == 0 => limit,
        Some(limit) => host_ram.min(limit),
        None => host_ram,
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub fn physical_memory_bytes() -> usize {
    0
}

/// Returns the currently available system memory in bytes.
///
/// "Available" here means memory the OS believes a new allocation could use
/// without forcing swap/compression. This is the ground-truth signal driving
/// the `MemoryPressure` observer (see ay-core::memory_pressure).
///
/// - macOS: `host_statistics64(HOST_VM_INFO64)` → `free + inactive` pages.
/// - Linux: reads `MemAvailable:` from `/proc/meminfo`.
/// - Fallback: returns `physical_memory_bytes()` (conservative over-estimate
///   when the fine-grained signal is unavailable; callers must still honor
///   `effective_available_bytes = min(rlimit, system_available * 0.75)`).
///
/// Returns 0 only when no memory figure is available at all.
#[cfg(target_os = "macos")]
pub fn system_available_bytes() -> usize {
    // Query vm_statistics64 via host_statistics64. `free + inactive` is the
    // macOS analogue of Linux's `MemAvailable`: inactive pages are clean and
    // the kernel can reclaim them without paging.
    //
    // SAFETY: `mach_host_self` returns a valid host port for the calling
    // process; `host_statistics64` fills the stats struct with a known count.
    unsafe {
        // `vm_statistics64_data_t` is 38 * u64 = 304 bytes as of macOS 14.
        // We only read `free_count`, `inactive_count`, `speculative_count`.
        // Allocate a zeroed buffer large enough for any reasonable variant.
        const VM_STATS_WORDS: usize = 64;
        let mut stats: [u64; VM_STATS_WORDS] = [0; VM_STATS_WORDS];
        // `HOST_VM_INFO64_COUNT` per Darwin XNU headers: 38 (natural_t = u32
        // count of 32-bit words, so 38 u32s = 19 u64s fit; we request
        // enough for the whole structure).
        const HOST_VM_INFO64: libc::c_int = 4;
        let mut count: u32 = (VM_STATS_WORDS * 2) as u32; // natural_t count
                                                          // Use `extern "C"` bindings for both `mach_host_self` and
                                                          // `host_statistics64`. The `libc::mach_host_self` wrapper is
                                                          // deprecated in favour of the `mach2` crate; binding directly
                                                          // avoids that deprecation without pulling in a new dep.
        extern "C" {
            fn mach_host_self() -> libc::mach_port_t;
            fn host_statistics64(
                host_priv: libc::mach_port_t,
                flavor: libc::c_int,
                host_info_out: *mut u32,
                host_info_outCnt: *mut u32,
            ) -> libc::c_int;
        }
        let host = mach_host_self();
        let ret = host_statistics64(
            host,
            HOST_VM_INFO64,
            stats.as_mut_ptr().cast::<u32>(),
            std::ptr::addr_of_mut!(count),
        );
        if ret != 0 {
            // Fallback: physical memory (caller's 0.75 headroom factor still
            // protects us from over-commit).
            return physical_memory_bytes();
        }
        // vm_statistics64 layout (first eight u32 fields):
        //   free_count, active_count, inactive_count, wire_count, ...
        // Read as u32 words:
        let words = stats.as_ptr().cast::<u32>();
        let free_count = u64::from(words.read());
        let inactive_count = u64::from(words.add(2).read());
        // speculative_count is at offset 15 in natural_t-words on modern macOS;
        // conservatively exclude it (treat as unavailable) rather than risk
        // misreading layout — `free + inactive` is the accepted approximation.
        let page_size = {
            let ps = libc::sysconf(libc::_SC_PAGESIZE);
            if ps > 0 {
                ps as u64
            } else {
                4096
            }
        };
        let avail_bytes = (free_count + inactive_count).saturating_mul(page_size);
        usize::try_from(avail_bytes).unwrap_or(usize::MAX)
    }
}

#[cfg(target_os = "linux")]
pub fn system_available_bytes() -> usize {
    // Parse `MemAvailable:` from /proc/meminfo. This is the kernel's own
    // estimate accounting for reclaimable slab/cache, suitable for use as
    // `effective_available` per the Linux kernel docs (Documentation/
    // filesystems/proc.rst, `/proc/meminfo`).
    use std::fs;
    let Ok(contents) = fs::read_to_string("/proc/meminfo") else {
        return physical_memory_bytes();
    };
    for line in contents.lines() {
        if let Some(rest) = line.strip_prefix("MemAvailable:") {
            // Format: "MemAvailable:   12345678 kB"
            let trimmed = rest.trim();
            let kb_str = trimmed.split_whitespace().next().unwrap_or("0");
            if let Ok(kb) = kb_str.parse::<u64>() {
                return usize::try_from(kb.saturating_mul(1024)).unwrap_or(usize::MAX);
            }
        }
    }
    physical_memory_bytes()
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub fn system_available_bytes() -> usize {
    physical_memory_bytes()
}

/// Effective memory budget for the current process in bytes.
///
/// Formula (per the development design notes §2.1):
/// ```text
/// effective_available = min(process_rlimit, system_available * 0.75)
/// ```
///
/// - `process_rlimit`: [`get_process_memory_limit()`] if non-zero, else ∞.
/// - `system_available`: [`system_available_bytes()`].
/// - The 0.75 leaves headroom for OS, other processes, and unaccounted heap.
///
/// Returns 0 if no memory figure can be obtained at all (caller should treat
/// as "unbounded" / skip pressure-based reclamation).
#[must_use]
pub fn effective_available_bytes() -> usize {
    effective_available_bytes_from(system_available_bytes(), get_process_memory_limit())
}

/// Pure core of [`effective_available_bytes`]: the effective memory headroom for
/// a given system-available figure and process rlimit.
///
/// Split out so the policy can be tested deterministically: the live
/// `system_available_bytes()` reading is volatile (it can change between two
/// reads, especially under memory pressure), which made the old tests — which
/// compared two independent live reads — flaky.
pub(crate) fn effective_available_bytes_from(system_avail: usize, rlimit: usize) -> usize {
    // 0.75 applied as `* 3 / 4` avoids floating point for determinism.
    let headroom = system_avail.saturating_mul(3) / 4;
    if rlimit == 0 {
        headroom
    } else {
        rlimit.min(headroom)
    }
}

/// Compute a default memory limit based on physical RAM.
///
/// Returns half of physical memory, clamped to \[2 GB, 64 GB\] — except the
/// 2 GB floor never exceeds the detected ceiling (see
/// [`default_memory_limit_from`]). This leaves room for the OS, other
/// processes, and concurrent ay instances.
///
/// Returns 0 if physical memory cannot be detected (limit will be disabled).
pub fn default_memory_limit() -> usize {
    // wasm32 has a 32-bit `usize`, so the 64 GB `MAX_LIMIT` const below overflows
    // const-eval. Inside a wasm sandbox there is no OS memory limit to enforce
    // (the host governs linear-memory growth), so disable the internal ceiling.
    #[cfg(target_arch = "wasm32")]
    {
        0
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        default_memory_limit_from(physical_memory_bytes())
    }
}

/// Pure core of [`default_memory_limit`], split out (like
/// [`effective_available_bytes_from`]) so the clamp policy is testable with a
/// fixed physical-memory figure.
#[cfg(not(target_arch = "wasm32"))]
pub(crate) fn default_memory_limit_from(phys: usize) -> usize {
    if phys == 0 {
        return 0;
    }
    // The floor must never exceed the detected ceiling: inside a small
    // cgroup/container `phys` can be under 2 GB, and a flat 2 GB floor would
    // set a limit the kernel OOM-kills at long before the 95% watermark trips.
    const MIN_LIMIT: usize = 2 * 1024 * 1024 * 1024; // 2 GB
    const MAX_LIMIT: usize = 64 * 1024 * 1024 * 1024; // 64 GB
    (phys / 2).clamp(MIN_LIMIT.min(phys), MAX_LIMIT)
}

/// Default process memory ceiling for the STANDALONE `ay` binary in
/// competition/benchmark use, where the solver is the machine's sole tenant:
/// 85% of physical RAM (2 GB floor). The phys/2 [`default_memory_limit`]
/// proved too tight for sole-tenant runs — on a 36 GiB host a 63M-clause
/// main-track instance peaked at 12.6 GB RSS (65% of the 18 GiB phys/2
/// limit) yet a transient allocator-ledger spike tripped the 95% gate and
/// degraded a solvable SAT instance to Unknown (#sparse-gap Cluster A).
/// Embedded/in-process users keep the tighter defaults.
#[must_use]
pub fn default_standalone_memory_limit() -> usize {
    default_standalone_memory_limit_from(physical_memory_bytes())
}

/// Pure core of [`default_standalone_memory_limit`]; see
/// [`default_memory_limit_from`] for the split rationale and the
/// floor-vs-ceiling rule.
pub(crate) fn default_standalone_memory_limit_from(phys: usize) -> usize {
    if phys == 0 {
        return 0;
    }
    const MIN_LIMIT: usize = 2 * 1024 * 1024 * 1024; // 2 GB
    ((phys / 20) * 17).max(MIN_LIMIT.min(phys))
}

/// Default process memory ceiling for EMBEDDED (in-process) solver use —
/// a solver linked into a host process (ay-dpll inside compiler_consumer) rather than
/// running as the standalone `ay` binary. Deliberately much tighter than
/// [`default_memory_limit`] (phys/2): a compiler verification pass is one of
/// many passes sharing the host, and an abandoned-on-timeout PDR bit-blast was
/// observed transiently holding ~28 GB under the phys/2 ceiling. phys/8
/// (2 GB floor, 16 GB cap) keeps a runaway attempt an early, cheap `Unknown`
/// — fail-closed, never a wrong verdict — while leaving plenty for real
/// obligation solves (healthy ones use well under 1 GB).
#[must_use]
pub fn default_embedded_memory_limit() -> usize {
    // wasm32 has a 32-bit `usize`; the 16 GB `MAX_LIMIT` const overflows const-eval
    // and there is no OS memory ceiling in a wasm sandbox. Disable it.
    #[cfg(target_arch = "wasm32")]
    {
        0
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        default_embedded_memory_limit_from(physical_memory_bytes())
    }
}

/// Pure core of [`default_embedded_memory_limit`]; see
/// [`default_memory_limit_from`] for the split rationale and the
/// floor-vs-ceiling rule.
#[cfg(not(target_arch = "wasm32"))]
pub(crate) fn default_embedded_memory_limit_from(phys: usize) -> usize {
    if phys == 0 {
        return 0;
    }
    const MIN_LIMIT: usize = 2 * 1024 * 1024 * 1024; // 2 GB
    const MAX_LIMIT: usize = 16 * 1024 * 1024 * 1024; // 16 GB
    (phys / 8).clamp(MIN_LIMIT.min(phys), MAX_LIMIT)
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
