// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Kernel-held memory bounds armed from inside the AY image.
//!
//! # Why this is in the binary and not in a wrapper
//!
//! On 2026-08-02 22:48 this machine took its fourth memory kernel panic:
//! `ay-fixed` at 137.9 GB and `ay-base` at 134.4 GB, plus 13 more `ay`
//! processes at 26.3 GB, reached 355.7 GB resident on a 128 GB box. The
//! compressor held 77.4 GB, free memory fell to 914 pages, WindowServer missed
//! 121 s of check-ins, and the kernel panicked.
//!
//! A separate tool existed to stop exactly this and did not, because it governed
//! a **path**: it replaced `<brew>/bin/<solver>` with a shim. (That tool has since
//! been removed; this module is the surviving mechanism.) The path model
//! structurally cannot cover us.
//!
//! - `cargo build` rewrites `target/release/<name>` on every build.
//! - `cargo run` execs a hash-named artifact under `target/*/deps/`.
//! - `ay-base` and `ay-fixed` were **copies of this binary at `/private/tmp`
//!   paths that did not exist at install time, under names in no list**.
//!
//! Three preconditions of path-shimming, all violated. So the bound has to be
//! armed by the image itself, which is what this module does. It survives being
//! rebuilt, copied, and renamed, because it *is* the program.
//!
//! # The two limits
//!
//! Both are kernel-held and both survive the parent's death. That last property
//! is the whole point: the processes that panic this machine are orphans. An
//! agent shell spawns a solver, the tool call times out, the shell dies, and the
//! solver reparents to launchd and keeps allocating with nothing supervising it.
//! Any userspace watchdog dies with its harness — it disarms exactly when it is
//! needed.
//!
//! **L1 — `taskpolicy -m <MB>`.** A fatal jetsam memlimit; the kernel SIGKILLs
//! within 0.2–0.5% of it, and it is exact on `phys_footprint`, the metric jetsam
//! and the compressor actually key on.
//!
//! > **The trap** (measured 2026-07-15): the memlimit
//! > binds ONLY the exact image `taskpolicy` execs. *Any* later `execve`
//! > destroys it — even in the same pid — and it is not inherited across `fork`.
//! > So `taskpolicy` must be the immediate exec'ing parent of the real image,
//! > with no shell, wrapper, or interpreter in between. That is why [`arm`]
//! > re-execs *this executable* directly under `taskpolicy` and then refuses to
//! > do it a second time.
//!
//! **L2 — `RLIMIT_AS = floor + 2 × budget`.** Inherited across both `fork` and
//! `execve`, so it covers descendants and any re-exec that L1 structurally
//! cannot. It is deliberately the loose layer: address space is a poor proxy for
//! footprint against an arena allocator, which pre-maps a large region and then
//! touches it — footprint grows while AS does not. Sizing it at 1× budget would
//! preempt the accurate cap with a misleading one.
//!
//! The floor is **not** a constant. It is this process's current address space
//! (macOS reserves an enormous shared-cache VA range) and differs per process;
//! setting `RLIMIT_AS` below it returns `EINVAL`, which is why `ulimit -v` fails
//! outright here. It is read at runtime from `proc_pidinfo`, never hardcoded.
//!
//! # What this does NOT do
//!
//! It does not bound the **aggregate**. That night had 19 ay processes; at the
//! default `RAM/16` budget that is still 152 GiB on a 128 GB machine. A
//! per-process cap turns *"two processes kill the machine"* into *"sixteen do"*.
//! macOS gives unentitled userspace no aggregate lever — no cgroups, coalitions
//! need an entitlement, and `launchctl limit` has no address-space knob. Sizing
//! concurrency remains the harness's job.
//!
//! **Forked children get L2 only.** The jetsam memlimit is not inherited across
//! `fork`, and a forked solve child that inherits [`ARMED_ENV`] will not re-arm
//! itself — deliberately, because re-exec'ing would throw away the copy-on-write
//! state that forking exists to share. Such a child is still covered by
//! `RLIMIT_AS`, which *is* inherited across both `fork` and `execve`, but its
//! footprint is bounded only loosely. This is the same limitation `govern-exec`
//! has, and it is not fixable without an aggregate accounting entity.
//!
//! **It costs one extra `execve` per invocation.** Startup pays a process
//! replacement it did not before. That is deliberate and cheap relative to a
//! solve, but a benchmark harness measuring sub-millisecond runs should know it
//! is there.

/// Environment variable marking that this process image is already governed.
///
/// It must live in the environment rather than in a process-local static:
/// [`arm`] re-execs, so the "already armed" fact has to survive `execve`. The
/// re-exec'd image runs this same constructor path and must fall straight
/// through, or it would re-exec forever.
pub const ARMED_ENV: &str = "AY_GOVERN_ARMED";

/// The pid of the ROOT `ay` process — the one a caller actually spawned.
///
/// [`arm`] re-execs this image under `taskpolicy` so the jetsam memlimit binds
/// the real binary (see the module docs). A caller that spawned `ay` and wants
/// to bind provenance to "the process I started" therefore CANNOT use
/// `std::process::id()` from inside the solver: by the time anything runs, the
/// image has been through `execv(taskpolicy)` and `taskpolicy`'s own exec of
/// the real binary, and the observed pid need not be the one the caller holds.
///
/// This is not hypothetical: external-codegen binds its exported BV CNF to the pid it
/// spawned, and measured the CNF reporting a DIFFERENT pid than the one it
/// launched — which made that binding permanently unsatisfiable.
///
/// `arm` records the root pid here BEFORE the exec chain. The environment
/// survives `execv`, and the re-exec'd image returns early from `arm` (it is
/// already armed), so the value is written exactly once, by the process the
/// caller spawned.
pub const ROOT_PID_ENV: &str = "AY_ROOT_PID";

/// The pid of the root `ay` process — the one a caller spawned.
///
/// Falls back to the live pid when the marker is absent (no `arm`, a platform
/// where `arm` is a no-op, or a direct library embedding), which is exactly the
/// case where the live pid IS the root pid.
#[must_use]
pub fn root_pid() -> u32 {
    std::env::var(ROOT_PID_ENV)
        .ok()
        .and_then(|raw| raw.trim().parse::<u32>().ok())
        .unwrap_or_else(std::process::id)
}

/// Per-process footprint budget override, in MiB. Falls back to
/// `GOVERN_DEFAULT_MB`, then to physical RAM / 16.
pub const BUDGET_ENV: &str = "GOVERN_AY_MB";

/// Shared spelling with the retired path-shim tool, kept so existing harness
/// scripts that set it keep working.
pub const SHARED_BUDGET_ENV: &str = "GOVERN_DEFAULT_MB";

/// `RLIMIT_AS` is set to this multiple of the footprint budget above the floor,
/// so it backstops a single enormous `mmap` and fork/exec descendants without
/// racing L1's accurate footprint cap.
#[cfg(target_os = "macos")]
const AS_SLACK: u64 = 2;

/// Minimum address-space headroom above the startup floor, in MiB.
///
/// # Why the footprint budget is the wrong unit for L2
///
/// `AS_SLACK * budget` sizes an ADDRESS SPACE limit from a FOOTPRINT budget,
/// and the two differ by orders of magnitude here. Measured on a 48 GiB box: a
/// trivial solve (`sbox_4_shg`, RSS 42-58 MiB) carries **429 GiB** of virtual
/// size — macOS's shared-cache reservation plus mimalloc's pre-mapped arenas.
/// That is a VA:footprint ratio of roughly 8000:1.
///
/// [`arm`] runs as the first statement of `main`, BEFORE any thread is spawned,
/// so `as_floor()` samples the VA before those arenas and thread stacks exist.
/// With `budget = RAM/16 = 3 GiB` the cap became `floor + 6 GiB`, which the
/// process then blew through during ordinary startup. Thread creation is a VA
/// allocation, so it failed with `EAGAIN`, `main` panicked, and every solve
/// answered `s UNKNOWN` — a resource guard converting correct answers into
/// silent non-answers, which for a solver is worse than no guard at all.
///
/// Bisected on that machine (headroom -> outcome):
///     6 GiB  -> dead, 8 GiB -> dead, 16 GiB -> OPTIMUM, 32/64 GiB -> OPTIMUM.
/// So even a trivial solve needs >8 GiB, and a real one needs more.
///
/// # Why a large value is still a real guard
///
/// L2 is documented above as the deliberately LOOSE layer whose job is to
/// "backstop a single enormous `mmap`" and cover fork/exec descendants; L1's
/// jetsam memlimit is the accurate footprint cap. A single enormous `mmap` is
/// hundreds of GiB, not six. Address space is free until touched, so headroom
/// costs nothing physical — and against an arena allocator L2 cannot catch a
/// footprint runaway anyway (footprint grows inside already-mapped VA), which
/// is exactly why it must not be sized as though it could.
#[cfg(target_os = "macos")]
const MIN_AS_HEADROOM_MB: u64 = 65_536;

/// Denominator for the default budget. Deliberately a small fraction of RAM:
/// one solver must never be able to approach the machine, and several of them
/// must still leave the OS its headroom.
const DEFAULT_BUDGET_DIVISOR: usize = 16;

#[cfg(target_os = "macos")]
const TASKPOLICY: &str = "/usr/sbin/taskpolicy";

/// Darwin major version of macOS 14 (Sonoma), the first release whose
/// `taskpolicy` accepts `-m <MB>`. Used ONLY to skip the probe in
/// [`imp::l1_installable`] — never to conclude the flag is missing.
#[cfg(target_os = "macos")]
const DARWIN_SONOMA: u32 = 23;

/// Program the `taskpolicy` probe runs. Needs only to exist and exit 0, so
/// that a non-zero status isolates `taskpolicy`'s own rejection of `-m`.
#[cfg(target_os = "macos")]
const PROBE_PROGRAM: &str = "/usr/bin/true";

/// Exit code used when the bound cannot be established.
///
/// Deliberately the shell's "found but not executable" code, matching
/// `govern-exec`. An unbounded solver on this machine is a kernel panic, so
/// refusing to run strictly beats maybe-panicking.
pub const EXIT_UNGOVERNED: i32 = 126;

/// Resolved budget in MiB, honoring the environment overrides.
#[must_use]
pub fn budget_mb() -> u64 {
    for key in [BUDGET_ENV, SHARED_BUDGET_ENV] {
        if let Ok(raw) = std::env::var(key) {
            if let Ok(mb) = raw.trim().parse::<u64>() {
                if mb > 0 {
                    return mb;
                }
            }
        }
    }
    let phys = crate::physical_memory_bytes();
    let mb = (phys / DEFAULT_BUDGET_DIVISOR / (1024 * 1024)) as u64;
    mb.max(1)
}

/// Whether this image has already been placed under the kernel bound.
#[must_use]
pub fn is_armed() -> bool {
    std::env::var_os(ARMED_ENV).is_some()
}

/// The kernel-held footprint budget in force for this process, in bytes, or
/// `None` when nothing has bounded it.
///
/// This is the figure any *cooperative* in-process limit must stay under. A
/// cooperative ceiling above the kernel's is worse than none: the process
/// believes it has headroom it does not have, never runs its graceful
/// degradation path, and dies to a signal instead of reporting `unknown`.
///
/// Returns `None` before [`arm`] has run, and on platforms where `arm` is a
/// no-op — there is genuinely no kernel bound to derive from, so callers should
/// fall back to their physical-RAM policy rather than invent one.
#[must_use]
pub fn active_budget_bytes() -> Option<usize> {
    if !is_armed() {
        return None;
    }
    usize::try_from(budget_mb()).ok()?.checked_mul(1024 * 1024)
}

#[cfg(target_os = "macos")]
mod imp {
    use super::{
        budget_mb, ARMED_ENV, AS_SLACK, DARWIN_SONOMA, EXIT_UNGOVERNED, MIN_AS_HEADROOM_MB,
        PROBE_PROGRAM, ROOT_PID_ENV, TASKPOLICY,
    };
    use std::ffi::{CString, OsString};
    use std::mem::{size_of, zeroed};
    use std::os::unix::ffi::OsStringExt;
    use std::process::{Command, Stdio};

    /// This process's current address space, which IS the smallest settable
    /// `RLIMIT_AS`. Read directly rather than searched for: `govern-exec`
    /// measured the bisecting alternative at 19.1 ms per invocation against a
    /// 4.4 ms solve (+437%), which would distort the very measurements these
    /// binaries exist to produce. One `proc_pidinfo` call instead.
    ///
    /// Returns `None` when unavailable, in which case the caller skips L2
    /// rather than guessing a floor and breaking `setrlimit` outright.
    fn as_floor() -> Option<u64> {
        // SAFETY: `proc_taskinfo` is a C record of integer counters with no
        // invalid bit patterns; zero is a valid initialization for every field.
        let mut ti = unsafe { zeroed::<libc::proc_taskinfo>() };
        let size = size_of::<libc::proc_taskinfo>();
        // SAFETY: `proc_pidinfo` writes at most `size` bytes into `ti`, which is
        // an owned, exclusively borrowed local of exactly that type. The return
        // value is checked against the expected byte count before fields are read.
        let n = unsafe {
            libc::proc_pidinfo(
                libc::getpid(),
                libc::PROC_PIDTASKINFO,
                0,
                std::ptr::from_mut(&mut ti).cast::<libc::c_void>(),
                size as i32,
            )
        };
        if n == size as i32 && ti.pti_virtual_size > 0 {
            Some(ti.pti_virtual_size)
        } else {
            None
        }
    }

    /// The absolute path of the running executable.
    ///
    /// Resolved from the kernel's record via `std::env::current_exe`
    /// (`_NSGetExecutablePath` + `realpath` underneath), **never from
    /// `argv[0]`**. Renaming is precisely what `ay-base` and `ay-fixed` did, and
    /// a governor that trusts `argv[0]` re-execs the wrong file — or, if the
    /// name is not on `PATH`, nothing at all.
    fn self_path() -> Option<CString> {
        let exe = std::env::current_exe().ok()?;
        CString::new(OsString::from(exe).into_vec()).ok()
    }

    /// This kernel's Darwin major version, e.g. `22` for `22.6.0`.
    ///
    /// `uname` rather than a `sysctl` name lookup or a spawned `sw_vers`: one
    /// syscall, no string table, no process.
    fn darwin_major() -> Option<u32> {
        // SAFETY: `uname` writes into an owned, zeroed, exclusively-borrowed
        // `utsname`. The return value is checked before any field is read.
        let mut u = unsafe { zeroed::<libc::utsname>() };
        if unsafe { libc::uname(&raw mut u) } != 0 {
            return None;
        }
        // `release` is a NUL-terminated C string in a fixed-size array.
        let release: Vec<u8> = u
            .release
            .iter()
            .take_while(|&&c| c != 0)
            .map(|&c| c as u8)
            .collect();
        std::str::from_utf8(&release)
            .ok()?
            .split('.')
            .next()?
            .parse()
            .ok()
    }

    /// Can L1 — the `taskpolicy -m <MB>` jetsam footprint cap — actually be
    /// installed on this system?
    ///
    /// This has to be answered BEFORE the `execv` below, because that `execv`
    /// **succeeds** on a system whose `taskpolicy` lacks `-m`: the binary is
    /// present, it simply rejects the argument. By then this process has been
    /// replaced, so there is no `fail_closed` left to reach — the caller just
    /// sees `taskpolicy`'s usage text where `ay`'s output should be, and an
    /// exit code attributed to nothing. Every invocation on such a host dies
    /// that way, with no diagnostic naming `ay` at all.
    ///
    /// Answered by RUNNING `taskpolicy`, not by consulting a version table:
    /// the question is whether this exact binary takes the flag. The Darwin
    /// check is a fast path only — it can skip the probe, never fail it — so a
    /// stale table costs at most one spawn and can never silently drop the
    /// guard. That matters because the probe costs ~3.3 ms against the ~4.4 ms
    /// reference solve that already ruled out the bisecting `as_floor`
    /// alternative above; on a supported host it must not be paid at all.
    fn l1_installable(budget: u64) -> bool {
        if darwin_major().is_some_and(|major| major >= DARWIN_SONOMA) {
            return true;
        }
        Command::new(TASKPOLICY)
            .arg("-m")
            .arg(budget.to_string())
            .arg(PROBE_PROGRAM)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok_and(|status| status.success())
    }

    /// Apply L2, then re-exec this image under `taskpolicy` to apply L1.
    ///
    /// Never returns on success — the process is replaced.
    pub(super) fn arm() {
        let budget = budget_mb();

        // L2 FIRST, so it is inherited across our exec of taskpolicy AND
        // taskpolicy's exec of this image, and onward through anything forked.
        if let Some(floor) = as_floor() {
            // Headroom is the MAX of the budget-derived slack and a floor that
            // ordinary startup cannot cross (see `MIN_AS_HEADROOM_MB`). An
            // explicit `GOVERN_AY_MB` large enough to exceed the minimum still
            // widens the cap, so the knob keeps working upward.
            let headroom_mb = (AS_SLACK * budget).max(MIN_AS_HEADROOM_MB);
            let want = floor.saturating_add(headroom_mb * 1024 * 1024);
            let rl = libc::rlimit {
                rlim_cur: want,
                rlim_max: want,
            };
            // SAFETY: `rl` is an owned, fully-initialized `rlimit`; `RLIMIT_AS`
            // is a valid resource on this platform. Failure is reported via the
            // return value and is non-fatal (L1 below is the hard cap).
            if unsafe { libc::setrlimit(libc::RLIMIT_AS, &raw const rl) } != 0 {
                eprintln!(
                    "ay: WARNING: RLIMIT_AS {want} failed ({}); proceeding with the \
                     taskpolicy memlimit only",
                    std::io::Error::last_os_error()
                );
            }
        } else {
            eprintln!(
                "ay: WARNING: could not determine the RLIMIT_AS floor; proceeding \
                 with the taskpolicy memlimit only"
            );
        }

        // Ask before the point of no return. `execv` cannot report that
        // `taskpolicy` rejected `-m`, because by then we are gone.
        if !l1_installable(budget) {
            fail_closed(&format!(
                "{TASKPOLICY} does not accept `-m <MB>` on this system, so L1 -- \
                 the jetsam footprint cap -- cannot be installed (`-m` is a macOS \
                 14+ flag; this kernel is Darwin {}). L2 (RLIMIT_AS) is NOT a \
                 substitute: it bounds ADDRESS SPACE, and the runaway this guard \
                 exists to stop grows the FOOTPRINT inside already-mapped arena \
                 pages, which never crosses it",
                darwin_major().map_or_else(|| "unknown".to_owned(), |m| m.to_string())
            ));
        }

        let Some(exe) = self_path() else {
            fail_closed("could not resolve this executable's own path");
        };

        // Mark BEFORE exec: the re-exec'd image reads this and falls through.
        // SAFETY: single-threaded here -- arm() is the first statement of main,
        // before any thread is spawned -- so there is no concurrent getenv.
        unsafe { std::env::set_var(ARMED_ENV, "1") };

        // Record the ROOT pid before the exec chain, for callers that bind
        // provenance to the process they spawned. This is the last point at
        // which `std::process::id()` is still that pid: below, `execv` hands
        // off to `taskpolicy`, which execs the real image. See `ROOT_PID_ENV`.
        // SAFETY: as above -- still single-threaded, no concurrent getenv.
        unsafe { std::env::set_var(ROOT_PID_ENV, std::process::id().to_string()) };

        // L1 LAST: taskpolicy must be the IMMEDIATE exec'ing parent of the real
        // image, because any subsequent execve destroys the memlimit. Nothing
        // may be inserted between taskpolicy and this binary.
        let mb = CString::new(budget.to_string()).expect("budget digits are NUL-free");
        let Ok(tp) = CString::new(TASKPOLICY) else {
            fail_closed("taskpolicy path is not a valid C string");
        };
        let Ok(arg0) = CString::new("taskpolicy") else {
            fail_closed("argv[0] is not a valid C string");
        };
        let Ok(flag) = CString::new("-m") else {
            fail_closed("flag is not a valid C string");
        };

        let mut owned: Vec<CString> = vec![arg0, flag, mb, exe];
        for a in std::env::args_os().skip(1) {
            match CString::new(a.into_vec()) {
                Ok(c) => owned.push(c),
                // An argument containing NUL cannot round-trip through execv.
                // It also cannot have reached us from a real shell. Refuse
                // rather than silently dropping a caller's argument.
                Err(_) => fail_closed("an argument contains an interior NUL byte"),
            }
        }
        let mut argv: Vec<*const libc::c_char> = owned.iter().map(|c| c.as_ptr()).collect();
        argv.push(std::ptr::null());

        // SAFETY: `tp` is a valid NUL-terminated path and `argv` is a
        // NULL-terminated array of pointers to NUL-terminated strings, all of
        // which outlive the call (`owned` is still in scope). On success execv
        // does not return.
        unsafe { libc::execv(tp.as_ptr(), argv.as_ptr()) };

        fail_closed(&format!(
            "exec {TASKPOLICY} failed ({})",
            std::io::Error::last_os_error()
        ));
    }

    /// Report why the bound could not be established and exit without running.
    fn fail_closed(why: &str) -> ! {
        eprintln!(
            "ay: FATAL: {why}. Refusing to run ungoverned -- an unbounded solver on \
             this machine is a kernel panic (four so far; the last was 2026-08-02, \
             355.7 GB on a 128 GB box)."
        );
        std::process::exit(EXIT_UNGOVERNED);
    }

    #[cfg(test)]
    mod tests {
        use super::{darwin_major, l1_installable, Command, Stdio, PROBE_PROGRAM, TASKPOLICY};

        /// The Darwin fast path exists only to SKIP the probe, so it must never
        /// disagree with it. If this fires on some host, `DARWIN_SONOMA` is
        /// wrong there — and a wrong table either refuses a machine that could
        /// be governed, or (worse) skips the probe on one that cannot.
        #[test]
        fn darwin_fast_path_agrees_with_the_taskpolicy_probe() {
            let authority = Command::new(TASKPOLICY)
                .arg("-m")
                .arg("64")
                .arg(PROBE_PROGRAM)
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .status()
                .is_ok_and(|status| status.success());

            assert_eq!(
                l1_installable(64),
                authority,
                "the Darwin {} fast path disagrees with actually running \
                 `{TASKPOLICY} -m`; DARWIN_SONOMA is wrong for this host",
                darwin_major().map_or_else(|| "?".to_owned(), |m| m.to_string())
            );
        }

        /// A `None` here silently sends every host down the probe path.
        #[test]
        fn darwin_major_is_readable() {
            assert!(
                darwin_major().is_some_and(|major| major >= 8),
                "uname gave no usable Darwin major version: {:?}",
                darwin_major()
            );
        }
    }
}

#[cfg(not(target_os = "macos"))]
mod imp {
    /// Non-macOS platforms have no `taskpolicy` and no jetsam. The panics this
    /// module exists to prevent are all macOS ones, and Linux harnesses already
    /// have `ulimit -v` / cgroups, which actually work there. Do nothing rather
    /// than pretend to a bound we are not holding.
    pub(super) fn arm() {}
}

/// Place this process under a kernel-held memory bound, then continue.
///
/// Call this as the **first statement of `main`**, before any allocation or
/// thread spawn — it re-execs the process, so anything done beforehand is
/// discarded work, and [`std::env::set_var`] requires single-threadedness.
///
/// On macOS this normally does not return: the process is replaced by itself
/// running under `taskpolicy`. The replacement re-enters here, observes
/// [`ARMED_ENV`], and returns immediately, so `main` runs exactly once.
///
/// # Panics
///
/// Does not panic. If the bound cannot be established it exits with
/// [`EXIT_UNGOVERNED`] rather than running unbounded.
pub fn arm() {
    if is_armed() {
        return;
    }
    imp::arm();
}
