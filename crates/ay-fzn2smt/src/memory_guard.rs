// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Stop `ay flatzinc solve` before a memory limit kills it.
//!
//! MiniZinc passes no memory flag. The limit is read the way ay's other
//! entries read theirs: the `MEMORY_LIMIT` variable (MiB) that the MiniZinc
//! harness sets for the job (sb's `run_mzn.py` sets it, as the Challenge's
//! containers do), and the bounds the kernel shows the process (cgroup
//! `memory.max` / `memory.limit_in_bytes` over the process's cgroup and its
//! ancestors, `RLIMIT_AS`, `RLIMIT_DATA`). ay's own limit is 90% of the
//! tightest of them ([`ay_sys::memory_ceiling`]).
//!
//! Three layers, as for `ay solve --memory-ceiling-bytes`:
//!
//! 1. `ay_sys::set_process_memory_limit`: solver checkpoints that poll the
//!    process memory end their query with `unknown`, and the FlatZinc loops
//!    then report what they have.
//! 2. A watchdog thread polls this process's resident memory against ay's
//!    limit and, on Linux, the job's cgroup usage against the cgroup limit:
//!    the cgroup also holds MiniZinc (2.2 GB resident on warehouse/wlp22),
//!    and it is the cgroup that the kernel kills. At 95% it asks the run to
//!    stop; if the run has not ended after a short grace, or usage reaches
//!    98%, it ends the process.
//! 3. The allocator's hard ceiling at ay's limit catches a burst between two
//!    polls.
//!
//! The same supervision holds the run to its `-t` deadline
//! ([`arm_deadline`]): half a second before the deadline the solvers are
//! asked to stop, and a run still going at the deadline is ended.
//!
//! Whichever ends the run prints `=====UNKNOWN=====` only when nothing has
//! been written to the solution stream: a solution already printed stays the
//! answer, and nothing follows it (a status line after a solution would be a
//! format fault).

use std::io::{self, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, PoisonError};
use std::time::{Duration, Instant};

use ay_sys::memory_ceiling::{KernelMemoryBounds, MemoryCeiling};
use ay_sys::CeilingSettlement;

/// The variable the MiniZinc harness sets to the job's memory limit, in MiB.
pub const MEMORY_LIMIT_ENV: &str = "MEMORY_LIMIT";

/// Where usage asks the run to stop, in percent of the budget.
const STOP_PERCENT: usize = 95;
/// Where usage ends the process without waiting out the grace, in percent.
const CRITICAL_PERCENT: usize = 98;
/// How often the watchdog samples memory.
const POLL: Duration = Duration::from_millis(20);
/// How long a requested stop may take before the watchdog ends the process.
const GRACE: Duration = Duration::from_secs(2);

/// The status line of a run that stopped with no solution.
const UNKNOWN_LINE: &[u8] = b"=====UNKNOWN=====\n";

/// Set once any byte of the solution stream has been written.
static OUTPUT_STARTED: AtomicBool = AtomicBool::new(false);
/// Serialises solution-stream writes with the watchdog's final status line.
static OUTPUT_GATE: Mutex<()> = Mutex::new(());

/// The allocator ceiling's breach action: UNKNOWN, unless the settlement
/// below finds a solution stream already started.
static HARD_CEILING_ACTION: ay_sys::HardMemoryCeiling = ay_sys::HardMemoryCeiling {
    stdout_line: UNKNOWN_LINE,
    stderr_line: b"warning: memory limit reached; stopping\n",
    exit_code: 0,
    statistics: None,
};

/// The solution-stream writer under supervision: it records that output has
/// started, so a memory stop never adds a status line after a solution.
pub struct GuardedOutput<W: Write> {
    inner: W,
}

impl<W: Write> GuardedOutput<W> {
    /// Wrap `inner`, normally stdout.
    pub fn new(inner: W) -> Self {
        Self { inner }
    }
}

impl<W: Write> Write for GuardedOutput<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let _gate = OUTPUT_GATE.lock().unwrap_or_else(PoisonError::into_inner);
        if !buf.is_empty() {
            OUTPUT_STARTED.store(true, Ordering::SeqCst);
        }
        self.inner.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        let _gate = OUTPUT_GATE.lock().unwrap_or_else(PoisonError::into_inner);
        self.inner.flush()
    }
}

/// The memory limit in bytes named by a `MEMORY_LIMIT` value in MiB; `None`
/// when it is unset, not a positive integer, or not addressable.
#[must_use]
pub fn env_ceiling_bytes(value: Option<&str>) -> Option<usize> {
    let mib: usize = value?.trim().parse().ok().filter(|&mib| mib > 0)?;
    mib.checked_mul(1024 * 1024)
}

/// ay's own limit for a FlatZinc run: 90% of the tightest of the harness's
/// `MEMORY_LIMIT` and the kernel bounds, or `None` when nothing bounds the
/// run (then nothing is supervised, as before).
#[must_use]
pub fn plan_limit(
    env_ceiling: Option<usize>,
    bounds: KernelMemoryBounds,
    peers: usize,
) -> Option<MemoryCeiling> {
    let kernel_bound = [
        bounds.cgroup,
        bounds.rlimit_as,
        bounds.rlimit_data,
        bounds.govern_budget,
    ]
    .into_iter()
    .flatten()
    .any(|bytes| bytes > 0);
    if env_ceiling.is_none() && !kernel_bound {
        return None;
    }
    Some(ay_sys::memory_ceiling::limit_under_ceiling_from(
        env_ceiling.unwrap_or(usize::MAX),
        bounds,
        peers,
    ))
}

/// One cgroup level that states a memory limit: its limit and its usage
/// other than page cache, which the kernel reclaims before it kills.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CgroupUsage {
    /// `memory.max` in bytes.
    pub limit: usize,
    /// `memory.current` less the `file` bytes of `memory.stat`.
    pub used: usize,
}

/// Where a memory sample stands against the limits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemoryState {
    /// Below every stop threshold.
    Within,
    /// At or past [`STOP_PERCENT`] of a budget: ask the run to stop.
    Stop,
    /// At or past [`CRITICAL_PERCENT`] of a budget: end the process now.
    Critical,
}

/// Classify a sample: this process's memory pressure against ay's limit,
/// and each limited cgroup level's usage against 90% of its limit (the same
/// headroom ay keeps below a kernel bound).
#[must_use]
pub fn memory_state(own_pressure: usize, own_limit: usize, cgroups: &[CgroupUsage]) -> MemoryState {
    let percent_of = |used: usize, budget: usize| -> usize {
        if budget == 0 {
            return 0;
        }
        used.saturating_mul(100) / budget
    };
    let mut worst = percent_of(own_pressure, own_limit);
    for level in cgroups {
        let budget = ay_sys::KERNEL_BUDGET_HEADROOM_PERCENT.saturating_mul(level.limit / 100);
        worst = worst.max(percent_of(level.used, budget));
    }
    if worst >= CRITICAL_PERCENT {
        MemoryState::Critical
    } else if worst >= STOP_PERCENT {
        MemoryState::Stop
    } else {
        MemoryState::Within
    }
}

/// Supervise this run's memory against the limit the harness and the kernel
/// state. Returns the limit, or `None` when nothing bounds the run.
pub fn arm_from_environment(err: &mut impl Write) -> Option<MemoryCeiling> {
    let env_value = std::env::var(MEMORY_LIMIT_ENV).ok();
    let env_ceiling = env_ceiling_bytes(env_value.as_deref());
    let bounds = KernelMemoryBounds::detect();
    // The peer split of `limit_under_ceiling` applies to the planned ceiling;
    // `plan_limit` only decides whether there is one.
    plan_limit(env_ceiling, bounds, 1)?;
    let ceiling = ay_sys::memory_ceiling::limit_under_ceiling(env_ceiling.unwrap_or(usize::MAX));
    let limit = ceiling.limit_bytes;
    let _ = writeln!(
        err,
        "info: FlatZinc memory limit {} MiB ({}); the run stops with UNKNOWN before it",
        limit / (1024 * 1024),
        ceiling.origin()
    );
    ay_sys::set_process_memory_limit(limit);
    ay_sys::set_hard_memory_ceiling_settlement(settle_at_hard_ceiling);
    ay_sys::arm_hard_memory_ceiling(limit, &HARD_CEILING_ACTION);
    std::thread::Builder::new()
        .name("fzn-memory-watchdog".to_string())
        .spawn(move || watchdog(limit))
        .ok()?;
    Some(ceiling)
}

/// The allocator ceiling's settlement: silent once a solution was written.
fn settle_at_hard_ceiling(armed_exit_code: i32) -> CeilingSettlement {
    if OUTPUT_STARTED.load(Ordering::SeqCst) {
        CeilingSettlement::Silent(armed_exit_code)
    } else {
        CeilingSettlement::ArmedVerdict
    }
}

fn sample(limit: usize) -> MemoryState {
    memory_state(
        ay_sys::current_memory_pressure_bytes(),
        limit,
        &live_cgroup_usage(),
    )
}

fn watchdog(limit: usize) {
    while sample(limit) == MemoryState::Within {
        std::thread::sleep(POLL);
    }
    // Ask the solvers to stop: their checkpoints answer `unknown` and the
    // FlatZinc loops report what they have.
    ay_core::resource::cancel_process();
    let stop_requested = Instant::now();
    while stop_requested.elapsed() < GRACE && sample(limit) != MemoryState::Critical {
        std::thread::sleep(POLL);
    }
    let _ = io::stderr().write_all(b"warning: memory limit reached; stopping\n");
    finish_without_answer();
}

/// How long before the `-t` deadline [`arm_deadline`] asks the run to stop
/// (also about how long [`finish_without_answer`] waits for a solution write
/// in progress).
const DEADLINE_GRACE: Duration = Duration::from_millis(500);

/// Hold the run to its `-t` deadline: [`DEADLINE_GRACE`] before it ask the
/// solvers to stop (as a memory stop does), and if the run has not ended at
/// the deadline, end the process the way a memory stop does: UNKNOWN when no
/// solution was written, else nothing after the incumbent.
///
/// The solvers keep the deadline themselves, but not every step of a run
/// polls it: translating and declaring a large model on the SMT path does
/// not, and MiniZinc `nside/EASY_1000_100` and `saeling/m016` ran 30 s past
/// a `-t 30000` until `timeout 60` killed them, with nothing printed
/// (2026-11-19). A run that outlives its time limit is a fault.
pub fn arm_deadline(deadline: Instant) {
    let _ = std::thread::Builder::new()
        .name("fzn-deadline-watchdog".to_string())
        .spawn(move || {
            deadline_watchdog(
                deadline,
                DEADLINE_GRACE,
                ay_core::resource::cancel_process,
                || {
                    let _ = io::stderr().write_all(b"warning: time limit reached; stopping\n");
                    finish_without_answer()
                },
            );
        });
}

/// [`arm_deadline`]'s schedule, with the two actions given: `stop` `grace`
/// before `deadline` (at once if that is past), `finish` at `deadline`.
pub(crate) fn deadline_watchdog(
    deadline: Instant,
    grace: Duration,
    stop: impl FnOnce(),
    finish: impl FnOnce(),
) {
    sleep_until(deadline.checked_sub(grace).unwrap_or(deadline));
    stop();
    sleep_until(deadline);
    finish();
}

fn sleep_until(when: Instant) {
    // `sleep` may wake early on some platforms: sleep until it is time.
    loop {
        let now = Instant::now();
        if now >= when {
            return;
        }
        std::thread::sleep(when - now);
    }
}

/// End the process: UNKNOWN when no solution was written, else nothing.
fn finish_without_answer() -> ! {
    // Wait briefly for a solution write in progress; never block the exit
    // on a writer stuck on a full pipe.
    let gate_deadline = Instant::now() + Duration::from_millis(500);
    let _gate = loop {
        match OUTPUT_GATE.try_lock() {
            Ok(gate) => break Some(gate),
            Err(std::sync::TryLockError::Poisoned(gate)) => break Some(gate.into_inner()),
            Err(std::sync::TryLockError::WouldBlock) if Instant::now() < gate_deadline => {
                std::thread::sleep(Duration::from_millis(5));
            }
            Err(std::sync::TryLockError::WouldBlock) => break None,
        }
    };
    if !OUTPUT_STARTED.swap(true, Ordering::SeqCst) {
        let mut out = io::stdout();
        let _ = out.write_all(UNKNOWN_LINE);
        let _ = out.flush();
    }
    std::process::exit(0)
}

/// The limited cgroup levels of this process (v2), outermost first.
#[cfg(target_os = "linux")]
fn live_cgroup_usage() -> Vec<CgroupUsage> {
    use std::path::{Component, Path, PathBuf};
    let own = std::fs::read_to_string("/proc/self/cgroup").unwrap_or_default();
    let Some(path) = own.lines().find_map(|line| line.strip_prefix("0::")) else {
        return Vec::new();
    };
    let mut dir = PathBuf::from("/sys/fs/cgroup");
    let mut levels = Vec::new();
    for component in Path::new(path).components() {
        match component {
            Component::Normal(name) => dir.push(name),
            Component::RootDir | Component::CurDir => continue,
            Component::ParentDir | Component::Prefix(_) => break,
        }
        if let Some(level) = cgroup_level_usage(
            std::fs::read_to_string(dir.join("memory.max"))
                .ok()
                .as_deref(),
            std::fs::read_to_string(dir.join("memory.current"))
                .ok()
                .as_deref(),
            std::fs::read_to_string(dir.join("memory.stat"))
                .ok()
                .as_deref(),
        ) {
            levels.push(level);
        }
    }
    levels
}

#[cfg(not(target_os = "linux"))]
fn live_cgroup_usage() -> Vec<CgroupUsage> {
    Vec::new()
}

/// One level's usage from its `memory.max`, `memory.current` and
/// `memory.stat` contents; `None` when it states no limit or no usage.
#[must_use]
pub fn cgroup_level_usage(
    max: Option<&str>,
    current: Option<&str>,
    stat: Option<&str>,
) -> Option<CgroupUsage> {
    let limit: usize = max?.trim().parse().ok().filter(|&bytes| bytes > 0)?;
    let current: usize = current?.trim().parse().ok()?;
    let file: usize = stat
        .and_then(|stat| {
            stat.lines()
                .find_map(|line| line.strip_prefix("file ")?.trim().parse().ok())
        })
        .unwrap_or(0);
    Some(CgroupUsage {
        limit,
        used: current.saturating_sub(file),
    })
}

#[cfg(test)]
#[path = "memory_guard_tests.rs"]
mod tests;
