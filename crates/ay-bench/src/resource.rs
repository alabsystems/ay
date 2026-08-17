// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared resource admission for benchmark subprocesses.
//!
//! `scripts/_oom_guard.py` is the repository's single source of truth for RAM
//! headroom, job caps, and RSS-backstop behavior.  Native Rust harnesses use
//! its machine-readable `plan` output and attach its `rss_watchdog` to external
//! solver process groups through one campaign-wide `watch-server` sidecar.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};
use wait_timeout::ChildExt as _;

use crate::error::{BenchError, Result, WithContext as _};

pub(crate) const MAX_DECOMPRESSED_BYTES: u64 = 8 * 1024 * 1024 * 1024;
pub(crate) const MAX_METADATA_BYTES: u64 = 64 * 1024 * 1024;
/// Fixed parent-memory bounds for corpus discovery. Callers may retain fewer
/// benchmark paths, but every traversal must enforce all three ceilings.
pub(crate) const MAX_CORPUS_TRAVERSAL_ENTRIES: usize = 2_000_000;
pub(crate) const MAX_CORPUS_PENDING_DIRECTORIES: usize = 100_000;
pub(crate) const MAX_DISCOVERED_BENCHMARKS: usize = 1_000_000;
// `Duration::from_days` is not stable/const on the workspace toolchain yet.
#[allow(
    clippy::duration_suboptimal_units,
    reason = "the clearer day constructor is not available as a stable const fn"
)]
const MAX_BENCHMARK_TIMEOUT: Duration = Duration::from_secs(7 * 24 * 60 * 60);

fn monotonic_time_ns() -> Result<u64> {
    #[cfg(unix)]
    {
        let timestamp = nix::time::clock_gettime(nix::time::ClockId::CLOCK_MONOTONIC)
            .map_err(|error| BenchError::msg(format!("reading monotonic clock failed: {error}")))?;
        let elapsed: Duration = timestamp.into();
        u64::try_from(elapsed.as_nanos())
            .map_err(|_| BenchError::msg("monotonic clock value exceeds u64 nanoseconds"))
    }
    #[cfg(not(unix))]
    {
        Err(BenchError::msg(
            "monotonic cross-process timestamps require POSIX clock_gettime",
        ))
    }
}

fn watchdog_breached_before(outcome: WatchdogOutcome, trigger_ns: u64) -> Result<bool> {
    if !outcome.breached {
        return Ok(false);
    }
    let breach_ns = outcome
        .breach_time_ns
        .ok_or_else(|| BenchError::msg("RSS watchdog breach timestamp is missing"))?;
    Ok(breach_ns <= trigger_ns)
}

/// Closed, machine-readable enforcement tags. Comparison code must reject
/// legacy free-form descriptions because they do not prove that the same
/// resource mechanism was actually active.
pub const ENFORCEMENT_RSS_WATCHDOG_V1: &str = "ay-resource-v1:rss-watchdog-zero-grace";
pub const ENFORCEMENT_AY_MEMORY_V1: &str = "ay-resource-v1:ay-memory";
pub const ENFORCEMENT_AY_MEMORY_RSS_V1: &str = "ay-resource-v1:ay-memory+rss-watchdog-zero-grace";
pub const ENFORCEMENT_AY_PB_MEMLIMIT_V1: &str = "ay-resource-v1:ay-pb-memlimit";
const AGGREGATE_ENFORCEMENT_V1: &str = "ay-host-exclusive-flock-v1";

pub(crate) fn checked_benchmark_timeout(value: f64, label: &str) -> Result<Duration> {
    let duration = Duration::try_from_secs_f64(value).map_err(|_| BenchError::InvalidArgs {
        reason: format!("{label} timeout must be finite, positive, and representable"),
    })?;
    if duration.is_zero() || duration > MAX_BENCHMARK_TIMEOUT {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "{label} timeout must be between one nanosecond and {} seconds",
                MAX_BENCHMARK_TIMEOUT.as_secs()
            ),
        });
    }
    Ok(duration)
}

/// Parse solver output only when every textual verdict agrees and the process
/// exit status is compatible with it. Signals, crashes, and contradictory
/// status lines are errors even if an earlier line looked definitive.
pub(crate) fn strict_solver_verdict(
    stdout: &str,
    stderr: &str,
    exit_code: Option<i32>,
) -> &'static str {
    let Some(exit_code) = exit_code else {
        return "error";
    };
    let fatal_diagnostic = stdout.lines().chain(stderr.lines()).any(|line| {
        let lower = line.trim().to_ascii_lowercase();
        lower == "error"
            || lower.starts_with("error:")
            || lower.starts_with("(error ")
            || lower == "fatal"
            || lower.starts_with("fatal:")
            || lower.starts_with("panic:")
            || lower.contains("panicked at")
            || lower == "segmentation fault"
    });
    if fatal_diagnostic {
        return "error";
    }
    let mut observed: Option<&'static str> = None;
    for line in stdout.lines().chain(stderr.lines()) {
        let lower = line.trim().to_ascii_lowercase();
        let verdict = match lower.as_str() {
            "sat" | "s satisfiable" | "satisfiable" => Some("sat"),
            "unsat" | "s unsatisfiable" | "unsatisfiable" => Some("unsat"),
            "unknown" | "s unknown" | "timeout" => Some("unknown"),
            _ => None,
        };
        let Some(verdict) = verdict else {
            continue;
        };
        if observed.is_some_and(|previous| previous != verdict) {
            return "error";
        }
        observed = Some(verdict);
    }
    match observed {
        Some("sat") if matches!(exit_code, 0 | 10) => "sat",
        Some("unsat") if matches!(exit_code, 0 | 20) => "unsat",
        Some("unknown") if exit_code == 0 => "unknown",
        Some(_) => "error",
        None if exit_code == 10 => "sat",
        None if exit_code == 20 => "unsat",
        None if exit_code == 0 => "error",
        None => "error",
    }
}

/// Read a manifest or report with a pre-allocation size check and a second
/// streaming limit for files that grow after `metadata` is sampled.
pub(crate) fn read_bounded_text(path: &Path, limit: u64, label: &str) -> Result<String> {
    use std::io::Read as _;

    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
    }
    let file = options
        .open(path)
        .with_bench_context(|| format!("opening {label} {}", path.display()))?;
    let metadata = file
        .metadata()
        .with_bench_context(|| format!("stat open {label} {}", path.display()))?;
    if !metadata.file_type().is_file() {
        return Err(BenchError::msg(format!(
            "{label} {} is not a non-symlink regular file",
            path.display()
        )));
    }
    if metadata.len() > limit {
        return Err(BenchError::msg(format!(
            "{label} {} exceeds the fixed {limit}-byte parent-memory limit",
            path.display()
        )));
    }
    let mut bytes = Vec::with_capacity(usize::try_from(metadata.len()).unwrap_or(0));
    file.take(limit.saturating_add(1))
        .read_to_end(&mut bytes)
        .with_bench_context(|| format!("reading {label} {}", path.display()))?;
    if bytes.len() as u64 > limit {
        return Err(BenchError::msg(format!(
            "{label} {} grew beyond the fixed {limit}-byte parent-memory limit",
            path.display()
        )));
    }
    String::from_utf8(bytes).map_err(|error| {
        BenchError::msg(format!(
            "{label} {} is not valid UTF-8: {error}",
            path.display()
        ))
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct StoreFileIdentity {
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
    #[cfg(not(unix))]
    created: Option<std::time::SystemTime>,
}

impl StoreFileIdentity {
    fn from_metadata(metadata: &std::fs::Metadata) -> Self {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            Self {
                device: metadata.dev(),
                inode: metadata.ino(),
            }
        }
        #[cfg(not(unix))]
        {
            Self {
                created: metadata.created().ok(),
            }
        }
    }
}

/// Retained authority for one SQLite evidence store. The reservation remains
/// open for the connection lifetime so later checks never infer ownership from
/// a mutable pathname alone.
pub(crate) struct PreparedStorePath {
    resolved: PathBuf,
    label: String,
    reservation: std::fs::File,
    identity: StoreFileIdentity,
    #[cfg(target_os = "linux")]
    descriptors_before_sqlite_open: std::collections::BTreeSet<i32>,
    #[cfg(target_os = "linux")]
    sqlite_descriptor: Option<i32>,
}

impl PreparedStorePath {
    pub(crate) fn path(&self) -> &Path {
        &self.resolved
    }

    fn validate_metadata(&self, metadata: &std::fs::Metadata, subject: &str) -> Result<()> {
        if !metadata.file_type().is_file() {
            return Err(BenchError::msg(format!(
                "{} {subject} is not a regular file: {}",
                self.label,
                self.resolved.display()
            )));
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            if metadata.nlink() != 1 {
                return Err(BenchError::msg(format!(
                    "{} {subject} has unexpected hard links: {}",
                    self.label,
                    self.resolved.display()
                )));
            }
        }
        if StoreFileIdentity::from_metadata(metadata) != self.identity {
            return Err(BenchError::msg(format!(
                "{} {subject} changed identity: {}",
                self.label,
                self.resolved.display()
            )));
        }
        Ok(())
    }

    fn verify_visible_reservation(&self) -> Result<()> {
        let descriptor_metadata = self.reservation.metadata().with_bench_context(|| {
            format!(
                "stat retained {} reservation {}",
                self.label,
                self.resolved.display()
            )
        })?;
        self.validate_metadata(&descriptor_metadata, "reservation descriptor")?;
        let path_metadata = std::fs::symlink_metadata(&self.resolved).with_bench_context(|| {
            format!(
                "stat visible {} reservation {}",
                self.label,
                self.resolved.display()
            )
        })?;
        self.validate_metadata(&path_metadata, "visible reservation")
    }

    #[cfg(target_os = "linux")]
    fn matching_linux_descriptors(&self) -> Result<std::collections::BTreeSet<i32>> {
        let entries = std::fs::read_dir("/proc/self/fd")
            .with_bench_context(|| format!("enumerating descriptors for {}", self.label))?
            .collect::<std::io::Result<Vec<_>>>()
            .with_bench_context(|| format!("reading descriptors for {}", self.label))?;
        let mut matching = std::collections::BTreeSet::new();
        for entry in entries {
            let Some(fd) = entry
                .file_name()
                .to_str()
                .and_then(|value| value.parse::<i32>().ok())
            else {
                continue;
            };
            let metadata = match std::fs::metadata(entry.path()) {
                Ok(metadata) => metadata,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
                Err(error) => return Err(error.into()),
            };
            if metadata.file_type().is_file()
                && StoreFileIdentity::from_metadata(&metadata) == self.identity
            {
                matching.insert(fd);
            }
        }
        Ok(matching)
    }

    /// Authenticate that the just-opened SQLite connection acquired a new OS
    /// descriptor for the exact retained reservation, rather than a pathname
    /// replacement. Linux exposes the connection's descriptor through procfs;
    /// other targets still retain and revalidate the reservation/path identity.
    pub(crate) fn authenticate_sqlite_open(&mut self) -> Result<()> {
        self.verify_visible_reservation()?;
        #[cfg(target_os = "linux")]
        {
            let after = self.matching_linux_descriptors()?;
            let sqlite_descriptors = after
                .difference(&self.descriptors_before_sqlite_open)
                .copied()
                .collect::<Vec<_>>();
            self.sqlite_descriptor = match sqlite_descriptors.as_slice() {
                [descriptor] => Some(*descriptor),
                [] => {
                    return Err(BenchError::msg(format!(
                        "SQLite did not retain a descriptor for the authenticated {} reservation {}",
                        self.label,
                        self.resolved.display()
                    )));
                }
                _ => {
                    return Err(BenchError::msg(format!(
                        "SQLite open produced ambiguous descriptors for the authenticated {} reservation {}",
                        self.label,
                        self.resolved.display()
                    )));
                }
            };
        }
        Ok(())
    }

    pub(crate) fn verify_connection_authority(&self) -> Result<()> {
        self.verify_visible_reservation()?;
        #[cfg(target_os = "linux")]
        {
            let descriptor = self.sqlite_descriptor.ok_or_else(|| {
                BenchError::msg(format!(
                    "SQLite {} descriptor was never authenticated for {}",
                    self.label,
                    self.resolved.display()
                ))
            })?;
            let descriptor_path = PathBuf::from(format!("/proc/self/fd/{descriptor}"));
            let metadata = std::fs::metadata(&descriptor_path).with_bench_context(|| {
                format!(
                    "checking authenticated SQLite {} descriptor {descriptor} for {}",
                    self.label,
                    self.resolved.display()
                )
            })?;
            self.validate_metadata(&metadata, "SQLite connection descriptor")?;
        }
        Ok(())
    }
}

/// Resolve and atomically reserve a SQLite evidence-store target through one
/// canonical, private parent directory. Existing targets are opened with
/// no-follow semantics; new targets are created mode 0600. The exact descriptor
/// is returned and must be retained for the SQLite connection lifetime.
pub(crate) fn prepare_private_store_path(path: &Path, label: &str) -> Result<PreparedStorePath> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let file_name = path.file_name().ok_or_else(|| BenchError::InvalidArgs {
        reason: format!("{label} path has no file name: {}", path.display()),
    })?;
    let parent_existed = parent.exists();
    std::fs::create_dir_all(parent)
        .with_bench_context(|| format!("creating {label} directory {}", parent.display()))?;
    #[cfg(unix)]
    if !parent_existed || parent.file_name().is_some_and(|name| name == ".ay-bench") {
        use std::os::unix::fs::PermissionsExt as _;
        std::fs::set_permissions(parent, std::fs::Permissions::from_mode(0o700))
            .with_bench_context(|| format!("securing {label} directory {}", parent.display()))?;
    }
    let canonical_parent = std::fs::canonicalize(parent)
        .with_bench_context(|| format!("resolving {label} directory {}", parent.display()))?;
    let parent_metadata = std::fs::metadata(&canonical_parent)?;
    if !parent_metadata.is_dir() {
        return Err(BenchError::msg(format!(
            "{label} parent is not a directory: {}",
            canonical_parent.display()
        )));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        if parent_metadata.permissions().mode() & 0o022 != 0 {
            return Err(BenchError::msg(format!(
                "{label} parent is group/world writable: {}",
                canonical_parent.display()
            )));
        }
    }
    let resolved = canonical_parent.join(file_name);
    let reservation = match std::fs::symlink_metadata(&resolved) {
        Ok(metadata) => {
            if !metadata.file_type().is_file() {
                return Err(BenchError::msg(format!(
                    "{label} target is not a non-symlink regular file: {}",
                    resolved.display()
                )));
            }
            #[cfg(unix)]
            {
                use std::os::unix::fs::MetadataExt as _;
                if metadata.nlink() != 1 {
                    return Err(BenchError::msg(format!(
                        "{label} target has unexpected hard links: {}",
                        resolved.display()
                    )));
                }
            }
            let mut options = std::fs::OpenOptions::new();
            options.read(true).write(true);
            #[cfg(unix)]
            {
                use std::os::unix::fs::OpenOptionsExt as _;
                options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
            }
            options.open(&resolved).with_bench_context(|| {
                format!(
                    "opening existing {label} reservation {}",
                    resolved.display()
                )
            })?
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            let mut options = std::fs::OpenOptions::new();
            options.read(true).write(true).create_new(true);
            #[cfg(unix)]
            {
                use std::os::unix::fs::OpenOptionsExt as _;
                options
                    .mode(0o600)
                    .custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
            }
            let file = options.open(&resolved).with_bench_context(|| {
                format!("securely reserving new {label} {}", resolved.display())
            })?;
            file.sync_all().with_bench_context(|| {
                format!("syncing new {label} reservation {}", resolved.display())
            })?;
            file
        }
        Err(error) => return Err(error.into()),
    };
    let descriptor_metadata = reservation.metadata().with_bench_context(|| {
        format!("stat retained {label} reservation {}", resolved.display())
    })?;
    if !descriptor_metadata.file_type().is_file() {
        return Err(BenchError::msg(format!(
            "{label} reservation is not a regular file: {}",
            resolved.display()
        )));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        if descriptor_metadata.nlink() != 1 {
            return Err(BenchError::msg(format!(
                "{label} reservation has unexpected hard links: {}",
                resolved.display()
            )));
        }
    }
    let identity = StoreFileIdentity::from_metadata(&descriptor_metadata);
    let prepared = PreparedStorePath {
        resolved,
        label: label.to_string(),
        reservation,
        identity,
        #[cfg(target_os = "linux")]
        descriptors_before_sqlite_open: std::collections::BTreeSet::new(),
        #[cfg(target_os = "linux")]
        sqlite_descriptor: None,
    };
    prepared.verify_visible_reservation()?;
    #[cfg(target_os = "linux")]
    let prepared = {
        let mut prepared = prepared;
        prepared.descriptors_before_sqlite_open = prepared.matching_linux_descriptors()?;
        prepared
    };
    Ok(prepared)
}

/// Stable corpus key shared by native results and harvested baselines.
/// Only strict UTF-8 normal components below the canonical corpus root are
/// accepted; absolute/lossy/basename fallback would make different inputs
/// collide in persistent evidence stores.
pub(crate) fn normalized_relative_id(path: &Path, corpus_root: &Path) -> Result<String> {
    let relative = path.strip_prefix(corpus_root).map_err(|_| {
        BenchError::msg(format!(
            "benchmark {} is outside corpus root {}",
            path.display(),
            corpus_root.display()
        ))
    })?;
    let mut segments = Vec::new();
    for component in relative.components() {
        let std::path::Component::Normal(segment) = component else {
            return Err(BenchError::msg(format!(
                "benchmark has a non-normal corpus-relative path: {}",
                path.display()
            )));
        };
        let segment = segment.to_str().ok_or_else(|| {
            BenchError::msg(format!(
                "benchmark path is not valid UTF-8: {}",
                path.display()
            ))
        })?;
        if segment.chars().any(char::is_control) {
            return Err(BenchError::msg(format!(
                "benchmark path contains control characters: {}",
                path.display()
            )));
        }
        segments.push(segment);
    }
    if segments.is_empty() {
        return Err(BenchError::msg(format!(
            "benchmark path has an empty corpus-relative identifier: {}",
            path.display()
        )));
    }
    Ok(segments.join("/"))
}

/// Persistable resource envelope returned by `_oom_guard.py plan`.
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct ResourcePlan {
    /// Parallelism requested by the caller before host admission.
    pub requested_jobs: usize,
    /// Parallelism admitted by the planner.
    pub jobs: usize,
    /// Enforced process-group RSS budget for each child.
    pub memlimit_mb_per_child: usize,
    /// Solver core budget exported as `NBCORE`.
    pub nbcore_per_child: usize,
    /// Host-memory headroom reserved outside child budgets.
    pub headroom_mb: usize,
    /// Repository-relative or absolute planner path used for admission.
    pub planner: String,
}

impl ResourcePlan {
    fn numeric_limits_valid(&self) -> bool {
        self.requested_jobs > 0
            && self.jobs > 0
            && self.memlimit_mb_per_child > 0
            && self.nbcore_per_child > 0
            && self.jobs <= self.requested_jobs
    }
}

/// Canonical persisted envelope for timing/throughput comparability. Numeric
/// admission alone is insufficient: the exact enforcement mechanism and the
/// normalized wall timeout are part of the execution envelope too.
pub fn effective_execution_envelope(
    plan: &ResourcePlan,
    enforcement: &str,
    timeout_sec: f64,
) -> Result<String> {
    if !plan.numeric_limits_valid() {
        return Err(BenchError::msg("invalid numeric resource limits"));
    }
    if !matches!(
        enforcement,
        ENFORCEMENT_RSS_WATCHDOG_V1
            | ENFORCEMENT_AY_MEMORY_V1
            | ENFORCEMENT_AY_MEMORY_RSS_V1
            | ENFORCEMENT_AY_PB_MEMLIMIT_V1
    ) {
        return Err(BenchError::msg(format!(
            "unrecognized exact resource enforcement tag: {enforcement:?}"
        )));
    }
    let timeout = checked_benchmark_timeout(timeout_sec, "resource envelope")?;
    let timeout_ns = u64::try_from(timeout.as_nanos())
        .map_err(|_| BenchError::msg("resource envelope timeout is too large"))?;
    Ok(format!(
        "oom-guard-v2:jobs={};memlimit_mb={};nbcore={};headroom_mb={};timeout_ns={timeout_ns};enforcement={enforcement};aggregate={AGGREGATE_ENFORCEMENT_V1}",
        plan.jobs, plan.memlimit_mb_per_child, plan.nbcore_per_child, plan.headroom_mb
    ))
}

/// Process holding the host-wide planner lease for one complete benchmark
/// campaign. Closing its stdin asks the Python sidecar to exit and releases
/// the advisory lock; the sidecar is isolated so failed cleanup cannot target
/// the benchmark parent process group.
#[derive(Debug)]
struct GlobalHarnessLease {
    process: std::sync::Mutex<Option<(Child, std::process::ChildStdin)>>,
}

static PROCESS_HARNESS_LEASE: std::sync::OnceLock<
    std::sync::Mutex<std::sync::Weak<GlobalHarnessLease>>,
> = std::sync::OnceLock::new();

// The production invariant intentionally rejects independently planned
// campaigns in one process. The Rust test harness, however, runs unrelated
// end-to-end campaign tests concurrently. Serialize only those test campaigns
// so they exercise the production lease one at a time instead of failing for
// test-runner scheduling reasons.
#[cfg(test)]
static TEST_CAMPAIGN_STATE: (std::sync::Mutex<bool>, std::sync::Condvar) =
    (std::sync::Mutex::new(false), std::sync::Condvar::new());

#[cfg(test)]
fn build_sandbox_test_lease_path() -> Option<PathBuf> {
    if std::env::var_os("AY_CONTINUOUS_BUILD_SANDBOX").as_deref() != Some(std::ffi::OsStr::new("1"))
    {
        return None;
    }
    Some(std::env::temp_dir().join(format!("ay-bench-test-lease-{}.lock", std::process::id())))
}

#[cfg(test)]
#[derive(Debug)]
struct TestCampaignLease;

#[cfg(test)]
impl TestCampaignLease {
    fn acquire() -> std::sync::Arc<Self> {
        let (state, available) = &TEST_CAMPAIGN_STATE;
        let mut active = state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        while *active {
            active = available
                .wait(active)
                .unwrap_or_else(|poisoned| poisoned.into_inner());
        }
        *active = true;
        std::sync::Arc::new(Self)
    }
}

#[cfg(test)]
impl Drop for TestCampaignLease {
    fn drop(&mut self) {
        let (state, available) = &TEST_CAMPAIGN_STATE;
        let mut active = state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        *active = false;
        available.notify_one();
    }
}

impl GlobalHarnessLease {
    fn exclusive(guard_script: &Path, label: &str) -> Result<std::sync::Arc<Self>> {
        let slot =
            PROCESS_HARNESS_LEASE.get_or_init(|| std::sync::Mutex::new(std::sync::Weak::new()));
        let mut weak = vacant_harness_lease_slot(slot)?;
        let lease = std::sync::Arc::new(Self::acquire(guard_script, label)?);
        *weak = std::sync::Arc::downgrade(&lease);
        Ok(lease)
    }

    fn acquire(guard_script: &Path, label: &str) -> Result<Self> {
        const READY_MARKER: &[u8] = b"AY_OOM_HARNESS_LEASE_READY_V1\n";

        let mut command = Command::new("python3");
        command
            .arg(guard_script)
            .arg("lease")
            .arg("--label")
            .arg(label)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        #[cfg(test)]
        if let Some(path) = build_sandbox_test_lease_path() {
            // The complete cargo-test process is already inside the
            // controller's host-leased, RSS-capped build namespace. Exercise
            // nested harness logic against _oom_guard's explicit test seam
            // instead of asking test code to mutate the read-only host lock.
            command.arg("--test-lock-path").arg(path);
        }
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt as _;
            command.process_group(0);
        }
        let mut child = command
            .spawn()
            .with_bench_context(|| format!("acquiring aggregate resource lease for {label}"))?;
        let stdin = match child.stdin.take() {
            Some(stdin) => stdin,
            None => {
                terminate_process_group(&mut child);
                return Err(BenchError::msg(format!(
                    "{label}: aggregate resource lease stdin is missing"
                )));
            }
        };
        let Some(mut ready_pipe) = child.stdout.take() else {
            terminate_process_group(&mut child);
            return Err(BenchError::msg(format!(
                "{label}: aggregate resource lease readiness pipe is missing"
            )));
        };
        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            use std::io::Read as _;

            let mut marker = vec![0_u8; READY_MARKER.len()];
            let result = ready_pipe
                .read_exact(&mut marker)
                .map(|()| marker == READY_MARKER)
                .map_err(|error| error.to_string());
            let _ = sender.send(result);
        });

        let deadline = Instant::now() + Duration::from_secs(10);
        loop {
            match receiver.try_recv() {
                Ok(Ok(true)) => break,
                Ok(Ok(false)) => {
                    terminate_process_group(&mut child);
                    return Err(BenchError::msg(format!(
                        "{label}: aggregate resource lease emitted an invalid readiness marker"
                    )));
                }
                Ok(Err(error)) => {
                    terminate_process_group(&mut child);
                    return Err(BenchError::msg(format!(
                        "{label}: reading aggregate resource lease readiness failed: {error}"
                    )));
                }
                Err(std::sync::mpsc::TryRecvError::Disconnected) => {
                    terminate_process_group(&mut child);
                    return Err(BenchError::msg(format!(
                        "{label}: aggregate resource lease readiness channel disconnected"
                    )));
                }
                Err(std::sync::mpsc::TryRecvError::Empty) => {}
            }
            match observe_child_unreaped(&child, false, label) {
                Ok(UnreapedChildState::Exited) => {
                    let status = kill_process_group_and_reap(&mut child, label)?;
                    return Err(BenchError::msg(format!(
                        "{label}: aggregate resource lease exited before arming ({status})"
                    )));
                }
                Ok(UnreapedChildState::Running) => {}
                Ok(UnreapedChildState::Stopped(_)) => {
                    terminate_process_group(&mut child);
                    return Err(BenchError::msg(format!(
                        "{label}: aggregate resource lease stopped before arming"
                    )));
                }
                Err(error) => {
                    terminate_process_group(&mut child);
                    return Err(BenchError::msg(format!(
                        "{label}: checking aggregate resource lease failed: {error}"
                    )));
                }
            }
            if Instant::now() >= deadline {
                terminate_process_group(&mut child);
                return Err(BenchError::msg(format!(
                    "{label}: aggregate resource lease did not arm within 10 seconds"
                )));
            }
            std::thread::sleep(Duration::from_millis(5));
        }

        match observe_child_unreaped(&child, false, label) {
            Ok(UnreapedChildState::Running) => {}
            Ok(status) => {
                terminate_process_group(&mut child);
                return Err(BenchError::msg(format!(
                    "{label}: aggregate resource lease died immediately after readiness ({status:?})"
                )));
            }
            Err(error) => {
                terminate_process_group(&mut child);
                return Err(BenchError::msg(format!(
                    "{label}: cannot verify aggregate resource lease after readiness: {error}"
                )));
            }
        }

        Ok(Self {
            process: std::sync::Mutex::new(Some((child, stdin))),
        })
    }

    fn ensure_alive(&self, label: &str) -> Result<()> {
        let process = self
            .process
            .lock()
            .map_err(|_| BenchError::msg("aggregate resource lease mutex was poisoned"))?;
        let Some((child, _stdin)) = process.as_ref() else {
            return Err(BenchError::msg(format!(
                "{label}: aggregate resource lease handle is missing"
            )));
        };
        match observe_child_unreaped(child, false, label) {
            Ok(UnreapedChildState::Running) => Ok(()),
            Ok(UnreapedChildState::Exited) => Err(BenchError::msg(format!(
                "{label}: aggregate resource lease exited and released the host admission lock"
            ))),
            Ok(UnreapedChildState::Stopped(signal)) => Err(BenchError::msg(format!(
                "{label}: aggregate resource lease stopped with {signal} and is not enforcing host admission"
            ))),
            Err(error) => Err(BenchError::msg(format!(
                "{label}: aggregate resource lease health check failed: {error}"
            ))),
        }
    }
}

fn vacant_harness_lease_slot(
    slot: &std::sync::Mutex<std::sync::Weak<GlobalHarnessLease>>,
) -> Result<std::sync::MutexGuard<'_, std::sync::Weak<GlobalHarnessLease>>> {
    let weak = slot
        .lock()
        .map_err(|_| BenchError::msg("aggregate resource lease mutex was poisoned"))?;
    if weak.upgrade().is_some() {
        return Err(BenchError::msg(
            "another independently planned benchmark campaign is already active in this process; clone its PlannedResources instead of replanning against full host capacity",
        ));
    }
    Ok(weak)
}

impl Drop for GlobalHarnessLease {
    fn drop(&mut self) {
        let process = match self.process.get_mut() {
            Ok(process) => process.take(),
            Err(poisoned) => poisoned.into_inner().take(),
        };
        let Some((mut child, stdin)) = process else {
            return;
        };
        drop(stdin);
        match wait_for_child_exit_unreaped(&child, Duration::from_secs(5), "aggregate lease") {
            Ok(true) => {
                let _ = kill_process_group_and_reap(&mut child, "aggregate lease");
            }
            Ok(false) | Err(_) => terminate_process_group(&mut child),
        }
    }
}

const WATCHDOG_SERVER_READY: &[u8] = b"AY_OOM_WATCHDOG_SERVER_READY_V1\n";
const WATCHDOG_SERVER_MAX_LINE: u64 = 4096;
const WATCHDOG_SERVER_HEARTBEAT_TIMEOUT: Duration = Duration::from_secs(1);
const WATCHDOG_SERVER_STATE_CHECK_INTERVAL: Duration = Duration::from_millis(100);

#[cfg(target_os = "linux")]
fn watchdog_server_process_is_responsive(pid: u32) -> bool {
    let Ok(stat) = std::fs::read_to_string(format!("/proc/{pid}/stat")) else {
        return false;
    };
    let Some((_, suffix)) = stat.rsplit_once(") ") else {
        return false;
    };
    !matches!(
        suffix.as_bytes().first().copied(),
        Some(b'T' | b't' | b'Z' | b'X')
    )
}

#[cfg(not(target_os = "linux"))]
fn watchdog_server_process_is_responsive(_pid: u32) -> bool {
    true
}

#[derive(Debug, Clone, Copy)]
enum WatchdogServerEvent {
    Ready,
    Done,
    Breach(u64),
}

type WatchdogServerMessage = std::result::Result<WatchdogServerEvent, String>;

#[derive(Debug)]
struct WatchdogServerProcess {
    child: Child,
    stdin: std::process::ChildStdin,
}

/// One Python watchdog process per benchmark campaign. Individual solver
/// groups retain independent authenticated guards, while the server's threads
/// share `_oom_guard.py`'s single cached `/proc` snapshot.
#[derive(Debug)]
struct SharedWatchdogServer {
    guard_script: PathBuf,
    process: std::sync::Mutex<Option<WatchdogServerProcess>>,
    registrations: std::sync::Arc<
        std::sync::Mutex<
            std::collections::HashMap<u64, std::sync::mpsc::Sender<WatchdogServerMessage>>,
        >,
    >,
    healthy: std::sync::Arc<std::sync::atomic::AtomicBool>,
    last_heartbeat_ns: std::sync::Arc<std::sync::atomic::AtomicU64>,
    last_process_check_ns: std::sync::atomic::AtomicU64,
    next_id: std::sync::atomic::AtomicU64,
}

impl SharedWatchdogServer {
    fn new(guard_script: PathBuf) -> std::sync::Arc<Self> {
        std::sync::Arc::new(Self {
            guard_script,
            process: std::sync::Mutex::new(None),
            registrations: std::sync::Arc::new(std::sync::Mutex::new(
                std::collections::HashMap::new(),
            )),
            healthy: std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false)),
            last_heartbeat_ns: std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0)),
            last_process_check_ns: std::sync::atomic::AtomicU64::new(0),
            next_id: std::sync::atomic::AtomicU64::new(1),
        })
    }

    fn ensure_started(&self) -> Result<()> {
        use std::sync::atomic::Ordering;

        let mut process = self
            .process
            .lock()
            .map_err(|_| BenchError::msg("RSS watchdog server mutex was poisoned"))?;
        if let Some(server) = process.as_mut() {
            if self.heartbeat_is_fresh() && watchdog_server_process_is_responsive(server.child.id())
            {
                return match server.child.try_wait() {
                    Ok(None) => Ok(()),
                    Ok(Some(status)) => {
                        self.healthy.store(false, Ordering::Release);
                        Err(BenchError::msg(format!(
                            "campaign RSS watchdog server exited unexpectedly ({status})"
                        )))
                    }
                    Err(error) => {
                        self.healthy.store(false, Ordering::Release);
                        Err(error.into())
                    }
                };
            }
            return Err(BenchError::msg(
                "campaign RSS watchdog server is no longer healthy",
            ));
        }

        let mut command = Command::new("python3");
        command
            .arg(&self.guard_script)
            .arg("watch-server")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt as _;
            command.process_group(0);
        }
        let mut child = command.spawn().with_bench_context(|| {
            format!(
                "starting campaign RSS watchdog server {}",
                self.guard_script.display()
            )
        })?;
        let Some(stdin) = child.stdin.take() else {
            terminate_process_group(&mut child);
            return Err(BenchError::msg("RSS watchdog server stdin is missing"));
        };
        let Some(stdout) = child.stdout.take() else {
            terminate_process_group(&mut child);
            return Err(BenchError::msg("RSS watchdog server stdout is missing"));
        };

        let (ready_sender, ready_receiver) = std::sync::mpsc::channel();
        let registrations = std::sync::Arc::clone(&self.registrations);
        let healthy = std::sync::Arc::clone(&self.healthy);
        let last_heartbeat_ns = std::sync::Arc::clone(&self.last_heartbeat_ns);
        std::thread::spawn(move || {
            watchdog_server_reader(
                stdout,
                registrations,
                healthy,
                last_heartbeat_ns,
                ready_sender,
            );
        });

        let deadline = Instant::now() + Duration::from_secs(10);
        loop {
            match ready_receiver.try_recv() {
                Ok(Ok(())) => break,
                Ok(Err(error)) => {
                    terminate_process_group(&mut child);
                    return Err(BenchError::msg(format!(
                        "RSS watchdog server readiness failed: {error}"
                    )));
                }
                Err(std::sync::mpsc::TryRecvError::Disconnected) => {
                    terminate_process_group(&mut child);
                    return Err(BenchError::msg(
                        "RSS watchdog server readiness channel disconnected",
                    ));
                }
                Err(std::sync::mpsc::TryRecvError::Empty) => {}
            }
            match child.try_wait() {
                Ok(Some(status)) => {
                    terminate_process_group(&mut child);
                    return Err(BenchError::msg(format!(
                        "RSS watchdog server exited before arming ({status})"
                    )));
                }
                Ok(None) => {}
                Err(error) => {
                    terminate_process_group(&mut child);
                    return Err(error.into());
                }
            }
            if Instant::now() >= deadline {
                terminate_process_group(&mut child);
                return Err(BenchError::msg(
                    "RSS watchdog server did not arm within 10 seconds",
                ));
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        *process = Some(WatchdogServerProcess { child, stdin });
        Ok(())
    }

    fn register(
        self: &std::sync::Arc<Self>,
        pid: u32,
        limit_mb: usize,
        label: &str,
    ) -> Result<RssWatchdog> {
        use std::fmt::Write as _;
        use std::io::Write as _;
        use std::sync::atomic::Ordering;

        self.ensure_started()?;
        if label.len() > 512 {
            return Err(BenchError::msg("RSS watchdog label exceeds 512 bytes"));
        }
        let watch_id = self.next_id.fetch_add(1, Ordering::Relaxed);
        if watch_id == 0 || watch_id == u64::MAX {
            return Err(BenchError::msg("RSS watchdog registration ID exhausted"));
        }
        let mut label_hex = String::with_capacity(label.len().saturating_mul(2));
        for byte in label.as_bytes() {
            write!(&mut label_hex, "{byte:02x}")
                .map_err(|_| BenchError::msg("encoding RSS watchdog label failed"))?;
        }
        let command = format!("WATCH {watch_id} {pid} {limit_mb} {label_hex}\n");
        if command.len() > WATCHDOG_SERVER_MAX_LINE as usize {
            return Err(BenchError::msg(
                "RSS watchdog command exceeds protocol limit",
            ));
        }
        let (sender, receiver) = std::sync::mpsc::channel();
        self.registrations
            .lock()
            .map_err(|_| BenchError::msg("RSS watchdog registration mutex was poisoned"))?
            .insert(watch_id, sender);
        let write_result = (|| -> Result<()> {
            if !self.healthy.load(Ordering::Acquire) {
                return Err(BenchError::msg("RSS watchdog server became unhealthy"));
            }
            let mut process = self
                .process
                .lock()
                .map_err(|_| BenchError::msg("RSS watchdog server mutex was poisoned"))?;
            let server = process
                .as_mut()
                .ok_or_else(|| BenchError::msg("RSS watchdog server process is missing"))?;
            server
                .stdin
                .write_all(command.as_bytes())
                .and_then(|()| server.stdin.flush())
                .with_bench_context(|| format!("registering RSS watchdog for child {pid}"))
        })();
        // `write_all` can fail after a partial command. Keep the ID registered
        // until server EOF drains it, so a late response can never become an
        // unknown-ID failure for unrelated children.
        write_result?;
        match receiver.recv_timeout(Duration::from_secs(10)) {
            Ok(Ok(WatchdogServerEvent::Ready)) => Ok(RssWatchdog {
                server: std::sync::Arc::clone(self),
                aggregate_lease: None,
                watch_id,
                target_pgid: i32::try_from(pid).ok(),
                terminal_breach: None,
                receiver,
            }),
            Ok(Ok(_)) => Err(BenchError::msg(format!(
                "RSS watchdog {watch_id} terminated before readiness"
            ))),
            Ok(Err(error)) => Err(BenchError::msg(format!(
                "RSS watchdog {watch_id} failed before readiness: {error}"
            ))),
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                // Keep the sender registered until the server's terminal
                // event. The caller will kill the stopped target; removing it
                // early would turn that expected late event into an unknown-ID
                // protocol failure for every other campaign child.
                Err(BenchError::msg(format!(
                    "RSS watchdog {watch_id} did not arm within 10 seconds"
                )))
            }
            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => Err(BenchError::msg(format!(
                "RSS watchdog {watch_id} readiness channel disconnected"
            ))),
        }
    }

    fn heartbeat_is_fresh(&self) -> bool {
        use std::sync::atomic::Ordering;

        if !self.healthy.load(Ordering::Acquire) {
            return false;
        }
        let Ok(now_ns) = monotonic_time_ns() else {
            self.healthy.store(false, Ordering::Release);
            return false;
        };
        let last_ns = self.last_heartbeat_ns.load(Ordering::Acquire);
        if last_ns == 0
            || now_ns.saturating_sub(last_ns)
                > u64::try_from(WATCHDOG_SERVER_HEARTBEAT_TIMEOUT.as_nanos()).unwrap_or(u64::MAX)
        {
            self.healthy.store(false, Ordering::Release);
            return false;
        }
        true
    }

    fn is_healthy(&self) -> bool {
        use std::sync::atomic::Ordering;

        if !self.heartbeat_is_fresh() {
            return false;
        }
        let Ok(now_ns) = monotonic_time_ns() else {
            self.healthy.store(false, Ordering::Release);
            return false;
        };
        let interval_ns =
            u64::try_from(WATCHDOG_SERVER_STATE_CHECK_INTERVAL.as_nanos()).unwrap_or(u64::MAX);
        let previous = self.last_process_check_ns.load(Ordering::Acquire);
        if now_ns.saturating_sub(previous) < interval_ns
            || self
                .last_process_check_ns
                .compare_exchange(previous, now_ns, Ordering::AcqRel, Ordering::Acquire)
                .is_err()
        {
            return true;
        }
        let responsive = self
            .process
            .lock()
            .ok()
            .and_then(|process| process.as_ref().map(|server| server.child.id()))
            .is_some_and(watchdog_server_process_is_responsive);
        if !responsive {
            self.healthy.store(false, Ordering::Release);
        }
        responsive
    }

    #[cfg(all(
        test,
        any(
            target_os = "android",
            target_os = "freebsd",
            target_os = "haiku",
            target_os = "macos",
            all(target_os = "linux", not(target_env = "uclibc")),
        ),
    ))]
    fn process_id(&self) -> Option<u32> {
        self.process
            .lock()
            .ok()
            .and_then(|process| process.as_ref().map(|server| server.child.id()))
    }
}

impl Drop for SharedWatchdogServer {
    fn drop(&mut self) {
        self.healthy
            .store(false, std::sync::atomic::Ordering::Release);
        let process = match self.process.get_mut() {
            Ok(process) => process.take(),
            Err(poisoned) => poisoned.into_inner().take(),
        };
        let Some(mut server) = process else {
            return;
        };
        drop(server.stdin);
        match server.child.wait_timeout(Duration::from_secs(10)) {
            Ok(Some(_)) => {}
            Ok(None) | Err(_) => terminate_process_group(&mut server.child),
        }
    }
}

fn watchdog_server_reader(
    stdout: std::process::ChildStdout,
    registrations: std::sync::Arc<
        std::sync::Mutex<
            std::collections::HashMap<u64, std::sync::mpsc::Sender<WatchdogServerMessage>>,
        >,
    >,
    healthy: std::sync::Arc<std::sync::atomic::AtomicBool>,
    last_heartbeat_ns: std::sync::Arc<std::sync::atomic::AtomicU64>,
    ready: std::sync::mpsc::Sender<std::result::Result<(), String>>,
) {
    use std::io::{BufRead as _, Read as _};
    use std::sync::atomic::Ordering;

    let result = (|| -> std::result::Result<(), String> {
        let mut reader = std::io::BufReader::new(stdout);
        let mut marker = vec![0_u8; WATCHDOG_SERVER_READY.len()];
        reader
            .read_exact(&mut marker)
            .map_err(|error| format!("reading server readiness failed: {error}"))?;
        if marker != WATCHDOG_SERVER_READY {
            return Err("invalid RSS watchdog server readiness marker".to_string());
        }
        last_heartbeat_ns.store(
            monotonic_time_ns().map_err(|error| error.to_string())?,
            Ordering::Release,
        );
        healthy.store(true, Ordering::Release);
        let _ = ready.send(Ok(()));
        loop {
            let mut line = Vec::new();
            let read = (&mut reader)
                .take(WATCHDOG_SERVER_MAX_LINE + 1)
                .read_until(b'\n', &mut line)
                .map_err(|error| format!("reading RSS watchdog server response failed: {error}"))?;
            if read == 0 {
                return Err("RSS watchdog server closed its response pipe".to_string());
            }
            if line.len() > WATCHDOG_SERVER_MAX_LINE as usize || !line.ends_with(b"\n") {
                return Err("RSS watchdog server response exceeds protocol limit".to_string());
            }
            let line = std::str::from_utf8(&line[..line.len() - 1])
                .map_err(|error| format!("RSS watchdog server emitted non-UTF-8: {error}"))?;
            if let Some(timestamp) = line.strip_prefix("HEARTBEAT ") {
                let timestamp = timestamp
                    .parse::<u64>()
                    .map_err(|_| "RSS watchdog server heartbeat has invalid timestamp")?;
                if timestamp == 0 {
                    return Err("RSS watchdog server heartbeat has zero timestamp".to_string());
                }
                last_heartbeat_ns.store(
                    monotonic_time_ns().map_err(|error| error.to_string())?,
                    Ordering::Release,
                );
                continue;
            }
            let (watch_id, event, terminal) = parse_watchdog_server_event(line)?;
            let sender = {
                let mut registrations = registrations
                    .lock()
                    .map_err(|_| "RSS watchdog registration mutex was poisoned".to_string())?;
                if terminal {
                    registrations.remove(&watch_id)
                } else {
                    registrations.get(&watch_id).cloned()
                }
            }
            .ok_or_else(|| format!("RSS watchdog server reported unknown id {watch_id}"))?;
            // A caller can time out and kill its stopped child immediately
            // before a late response arrives. That receiver disappearing is
            // local to the registration, not a reason to disarm the campaign.
            let _ = sender.send(event);
        }
    })();
    if !healthy.swap(false, Ordering::AcqRel) {
        let _ = ready.send(Err(result
            .as_ref()
            .err()
            .cloned()
            .unwrap_or_else(|| "RSS watchdog server stopped".to_string())));
    }
    let failure = result
        .err()
        .unwrap_or_else(|| "RSS watchdog server stopped".to_string());
    if let Ok(mut registrations) = registrations.lock() {
        for (_, sender) in registrations.drain() {
            let _ = sender.send(Err(failure.clone()));
        }
    }
}

fn parse_watchdog_server_event(
    line: &str,
) -> std::result::Result<(u64, WatchdogServerMessage, bool), String> {
    let fields = line.split(' ').collect::<Vec<_>>();
    let watch_id = fields
        .get(1)
        .ok_or_else(|| "watchdog server response omitted id".to_string())?
        .parse::<u64>()
        .map_err(|_| "watchdog server response has invalid id".to_string())?;
    if watch_id == 0 {
        return Err("watchdog server response has zero id".to_string());
    }
    match fields.as_slice() {
        ["READY", _] => Ok((watch_id, Ok(WatchdogServerEvent::Ready), false)),
        ["DONE", _] => Ok((watch_id, Ok(WatchdogServerEvent::Done), true)),
        ["BREACH", _, timestamp] => {
            let timestamp = timestamp
                .parse::<u64>()
                .map_err(|_| "watchdog server breach has invalid timestamp".to_string())?;
            if timestamp == 0 {
                return Err("watchdog server breach has zero timestamp".to_string());
            }
            Ok((watch_id, Ok(WatchdogServerEvent::Breach(timestamp)), true))
        }
        ["ERROR", _, encoded] => {
            if encoded.len() > 1024 || encoded.len() % 2 != 0 {
                return Err("watchdog server error has invalid encoding".to_string());
            }
            let mut bytes = Vec::with_capacity(encoded.len() / 2);
            for pair in encoded.as_bytes().as_chunks::<2>().0 {
                let pair = std::str::from_utf8(pair)
                    .map_err(|_| "watchdog server error has invalid encoding".to_string())?;
                bytes.push(
                    u8::from_str_radix(pair, 16)
                        .map_err(|_| "watchdog server error has invalid encoding".to_string())?,
                );
            }
            let message = String::from_utf8(bytes)
                .map_err(|_| "watchdog server error is not UTF-8".to_string())?;
            Ok((watch_id, Err(message), true))
        }
        _ => Err("invalid RSS watchdog server response".to_string()),
    }
}

/// A planned envelope plus the executable planner used to enforce it.
#[derive(Debug, Clone)]
pub struct PlannedResources {
    /// Exact numeric resource plan admitted for this campaign.
    pub plan: ResourcePlan,
    guard_script: PathBuf,
    _aggregate_lease: Option<std::sync::Arc<GlobalHarnessLease>>,
    watchdog_server: std::sync::Arc<SharedWatchdogServer>,
    #[cfg(test)]
    _test_campaign_lease: Option<std::sync::Arc<TestCampaignLease>>,
}

#[derive(Debug)]
pub(crate) struct CapturedOutput {
    pub status: ExitStatus,
    pub stdout: String,
    pub stderr: String,
}

#[derive(Debug)]
pub(crate) struct GuardedChildOutcome {
    pub status: Option<ExitStatus>,
    pub timed_out: bool,
    pub memout: bool,
}

/// Maximum input accepted by [`PlannedResources::run_external_transcript`].
///
/// Keeping this fixed makes the transcript runner safe to call with
/// untrusted corpus entries without adding another user-facing resource knob.
pub const GUARDED_TRANSCRIPT_INPUT_LIMIT: usize = 1024 * 1024;
/// Maximum bytes retained from each transcript output stream.
///
/// Both pipes are still drained after reaching this limit so a verbose child
/// cannot deadlock while its process group remains under supervision.
pub const GUARDED_TRANSCRIPT_STREAM_LIMIT: usize = 1024 * 1024;
const EXTERNAL_CAPTURE_LIMIT: usize = GUARDED_TRANSCRIPT_STREAM_LIMIT;
const METADATA_CAPTURE_LIMIT: usize = 64 * 1024;

/// Bounded output and exact termination state for one externally guarded
/// process group.
#[derive(Debug)]
pub struct GuardedCapturedOutput {
    /// Reaped leader status, absent only after forced cleanup where the host
    /// could not recover a status.
    pub status: Option<ExitStatus>,
    /// Bounded stdout retained from the process group.
    pub stdout: Vec<u8>,
    /// Parent-observed wall time from spawn through cleanup and capture.
    pub observed: Duration,
    /// Whether the hard wall deadline was the first termination cause.
    pub timed_out: bool,
    /// Whether the RSS watchdog was the first termination cause.
    pub memout: bool,
    /// Whether stdout exceeded the fixed retained-byte limit.
    pub output_truncated: bool,
}

/// Bounded input/output transcript and exact termination state for one
/// externally guarded process group.
#[derive(Debug)]
#[non_exhaustive]
pub struct GuardedTranscriptOutput {
    /// Reaped leader status, absent only after forced cleanup where the host
    /// could not recover a status.
    pub status: Option<ExitStatus>,
    /// Bounded stdout retained from the process group.
    pub stdout: Vec<u8>,
    /// Bounded stderr retained from the process group.
    pub stderr: Vec<u8>,
    /// Parent-observed wall time from spawn through cleanup and capture.
    pub observed: Duration,
    /// Whether the hard wall deadline was the first termination cause.
    pub timed_out: bool,
    /// Whether the RSS watchdog was the first termination cause.
    pub memout: bool,
    /// Whether the writer delivered the complete bounded transcript to the
    /// child's stdin pipe.
    ///
    /// This is false when the child closed its input pipe before the writer
    /// completed, including during timeout or memout cleanup. A true value
    /// does not by itself prove that the child read or processed every byte.
    pub stdin_complete: bool,
    /// Whether stdout exceeded [`GUARDED_TRANSCRIPT_STREAM_LIMIT`].
    pub stdout_truncated: bool,
    /// Whether stderr exceeded [`GUARDED_TRANSCRIPT_STREAM_LIMIT`].
    pub stderr_truncated: bool,
}

#[derive(Debug)]
pub(crate) struct BoundedFileOutput {
    pub text: String,
    pub incomplete: bool,
}

pub(crate) struct BoundedFileCapture {
    receiver: std::sync::mpsc::Receiver<(Vec<u8>, bool, bool)>,
}

#[derive(Debug)]
pub(crate) struct LimitedFileOutput {
    pub exceeded: bool,
    pub write_failed: bool,
    pub bytes_written: u64,
    pub sha256: String,
}

/// Drain a child pipe without allowing the destination file to grow past a
/// fixed limit. Bytes beyond the limit are discarded so the producer cannot
/// deadlock on a full pipe; callers must reject `exceeded` and `write_failed`.
pub(crate) struct LimitedFileCapture {
    receiver: std::sync::mpsc::Receiver<(bool, bool, u64, String)>,
    limit_breached: std::sync::Arc<std::sync::atomic::AtomicBool>,
}

impl LimitedFileCapture {
    pub(crate) fn start<R>(mut reader: R, mut output: std::fs::File, limit: u64) -> Self
    where
        R: std::io::Read + Send + 'static,
    {
        use sha2::{Digest as _, Sha256};
        use std::io::Write as _;

        let (sender, receiver) = std::sync::mpsc::channel();
        let limit_breached = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let worker_breach = std::sync::Arc::clone(&limit_breached);
        std::thread::spawn(move || {
            let mut written = 0_u64;
            let mut hasher = Sha256::new();
            let mut exceeded = false;
            let mut write_failed = false;
            let mut chunk = vec![0_u8; 64 * 1024];
            loop {
                match reader.read(&mut chunk) {
                    Ok(0) => break,
                    Ok(read) => {
                        let remaining = limit.saturating_sub(written);
                        let retain = read.min(usize::try_from(remaining).unwrap_or(usize::MAX));
                        if retain > 0 {
                            if output.write_all(&chunk[..retain]).is_err() {
                                write_failed = true;
                                worker_breach.store(true, std::sync::atomic::Ordering::Release);
                                break;
                            }
                            hasher.update(&chunk[..retain]);
                            written = written.saturating_add(retain as u64);
                        }
                        if retain < read {
                            exceeded = true;
                            worker_breach.store(true, std::sync::atomic::Ordering::Release);
                            break;
                        }
                    }
                    Err(_) => {
                        write_failed = true;
                        worker_breach.store(true, std::sync::atomic::Ordering::Release);
                        break;
                    }
                }
            }
            if output.sync_all().is_err() {
                write_failed = true;
                worker_breach.store(true, std::sync::atomic::Ordering::Release);
            }
            let _ = sender.send((
                exceeded,
                write_failed,
                written,
                format!("sha256:{:x}", hasher.finalize()),
            ));
        });
        Self {
            receiver,
            limit_breached,
        }
    }

    pub(crate) fn breach_flag(&self) -> std::sync::Arc<std::sync::atomic::AtomicBool> {
        std::sync::Arc::clone(&self.limit_breached)
    }

    pub(crate) fn finish(self) -> Result<LimitedFileOutput> {
        let (exceeded, write_failed, bytes_written, sha256) = self
            .receiver
            .recv_timeout(Duration::from_secs(5))
            .map_err(|_| BenchError::msg("limited file capture did not finish"))?;
        Ok(LimitedFileOutput {
            exceeded,
            write_failed,
            bytes_written,
            sha256,
        })
    }
}

impl BoundedFileCapture {
    /// Drain a child pipe while writing/retaining at most one MiB.
    pub(crate) fn start<R>(mut reader: R, mut evidence_file: std::fs::File) -> Self
    where
        R: std::io::Read + Send + 'static,
    {
        use std::io::Write as _;

        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let mut kept = Vec::with_capacity(EXTERNAL_CAPTURE_LIMIT);
            let mut truncated = false;
            let mut failed = false;
            let mut chunk = [0_u8; 8192];
            loop {
                match reader.read(&mut chunk) {
                    Ok(0) => break,
                    Ok(read) => {
                        let remaining = EXTERNAL_CAPTURE_LIMIT.saturating_sub(kept.len());
                        let retain = read.min(remaining);
                        if retain > 0 {
                            kept.extend_from_slice(&chunk[..retain]);
                            if evidence_file.write_all(&chunk[..retain]).is_err() {
                                failed = true;
                            }
                        }
                        truncated |= read > remaining;
                    }
                    Err(_) => {
                        failed = true;
                        break;
                    }
                }
            }
            let _ = sender.send((kept, truncated, failed));
        });
        Self { receiver }
    }

    pub(crate) fn finish(self) -> Result<BoundedFileOutput> {
        let (bytes, truncated, failed) = self
            .receiver
            .recv_timeout(Duration::from_secs(5))
            .map_err(|_| BenchError::msg("bounded evidence capture did not finish"))?;
        Ok(BoundedFileOutput {
            text: String::from_utf8_lossy(&bytes).into_owned(),
            incomplete: truncated || failed,
        })
    }
}

pub(crate) struct BoundedPipeCapture {
    receiver: std::sync::mpsc::Receiver<(Vec<u8>, bool, bool)>,
}

impl BoundedPipeCapture {
    pub(crate) fn start<R>(mut reader: R) -> Self
    where
        R: std::io::Read + Send + 'static,
    {
        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let mut kept = Vec::with_capacity(METADATA_CAPTURE_LIMIT);
            let mut truncated = false;
            let mut read_failed = false;
            let mut chunk = [0_u8; 8192];
            loop {
                match reader.read(&mut chunk) {
                    Ok(0) => break,
                    Ok(read) => {
                        let remaining = METADATA_CAPTURE_LIMIT.saturating_sub(kept.len());
                        kept.extend_from_slice(&chunk[..read.min(remaining)]);
                        truncated |= read > remaining;
                    }
                    Err(_) => {
                        read_failed = true;
                        break;
                    }
                }
            }
            let _ = sender.send((kept, truncated, read_failed));
        });
        Self { receiver }
    }

    pub(crate) fn finish(self, label: &str, stream: &str) -> Result<String> {
        let (bytes, truncated, read_failed) = self
            .receiver
            .recv_timeout(Duration::from_secs(5))
            .map_err(|_| BenchError::msg(format!("{label}: {stream} capture did not finish")))?;
        if truncated || read_failed {
            return Err(BenchError::msg(format!(
                "{label}: {stream} exceeded the 64 KiB metadata capture limit or was unreadable"
            )));
        }
        Ok(String::from_utf8_lossy(&bytes).into_owned())
    }
}

struct BoundedBytesCapture {
    receiver: std::sync::mpsc::Receiver<(Vec<u8>, bool, bool)>,
}

impl BoundedBytesCapture {
    fn start<R>(mut reader: R) -> Self
    where
        R: std::io::Read + Send + 'static,
    {
        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let mut kept = Vec::with_capacity(EXTERNAL_CAPTURE_LIMIT);
            let mut truncated = false;
            let mut read_failed = false;
            let mut chunk = [0_u8; 8192];
            loop {
                match reader.read(&mut chunk) {
                    Ok(0) => break,
                    Ok(read) => {
                        let remaining = EXTERNAL_CAPTURE_LIMIT.saturating_sub(kept.len());
                        kept.extend_from_slice(&chunk[..read.min(remaining)]);
                        truncated |= read > remaining;
                    }
                    Err(_) => {
                        read_failed = true;
                        break;
                    }
                }
            }
            let _ = sender.send((kept, truncated, read_failed));
        });
        Self { receiver }
    }

    fn finish(self, label: &str, stream: &str) -> Result<(Vec<u8>, bool)> {
        let (bytes, truncated, read_failed) = self
            .receiver
            .recv_timeout(Duration::from_secs(5))
            .map_err(|_| {
                BenchError::msg(format!("{label}: guarded {stream} capture did not finish"))
            })?;
        if read_failed {
            return Err(BenchError::msg(format!(
                "{label}: reading guarded {stream} failed"
            )));
        }
        Ok((bytes, truncated))
    }
}

struct BoundedStdinWriter {
    receiver: std::sync::mpsc::Receiver<std::io::Result<()>>,
}

impl BoundedStdinWriter {
    fn start<W>(mut writer: W, bytes: Vec<u8>) -> Self
    where
        W: std::io::Write + Send + 'static,
    {
        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let result = writer.write_all(&bytes).and_then(|()| writer.flush());
            let _ = sender.send(result);
        });
        Self { receiver }
    }

    fn finish(self, label: &str) -> Result<bool> {
        match self.receiver.recv_timeout(Duration::from_secs(5)) {
            Ok(Ok(())) => Ok(true),
            // Closing stdin before consuming the complete transcript is child
            // behavior, not a harness failure. Its exit status and captured
            // diagnostics remain available, while `stdin_complete` prevents a
            // caller from mistaking the partial exchange for a full one.
            Ok(Err(error))
                if matches!(
                    error.kind(),
                    std::io::ErrorKind::BrokenPipe
                        | std::io::ErrorKind::ConnectionAborted
                        | std::io::ErrorKind::ConnectionReset
                ) =>
            {
                Ok(false)
            }
            Ok(Err(error)) => Err(BenchError::msg(format!(
                "{label}: writing guarded stdin failed: {error}"
            ))),
            Err(_) => Err(BenchError::msg(format!(
                "{label}: guarded stdin writer did not finish"
            ))),
        }
    }
}

/// Run a short local metadata command with bounded pipes and a hard wall
/// deadline. This is not a solver execution path (and therefore has no solver
/// resource envelope), but it still prevents provenance helpers from hanging
/// or allocating unbounded parent memory.
pub(crate) fn capture_local_output<I, S>(
    program: impl AsRef<std::ffi::OsStr>,
    args: I,
    timeout: Duration,
    label: &str,
) -> Result<CapturedOutput>
where
    I: IntoIterator<Item = S>,
    S: AsRef<std::ffi::OsStr>,
{
    capture_local_output_in(program, args, timeout, label, None)
}

pub(crate) fn capture_local_output_in<I, S>(
    program: impl AsRef<std::ffi::OsStr>,
    args: I,
    timeout: Duration,
    label: &str,
    current_dir: Option<&Path>,
) -> Result<CapturedOutput>
where
    I: IntoIterator<Item = S>,
    S: AsRef<std::ffi::OsStr>,
{
    if timeout.is_zero() {
        return Err(BenchError::msg(format!(
            "{label}: timeout must be positive"
        )));
    }
    let guard_script = crate::runner::repo_root_public()
        .join("scripts")
        .join("_oom_guard.py");
    if !guard_script.is_file() {
        return Err(BenchError::msg(format!(
            "{label}: required stopped-child wrapper is missing: {}",
            guard_script.display()
        )));
    }
    let mut command = Command::new("python3");
    command
        .arg(&guard_script)
        .arg("exec-stopped")
        .arg("--")
        .arg(program)
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if let Some(current_dir) = current_dir {
        command.current_dir(current_dir);
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt as _;
        command.process_group(0);
    }
    let mut child = command
        .spawn()
        .with_bench_context(|| format!("spawning stopped metadata child for {label}"))?;
    #[cfg(unix)]
    resume_stopped_metadata_child(&mut child, label)?;
    #[cfg(not(unix))]
    {
        terminate_process_group(&mut child);
        return Err(BenchError::msg(format!(
            "{label}: bounded metadata execution requires POSIX process groups"
        )));
    }
    let stdout_capture = child.stdout.take().map(BoundedPipeCapture::start);
    let stderr_capture = child.stderr.take().map(BoundedPipeCapture::start);
    let status = match wait_for_child_exit_unreaped(&child, timeout, label) {
        Ok(true) => kill_process_group_and_reap(&mut child, label)?,
        Ok(false) => {
            terminate_process_group(&mut child);
            return Err(BenchError::msg(format!(
                "{label}: exceeded {:.3}s",
                timeout.as_secs_f64()
            )));
        }
        Err(error) => {
            terminate_process_group(&mut child);
            return Err(error);
        }
    };
    let stdout_result = stdout_capture
        .ok_or_else(|| BenchError::msg(format!("{label}: stdout pipe missing")))?
        .finish(label, "stdout");
    let stderr_result = stderr_capture
        .ok_or_else(|| BenchError::msg(format!("{label}: stderr pipe missing")))?
        .finish(label, "stderr");
    let stdout = stdout_result?;
    let stderr = stderr_result?;
    Ok(CapturedOutput {
        status,
        stdout,
        stderr,
    })
}

#[cfg(unix)]
fn resume_stopped_metadata_child(child: &mut Child, label: &str) -> Result<()> {
    let pid_raw = i32::try_from(child.id())
        .map_err(|_| BenchError::msg(format!("{label}: metadata child PID does not fit pid_t")))?;
    let pid = nix::unistd::Pid::from_raw(pid_raw);
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        match observe_child_unreaped(child, true, label) {
            Ok(UnreapedChildState::Stopped(nix::sys::signal::Signal::SIGSTOP)) => break,
            Ok(UnreapedChildState::Running) if Instant::now() < deadline => {
                std::thread::sleep(Duration::from_millis(5));
            }
            Ok(UnreapedChildState::Running) => {
                terminate_process_group(child);
                return Err(BenchError::msg(format!(
                    "{label}: metadata child did not stop within 10 seconds"
                )));
            }
            Ok(status) => {
                terminate_process_group(child);
                return Err(BenchError::msg(format!(
                    "{label}: metadata child exited before its safety stop ({status:?})"
                )));
            }
            Err(error) => {
                terminate_process_group(child);
                return Err(BenchError::msg(format!(
                    "{label}: waiting for metadata child safety stop failed: {error}"
                )));
            }
        }
    }
    if nix::unistd::getpgid(Some(pid)) != Ok(pid) {
        terminate_process_group(child);
        return Err(BenchError::msg(format!(
            "{label}: stopped metadata child is not its process-group leader"
        )));
    }
    nix::sys::signal::kill(pid, nix::sys::signal::Signal::SIGCONT).map_err(|error| {
        terminate_process_group(child);
        BenchError::msg(format!("{label}: resuming metadata child failed: {error}"))
    })
}

impl PlannedResources {
    /// Ask the repository OOM guard to cap `requested_jobs` and split RAM/CPU.
    pub fn plan(repo_root: &Path, requested_jobs: usize, label: &str) -> Result<Self> {
        if requested_jobs == 0 {
            return Err(BenchError::InvalidArgs {
                reason: "requested benchmark jobs must be positive".to_string(),
            });
        }
        let guard_script = repo_root.join("scripts").join("_oom_guard.py");
        if !guard_script.is_file() {
            return Err(BenchError::msg(format!(
                "required resource planner is missing: {}",
                guard_script.display()
            )));
        }
        #[cfg(test)]
        let test_campaign_lease = TestCampaignLease::acquire();
        let aggregate_lease = GlobalHarnessLease::exclusive(&guard_script, label)?;

        let mut command = Command::new("python3");
        command
            .arg(&guard_script)
            .arg("plan")
            .arg("--jobs")
            .arg(requested_jobs.to_string())
            .arg("--label")
            .arg(label);
        // Unit tests invoke focused fake-solver harnesses from a live
        // `cargo test` parent. Production binaries retain the strict build
        // exclusion; tests exercise that policy directly in _oom_guard.py.
        #[cfg(not(test))]
        command.arg("--warn-concurrent-build");
        command.stdout(Stdio::piped()).stderr(Stdio::piped());
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt as _;
            command.process_group(0);
        }
        let mut child = command.spawn().with_bench_context(|| {
            format!(
                "running resource planner {} for {label}",
                guard_script.display()
            )
        })?;
        let stdout_capture = child.stdout.take().map(BoundedPipeCapture::start);
        let stderr_capture = child.stderr.take().map(BoundedPipeCapture::start);
        let status =
            match wait_for_child_exit_unreaped(&child, Duration::from_secs(30), "resource planner")
            {
                Ok(true) => kill_process_group_and_reap(&mut child, "resource planner")?,
                Ok(false) => {
                    terminate_process_group(&mut child);
                    return Err(BenchError::msg(format!(
                        "resource planner {} did not finish within 30 seconds",
                        guard_script.display()
                    )));
                }
                Err(error) => {
                    terminate_process_group(&mut child);
                    return Err(error);
                }
            };
        let stdout = stdout_capture
            .ok_or_else(|| BenchError::msg("resource planner stdout pipe missing"))?
            .finish("resource planner", "stdout")?;
        let stderr = stderr_capture
            .ok_or_else(|| BenchError::msg("resource planner stderr pipe missing"))?
            .finish("resource planner", "stderr")?;

        if !stderr.is_empty() {
            eprint!("{stderr}");
        }
        if !status.success() {
            return Err(BenchError::msg(format!(
                "resource planner {} exited with {}",
                guard_script.display(),
                status
            )));
        }

        let values = parse_plan_output(&stdout)?;
        let jobs = plan_value(&values, "PLAN_JOBS")?;
        let memlimit_mb_per_child = plan_value(&values, "PLAN_MEMLIMIT_MB")?;
        let nbcore_per_child = plan_value(&values, "PLAN_NBCORE")?;
        let headroom_mb = plan_value(&values, "PLAN_HEADROOM_MB")?;
        if jobs == 0 || jobs > requested_jobs {
            return Err(BenchError::msg(format!(
                "resource planner returned invalid job count {jobs} for request {requested_jobs}"
            )));
        }
        if memlimit_mb_per_child == 0 {
            return Err(BenchError::msg(
                "resource planner returned PLAN_MEMLIMIT_MB=0; refusing to spawn an unenveloped child",
            ));
        }
        if nbcore_per_child == 0 {
            return Err(BenchError::msg("resource planner returned PLAN_NBCORE=0"));
        }
        aggregate_lease.ensure_alive(label)?;

        Ok(Self {
            plan: ResourcePlan {
                requested_jobs,
                jobs,
                memlimit_mb_per_child,
                nbcore_per_child,
                headroom_mb,
                planner: guard_script.display().to_string(),
            },
            watchdog_server: SharedWatchdogServer::new(guard_script.clone()),
            guard_script,
            _aggregate_lease: Some(aggregate_lease),
            #[cfg(test)]
            _test_campaign_lease: Some(test_campaign_lease),
        })
    }

    /// Reduce the planner-admitted per-child envelope for a campaign profile.
    ///
    /// The OOM guard remains the source of admission and aggregate exclusion;
    /// profile caps may only make its plan stricter. The reduced values are
    /// the ones exported to children, enforced by the watchdog, and persisted
    /// in result packets.
    pub(crate) fn apply_per_child_caps(
        &mut self,
        memory_mib: Option<usize>,
        cores: Option<usize>,
    ) -> Result<()> {
        if memory_mib == Some(0) || cores == Some(0) {
            return Err(BenchError::InvalidArgs {
                reason: "resource profile caps must be positive".to_string(),
            });
        }
        if let Some(memory_mib) = memory_mib {
            self.plan.memlimit_mb_per_child = self.plan.memlimit_mb_per_child.min(memory_mib);
        }
        if let Some(cores) = cores {
            self.plan.nbcore_per_child = self.plan.nbcore_per_child.min(cores);
        }
        Ok(())
    }

    /// Spawn an external child suspended, arm `_oom_guard.rss_watchdog`, then
    /// let the child exec. This handshake eliminates the old attach-after-spawn
    /// window in which a fast allocator could run before its RSS limit existed.
    pub(crate) fn external_command(&self, program: impl AsRef<std::ffi::OsStr>) -> Command {
        let mut command = Command::new("python3");
        command
            .arg(&self.guard_script)
            .arg("exec-stopped")
            .arg("--")
            .arg(program);
        command
    }

    /// Build a stopped-start command whose target inherits a hard regular-file
    /// size ceiling before it is resumed under the RSS watchdog.
    pub(crate) fn external_command_with_file_limit(
        &self,
        program: impl AsRef<std::ffi::OsStr>,
        bytes: u64,
    ) -> Command {
        let mut command = Command::new("python3");
        command
            .arg(&self.guard_script)
            .arg("exec-stopped")
            .arg("--fsize-bytes")
            .arg(bytes.to_string())
            .arg("--")
            .arg(program);
        command
    }

    /// Capture a short metadata command without unbounded parent-memory pipes.
    /// The child is handshake-guarded; output is spooled to anonymous files and
    /// rejected if either stream exceeds 1 MiB.
    pub(crate) fn capture_external_output<I, S>(
        &self,
        program: &Path,
        args: I,
        timeout: Duration,
        label: &str,
    ) -> Result<CapturedOutput>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<std::ffi::OsStr>,
    {
        let mut command = self.external_command(program);
        command.args(args);
        command.env("MEMLIMIT", self.plan.memlimit_mb_per_child.to_string());
        command.env("NBCORE", self.plan.nbcore_per_child.to_string());
        command.stdout(Stdio::piped());
        command.stderr(Stdio::piped());
        command.stdin(Stdio::null());
        let (mut child, watchdog) = self.spawn_external_child(&mut command, label)?;
        let stdout_capture = child.stdout.take().map(BoundedPipeCapture::start);
        let stderr_capture = child.stderr.take().map(BoundedPipeCapture::start);
        let outcome = wait_for_guarded_child(&mut child, watchdog, timeout, label)?;
        if outcome.memout {
            return Err(BenchError::msg(format!(
                "{label}: metadata command exceeded its memory envelope"
            )));
        }
        if outcome.timed_out {
            return Err(BenchError::msg(format!(
                "{label}: metadata command exceeded {:.3}s",
                timeout.as_secs_f64()
            )));
        }
        let status = outcome
            .status
            .ok_or_else(|| BenchError::msg(format!("{label}: metadata command was not reaped")))?;

        let stdout = stdout_capture
            .ok_or_else(|| BenchError::msg(format!("{label}: stdout pipe missing")))?
            .finish(label, "stdout")?;
        let stderr = stderr_capture
            .ok_or_else(|| BenchError::msg(format!("{label}: stderr pipe missing")))?
            .finish(label, "stderr")?;
        Ok(CapturedOutput {
            status,
            stdout,
            stderr,
        })
    }

    /// Run one external command under the campaign's stopped-exec RSS
    /// watchdog, retaining at most one MiB of stdout while draining the pipe
    /// completely. The returned timeout and memout flags are mutually
    /// exclusive and preserve the watchdog's timestamped first cause.
    pub fn run_external_captured<I, S>(
        &self,
        program: impl AsRef<std::ffi::OsStr>,
        args: I,
        timeout: Duration,
        label: &str,
    ) -> Result<GuardedCapturedOutput>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<std::ffi::OsStr>,
    {
        let started = Instant::now();
        let mut command = self.external_command(program);
        command
            .args(args)
            .env("MEMLIMIT", self.plan.memlimit_mb_per_child.to_string())
            .env("NBCORE", self.plan.nbcore_per_child.to_string())
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::null());
        let (mut child, watchdog) = self.spawn_external_child(&mut command, label)?;
        let Some(stdout) = child.stdout.take() else {
            terminate_guarded_child(&mut child, watchdog, label)?;
            return Err(BenchError::msg(format!(
                "{label}: guarded stdout pipe is missing"
            )));
        };
        let capture = BoundedBytesCapture::start(stdout);
        let outcome = wait_for_guarded_child(&mut child, watchdog, timeout, label);
        let captured = capture.finish(label, "stdout");
        let (outcome, (stdout, output_truncated)) = match (outcome, captured) {
            (Ok(outcome), Ok(captured)) => (outcome, captured),
            (Err(error), Ok(_)) | (Ok(_), Err(error)) => return Err(error),
            (Err(wait_error), Err(capture_error)) => {
                return Err(BenchError::msg(format!(
                    "{wait_error}; stdout cleanup failed: {capture_error}"
                )))
            }
        };
        Ok(GuardedCapturedOutput {
            status: outcome.status,
            stdout,
            observed: started.elapsed(),
            timed_out: outcome.timed_out,
            memout: outcome.memout,
            output_truncated,
        })
    }

    /// Run one byte transcript under the campaign's stopped-exec RSS
    /// watchdog.
    ///
    /// Input larger than [`GUARDED_TRANSCRIPT_INPUT_LIMIT`] is rejected before
    /// spawning. Stdout and stderr are drained concurrently and independently,
    /// retaining at most [`GUARDED_TRANSCRIPT_STREAM_LIMIT`] bytes from each.
    /// The returned first-cause timeout and memout flags come from the same
    /// timestamped watchdog cleanup path as [`Self::run_external_captured`].
    pub fn run_external_transcript<I, S>(
        &self,
        program: impl AsRef<std::ffi::OsStr>,
        args: I,
        stdin: &[u8],
        timeout: Duration,
        label: &str,
    ) -> Result<GuardedTranscriptOutput>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<std::ffi::OsStr>,
    {
        self.run_external_transcript_impl(program, args, stdin, timeout, label, &[])
    }

    /// Run one byte transcript while removing dynamic-loader injection and
    /// search-path variables from the child before its first `exec`.
    ///
    /// Use this for authenticated shared-library probes: clearing only inside a
    /// shell wrapper is too late because the wrapper itself has already been
    /// loaded under the inherited environment. The RSS watchdog and explicit
    /// `MEMLIMIT`/`NBCORE` settings remain identical to
    /// [`Self::run_external_transcript`].
    pub fn run_external_transcript_scrubbed<I, S>(
        &self,
        program: impl AsRef<std::ffi::OsStr>,
        args: I,
        stdin: &[u8],
        timeout: Duration,
        label: &str,
    ) -> Result<GuardedTranscriptOutput>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<std::ffi::OsStr>,
    {
        const LOADER_ENVIRONMENT: &[&str] = &[
            "DYLD_FRAMEWORK_PATH",
            "DYLD_FALLBACK_FRAMEWORK_PATH",
            "DYLD_FALLBACK_LIBRARY_PATH",
            "DYLD_IMAGE_SUFFIX",
            "DYLD_INSERT_LIBRARIES",
            "DYLD_LIBRARY_PATH",
            "DYLD_ROOT_PATH",
            "DYLD_VERSIONED_FRAMEWORK_PATH",
            "DYLD_VERSIONED_LIBRARY_PATH",
            "LD_AUDIT",
            "LD_DEBUG",
            "LD_LIBRARY_PATH",
            "LD_PRELOAD",
            "LD_PROFILE",
            "LIBPATH",
            "SHLIB_PATH",
        ];
        self.run_external_transcript_impl(program, args, stdin, timeout, label, LOADER_ENVIRONMENT)
    }

    fn run_external_transcript_impl<I, S>(
        &self,
        program: impl AsRef<std::ffi::OsStr>,
        args: I,
        stdin: &[u8],
        timeout: Duration,
        label: &str,
        removed_environment: &[&str],
    ) -> Result<GuardedTranscriptOutput>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<std::ffi::OsStr>,
    {
        if stdin.len() > GUARDED_TRANSCRIPT_INPUT_LIMIT {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "{label}: guarded stdin is {} bytes, exceeding the fixed {}-byte limit",
                    stdin.len(),
                    GUARDED_TRANSCRIPT_INPUT_LIMIT
                ),
            });
        }

        let started = Instant::now();
        let mut command = self.external_command(program);
        for variable in removed_environment {
            command.env_remove(variable);
        }
        command
            .args(args)
            .env("MEMLIMIT", self.plan.memlimit_mb_per_child.to_string())
            .env("NBCORE", self.plan.nbcore_per_child.to_string())
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        let (mut child, watchdog) = self.spawn_external_child(&mut command, label)?;
        let (Some(child_stdin), Some(stdout), Some(stderr)) =
            (child.stdin.take(), child.stdout.take(), child.stderr.take())
        else {
            terminate_guarded_child(&mut child, watchdog, label)?;
            return Err(BenchError::msg(format!(
                "{label}: guarded transcript pipe is missing"
            )));
        };

        let stdin_writer = BoundedStdinWriter::start(child_stdin, stdin.to_vec());
        let stdout_capture = BoundedBytesCapture::start(stdout);
        let stderr_capture = BoundedBytesCapture::start(stderr);
        let outcome = wait_for_guarded_child(&mut child, watchdog, timeout, label);
        let stdin_result = stdin_writer.finish(label);
        let stdout_result = stdout_capture.finish(label, "stdout");
        let stderr_result = stderr_capture.finish(label, "stderr");

        let mut failures = Vec::new();
        let outcome = match outcome {
            Ok(outcome) => Some(outcome),
            Err(error) => {
                failures.push(error.to_string());
                None
            }
        };
        let stdin_complete = match stdin_result {
            Ok(stdin_complete) => Some(stdin_complete),
            Err(error) => {
                failures.push(error.to_string());
                None
            }
        };
        let stdout = match stdout_result {
            Ok(stdout) => Some(stdout),
            Err(error) => {
                failures.push(error.to_string());
                None
            }
        };
        let stderr = match stderr_result {
            Ok(stderr) => Some(stderr),
            Err(error) => {
                failures.push(error.to_string());
                None
            }
        };
        if !failures.is_empty() {
            return Err(BenchError::msg(failures.join("; ")));
        }

        let outcome =
            outcome.ok_or_else(|| BenchError::msg(format!("{label}: guarded outcome missing")))?;
        let (stdout, stdout_truncated) =
            stdout.ok_or_else(|| BenchError::msg(format!("{label}: guarded stdout missing")))?;
        let (stderr, stderr_truncated) =
            stderr.ok_or_else(|| BenchError::msg(format!("{label}: guarded stderr missing")))?;
        let stdin_complete = stdin_complete
            .ok_or_else(|| BenchError::msg(format!("{label}: guarded stdin outcome missing")))?;
        Ok(GuardedTranscriptOutput {
            status: outcome.status,
            stdout,
            stderr,
            observed: started.elapsed(),
            timed_out: outcome.timed_out,
            memout: outcome.memout,
            stdin_complete,
            stdout_truncated,
            stderr_truncated,
        })
    }

    #[cfg(unix)]
    pub(crate) fn spawn_external_child(
        &self,
        command: &mut Command,
        label: &str,
    ) -> Result<(Child, RssWatchdog)> {
        use std::os::unix::process::CommandExt as _;

        self.ensure_aggregate_lease_alive(label)?;
        command.process_group(0);

        let mut child = command
            .spawn()
            .with_bench_context(|| format!("spawning suspended child for {label}"))?;
        let pid_raw = match i32::try_from(child.id()) {
            Ok(pid) if pid > 0 => pid,
            _ => {
                terminate_process_group(&mut child);
                return Err(BenchError::msg(format!(
                    "{label}: child PID does not fit a POSIX pid_t"
                )));
            }
        };
        let pid = nix::unistd::Pid::from_raw(pid_raw);
        let stop_deadline = Instant::now() + Duration::from_secs(10);
        loop {
            match observe_child_unreaped(&child, true, label) {
                Ok(UnreapedChildState::Stopped(nix::sys::signal::Signal::SIGSTOP)) => break,
                Ok(UnreapedChildState::Running) if Instant::now() < stop_deadline => {
                    std::thread::sleep(Duration::from_millis(5));
                }
                Ok(UnreapedChildState::Running) => {
                    terminate_process_group(&mut child);
                    return Err(BenchError::msg(format!(
                        "{label}: child did not enter the watchdog handshake stop within 10 seconds"
                    )));
                }
                Ok(status) => {
                    terminate_process_group(&mut child);
                    return Err(BenchError::msg(format!(
                        "{label}: child did not enter the watchdog handshake stop ({status:?})"
                    )));
                }
                Err(error) => {
                    terminate_process_group(&mut child);
                    return Err(BenchError::msg(format!(
                        "{label}: waiting for watchdog handshake stop failed: {error}"
                    )));
                }
            }
        }
        if nix::unistd::getpgid(Some(pid)) != Ok(pid) {
            terminate_process_group(&mut child);
            return Err(BenchError::msg(format!(
                "{label}: suspended child is not its own process-group leader"
            )));
        }

        // Registration travels over private inherited pipes to the single
        // campaign watcher. `register` returns only after this exact PGID's
        // zero-grace guard has authenticated and armed while the child remains
        // SIGSTOPped.
        let mut watchdog =
            match self
                .watchdog_server
                .register(child.id(), self.plan.memlimit_mb_per_child, label)
            {
                Ok(watchdog) => watchdog,
                Err(error) => {
                    terminate_process_group(&mut child);
                    return Err(error);
                }
            };
        watchdog.aggregate_lease = self._aggregate_lease.clone();
        if let Err(error) = self.ensure_aggregate_lease_alive(label) {
            terminate_process_group(&mut child);
            // The primary failure already proves this lease is dead. Cleanup
            // still needs the watchdog's terminal record, but rechecking the
            // same dead lease there would only obscure it with a duplicate
            // "watchdog cleanup failed" suffix.
            watchdog.aggregate_lease = None;
            let cleanup = watchdog.finish_after_target_cleanup().err();
            return Err(BenchError::msg(format!(
                "{error}{}",
                cleanup
                    .map(|cleanup| format!("; watchdog cleanup failed: {cleanup}"))
                    .unwrap_or_default()
            )));
        }

        if let Err(error) = nix::sys::signal::kill(pid, nix::sys::signal::Signal::SIGCONT) {
            terminate_process_group(&mut child);
            let cleanup = watchdog.finish_after_target_cleanup().err();
            return Err(BenchError::msg(format!(
                "{label}: resuming guarded child failed: {error}{}",
                cleanup
                    .map(|cleanup| format!("; watchdog cleanup failed: {cleanup}"))
                    .unwrap_or_default()
            )));
        }
        Ok((child, watchdog))
    }

    #[cfg(not(unix))]
    pub(crate) fn spawn_external_child(
        &self,
        _command: &mut Command,
        label: &str,
    ) -> Result<(Child, RssWatchdog)> {
        Err(BenchError::msg(format!(
            "{label}: exact external-child RSS enforcement requires POSIX process groups"
        )))
    }

    #[cfg(test)]
    pub(crate) fn for_test(repo_root: &Path, memlimit_mb_per_child: usize) -> Self {
        Self {
            plan: ResourcePlan {
                requested_jobs: 1,
                jobs: 1,
                memlimit_mb_per_child,
                nbcore_per_child: 1,
                headroom_mb: 0,
                planner: "test".to_string(),
            },
            guard_script: repo_root.join("scripts").join("_oom_guard.py"),
            _aggregate_lease: None,
            watchdog_server: SharedWatchdogServer::new(
                repo_root.join("scripts").join("_oom_guard.py"),
            ),
            _test_campaign_lease: None,
        }
    }

    #[cfg(all(
        test,
        any(
            target_os = "android",
            target_os = "freebsd",
            target_os = "haiku",
            target_os = "macos",
            all(target_os = "linux", not(target_env = "uclibc")),
        ),
    ))]
    fn watchdog_server_pid(&self) -> Option<u32> {
        self.watchdog_server.process_id()
    }

    fn ensure_aggregate_lease_alive(&self, label: &str) -> Result<()> {
        match self._aggregate_lease.as_deref() {
            Some(lease) => lease.ensure_alive(label),
            None => Ok(()),
        }
    }
}

/// Wait for a handshake-guarded child while continuously checking that its
/// RSS watchdog remains alive. Every return path reaps the isolated process
/// group and its campaign-server registration, so callers cannot accidentally
/// leak either handle.
pub(crate) fn wait_for_guarded_child(
    child: &mut Child,
    watchdog: RssWatchdog,
    timeout: Duration,
    label: &str,
) -> Result<GuardedChildOutcome> {
    wait_for_guarded_child_with_limits(child, watchdog, timeout, label, None, None)
}

pub(crate) fn wait_for_guarded_child_with_file_limit(
    child: &mut Child,
    watchdog: RssWatchdog,
    timeout: Duration,
    label: &str,
    file_limit: Option<(&Path, u64)>,
) -> Result<GuardedChildOutcome> {
    wait_for_guarded_child_with_limits(child, watchdog, timeout, label, file_limit, None)
}

include!("resource/unreaped_child_state.rs");

#[cfg(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
))]
fn observe_child_unreaped(
    child: &Child,
    include_stopped: bool,
    label: &str,
) -> Result<UnreapedChildState> {
    use nix::sys::wait::{waitid, Id, WaitPidFlag, WaitStatus};
    use nix::unistd::Pid;

    let raw_pid = i32::try_from(child.id())
        .map_err(|_| BenchError::msg(format!("{label}: child PID does not fit pid_t")))?;
    let mut flags = WaitPidFlag::WEXITED | WaitPidFlag::WNOHANG | WaitPidFlag::WNOWAIT;
    if include_stopped {
        flags |= WaitPidFlag::WSTOPPED;
    }
    match waitid(Id::Pid(Pid::from_raw(raw_pid)), flags) {
        Ok(WaitStatus::Exited(..) | WaitStatus::Signaled(..)) => Ok(UnreapedChildState::Exited),
        Ok(WaitStatus::Stopped(_, signal)) if include_stopped => {
            Ok(UnreapedChildState::Stopped(signal))
        }
        Ok(WaitStatus::StillAlive | WaitStatus::Continued(..)) => Ok(UnreapedChildState::Running),
        Ok(status) => Err(BenchError::msg(format!(
            "{label}: unexpected unreaped child status: {status:?}"
        ))),
        Err(error) => Err(BenchError::msg(format!(
            "{label}: observing child without reaping failed: {error}"
        ))),
    }
}

#[cfg(target_os = "macos")]
fn observe_child_unreaped(
    child: &Child,
    include_stopped: bool,
    label: &str,
) -> Result<UnreapedChildState> {
    use ay_sys::supervisor::UnreapedChildState as SystemChildState;

    match ay_sys::supervisor::observe_child_unreaped(child, include_stopped) {
        Ok(SystemChildState::Running) => Ok(UnreapedChildState::Running),
        Ok(SystemChildState::Exited) => Ok(UnreapedChildState::Exited),
        Ok(SystemChildState::Stopped(signal)) if include_stopped => {
            let signal = nix::sys::signal::Signal::try_from(signal).map_err(|error| {
                BenchError::msg(format!(
                    "{label}: child stopped with invalid signal {signal}: {error}"
                ))
            })?;
            Ok(UnreapedChildState::Stopped(signal))
        }
        Ok(SystemChildState::Stopped(signal)) => Err(BenchError::msg(format!(
            "{label}: unexpectedly observed stopped child with signal {signal}"
        ))),
        Err(error) => Err(BenchError::msg(format!(
            "{label}: observing child without reaping failed: {error}"
        ))),
    }
}

#[cfg(not(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    target_os = "macos",
    all(target_os = "linux", not(target_env = "uclibc")),
)))]
fn observe_child_unreaped(
    _child: &Child,
    _include_stopped: bool,
    label: &str,
) -> Result<UnreapedChildState> {
    // Unix-only: off Unix the witness does not exist (see its definition).
    #[cfg(unix)]
    let _ = UNREAPED_CHILD_STATE_TYPE_WITNESS;
    Err(BenchError::msg(format!(
        "{label}: safe unreaped child observation is unavailable on this platform"
    )))
}

#[cfg(all(
    test,
    unix,
    not(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc")),
    )),
))]
#[test]
fn unsupported_target_rejects_unreaped_child_observation() {
    let mut child = std::process::Command::new("/usr/bin/true")
        .spawn()
        .expect("spawn policy probe");
    let error = observe_child_unreaped(&child, false, "target-policy regression")
        .expect_err("unsupported targets must fail closed");
    assert!(error
        .to_string()
        .contains("safe unreaped child observation is unavailable"));
    child.wait().expect("reap policy probe");
}

fn wait_for_child_exit_unreaped(child: &Child, timeout: Duration, label: &str) -> Result<bool> {
    let deadline = Instant::now()
        .checked_add(timeout)
        .ok_or_else(|| BenchError::msg(format!("{label}: child wait deadline overflow")))?;
    loop {
        match observe_child_unreaped(child, false, label)? {
            UnreapedChildState::Exited => return Ok(true),
            UnreapedChildState::Running => {}
            UnreapedChildState::Stopped(_) => {
                return Err(BenchError::msg(format!(
                    "{label}: child stopped unexpectedly while awaiting exit"
                )))
            }
        }
        if Instant::now() >= deadline {
            return Ok(false);
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

pub(crate) fn wait_for_guarded_child_with_limits(
    child: &mut Child,
    mut watchdog: RssWatchdog,
    timeout: Duration,
    label: &str,
    file_limit: Option<(&Path, u64)>,
    abort_flag: Option<&std::sync::atomic::AtomicBool>,
) -> Result<GuardedChildOutcome> {
    let (deadline, invalid_reason) = if timeout.is_zero() {
        (None, Some("guarded child timeout must be positive"))
    } else if file_limit.is_some_and(|(_, limit)| limit == 0) {
        (None, Some("guarded file-size limit must be positive"))
    } else {
        match Instant::now().checked_add(timeout) {
            Some(deadline) => (Some(deadline), None),
            None => (
                None,
                Some("guarded child timeout is too large for the monotonic clock"),
            ),
        }
    };
    if let Some(reason) = invalid_reason {
        terminate_process_group(child);
        let cleanup = watchdog.finish_after_target_cleanup().err();
        return Err(BenchError::msg(match cleanup {
            Some(error) => format!("{label}: {reason}; watchdog cleanup failed: {error}"),
            None => format!("{label}: {reason}"),
        }));
    }
    let deadline = match deadline {
        Some(deadline) => deadline,
        None => {
            terminate_process_group(child);
            let cleanup = watchdog.finish_after_target_cleanup().err();
            return Err(BenchError::msg(match cleanup {
                Some(error) => format!(
                    "{label}: internal deadline validation failed; watchdog cleanup failed: {error}"
                ),
                None => format!("{label}: internal deadline validation failed"),
            }));
        }
    };
    loop {
        if abort_flag.is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Acquire)) {
            terminate_process_group(child);
            let cleanup = watchdog.finish_after_target_cleanup().err();
            return Err(BenchError::msg(match cleanup {
                Some(error) => format!(
                    "{label}: bounded output capture failed or exceeded its fixed size limit; watchdog cleanup failed: {error}"
                ),
                None => format!(
                    "{label}: bounded output capture failed or exceeded its fixed size limit"
                ),
            }));
        }
        if let Some((path, limit)) = file_limit {
            match std::fs::symlink_metadata(path) {
                Ok(metadata) if !metadata.file_type().is_file() => {
                    terminate_process_group(child);
                    let cleanup = watchdog.finish_after_target_cleanup().err();
                    return Err(BenchError::msg(match cleanup {
                        Some(error) => format!(
                            "{label}: guarded artifact is not a regular file: {}; watchdog cleanup failed: {error}",
                            path.display()
                        ),
                        None => format!(
                            "{label}: guarded artifact is not a regular file: {}",
                            path.display()
                        ),
                    }));
                }
                Ok(metadata) if metadata.len() > limit => {
                    terminate_process_group(child);
                    let cleanup = watchdog.finish_after_target_cleanup().err();
                    return Err(BenchError::msg(match cleanup {
                        Some(error) => format!(
                            "{label}: guarded artifact {} exceeded the fixed {limit}-byte limit; watchdog cleanup failed: {error}",
                            path.display()
                        ),
                        None => format!(
                            "{label}: guarded artifact {} exceeded the fixed {limit}-byte limit",
                            path.display()
                        ),
                    }));
                }
                Ok(_) => {}
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => {
                    terminate_process_group(child);
                    let cleanup = watchdog.finish_after_target_cleanup().err();
                    return Err(BenchError::msg(match cleanup {
                        Some(cleanup_error) => format!(
                            "{label}: cannot inspect guarded artifact {}: {error}; watchdog cleanup failed: {cleanup_error}",
                            path.display()
                        ),
                        None => format!(
                            "{label}: cannot inspect guarded artifact {}: {error}",
                            path.display()
                        ),
                    }));
                }
            }
        }
        match observe_child_unreaped(child, false, label) {
            Ok(UnreapedChildState::Exited) => {
                let trigger_ns = match monotonic_time_ns() {
                    Ok(trigger_ns) => trigger_ns,
                    Err(error) => {
                        terminate_process_group(child);
                        let cleanup = watchdog.finish_after_target_cleanup().err();
                        return Err(BenchError::msg(match cleanup {
                            Some(cleanup) => format!(
                                "{label}: cannot timestamp child completion: {error}; watchdog cleanup failed: {cleanup}"
                            ),
                            None => format!(
                                "{label}: cannot timestamp child completion: {error}"
                            ),
                        }));
                    }
                };
                // Keep the exited leader unreaped until every residual
                // descendant in its process group has been killed. Reaping
                // first would permit an inherited stdout descriptor to keep
                // the bounded reader alive indefinitely.
                let status_result = kill_process_group_and_reap(child, label);
                let watchdog_result = watchdog.finish_after_target_cleanup();
                let (status, watchdog_outcome) = match (status_result, watchdog_result) {
                    (Ok(status), Ok(watchdog_outcome)) => (status, watchdog_outcome),
                    (Err(status_error), Ok(_)) => return Err(status_error),
                    (Ok(_), Err(watchdog_error)) => return Err(watchdog_error),
                    (Err(status_error), Err(watchdog_error)) => {
                        return Err(BenchError::msg(format!(
                            "{status_error}; watchdog cleanup failed: {watchdog_error}"
                        )))
                    }
                };
                let memout = watchdog_breached_before(watchdog_outcome, trigger_ns)?;
                return Ok(GuardedChildOutcome {
                    status: Some(status),
                    timed_out: false,
                    memout,
                });
            }
            Ok(UnreapedChildState::Running) => {}
            Ok(UnreapedChildState::Stopped(_)) => {
                terminate_process_group(child);
                let watchdog_error = watchdog.finish_after_target_cleanup().err();
                return Err(BenchError::msg(match watchdog_error {
                    Some(error) => format!(
                        "{label}: guarded child stopped unexpectedly; watchdog cleanup failed: {error}"
                    ),
                    None => format!("{label}: guarded child stopped unexpectedly"),
                }));
            }
            Err(error) => {
                terminate_process_group(child);
                let watchdog_error = watchdog.finish_after_target_cleanup().err();
                return Err(BenchError::msg(match watchdog_error {
                    Some(watchdog_error) => {
                        format!("{label}: waiting for child failed: {error}; watchdog cleanup failed: {watchdog_error}")
                    }
                    None => format!("{label}: waiting for child failed: {error}"),
                }));
            }
        }

        match watchdog.poll() {
            Ok(None) => {}
            Ok(Some(observed)) if observed.breached => {
                terminate_process_group(child);
                let final_outcome = watchdog.finish_after_target_cleanup()?;
                if !final_outcome.breached {
                    return Err(BenchError::msg(
                        "RSS watchdog lost a previously observed breach",
                    ));
                }
                return Ok(GuardedChildOutcome {
                    status: child.try_wait().ok().flatten(),
                    timed_out: false,
                    memout: true,
                });
            }
            Ok(Some(_)) => {
                terminate_process_group(child);
                return Err(BenchError::msg(format!(
                    "{label}: RSS watchdog stopped before the child"
                )));
            }
            Err(error) => {
                terminate_process_group(child);
                return Err(BenchError::msg(format!(
                    "{label}: RSS watchdog failed while the child was active: {error}"
                )));
            }
        }

        if Instant::now() >= deadline {
            let trigger_ns = match monotonic_time_ns() {
                Ok(trigger_ns) => trigger_ns,
                Err(error) => {
                    terminate_process_group(child);
                    let cleanup = watchdog.finish_after_target_cleanup().err();
                    return Err(BenchError::msg(match cleanup {
                        Some(cleanup) => format!(
                            "{label}: cannot timestamp timeout trigger: {error}; watchdog cleanup failed: {cleanup}"
                        ),
                        None => format!("{label}: cannot timestamp timeout trigger: {error}"),
                    }));
                }
            };
            terminate_process_group(child);
            let watchdog_outcome = watchdog.finish_after_target_cleanup()?;
            let memout = watchdog_breached_before(watchdog_outcome, trigger_ns)?;
            return Ok(GuardedChildOutcome {
                status: child.try_wait().ok().flatten(),
                timed_out: !memout,
                memout,
            });
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// Handle for one registration in the campaign-wide `_oom_guard.py` server.
#[derive(Debug, Clone, Copy)]
pub(crate) struct WatchdogOutcome {
    breached: bool,
    breach_time_ns: Option<u64>,
}

#[derive(Debug)]
pub(crate) struct RssWatchdog {
    server: std::sync::Arc<SharedWatchdogServer>,
    aggregate_lease: Option<std::sync::Arc<GlobalHarnessLease>>,
    watch_id: u64,
    target_pgid: Option<i32>,
    terminal_breach: Option<WatchdogOutcome>,
    receiver: std::sync::mpsc::Receiver<WatchdogServerMessage>,
}

impl RssWatchdog {
    fn ensure_aggregate_lease_alive(&mut self) -> Result<()> {
        let result = match self.aggregate_lease.as_deref() {
            Some(lease) => lease.ensure_alive("guarded solver"),
            None => Ok(()),
        };
        if let Err(error) = result {
            self.kill_target();
            return Err(error);
        }
        Ok(())
    }

    fn kill_target(&mut self) {
        #[cfg(unix)]
        if let Some(raw) = self.target_pgid.take() {
            let _ = nix::sys::signal::killpg(
                nix::unistd::Pid::from_raw(raw),
                nix::sys::signal::Signal::SIGKILL,
            );
        }
        #[cfg(not(unix))]
        {
            self.target_pgid = None;
        }
    }

    /// Poll watchdog health while the guarded child is still running.
    pub(crate) fn poll(&mut self) -> Result<Option<WatchdogOutcome>> {
        self.ensure_aggregate_lease_alive()?;
        if let Some(breached) = self.terminal_breach {
            return Ok(Some(breached));
        }
        if !self.server.is_healthy() {
            self.kill_target();
            return Err(BenchError::msg(
                "campaign RSS watchdog server stopped while a solver was active",
            ));
        }
        match self.receiver.try_recv() {
            Ok(message) => {
                // Receiving any post-readiness response ends this server-side
                // registration. Disarm the authenticated PGID before decoding
                // the response: decoding is fallible, and the caller kills and
                // reaps a still-live target on that error path. Retaining the
                // numeric PGID until `Drop` would let it signal an unrelated
                // group if the kernel reused the number after that reap.
                self.target_pgid = None;
                let outcome = self.decode_terminal_event(message)?;
                self.terminal_breach = Some(outcome);
                Ok(Some(outcome))
            }
            Err(std::sync::mpsc::TryRecvError::Empty) => Ok(None),
            Err(std::sync::mpsc::TryRecvError::Disconnected) => {
                self.kill_target();
                Err(BenchError::msg(format!(
                    "RSS watchdog {} response channel disconnected",
                    self.watch_id
                )))
            }
        }
    }

    /// Receive the terminal report for this registration.
    pub(crate) fn finish(mut self) -> Result<WatchdogOutcome> {
        self.ensure_aggregate_lease_alive()?;
        if let Some(breached) = self.terminal_breach {
            self.target_pgid = None;
            return Ok(breached);
        }
        if !self.server.is_healthy() {
            self.kill_target();
            return Err(BenchError::msg(
                "campaign RSS watchdog server stopped before reporting completion",
            ));
        }
        let message = match self.receiver.recv_timeout(Duration::from_secs(12)) {
            Ok(message) => message,
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                self.kill_target();
                return Err(BenchError::msg(format!(
                    "RSS watchdog {} did not report completion within 12 seconds",
                    self.watch_id
                )));
            }
            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
                self.kill_target();
                return Err(BenchError::msg(format!(
                    "RSS watchdog {} response channel disconnected",
                    self.watch_id
                )));
            }
        };
        let outcome = self.decode_terminal_event(message);
        if outcome.is_ok() {
            self.target_pgid = None;
            self.ensure_aggregate_lease_alive()?;
        }
        outcome
    }

    /// Finish after the caller has already killed and reaped the authenticated
    /// target group. Disarming first prevents an error-path `Drop` from ever
    /// signalling a PGID that could have been reused after the leader reap.
    fn finish_after_target_cleanup(mut self) -> Result<WatchdogOutcome> {
        self.target_pgid = None;
        self.finish()
    }

    fn decode_terminal_event(&self, event: WatchdogServerMessage) -> Result<WatchdogOutcome> {
        match event.map_err(|error| {
            BenchError::msg(format!("RSS watchdog {} failed: {error}", self.watch_id))
        })? {
            WatchdogServerEvent::Done => Ok(WatchdogOutcome {
                breached: false,
                breach_time_ns: None,
            }),
            WatchdogServerEvent::Breach(breach_time_ns) => Ok(WatchdogOutcome {
                breached: true,
                breach_time_ns: Some(breach_time_ns),
            }),
            WatchdogServerEvent::Ready => Err(BenchError::msg(format!(
                "RSS watchdog {} emitted duplicate readiness",
                self.watch_id
            ))),
        }
    }
}

impl Drop for RssWatchdog {
    fn drop(&mut self) {
        self.kill_target();
    }
}

fn kill_process_group(child: &mut Child) {
    #[cfg(unix)]
    {
        if let Ok(pid) = i32::try_from(child.id()) {
            let pgid = nix::unistd::Pid::from_raw(pid);
            let _ = nix::sys::signal::killpg(pgid, nix::sys::signal::Signal::SIGKILL);
        }
    }
    #[cfg(not(unix))]
    {
        let _ = child.kill();
    }
}

fn kill_process_group_and_reap(child: &mut Child, label: &str) -> Result<ExitStatus> {
    kill_process_group(child);
    match child.wait_timeout(Duration::from_secs(5)) {
        Ok(Some(status)) => Ok(status),
        Ok(None) => Err(BenchError::msg(format!(
            "{label}: process-group leader could not be reaped within 5 seconds after SIGKILL"
        ))),
        Err(error) => Err(BenchError::msg(format!(
            "{label}: reaping process-group leader after SIGKILL failed: {error}"
        ))),
    }
}

pub(crate) fn terminate_guarded_child(
    child: &mut Child,
    watchdog: RssWatchdog,
    label: &str,
) -> Result<()> {
    let child_result = kill_process_group_and_reap(child, label).map(|_| ());
    let watchdog_result = watchdog.finish_after_target_cleanup().map(|_| ());
    match (child_result, watchdog_result) {
        (Ok(()), Ok(())) => Ok(()),
        (Err(error), Ok(())) | (Ok(()), Err(error)) => Err(error),
        (Err(child_error), Err(watchdog_error)) => Err(BenchError::msg(format!(
            "{child_error}; watchdog cleanup failed: {watchdog_error}"
        ))),
    }
}

/// Kill and reap an isolated solver process group. Callers must not reap the
/// leader before invoking this helper: the unreaped PID prevents PGID reuse
/// between group signalling and cleanup.
pub(crate) fn terminate_process_group(child: &mut Child) {
    kill_process_group(child);
    // SIGKILL does not wake an uninterruptible (D-state) task. Never let
    // cleanup turn a bounded harness deadline into an unbounded parent wait.
    let _ = child.wait_timeout(Duration::from_secs(5));
}

fn parse_plan_output(output: &str) -> Result<BTreeMap<&str, usize>> {
    let mut values = BTreeMap::new();
    for line in output.lines() {
        let Some((key, value)) = line.trim().split_once('=') else {
            continue;
        };
        if !key.starts_with("PLAN_") {
            continue;
        }
        if !matches!(
            key,
            "PLAN_JOBS" | "PLAN_MEMLIMIT_MB" | "PLAN_NBCORE" | "PLAN_HEADROOM_MB"
        ) {
            return Err(BenchError::msg(format!(
                "resource planner returned unknown field {key}"
            )));
        }
        let value = value.parse::<usize>().map_err(|_| {
            BenchError::msg(format!("resource planner returned invalid {key}={value:?}"))
        })?;
        if values.insert(key, value).is_some() {
            return Err(BenchError::msg(format!(
                "resource planner returned duplicate field {key}"
            )));
        }
    }
    for key in [
        "PLAN_JOBS",
        "PLAN_MEMLIMIT_MB",
        "PLAN_NBCORE",
        "PLAN_HEADROOM_MB",
    ] {
        if !values.contains_key(key) {
            return Err(BenchError::msg(format!("resource planner omitted {key}")));
        }
    }
    Ok(values)
}

fn plan_value(values: &BTreeMap<&str, usize>, key: &'static str) -> Result<usize> {
    values
        .get(key)
        .copied()
        .ok_or_else(|| BenchError::msg(format!("resource planner omitted {key}")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(target_os = "linux")]
    fn secure_test_directory(path: &Path) {
        use std::os::unix::fs::PermissionsExt as _;
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700))
            .expect("secure test directory");
    }

    #[test]
    fn parses_complete_plan_without_shell_evaluation() {
        let parsed = parse_plan_output(
            "PLAN_JOBS=3\nPLAN_MEMLIMIT_MB=2048\nPLAN_NBCORE=2\nPLAN_HEADROOM_MB=16000\n",
        )
        .expect("parse plan");
        assert_eq!(plan_value(&parsed, "PLAN_JOBS").unwrap(), 3);
        assert_eq!(plan_value(&parsed, "PLAN_MEMLIMIT_MB").unwrap(), 2048);
    }

    #[test]
    fn rejects_non_numeric_plan_values() {
        let err = parse_plan_output("PLAN_JOBS=$(bad)\n").expect_err("must reject");
        assert!(err.to_string().contains("invalid PLAN_JOBS"));
    }

    #[test]
    fn rejects_duplicate_or_unknown_plan_fields() {
        let complete = "PLAN_JOBS=1\nPLAN_MEMLIMIT_MB=1024\nPLAN_NBCORE=1\nPLAN_HEADROOM_MB=0\n";
        assert!(parse_plan_output(&format!("{complete}PLAN_JOBS=2\n")).is_err());
        assert!(parse_plan_output(&format!("{complete}PLAN_SURPRISE=1\n")).is_err());
    }

    #[test]
    fn profile_caps_only_reduce_the_admitted_envelope() {
        let mut resources = PlannedResources::for_test(Path::new("/tmp"), 4096);
        resources.plan.nbcore_per_child = 8;
        resources
            .apply_per_child_caps(Some(2048), Some(2))
            .expect("apply stricter profile caps");
        assert_eq!(resources.plan.memlimit_mb_per_child, 2048);
        assert_eq!(resources.plan.nbcore_per_child, 2);

        resources
            .apply_per_child_caps(Some(8192), Some(16))
            .expect("larger caps must not expand the plan");
        assert_eq!(resources.plan.memlimit_mb_per_child, 2048);
        assert_eq!(resources.plan.nbcore_per_child, 2);
        assert!(resources.apply_per_child_caps(Some(0), None).is_err());
    }

    #[test]
    fn normalized_ids_reject_escapes_and_preserve_directories() {
        assert_eq!(
            normalized_relative_id(Path::new("/corpus/a/case.smt2"), Path::new("/corpus")).unwrap(),
            "a/case.smt2"
        );
        assert!(
            normalized_relative_id(Path::new("/other/case.smt2"), Path::new("/corpus")).is_err()
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn retained_store_authority_tracks_the_exact_sqlite_descriptor_lifecycle() {
        let temp = tempfile::tempdir().expect("tempdir");
        secure_test_directory(temp.path());
        let path = temp.path().join("results.sqlite");
        let mut authority = prepare_private_store_path(&path, "test store").expect("prepare store");
        let connection = rusqlite::Connection::open_with_flags(
            &path,
            rusqlite::OpenFlags::SQLITE_OPEN_READ_WRITE | rusqlite::OpenFlags::SQLITE_OPEN_NOFOLLOW,
        )
        .expect("open SQLite connection");

        authority
            .authenticate_sqlite_open()
            .expect("authenticate SQLite descriptor");
        authority
            .verify_connection_authority()
            .expect("live descriptor remains authoritative");
        drop(connection);

        let error = authority
            .verify_connection_authority()
            .expect_err("closed SQLite descriptor must fail lifecycle check");
        assert!(
            error.to_string().contains("checking authenticated SQLite"),
            "unexpected error: {error}"
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn sqlite_authentication_rejects_replace_open_restore_race() {
        let temp = tempfile::tempdir().expect("tempdir");
        secure_test_directory(temp.path());
        let path = temp.path().join("results.sqlite");
        let authentic_saved = temp.path().join("authentic.sqlite");
        let replacement_saved = temp.path().join("replacement.sqlite");
        let mut authority = prepare_private_store_path(&path, "test store").expect("prepare store");

        std::fs::rename(&path, &authentic_saved).expect("displace reservation");
        std::fs::File::create(&path).expect("plant replacement database");
        let connection = rusqlite::Connection::open_with_flags(
            &path,
            rusqlite::OpenFlags::SQLITE_OPEN_READ_WRITE | rusqlite::OpenFlags::SQLITE_OPEN_NOFOLLOW,
        )
        .expect("open replacement with SQLite");
        std::fs::rename(&path, &replacement_saved).expect("preserve replacement");
        std::fs::rename(&authentic_saved, &path).expect("restore visible reservation");

        let error = authority
            .authenticate_sqlite_open()
            .expect_err("SQLite replacement descriptor must not authenticate");
        assert!(
            error.to_string().contains("did not retain a descriptor"),
            "unexpected error: {error}"
        );
        assert!(replacement_saved.exists(), "replacement is never unlinked");
        drop(connection);
    }

    #[test]
    fn resource_plan_rejects_zero_requested_jobs() {
        assert!(PlannedResources::plan(
            &crate::runner::repo_root_public(),
            0,
            "zero-job regression"
        )
        .is_err());
    }

    #[test]
    fn build_sandbox_uses_only_the_explicit_test_lease_seam() {
        let marked = std::env::var_os("AY_CONTINUOUS_BUILD_SANDBOX").as_deref()
            == Some(std::ffi::OsStr::new("1"));
        let path = build_sandbox_test_lease_path();
        assert_eq!(path.is_some(), marked);
        if let Some(path) = path {
            assert!(path.is_absolute());
            assert_eq!(path.parent(), Some(std::env::temp_dir().as_path()));
            let name = path
                .file_name()
                .and_then(std::ffi::OsStr::to_str)
                .expect("test lease filename");
            assert!(name.starts_with("ay-bench-test-lease-"));
            assert!(!name.starts_with("ay-oom-guard-"));
        }
    }

    #[test]
    fn independent_active_campaign_cannot_reuse_process_lease() {
        let slot = std::sync::Mutex::new(std::sync::Weak::new());
        let lease = std::sync::Arc::new(GlobalHarnessLease {
            process: std::sync::Mutex::new(None),
        });
        *slot.lock().expect("slot") = std::sync::Arc::downgrade(&lease);

        let error = vacant_harness_lease_slot(&slot).expect_err("active lease must be exclusive");
        assert!(error.to_string().contains("already active"));
        drop(lease);
        assert!(vacant_harness_lease_slot(&slot).is_ok());
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn aggregate_lease_death_before_spawn_fails_closed() {
        let temp = tempfile::tempdir().expect("tempdir");
        let script = temp.path().join("short-lived-lease.py");
        std::fs::write(
            &script,
            "import time\nprint('AY_OOM_HARNESS_LEASE_READY_V1', flush=True)\ntime.sleep(0.2)\n",
        )
        .expect("fake lease script");
        let lease = std::sync::Arc::new(
            GlobalHarnessLease::acquire(&script, "short-lived test lease")
                .expect("acquire fake lease"),
        );
        std::thread::sleep(Duration::from_millis(400));

        let mut resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 4096);
        resources._aggregate_lease = Some(lease);
        let mut command = resources.external_command("/bin/sh");
        command.arg("-c").arg("exit 0");
        let error = resources
            .spawn_external_child(&mut command, "post-lease-death child")
            .expect_err("dead aggregate lease must prevent spawn");
        assert!(error
            .to_string()
            .contains("released the host admission lock"));
        assert_eq!(resources.watchdog_server_pid(), None);
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn aggregate_lease_death_during_run_kills_guarded_child() {
        let temp = tempfile::tempdir().expect("tempdir");
        let script = temp.path().join("persistent-lease.py");
        std::fs::write(
            &script,
            "import sys\nprint('AY_OOM_HARNESS_LEASE_READY_V1', flush=True)\nwhile sys.stdin.buffer.read(8192):\n    pass\n",
        )
        .expect("fake lease script");
        let lease = std::sync::Arc::new(
            GlobalHarnessLease::acquire(&script, "persistent test lease")
                .expect("acquire fake lease"),
        );
        let mut resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 4096);
        resources._aggregate_lease = Some(std::sync::Arc::clone(&lease));
        let mut command = resources.external_command("/bin/sh");
        command
            .arg("-c")
            .arg("sleep 60")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let (mut child, watchdog) = resources
            .spawn_external_child(&mut command, "lease-loss child")
            .expect("spawn guarded child");
        let lease_pid = {
            let process = lease.process.lock().expect("lease process lock");
            process.as_ref().expect("lease process").0.id()
        };
        nix::sys::signal::kill(
            nix::unistd::Pid::from_raw(i32::try_from(lease_pid).expect("lease pid")),
            nix::sys::signal::Signal::SIGKILL,
        )
        .expect("kill fake lease");

        let error = wait_for_guarded_child(
            &mut child,
            watchdog,
            Duration::from_secs(5),
            "lease-loss child",
        )
        .expect_err("lease loss must invalidate and kill active child");
        assert!(error
            .to_string()
            .contains("released the host admission lock"));
        assert!(child.try_wait().expect("child status").is_some());
    }

    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc")),
    ))]
    #[test]
    fn completion_observation_keeps_group_leader_unreaped_until_cleanup() {
        use std::os::unix::process::CommandExt as _;

        let mut command = Command::new("sh");
        command.arg("-c").arg("exit 7").process_group(0);
        let mut child = command.spawn().expect("spawn child");
        assert!(
            wait_for_child_exit_unreaped(&child, Duration::from_secs(2), "test child")
                .expect("observe child")
        );
        let status = kill_process_group_and_reap(&mut child, "test child").expect("cleanup child");
        assert_eq!(status.code(), Some(7));
    }

    #[test]
    fn effective_envelope_includes_timeout_and_exact_enforcement() {
        let plan = ResourcePlan {
            requested_jobs: 2,
            jobs: 2,
            memlimit_mb_per_child: 1024,
            nbcore_per_child: 1,
            headroom_mb: 512,
            planner: "test".to_string(),
        };
        let first =
            effective_execution_envelope(&plan, ENFORCEMENT_AY_MEMORY_V1, 1.0).expect("envelope");
        let different_timeout =
            effective_execution_envelope(&plan, ENFORCEMENT_AY_MEMORY_V1, 2.0).expect("envelope");
        let different_enforcement =
            effective_execution_envelope(&plan, ENFORCEMENT_RSS_WATCHDOG_V1, 1.0)
                .expect("envelope");
        assert_ne!(first, different_timeout);
        assert_ne!(first, different_enforcement);
        assert!(first.contains("timeout_ns=1000000000"));
        assert!(first.contains(ENFORCEMENT_AY_MEMORY_V1));
    }

    #[test]
    fn effective_envelope_rejects_legacy_enforcement() {
        let plan = ResourcePlan {
            requested_jobs: 1,
            jobs: 1,
            memlimit_mb_per_child: 1024,
            nbcore_per_child: 1,
            headroom_mb: 0,
            planner: "test".to_string(),
        };
        assert!(effective_execution_envelope(&plan, "rss watchdog", 1.0).is_err());
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn guarded_capture_arms_before_target_and_captures_bounded_output() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        let output = resources
            .capture_external_output(
                Path::new("/bin/sh"),
                ["-c", "printf 'ready-output\\n'"],
                Duration::from_secs(5),
                "resource handshake test",
            )
            .expect("guarded capture");
        assert!(output.status.success());
        assert_eq!(output.stdout, "ready-output\n");
        assert!(output.stderr.is_empty());
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn guarded_capture_reaps_descendants_before_bounded_reader_completion() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        let script = r#"import os,sys,time
pid=os.fork()
if pid == 0:
    print('descendant-ready', flush=True)
    time.sleep(60)
    os._exit(0)
time.sleep(0.1)
os._exit(0)
"#;
        let started = Instant::now();
        let output = resources
            .run_external_captured(
                "python3",
                ["-c", script],
                Duration::from_secs(5),
                "descendant stdout regression",
            )
            .expect("guarded descendant capture");
        assert!(started.elapsed() < Duration::from_secs(3));
        assert!(output.status.is_some_and(|status| status.success()));
        assert!(!output.timed_out && !output.memout);
        assert_eq!(output.stdout, b"descendant-ready\n");
        assert!(!output.output_truncated);
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn guarded_capture_marks_stdout_over_fixed_parent_limit() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        let output = resources
            .run_external_captured(
                "python3",
                ["-c", "import sys; sys.stdout.write('x' * 1100000)"],
                Duration::from_secs(5),
                "bounded stdout regression",
            )
            .expect("guarded oversized capture");
        assert!(output.status.is_some_and(|status| status.success()));
        assert_eq!(output.stdout.len(), EXTERNAL_CAPTURE_LIMIT);
        assert!(output.output_truncated);
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn guarded_transcript_writes_stdin_and_captures_both_streams() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        let script = concat!(
            "import sys\n",
            "data = sys.stdin.buffer.read()\n",
            "sys.stdout.buffer.write(b'out:' + data)\n",
            "sys.stderr.buffer.write(b'err:' + data)\n",
        );
        let output = resources
            .run_external_transcript(
                "python3",
                ["-c", script],
                b"(check-sat)\n",
                Duration::from_secs(5),
                "guarded transcript round trip",
            )
            .expect("guarded transcript");
        assert!(output.status.is_some_and(|status| status.success()));
        assert!(!output.timed_out && !output.memout);
        assert_eq!(output.stdout, b"out:(check-sat)\n");
        assert_eq!(output.stderr, b"err:(check-sat)\n");
        assert!(output.stdin_complete);
        assert!(!output.stdout_truncated);
        assert!(!output.stderr_truncated);
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn guarded_transcript_marks_each_truncated_stream() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        let script = concat!(
            "import sys\n",
            "sys.stdout.buffer.write(b'o' * 1100000)\n",
            "sys.stderr.buffer.write(b'e' * 1100000)\n",
        );
        let output = resources
            .run_external_transcript(
                "python3",
                ["-c", script],
                b"",
                Duration::from_secs(5),
                "guarded transcript truncation",
            )
            .expect("guarded transcript");
        assert!(output.status.is_some_and(|status| status.success()));
        assert_eq!(output.stdout.len(), GUARDED_TRANSCRIPT_STREAM_LIMIT);
        assert_eq!(output.stderr.len(), GUARDED_TRANSCRIPT_STREAM_LIMIT);
        assert!(output.stdin_complete);
        assert!(output.stdout_truncated);
        assert!(output.stderr_truncated);
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn guarded_transcript_timeout_unblocks_full_stdin_writer() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        let script = concat!(
            "import sys,time\n",
            "sys.stdin.close()\n",
            "print('stdout-ready', flush=True)\n",
            "print('stderr-ready', file=sys.stderr, flush=True)\n",
            "time.sleep(60)\n",
        );
        let stdin = vec![b'i'; GUARDED_TRANSCRIPT_INPUT_LIMIT];
        let output = resources
            .run_external_transcript(
                "python3",
                ["-c", script],
                &stdin,
                Duration::from_millis(200),
                "guarded blocked-stdin timeout",
            )
            .expect("timeout must clean up all transcript workers");
        assert!(output.timed_out);
        assert!(!output.memout);
        assert_eq!(output.stdout, b"stdout-ready\n");
        assert_eq!(output.stderr, b"stderr-ready\n");
        assert!(!output.stdin_complete);
        assert!(!output.stdout_truncated);
        assert!(!output.stderr_truncated);
    }

    #[test]
    fn guarded_transcript_rejects_oversized_stdin_before_spawn() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        let stdin = vec![0; GUARDED_TRANSCRIPT_INPUT_LIMIT + 1];
        let error = resources
            .run_external_transcript(
                "/definitely/missing/guarded-transcript-program",
                std::iter::empty::<&str>(),
                &stdin,
                Duration::from_secs(5),
                "oversized guarded transcript",
            )
            .expect_err("oversized stdin must fail before spawning");
        assert!(error.to_string().contains("guarded stdin"));
        assert!(error.to_string().contains("fixed"));
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn concurrent_children_share_one_campaign_watchdog_server() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        let mut first_command = resources.external_command("/bin/sh");
        first_command
            .args(["-c", "sleep 0.2"])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let (mut first, first_watchdog) = resources
            .spawn_external_child(&mut first_command, "first shared-server child")
            .expect("spawn first child");
        let server_pid = resources
            .watchdog_server_pid()
            .expect("campaign server started");

        let mut second_command = resources.external_command("/bin/sh");
        second_command
            .args(["-c", "sleep 0.2"])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let (mut second, second_watchdog) = resources
            .spawn_external_child(&mut second_command, "second shared-server child")
            .expect("spawn second child");
        assert_eq!(resources.watchdog_server_pid(), Some(server_pid));

        let first_outcome = wait_for_guarded_child(
            &mut first,
            first_watchdog,
            Duration::from_secs(5),
            "first shared-server child",
        )
        .expect("wait first child");
        let second_outcome = wait_for_guarded_child(
            &mut second,
            second_watchdog,
            Duration::from_secs(5),
            "second shared-server child",
        )
        .expect("wait second child");
        assert!(first_outcome.status.is_some_and(|status| status.success()));
        assert!(second_outcome.status.is_some_and(|status| status.success()));
        assert!(!first_outcome.memout && !second_outcome.memout);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn stopped_campaign_watchdog_fails_closed_and_kills_target() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        let mut command = resources.external_command("/bin/sh");
        command
            .args(["-c", "sleep 60"])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let (mut child, watchdog) = resources
            .spawn_external_child(&mut command, "stopped-watchdog child")
            .expect("spawn guarded child");
        let server_pid = resources.watchdog_server_pid().expect("watchdog pid");
        nix::sys::signal::kill(
            nix::unistd::Pid::from_raw(i32::try_from(server_pid).expect("server pid")),
            nix::sys::signal::Signal::SIGSTOP,
        )
        .expect("stop watchdog server");

        let started = Instant::now();
        let error = wait_for_guarded_child(
            &mut child,
            watchdog,
            Duration::from_secs(5),
            "stopped-watchdog child",
        )
        .expect_err("stopped watchdog must fail closed");
        assert!(started.elapsed() < Duration::from_secs(3), "{error}");
        assert!(error.to_string().contains("watchdog"), "{error}");
        assert!(child.try_wait().expect("child status").is_some());

        nix::sys::signal::kill(
            nix::unistd::Pid::from_raw(i32::try_from(server_pid).expect("server pid")),
            nix::sys::signal::Signal::SIGCONT,
        )
        .expect("resume watchdog server for cleanup");
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn missing_campaign_watchdog_heartbeat_kills_target() {
        let temp = tempfile::tempdir().expect("tempdir");
        let fake_server = temp.path().join("watch-server.py");
        std::fs::write(
            &fake_server,
            "import sys\nsys.stdout.write('AY_OOM_WATCHDOG_SERVER_READY_V1\\n')\nsys.stdout.flush()\nfor line in sys.stdin.buffer:\n    fields = line.decode('ascii').strip().split(' ')\n    if len(fields) == 5 and fields[0] == 'WATCH':\n        print(f'READY {fields[1]}', flush=True)\n",
        )
        .expect("write fake watch server");
        let mut resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        resources.watchdog_server = SharedWatchdogServer::new(fake_server);
        let mut command = resources.external_command("/bin/sh");
        command
            .args(["-c", "sleep 60"])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let (mut child, watchdog) = resources
            .spawn_external_child(&mut command, "heartbeat-loss child")
            .expect("spawn guarded child");

        let started = Instant::now();
        let error = wait_for_guarded_child(
            &mut child,
            watchdog,
            Duration::from_secs(5),
            "heartbeat-loss child",
        )
        .expect_err("heartbeat loss must fail closed");
        assert!(started.elapsed() < Duration::from_secs(3), "{error}");
        assert!(error.to_string().contains("watchdog"), "{error}");
        assert!(child.try_wait().expect("child status").is_some());
    }

    #[cfg(unix)]
    #[test]
    fn terminal_watchdog_error_disarms_pgid_before_drop() {
        use std::os::unix::process::CommandExt as _;
        use std::sync::atomic::Ordering;
        use wait_timeout::ChildExt as _;

        // This process group represents an unrelated group that has reused a
        // completed target's numeric PGID before the watchdog handle drops.
        let mut replacement_command = Command::new("/bin/sh");
        replacement_command
            .args(["-c", "exec sleep 60"])
            .process_group(0)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let mut replacement = replacement_command
            .spawn()
            .expect("spawn replacement group");
        let replacement_pgid = i32::try_from(replacement.id()).expect("replacement PID fits pid_t");

        // Construct the post-READY state directly and inject the terminal
        // ERROR delivered by the server reader. Future timestamps keep this
        // process-free test server healthy for the duration of the poll.
        let server = SharedWatchdogServer::new(PathBuf::from("unused-watchdog-test-script"));
        server.healthy.store(true, Ordering::Release);
        server.last_heartbeat_ns.store(u64::MAX, Ordering::Release);
        server
            .last_process_check_ns
            .store(u64::MAX, Ordering::Release);
        let (sender, receiver) = std::sync::mpsc::channel();
        sender
            .send(Err("injected terminal watchdog failure".to_string()))
            .expect("inject terminal error");
        let mut watchdog = RssWatchdog {
            server,
            aggregate_lease: None,
            watch_id: 41,
            target_pgid: Some(replacement_pgid),
            terminal_breach: None,
            receiver,
        };

        let poll_result = watchdog.poll();
        let disarmed_before_drop = watchdog.target_pgid.is_none();
        drop(watchdog);
        let replacement_status = replacement
            .wait_timeout(Duration::from_millis(250))
            .expect("observe replacement group");
        if replacement_status.is_none() {
            terminate_process_group(&mut replacement);
        }

        let error = poll_result.expect_err("terminal watchdog error must fail closed");
        assert!(error
            .to_string()
            .contains("injected terminal watchdog failure"));
        assert!(disarmed_before_drop, "terminal error retained a stale PGID");
        assert!(
            replacement_status.is_none(),
            "watchdog cleanup signalled the replacement process group"
        );
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn campaign_watchdog_preserves_zero_grace_memout_enforcement() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 16);
        let mut command = resources.external_command("python3");
        command
            .args([
                "-c",
                "import time; allocation=bytearray(64*1024*1024); time.sleep(60)",
            ])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let (mut child, watchdog) = resources
            .spawn_external_child(&mut command, "campaign memout child")
            .expect("spawn guarded memory hog");
        let outcome = wait_for_guarded_child(
            &mut child,
            watchdog,
            Duration::from_secs(10),
            "campaign memout child",
        )
        .expect("wait memory hog");
        assert!(outcome.memout);
        assert!(!outcome.timed_out);
    }

    #[cfg(unix)]
    #[test]
    fn guarded_capture_rejects_oversized_metadata_output() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        let error = resources
            .capture_external_output(
                Path::new("/bin/sh"),
                ["-c", "yes x | head -c 1100000"],
                Duration::from_secs(5),
                "resource capture limit test",
            )
            .expect_err("oversized output must fail closed");
        assert!(error.to_string().contains("capture limit"));
    }
}
