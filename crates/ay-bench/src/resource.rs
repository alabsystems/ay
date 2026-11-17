// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared resource admission for benchmark subprocesses.
//!
//! Native measurements restrict RAM headroom and job/CPU requests. The existing
//! campaign lease owns aggregate exclusion; a native observer enforces the RSS
//! backstop. Measurements do not confer a shared-machine grant.

use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

// Every target stdin pipe this module writes goes through
// `ChildPipeWriter`: a `unix_hardened` build runs with SIGPIPE at its default
// (terminate) disposition, so a write to a child that has died would kill the
// benchmark parent instead of returning the `EPIPE` the callers handle.
use ay_sys::child_pipe::ChildPipeWriter;

use crate::error::{BenchError, Result, WithContext as _};

mod deadline;
#[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
mod native;
#[cfg(all(test, unix))]
mod native_metadata_tests;
mod owned_child;
use deadline::terminate_after_deadline;

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

/// The textual verdict grammar shared by process assessment and strict
/// single-observation routes. This helper does not infer status from an exit.
pub(crate) fn solver_verdict_line(line: &str) -> Option<&'static str> {
    let line = line.trim();
    for (spelling, verdict) in [
        ("sat", "sat"),
        ("s satisfiable", "sat"),
        ("satisfiable", "sat"),
        ("unsat", "unsat"),
        ("s unsatisfiable", "unsat"),
        ("unsatisfiable", "unsat"),
        ("unknown", "unknown"),
        ("s unknown", "unknown"),
        ("timeout", "unknown"),
    ] {
        if line.eq_ignore_ascii_case(spelling) {
            return Some(verdict);
        }
    }
    None
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
        let verdict = solver_verdict_line(line);
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
    let mut bytes = Vec::new();
    bytes
        .try_reserve(usize::try_from(metadata.len()).unwrap_or(0))
        .map_err(|_| {
            BenchError::msg(format!(
                "cannot allocate {} bytes for {label} {}",
                metadata.len(),
                path.display()
            ))
        })?;
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

/// Persistable resource envelope restricted by native host/controller readings.
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
    /// Measurement implementation and actual enforcement component identity.
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

/// Actual native owner of the SAME legacy host/user campaign flock. This
/// excludes cooperating campaigns; it is not a Targo shared-machine claim.
#[derive(Debug)]
struct GlobalHarnessLease {
    #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
    native: native::CampaignLease,
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

// Tests use one private per-process inode and serialize real campaigns against
// it. Production always uses /tmp, never TMPDIR; this test-only path is not an
// admission bypass or a second production exclusion domain.
#[cfg(all(test, unix, not(any(target_os = "redox", target_os = "solaris"))))]
fn test_campaign_lease_path() -> PathBuf {
    std::env::temp_dir().join(format!("ay-bench-test-lease-{}.lock", std::process::id()))
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
    fn exclusive(label: &str) -> Result<std::sync::Arc<Self>> {
        let slot =
            PROCESS_HARNESS_LEASE.get_or_init(|| std::sync::Mutex::new(std::sync::Weak::new()));
        let mut weak = vacant_harness_lease_slot(slot)?;
        let lease = std::sync::Arc::new(Self::acquire(label)?);
        *weak = std::sync::Arc::downgrade(&lease);
        Ok(lease)
    }

    fn acquire(label: &str) -> Result<Self> {
        #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
        {
            #[cfg(test)]
            let path = test_campaign_lease_path();
            #[cfg(not(test))]
            let path = PathBuf::from(format!(
                "/tmp/ay-oom-guard-{}.lock",
                nix::unistd::getuid().as_raw()
            ));
            Ok(Self {
                native: native::CampaignLease::acquire(&path, label)?,
            })
        }
        #[cfg(not(all(unix, not(any(target_os = "redox", target_os = "solaris")))))]
        {
            let _ = label;
            Err(BenchError::msg(
                "native campaign exclusion requires supported POSIX flock",
            ))
        }
    }

    #[cfg(all(test, unix, not(any(target_os = "redox", target_os = "solaris"))))]
    fn at_test_path(path: &Path, label: &str) -> Result<Self> {
        Ok(Self {
            native: native::CampaignLease::acquire(path, label)?,
        })
    }

    fn path(&self) -> Result<&Path> {
        #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
        {
            Ok(self.native.path())
        }
        #[cfg(not(all(unix, not(any(target_os = "redox", target_os = "solaris")))))]
        {
            Err(BenchError::msg("native campaign exclusion unsupported"))
        }
    }

    fn ensure_alive(&self, label: &str) -> Result<()> {
        #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
        {
            self.native
                .ensure_alive()
                .map_err(|error| BenchError::msg(format!("{label}: {error}")))
        }
        #[cfg(not(all(unix, not(any(target_os = "redox", target_os = "solaris")))))]
        {
            let _ = label;
            Err(BenchError::msg("native campaign exclusion unsupported"))
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

/// Native restrictions, campaign exclusion, and one shared RSS observer.
#[derive(Debug, Clone)]
pub struct PlannedResources {
    /// Exact numeric resource plan admitted for this campaign.
    pub plan: ResourcePlan,
    guard_script: PathBuf,
    _aggregate_lease: Option<std::sync::Arc<GlobalHarnessLease>>,
    #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
    observer: std::sync::Arc<native::Observer>,
    #[cfg(test)]
    _test_campaign_lease: Option<std::sync::Arc<TestCampaignLease>>,
}

fn measured_native_plan(requested: usize, lease_path: &Path) -> Result<ResourcePlan> {
    #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
    {
        native::plan(requested, lease_path)
    }
    #[cfg(not(all(unix, not(any(target_os = "redox", target_os = "solaris")))))]
    {
        let _ = (requested, lease_path);
        Err(BenchError::msg(
            "native benchmark measurement unsupported on this target",
        ))
    }
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
                            let Some(retained) = chunk.get(..retain) else {
                                write_failed = true;
                                worker_breach.store(true, std::sync::atomic::Ordering::Release);
                                break;
                            };
                            if output.write_all(retained).is_err() {
                                write_failed = true;
                                worker_breach.store(true, std::sync::atomic::Ordering::Release);
                                break;
                            }
                            hasher.update(retained);
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
                            let Some(retained) = chunk.get(..retain) else {
                                failed = true;
                                break;
                            };
                            kept.extend_from_slice(retained);
                            if evidence_file.write_all(retained).is_err() {
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

/// Bounded terminal evidence, including a prefix when capture was incomplete.
pub(crate) use ay_sys::metadata_capture::{BoundedPipeCapture, PipeCaptureEvidence};

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
                        let Some(retained) = chunk.get(..read.min(remaining)) else {
                            read_failed = true;
                            break;
                        };
                        kept.extend_from_slice(retained);
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
    fn start<W>(mut writer: ChildPipeWriter<W>, bytes: Vec<u8>) -> Self
    where
        W: std::io::Write + Send + 'static,
    {
        use std::io::Write as _;
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
            // caller from mistaking the partial exchange for a full one. The
            // writer is a `ChildPipeWriter`, so that close arrives here as
            // `EPIPE`, never as a SIGPIPE that kills the harness.
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
    let mut command = Command::new(program);
    command.args(args);
    if let Some(current_dir) = current_dir {
        command.current_dir(current_dir);
    }
    let output = ay_sys::metadata_capture::capture(
        command,
        ay_sys::metadata_capture::CaptureLimits {
            timeout,
            output_bytes: METADATA_CAPTURE_LIMIT,
            resident_bytes: None,
        },
        label,
    )?;
    Ok(CapturedOutput {
        status: output.status,
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    })
}

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

impl PlannedResources {
    /// Hold the existing campaign lease and restrict jobs/RAM/CPU using native
    /// observations. The lease and watchdog remain the enforcement owners.
    pub fn plan(repo_root: &Path, requested_jobs: usize, label: &str) -> Result<Self> {
        if requested_jobs == 0 {
            return Err(BenchError::InvalidArgs {
                reason: "requested benchmark jobs must be positive".to_string(),
            });
        }
        // Child launching still uses this component until its native worker
        // lands. Campaign lease ownership itself is now entirely native.
        let guard_script = repo_root.join("scripts").join("_oom_guard.py");
        if !guard_script.is_file() {
            return Err(BenchError::msg(format!(
                "required resource enforcement component is missing: {}",
                guard_script.display()
            )));
        }
        #[cfg(test)]
        let test_campaign_lease = TestCampaignLease::acquire();
        let aggregate_lease = GlobalHarnessLease::exclusive(label)?;
        let plan = measured_native_plan(requested_jobs, aggregate_lease.path()?)?;
        aggregate_lease.ensure_alive(label)?;

        #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
        let observer = std::sync::Arc::new(native::Observer::new(plan.jobs)?);

        Ok(Self {
            plan,
            #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
            observer,
            guard_script,
            _aggregate_lease: Some(aggregate_lease),
            #[cfg(test)]
            _test_campaign_lease: Some(test_campaign_lease),
        })
    }

    /// Reduce the planner-admitted per-child envelope for a campaign profile.
    ///
    /// The existing campaign lease retains aggregate exclusion; profile caps
    /// may only tighten the native measured plan. The reduced values are
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

    /// Spawn an external child suspended, arm the native RSS observer, then
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
        let mut child = self.spawn_owned_child(&mut command, label)?;
        let stdout_capture = child
            .take_stdout()
            .map(BoundedPipeCapture::start)
            .transpose()?;
        let stderr_capture = child
            .take_stderr()
            .map(BoundedPipeCapture::start)
            .transpose()?;
        let outcome = child.wait(timeout)?;
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
        let mut child = self.spawn_owned_child(&mut command, label)?;
        let Some(stdout) = child.take_stdout() else {
            child.cancel()?;
            return Err(BenchError::msg(format!(
                "{label}: guarded stdout pipe is missing"
            )));
        };
        let capture = BoundedBytesCapture::start(stdout);
        let outcome = child.wait(timeout);
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
        self.run_external_transcript_impl(program, args, stdin, timeout, label, &[], None)
    }

    /// Run a bounded transcript whose child also has a kernel-enforced
    /// per-file output ceiling. Proof producers can otherwise fill the disk
    /// while their stdout, RSS, and elapsed time remain within limits.
    pub fn run_external_transcript_with_file_limit<I, S>(
        &self,
        program: impl AsRef<std::ffi::OsStr>,
        args: I,
        stdin: &[u8],
        timeout: Duration,
        label: &str,
        max_file_bytes: u64,
    ) -> Result<GuardedTranscriptOutput>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<std::ffi::OsStr>,
    {
        if max_file_bytes == 0 {
            return Err(BenchError::InvalidArgs {
                reason: "guarded transcript file limit must be positive".to_string(),
            });
        }
        self.run_external_transcript_impl(
            program,
            args,
            stdin,
            timeout,
            label,
            &[],
            Some(max_file_bytes),
        )
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
        self.run_external_transcript_impl(
            program,
            args,
            stdin,
            timeout,
            label,
            LOADER_ENVIRONMENT,
            None,
        )
    }

    /// Combine authenticated loader isolation with a hard file-output bound.
    pub fn run_external_transcript_scrubbed_with_file_limit<I, S>(
        &self,
        program: impl AsRef<std::ffi::OsStr>,
        args: I,
        stdin: &[u8],
        timeout: Duration,
        label: &str,
        max_file_bytes: u64,
    ) -> Result<GuardedTranscriptOutput>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<std::ffi::OsStr>,
    {
        if max_file_bytes == 0 {
            return Err(BenchError::InvalidArgs {
                reason: "guarded transcript file limit must be positive".to_string(),
            });
        }
        self.run_external_transcript_impl(
            program,
            args,
            stdin,
            timeout,
            label,
            LOADER_ENVIRONMENT,
            Some(max_file_bytes),
        )
    }

    fn run_external_transcript_impl<I, S>(
        &self,
        program: impl AsRef<std::ffi::OsStr>,
        args: I,
        stdin: &[u8],
        timeout: Duration,
        label: &str,
        removed_environment: &[&str],
        max_file_bytes: Option<u64>,
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
        let mut command = match max_file_bytes {
            Some(bytes) => self.external_command_with_file_limit(program, bytes),
            None => self.external_command(program),
        };
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
        let mut child = self.spawn_owned_child(&mut command, label)?;
        let (child_stdin, Some(stdout), Some(stderr)) =
            (child.take_stdin(), child.take_stdout(), child.take_stderr())
        else {
            child.cancel()?;
            return Err(BenchError::msg(format!(
                "{label}: guarded transcript output pipe is missing"
            )));
        };
        // Named explicitly so the SIGPIPE-safe writer is visible at the
        // spawn site: `OwnedChild::take_stdin` wraps
        // `ChildPipeWriter::take_from`, which the child-pipe gate cannot
        // see through from this function.
        let child_stdin: ChildPipeWriter<ChildStdin> = match child_stdin {
            Ok(writer) => writer,
            Err(error) => {
                child.cancel()?;
                return Err(BenchError::msg(format!(
                    "{label}: guarded transcript stdin is missing or cannot be protected from SIGPIPE: {error}"
                )));
            }
        };
        let stdin_writer = BoundedStdinWriter::start(child_stdin, stdin.to_vec());
        let stdout_capture = BoundedBytesCapture::start(stdout);
        let stderr_capture = BoundedBytesCapture::start(stderr);
        let outcome = child.wait(timeout);
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

    pub(crate) fn spawn_owned_child(
        &self,
        command: &mut Command,
        label: &str,
    ) -> Result<owned_child::LocalOwnedChild> {
        let label = label.to_owned();
        let (child, watchdog) = self.spawn_external_child(command, &label)?;
        Ok(owned_child::LocalOwnedChild::new(child, watchdog, label))
    }

    #[cfg(unix)]
    fn spawn_external_child(
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

        // Register the exact unreaped Child with the campaign's native census
        // while its launch barrier is still stopped. Only this Child owner
        // resumes or cleans up the isolated group.
        let mut watchdog = match self.watch_stopped_child(&child) {
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
            #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
            observer: std::sync::Arc::new(native::Observer::new(1).expect("test observer")),
            _test_campaign_lease: None,
        }
    }

    fn watch_stopped_child(&self, child: &Child) -> Result<RssWatchdog> {
        #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
        {
            self.observer
                .register(child, self.plan.memlimit_mb_per_child)
                .map(|watch| RssWatchdog::new(std::sync::Arc::clone(&self.observer), watch))
        }
        #[cfg(not(all(unix, not(any(target_os = "redox", target_os = "solaris")))))]
        {
            let _ = child;
            Err(BenchError::msg(
                "native campaign watchdog unsupported on this target",
            ))
        }
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
/// group and its native observer registration, so callers cannot accidentally
/// leak either handle.
#[cfg(test)]
fn wait_for_guarded_child(
    child: &mut Child,
    watchdog: RssWatchdog,
    timeout: Duration,
    label: &str,
) -> Result<GuardedChildOutcome> {
    wait_for_guarded_child_with_limits(child, watchdog, timeout, label, None, None)
}

use ay_sys::owned_child::UnreapedChildState;

fn observe_child_unreaped(
    child: &Child,
    include_stopped: bool,
    label: &str,
) -> Result<UnreapedChildState> {
    let events = if include_stopped {
        ay_sys::owned_child::ChildEvents::ExitOrStop
    } else {
        ay_sys::owned_child::ChildEvents::Exit
    };
    ay_sys::owned_child::observe_child_unreaped(child, events, label).map_err(Into::into)
}

fn wait_for_guarded_child_with_limits(
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
        let cleanup = terminate_guarded_child(child, watchdog, label).err();
        return Err(BenchError::msg(match cleanup {
            Some(error) => format!("{label}: {reason}; watchdog cleanup failed: {error}"),
            None => format!("{label}: {reason}"),
        }));
    }
    let deadline = match deadline {
        Some(deadline) => deadline,
        None => {
            let cleanup = terminate_guarded_child(child, watchdog, label).err();
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
            let cleanup = terminate_guarded_child(child, watchdog, label).err();
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
                    let cleanup = terminate_guarded_child(child, watchdog, label).err();
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
                    let cleanup = terminate_guarded_child(child, watchdog, label).err();
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
                    let cleanup = terminate_guarded_child(child, watchdog, label).err();
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
        match watchdog.observe_owned_child(child, label) {
            Ok(UnreapedChildState::Exited) => {
                let trigger_ns = match monotonic_time_ns() {
                    Ok(trigger_ns) => trigger_ns,
                    Err(error) => {
                        let cleanup = terminate_guarded_child(child, watchdog, label).err();
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
                let cleanup = GroupCleanup::begin(child)?;
                let watchdog_result = watchdog.finish_after_target_cleanup();
                let status_result = cleanup.reap(label).map_err(BenchError::from);
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
                let watchdog_error = terminate_guarded_child(child, watchdog, label).err();
                return Err(BenchError::msg(match watchdog_error {
                    Some(error) => format!(
                        "{label}: guarded child stopped unexpectedly; watchdog cleanup failed: {error}"
                    ),
                    None => format!("{label}: guarded child stopped unexpectedly"),
                }));
            }
            Err(BenchError::Io(error)) if error.kind() == std::io::ErrorKind::WouldBlock => {
                // The original child can be between live identity and an
                // observable exit. Pending grants no signal/group authority.
                // Retain both owners, then recheck all existing stop/artifact
                // controls under the SAME absolute deadline and poll cadence.
                if Instant::now() >= deadline {
                    return terminate_after_deadline(child, watchdog, label);
                }
                std::thread::sleep(Duration::from_millis(20));
                continue;
            }
            Err(error) => {
                // An ownership observation failure (especially ECHILD) must
                // never turn into numeric PID/group signal authority.
                return Err(BenchError::msg(format!(
                    "{label}: child ownership unavailable; cleanup refused: {error}"
                )));
            }
        }

        match watchdog.poll() {
            Ok(None) => {}
            Ok(Some(observed)) if observed.breached => {
                let cleanup = GroupCleanup::begin(child)?;
                let final_outcome = watchdog.finish_after_target_cleanup();
                let status = cleanup.reap(label)?;
                let final_outcome = final_outcome?;
                if !final_outcome.breached {
                    return Err(BenchError::msg(
                        "RSS watchdog lost a previously observed breach",
                    ));
                }
                return Ok(GuardedChildOutcome {
                    status: Some(status),
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
            return terminate_after_deadline(child, watchdog, label);
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct WatchdogOutcome {
    breached: bool,
    breach_time_ns: Option<u64>,
}

mod rss_watchdog;
pub(crate) use rss_watchdog::RssWatchdog;

use ay_sys::owned_child::GroupCleanup;

fn kill_process_group_and_reap(child: &mut Child, label: &str) -> Result<ExitStatus> {
    ay_sys::owned_child::kill_process_group_and_reap(child, label).map_err(Into::into)
}

fn terminate_guarded_child(child: &mut Child, watchdog: RssWatchdog, label: &str) -> Result<()> {
    watchdog.observe_owned_child(child, label)?;
    let cleanup = GroupCleanup::begin(child)?;
    let watchdog_result = watchdog.finish_after_target_cleanup().map(|_| ());
    let child_result = cleanup.reap(label).map(|_| ()).map_err(BenchError::from);
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
pub(crate) use ay_sys::owned_child::terminate_process_group;

#[cfg(test)]
mod child_pipe_tests;

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

    #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
    #[test]
    fn native_campaigns_take_the_aggregate_lease_only_on_the_private_test_seam() {
        let _serialized = TestCampaignLease::acquire();
        let lease = GlobalHarnessLease::acquire("private native lease").unwrap();
        assert_eq!(lease.path().unwrap(), test_campaign_lease_path());
        let record = std::fs::read_to_string(lease.path().unwrap()).unwrap();
        assert!(record.starts_with(&format!("pid={} ", std::process::id())));
        assert!(record.contains(" start=- "));
        assert!(record.contains(" native_birth="));
        lease.ensure_alive("native original owner").unwrap();
        assert!(GlobalHarnessLease::acquire("independent native contender").is_err());
        drop(lease);
        GlobalHarnessLease::acquire("after original native drop").unwrap();
    }

    #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
    #[test]
    fn independent_active_campaign_cannot_reuse_process_lease() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("native-lease");
        let slot = std::sync::Mutex::new(std::sync::Weak::new());
        let lease =
            std::sync::Arc::new(GlobalHarnessLease::at_test_path(&path, "original").unwrap());
        *slot.lock().unwrap() = std::sync::Arc::downgrade(&lease);
        assert!(vacant_harness_lease_slot(&slot).is_err());
        let clone = std::sync::Arc::clone(&lease);
        drop(lease);
        assert!(vacant_harness_lease_slot(&slot).is_err());
        assert!(GlobalHarnessLease::at_test_path(&path, "still held by clone").is_err());
        drop(clone);
        assert!(vacant_harness_lease_slot(&slot).is_ok());
        GlobalHarnessLease::at_test_path(&path, "after last clone").unwrap();
    }

    #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
    #[test]
    fn native_aggregate_lease_invalidation_before_spawn_stays_refused_after_path_restore() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("lease");
        let saved = directory.path().join("held-inode");
        let marker = directory.path().join("target-started");
        let lease =
            std::sync::Arc::new(GlobalHarnessLease::at_test_path(&path, "original").unwrap());
        let mut resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 4096);
        resources._aggregate_lease = Some(std::sync::Arc::clone(&lease));
        std::fs::rename(&path, &saved).unwrap();
        let mut command = resources.external_command("/bin/sh");
        command.args([
            std::ffi::OsStr::new("-c"),
            std::ffi::OsStr::new("printf started > \"$1\""),
            std::ffi::OsStr::new("target"),
            marker.as_os_str(),
        ]);
        assert!(resources
            .spawn_external_child(&mut command, "invalid native lease")
            .is_err());
        assert!(!marker.exists());
        std::fs::rename(&saved, &path).unwrap();
        assert!(lease.ensure_alive("restored path").is_err());
        assert!(resources
            .spawn_external_child(&mut command, "restored but refused lease")
            .is_err());
        assert!(!marker.exists());
        assert_eq!(resources.observer.registered_children(), 0);
    }

    #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
    #[test]
    fn native_aggregate_lease_invalidation_during_run_reaps_the_original_child() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("lease");
        let saved = directory.path().join("held-inode");
        let lease =
            std::sync::Arc::new(GlobalHarnessLease::at_test_path(&path, "original").unwrap());
        let mut resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 4096);
        resources._aggregate_lease = Some(std::sync::Arc::clone(&lease));
        let mut command = resources.external_command("/bin/sh");
        command
            .args(["-c", "sleep 60"])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let (mut child, watchdog) = resources
            .spawn_external_child(&mut command, "native lease target")
            .unwrap();
        std::fs::rename(&path, &saved).unwrap();
        assert!(wait_for_guarded_child(
            &mut child,
            watchdog,
            Duration::from_secs(5),
            "native lease target"
        )
        .is_err());
        assert!(child.try_wait().unwrap().is_some());
        std::fs::rename(&saved, &path).unwrap();
        assert!(lease.ensure_alive("after cleanup").is_err());
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
        assert!(ay_sys::owned_child::wait_for_child_exit_unreaped(
            &child,
            Duration::from_secs(2),
            "test child"
        )
        .expect("observe child"));
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
        assert_eq!(output.stderr, "");
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
    fn guarded_transcript_file_limit_bounds_proof_artifacts() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        let temporary = tempfile::tempdir().expect("artifact directory");
        let path = temporary.path().join("proof");
        let output = resources
            .run_external_transcript_with_file_limit(
                "python3",
                [
                    "-c",
                    "import sys; open(sys.argv[1], 'wb').write(b'x' * 16384)",
                    path.to_str().expect("UTF-8 path"),
                ],
                b"",
                Duration::from_secs(5),
                "proof size refusal",
                4096,
            )
            .expect("guarded producer");
        assert!(!output.status.is_some_and(|status| status.success()));
        assert!(std::fs::metadata(&path).expect("partial proof").len() <= 4096);
        let accepted = temporary.path().join("small-proof");
        let output = resources
            .run_external_transcript_with_file_limit(
                "python3",
                [
                    "-c",
                    "import sys; open(sys.argv[1], 'wb').write(b'x' * 32)",
                    accepted.to_str().expect("UTF-8 path"),
                ],
                b"",
                Duration::from_secs(5),
                "bounded proof",
                4096,
            )
            .expect("guarded producer");
        assert!(output.status.is_some_and(|status| status.success()));
        assert_eq!(std::fs::metadata(accepted).expect("proof").len(), 32);
    }

    #[test]
    fn guarded_transcript_refuses_zero_file_limit_before_spawn() {
        let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        let error = resources
            .run_external_transcript_with_file_limit(
                "/no/such/producer",
                std::iter::empty::<&str>(),
                b"",
                Duration::from_secs(5),
                "invalid file limit",
                0,
            )
            .expect_err("zero file limit must fail before spawn");
        assert!(error.to_string().contains("file limit must be positive"));
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
    fn concurrent_children_share_one_campaign_native_observer() {
        let mut resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
        resources.plan.jobs = 2;
        resources.observer = std::sync::Arc::new(native::Observer::new(2).unwrap());
        let mut first_command = resources.external_command("/bin/sh");
        first_command
            .args(["-c", "sleep 0.2"])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let (mut first, first_watchdog) = resources
            .spawn_external_child(&mut first_command, "first shared-server child")
            .expect("spawn first child");

        let mut second_command = resources.external_command("/bin/sh");
        second_command
            .args(["-c", "sleep 0.2"])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let (mut second, second_watchdog) = resources
            .spawn_external_child(&mut second_command, "second shared-server child")
            .expect("spawn second child");
        assert_eq!(resources.observer.registered_children(), 2);

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
        assert_eq!(resources.observer.registered_children(), 0);
    }

    #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
    #[test]
    fn campaign_watchdog_preserves_zero_grace_memout_enforcement() {
        for pending in [0, 3] {
            let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 16);
            let mut command = resources.external_command(std::env::current_exe().unwrap());
            command
                .args([
                    "--exact",
                    "resource::native::tests::native_rss_allocation_fixture",
                ])
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::null());
            let (mut child, watchdog) = resources
                .spawn_external_child(&mut command, "campaign memout child")
                .expect("spawn guarded memory hog");
            // Pending observations provide no identity/signal authority. The
            // original wait owner must retain the real Child/watchdog and still
            // return the actual zero-grace memory cause after native reaping.
            watchdog.pending_identity_observations.set(pending);
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
