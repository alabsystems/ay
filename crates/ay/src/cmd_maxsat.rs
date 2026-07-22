// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MaxSAT Evaluation command surface: solving and benchmarking.

use std::collections::{BTreeMap, VecDeque};
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use anyhow::{bail, Context, Result};
use ay_maxsat::{MaxSatResult, MaxSatSolver};
use clap::Subcommand;
use serde::Serialize;

const EMBEDDED_OOM_GUARD: &str = include_str!("../../../scripts/_oom_guard.py");
const MAXSAT_WATCHDOG_SERVER_READY: &[u8] = b"AY_OOM_WATCHDOG_SERVER_READY_V1\n";
const MAXSAT_WATCHDOG_SERVER_MAX_LINE: u64 = 4096;
const MAXSAT_WATCHDOG_SERVER_HEARTBEAT_TIMEOUT: Duration = Duration::from_secs(1);
const MAXSAT_WATCHDOG_SERVER_STATE_CHECK_INTERVAL: Duration = Duration::from_millis(100);
const MAXSAT_RESOURCE_ENVELOPE_SCHEMA_V2: &str = "ay.maxsat-resource-envelope/v2";
const MAXSAT_RESOURCE_PLANNER_PROTOCOL_V1: &str = "ay-oom-guard-plan/v1";
const MAXSAT_CHILD_ENFORCEMENT_V1: &str = "ay-resource-v1:rss-watchdog-zero-grace";
const MAXSAT_SOLVER_ENVIRONMENT_V1: &str = "ay-maxsat-solver-env/v1:MEMLIMIT+NBCORE";
const MAXSAT_AGGREGATE_ENFORCEMENT_V1: &str = "ay-host-exclusive-flock-v1";
const MAXSAT_LEASE_PROTOCOL_V1: &str = "ay-oom-guard-lease-sidecar/v1";
const MAXSAT_LEASE_READINESS_V1: &str = "AY_OOM_HARNESS_LEASE_READY_V1";
const MAXSAT_LEASE_LOCATION_V1: &str = "ay-host-user-lock-path/v1:/tmp/ay-oom-guard-<uid>.lock";
const MAXSAT_LEASE_READY_MARKER: &[u8] = b"AY_OOM_HARNESS_LEASE_READY_V1\n";

#[derive(Debug, Clone)]
enum OomGuardSource {
    Checkout(PathBuf),
    Embedded,
}

impl OomGuardSource {
    fn provenance(&self) -> String {
        match self {
            Self::Checkout(path) => path.display().to_string(),
            Self::Embedded => "embedded:scripts/_oom_guard.py".to_string(),
        }
    }

    fn command(&self) -> Command {
        let mut command = Command::new("python3");
        match self {
            Self::Checkout(path) => {
                command.arg(path);
            }
            Self::Embedded => {
                command.arg("-c").arg(EMBEDDED_OOM_GUARD);
            }
        }
        command
    }
}

#[derive(Debug, Clone, Serialize)]
struct MaxSatResourcePlan {
    schema: &'static str,
    requested_jobs: usize,
    jobs: usize,
    memlimit_mb_per_child: usize,
    nbcore_per_child: usize,
    headroom_mb: usize,
    planner: String,
    planner_protocol: &'static str,
    enforcement: &'static str,
    solver_environment: &'static str,
    aggregate_enforcement: &'static str,
    lease_protocol: &'static str,
    lease_readiness: &'static str,
    lease_location: &'static str,
}

#[derive(Debug)]
struct MaxSatResources {
    plan: MaxSatResourcePlan,
    guard: OomGuardSource,
    watchdog_server: Arc<MaxSatWatchdogServer>,
    // Declared after the server so Rust's field drop order keeps aggregate
    // admission alive through watch-server teardown.
    campaign_lease: Arc<MaxSatCampaignLease>,
}

/// Host-wide admission lease retained from before planning until every
/// campaign child and report has finished. The Python sidecar owns the flock;
/// keeping its stdin open owns the sidecar lifetime.
#[derive(Debug)]
struct MaxSatCampaignLease {
    label: String,
    process: Mutex<Option<(Child, ChildStdin)>>,
}

impl MaxSatCampaignLease {
    fn acquire(guard: &OomGuardSource, label: &str) -> Result<Self> {
        let command = guard.command();
        Self::acquire_command(command, label, Stdio::inherit(), None)
    }

    #[cfg(unix)]
    fn acquire_command(
        mut command: Command,
        label: &str,
        stderr: Stdio,
        test_lock_path: Option<&Path>,
    ) -> Result<Self> {
        use std::io::Read as _;
        use std::os::unix::process::CommandExt as _;

        command
            .arg("lease")
            .arg("--label")
            .arg(label)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(stderr)
            .process_group(0);
        if let Some(test_lock_path) = test_lock_path {
            command.arg("--test-lock-path").arg(test_lock_path);
        }
        let mut child = command
            .spawn()
            .with_context(|| format!("failed to acquire host-wide MaxSAT lease for {label}"))?;
        let stdin = match child.stdin.take() {
            Some(stdin) => stdin,
            None => {
                terminate_maxsat_process_group(&mut child);
                bail!("{label}: MaxSAT campaign lease stdin is missing");
            }
        };
        let mut ready_pipe = match child.stdout.take() {
            Some(stdout) => stdout,
            None => {
                drop(stdin);
                terminate_maxsat_process_group(&mut child);
                bail!("{label}: MaxSAT campaign lease readiness pipe is missing");
            }
        };
        let (ready_sender, ready_receiver) = mpsc::channel();
        let ready_reader = std::thread::spawn(move || {
            let mut marker = vec![0_u8; MAXSAT_LEASE_READY_MARKER.len()];
            let result = ready_pipe
                .read_exact(&mut marker)
                .map(|()| marker == MAXSAT_LEASE_READY_MARKER)
                .map_err(|error| error.to_string());
            let _ = ready_sender.send(result);
        });

        let deadline = Instant::now() + Duration::from_secs(10);
        loop {
            match ready_receiver.try_recv() {
                Ok(Ok(true)) => break,
                Ok(Ok(false)) => {
                    drop(stdin);
                    terminate_maxsat_process_group(&mut child);
                    let _ = ready_reader.join();
                    bail!("{label}: MaxSAT campaign lease emitted an invalid readiness marker");
                }
                Ok(Err(error)) => {
                    drop(stdin);
                    terminate_maxsat_process_group(&mut child);
                    let _ = ready_reader.join();
                    bail!("{label}: reading MaxSAT campaign lease readiness failed: {error}");
                }
                Err(mpsc::TryRecvError::Disconnected) => {
                    drop(stdin);
                    terminate_maxsat_process_group(&mut child);
                    let _ = ready_reader.join();
                    bail!("{label}: MaxSAT campaign lease readiness channel disconnected");
                }
                Err(mpsc::TryRecvError::Empty) => {}
            }
            match child.try_wait() {
                Ok(Some(status)) => {
                    drop(stdin);
                    let _ = ready_reader.join();
                    bail!("{label}: MaxSAT campaign lease exited before arming ({status})");
                }
                Ok(None) => {}
                Err(error) => {
                    drop(stdin);
                    terminate_maxsat_process_group(&mut child);
                    let _ = ready_reader.join();
                    bail!("{label}: checking MaxSAT campaign lease failed: {error}");
                }
            }
            if Instant::now() >= deadline {
                drop(stdin);
                terminate_maxsat_process_group(&mut child);
                let _ = ready_reader.join();
                bail!("{label}: MaxSAT campaign lease did not arm within 10 seconds");
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        let _ = ready_reader.join();
        if let Some(status) = child
            .try_wait()
            .with_context(|| format!("{label}: checking armed MaxSAT campaign lease"))?
        {
            drop(stdin);
            bail!("{label}: MaxSAT campaign lease exited immediately after arming ({status})");
        }
        Ok(Self {
            label: label.to_string(),
            process: Mutex::new(Some((child, stdin))),
        })
    }

    #[cfg(not(unix))]
    fn acquire_command(
        _command: Command,
        label: &str,
        _stderr: Stdio,
        _test_lock_path: Option<&Path>,
    ) -> Result<Self> {
        bail!(
            "{label}: host-wide MaxSAT campaign admission requires POSIX process groups and flock"
        )
    }

    fn ensure_alive(&self) -> Result<()> {
        let mut process = self
            .process
            .lock()
            .map_err(|_| anyhow::anyhow!("{}: MaxSAT campaign lease mutex poisoned", self.label))?;
        let Some((child, _stdin)) = process.as_mut() else {
            bail!("{}: MaxSAT campaign lease is not active", self.label);
        };
        match child.try_wait() {
            Ok(None) => Ok(()),
            Ok(Some(status)) => bail!(
                "{}: MaxSAT campaign lease exited early ({status}); refusing uncoordinated execution",
                self.label
            ),
            Err(error) => bail!(
                "{}: checking MaxSAT campaign lease failed: {error}",
                self.label
            ),
        }
    }

    #[cfg(test)]
    fn kill_process_for_test(&self) {
        if let Ok(mut process) = self.process.lock() {
            if let Some((child, _stdin)) = process.as_mut() {
                terminate_maxsat_process_group(child);
            }
        }
    }
}

impl Drop for MaxSatCampaignLease {
    fn drop(&mut self) {
        let process = match self.process.get_mut() {
            Ok(process) => process.take(),
            Err(poisoned) => poisoned.into_inner().take(),
        };
        let Some((mut child, stdin)) = process else {
            return;
        };
        drop(stdin);
        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            match child.try_wait() {
                Ok(Some(_)) => return,
                Ok(None) if Instant::now() < deadline => {
                    std::thread::sleep(Duration::from_millis(5));
                }
                Ok(None) | Err(_) => {
                    terminate_maxsat_process_group(&mut child);
                    return;
                }
            }
        }
    }
}

impl MaxSatResources {
    fn plan(requested_jobs: usize) -> Result<Self> {
        let requested_jobs = requested_jobs.max(1);
        let guard = locate_oom_guard().map_or(OomGuardSource::Embedded, OomGuardSource::Checkout);
        let campaign_lease = Arc::new(MaxSatCampaignLease::acquire(&guard, "ay maxsat bench")?);
        campaign_lease.ensure_alive()?;
        let output = guard
            .command()
            .arg("plan")
            .arg("--jobs")
            .arg(requested_jobs.to_string())
            .arg("--label")
            .arg("ay maxsat bench")
            .arg("--warn-concurrent-build")
            .output()
            .context("failed to run scripts/_oom_guard.py resource planner")?;
        if !output.stderr.is_empty() {
            eprint!("{}", String::from_utf8_lossy(&output.stderr));
        }
        if !output.status.success() {
            bail!(
                "resource planner {} exited with {}",
                guard.provenance(),
                output.status
            );
        }
        campaign_lease
            .ensure_alive()
            .context("host-wide MaxSAT lease exited while resource planning")?;
        let mut values = BTreeMap::new();
        for line in String::from_utf8_lossy(&output.stdout).lines() {
            let Some((key, raw)) = line.trim().split_once('=') else {
                continue;
            };
            if key.starts_with("PLAN_") {
                values.insert(
                    key.to_string(),
                    raw.parse::<usize>()
                        .with_context(|| format!("invalid resource plan value {key}={raw:?}"))?,
                );
            }
        }
        let value = |key: &str| -> Result<usize> {
            values
                .get(key)
                .copied()
                .with_context(|| format!("resource planner omitted {key}"))
        };
        let jobs = value("PLAN_JOBS")?;
        let memlimit_mb_per_child = value("PLAN_MEMLIMIT_MB")?;
        let nbcore_per_child = value("PLAN_NBCORE")?;
        let headroom_mb = value("PLAN_HEADROOM_MB")?;
        if jobs == 0 || jobs > requested_jobs || memlimit_mb_per_child == 0 || nbcore_per_child == 0
        {
            bail!(
                "invalid resource plan: requested_jobs={requested_jobs} jobs={jobs} memory={memlimit_mb_per_child}MiB NBCORE={nbcore_per_child}"
            );
        }
        Ok(Self {
            plan: MaxSatResourcePlan {
                schema: MAXSAT_RESOURCE_ENVELOPE_SCHEMA_V2,
                requested_jobs,
                jobs,
                memlimit_mb_per_child,
                nbcore_per_child,
                headroom_mb,
                planner: guard.provenance(),
                planner_protocol: MAXSAT_RESOURCE_PLANNER_PROTOCOL_V1,
                enforcement: MAXSAT_CHILD_ENFORCEMENT_V1,
                solver_environment: MAXSAT_SOLVER_ENVIRONMENT_V1,
                aggregate_enforcement: MAXSAT_AGGREGATE_ENFORCEMENT_V1,
                lease_protocol: MAXSAT_LEASE_PROTOCOL_V1,
                lease_readiness: MAXSAT_LEASE_READINESS_V1,
                lease_location: MAXSAT_LEASE_LOCATION_V1,
            },
            watchdog_server: MaxSatWatchdogServer::new(guard.clone()),
            guard,
            campaign_lease,
        })
    }

    fn ensure_campaign_lease(&self) -> Result<()> {
        self.campaign_lease.ensure_alive()
    }

    fn wrap_stopped(&self, target: &Command) -> Command {
        let mut command = self.guard.command();
        command
            .arg("exec-stopped")
            .arg("--")
            .arg(target.get_program())
            .args(target.get_args());
        command
    }

    fn watch(&self, child: &mut Child, label: &str) -> Result<MaxSatWatchdog> {
        if let Err(error) = self
            .ensure_campaign_lease()
            .context("host-wide MaxSAT lease exited before watchdog registration")
        {
            terminate_maxsat_process_group(child);
            return Err(error);
        }
        if let Err(error) = wait_for_maxsat_guard_stop(child, label) {
            terminate_maxsat_process_group(child);
            return Err(error);
        }
        let watchdog = match self.watchdog_server.register(
            child.id(),
            self.plan.memlimit_mb_per_child,
            label,
            Some(Arc::clone(&self.campaign_lease)),
        ) {
            Ok(watchdog) => watchdog,
            Err(error) => {
                terminate_maxsat_process_group(child);
                return Err(error);
            }
        };
        if let Err(error) = self
            .ensure_campaign_lease()
            .context("host-wide MaxSAT lease exited while watchdog was arming")
        {
            drop(watchdog);
            terminate_maxsat_process_group(child);
            return Err(error);
        }
        #[cfg(unix)]
        {
            let resumed = i32::try_from(child.id())
                .context("MaxSAT child PID does not fit pid_t")
                .and_then(|pid| {
                    nix::sys::signal::killpg(
                        nix::unistd::Pid::from_raw(pid),
                        nix::sys::signal::Signal::SIGCONT,
                    )
                    .context("resuming guarded MaxSAT child")
                });
            if let Err(error) = resumed {
                drop(watchdog);
                terminate_maxsat_process_group(child);
                return Err(error);
            }
        }
        #[cfg(not(unix))]
        {
            drop(watchdog);
            terminate_maxsat_process_group(child);
            bail!("guarded MaxSAT execution requires POSIX process groups");
        }
        Ok(watchdog)
    }
}

fn locate_oom_guard() -> Option<PathBuf> {
    let mut starts = Vec::new();
    if let Ok(cwd) = std::env::current_dir() {
        starts.push(cwd);
    }
    if let Ok(exe) = std::env::current_exe() {
        if let Some(parent) = exe.parent() {
            starts.push(parent.to_path_buf());
        }
    }
    starts.push(PathBuf::from(env!("CARGO_MANIFEST_DIR")));
    for start in starts {
        for ancestor in start.ancestors() {
            let candidate = ancestor.join("scripts").join("_oom_guard.py");
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    None
}

#[derive(Debug, Clone, Copy)]
enum MaxSatWatchdogServerEvent {
    Ready,
    Done,
    Breach(u64),
}

type MaxSatWatchdogServerMessage = std::result::Result<MaxSatWatchdogServerEvent, String>;

#[derive(Debug, Clone, Copy)]
struct MaxSatWatchdogOutcome {
    breached: bool,
    breach_time_ns: Option<u64>,
}

fn maxsat_monotonic_time_ns() -> Result<u64> {
    #[cfg(unix)]
    {
        let timestamp = nix::time::clock_gettime(nix::time::ClockId::CLOCK_MONOTONIC)
            .context("reading monotonic clock for MaxSAT watchdog attribution")?;
        let elapsed: Duration = timestamp.into();
        u64::try_from(elapsed.as_nanos())
            .context("monotonic clock exceeds MaxSAT watchdog timestamp range")
    }
    #[cfg(not(unix))]
    {
        bail!("MaxSAT watchdog attribution requires POSIX clock_gettime")
    }
}

fn maxsat_watchdog_breached_before(
    outcome: MaxSatWatchdogOutcome,
    trigger_ns: u64,
) -> Result<bool> {
    if !outcome.breached {
        return Ok(false);
    }
    let breach_time_ns = outcome
        .breach_time_ns
        .context("MaxSAT RSS watchdog breach timestamp is missing")?;
    Ok(breach_time_ns <= trigger_ns)
}

#[cfg(target_os = "linux")]
fn maxsat_watchdog_server_process_is_responsive(pid: u32) -> bool {
    let Ok(stat) = fs::read_to_string(format!("/proc/{pid}/stat")) else {
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
fn maxsat_watchdog_server_process_is_responsive(_pid: u32) -> bool {
    true
}

#[derive(Debug)]
struct MaxSatWatchdogServerProcess {
    child: Child,
    stdin: ChildStdin,
}

/// One `_oom_guard.py watch-server` per MaxSAT campaign. Each registration
/// retains its own zero-grace process-group envelope, while all registrations
/// share the server interpreter's cached `/proc` snapshot.
#[derive(Debug)]
struct MaxSatWatchdogServer {
    guard: OomGuardSource,
    process: Mutex<Option<MaxSatWatchdogServerProcess>>,
    registrations:
        Arc<Mutex<std::collections::HashMap<u64, mpsc::Sender<MaxSatWatchdogServerMessage>>>>,
    healthy: Arc<AtomicBool>,
    last_heartbeat_ns: Arc<AtomicU64>,
    last_process_check_ns: AtomicU64,
    next_id: AtomicU64,
}

impl MaxSatWatchdogServer {
    fn new(guard: OomGuardSource) -> Arc<Self> {
        Arc::new(Self {
            guard,
            process: Mutex::new(None),
            registrations: Arc::new(Mutex::new(std::collections::HashMap::new())),
            healthy: Arc::new(AtomicBool::new(false)),
            last_heartbeat_ns: Arc::new(AtomicU64::new(0)),
            last_process_check_ns: AtomicU64::new(0),
            next_id: AtomicU64::new(1),
        })
    }

    fn reserve_watch_id(&self) -> Result<u64> {
        let mut id = self.next_id.load(Ordering::Relaxed);
        loop {
            let Some(next) = id.checked_add(1).filter(|_| id != 0) else {
                bail!("MaxSAT RSS watchdog registration ID exhausted");
            };
            match self
                .next_id
                .compare_exchange_weak(id, next, Ordering::Relaxed, Ordering::Relaxed)
            {
                Ok(_) => return Ok(id),
                Err(observed) => id = observed,
            }
        }
    }

    fn ensure_started(&self) -> Result<()> {
        let mut process = self
            .process
            .lock()
            .map_err(|_| anyhow::anyhow!("MaxSAT RSS watchdog server mutex poisoned"))?;
        if let Some(server) = process.as_mut() {
            if self.heartbeat_is_fresh()
                && maxsat_watchdog_server_process_is_responsive(server.child.id())
            {
                return match server.child.try_wait() {
                    Ok(None) => Ok(()),
                    Ok(Some(status)) => {
                        self.healthy.store(false, Ordering::Release);
                        bail!("MaxSAT campaign RSS watchdog server exited unexpectedly ({status})")
                    }
                    Err(error) => {
                        self.healthy.store(false, Ordering::Release);
                        Err(error).context("checking MaxSAT RSS watchdog server")
                    }
                };
            }
            bail!("MaxSAT campaign RSS watchdog server is no longer healthy");
        }

        let mut command = self.guard.command();
        command
            .arg("watch-server")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        isolate_maxsat_process_group(&mut command);
        let mut child = command.spawn().with_context(|| {
            format!(
                "starting MaxSAT RSS watchdog server {}",
                self.guard.provenance()
            )
        })?;
        let Some(stdin) = child.stdin.take() else {
            terminate_maxsat_process_group(&mut child);
            bail!("MaxSAT RSS watchdog server stdin is missing");
        };
        let Some(stdout) = child.stdout.take() else {
            drop(stdin);
            terminate_maxsat_process_group(&mut child);
            bail!("MaxSAT RSS watchdog server stdout is missing");
        };

        let (ready_sender, ready_receiver) = mpsc::channel();
        let registrations = Arc::clone(&self.registrations);
        let healthy = Arc::clone(&self.healthy);
        let last_heartbeat_ns = Arc::clone(&self.last_heartbeat_ns);
        std::thread::spawn(move || {
            maxsat_watchdog_server_reader(
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
                    drop(stdin);
                    terminate_maxsat_process_group(&mut child);
                    bail!("MaxSAT RSS watchdog server readiness failed: {error}");
                }
                Err(mpsc::TryRecvError::Disconnected) => {
                    drop(stdin);
                    terminate_maxsat_process_group(&mut child);
                    bail!("MaxSAT RSS watchdog server readiness channel disconnected");
                }
                Err(mpsc::TryRecvError::Empty) => {}
            }
            match child.try_wait() {
                Ok(Some(status)) => {
                    drop(stdin);
                    terminate_maxsat_process_group(&mut child);
                    bail!("MaxSAT RSS watchdog server exited before arming ({status})");
                }
                Ok(None) => {}
                Err(error) => {
                    drop(stdin);
                    terminate_maxsat_process_group(&mut child);
                    return Err(error).context("checking MaxSAT RSS watchdog server startup");
                }
            }
            if Instant::now() >= deadline {
                drop(stdin);
                terminate_maxsat_process_group(&mut child);
                bail!("MaxSAT RSS watchdog server did not arm within 10 seconds");
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        *process = Some(MaxSatWatchdogServerProcess { child, stdin });
        Ok(())
    }

    fn register(
        self: &Arc<Self>,
        pid: u32,
        limit_mb: usize,
        label: &str,
        campaign_lease: Option<Arc<MaxSatCampaignLease>>,
    ) -> Result<MaxSatWatchdog> {
        use std::fmt::Write as _;

        self.ensure_started()?;
        if label.len() > 512 {
            bail!("MaxSAT RSS watchdog label exceeds 512 bytes");
        }
        let watch_id = self.reserve_watch_id()?;
        let mut label_hex = String::with_capacity(label.len().saturating_mul(2));
        for byte in label.as_bytes() {
            write!(&mut label_hex, "{byte:02x}")
                .map_err(|_| anyhow::anyhow!("encoding MaxSAT RSS watchdog label failed"))?;
        }
        let command = format!("WATCH {watch_id} {pid} {limit_mb} {label_hex}\n");
        if command.len() > MAXSAT_WATCHDOG_SERVER_MAX_LINE as usize {
            bail!("MaxSAT RSS watchdog command exceeds protocol limit");
        }

        let (sender, receiver) = mpsc::channel();
        self.registrations
            .lock()
            .map_err(|_| anyhow::anyhow!("MaxSAT RSS watchdog registration mutex poisoned"))?
            .insert(watch_id, sender);
        let write_result = (|| -> Result<()> {
            if !self.healthy.load(Ordering::Acquire) {
                bail!("MaxSAT RSS watchdog server became unhealthy");
            }
            let mut process = self
                .process
                .lock()
                .map_err(|_| anyhow::anyhow!("MaxSAT RSS watchdog server mutex poisoned"))?;
            let server = process
                .as_mut()
                .context("MaxSAT RSS watchdog server process is missing")?;
            server
                .stdin
                .write_all(command.as_bytes())
                .and_then(|()| server.stdin.flush())
                .with_context(|| format!("registering MaxSAT RSS watchdog for child {pid}"))
        })();
        // A failed write may have delivered a command prefix. Retain the
        // sender until server EOF drains registrations, so a late response
        // cannot become an unknown-id campaign-wide protocol failure.
        write_result?;

        match receiver.recv_timeout(Duration::from_secs(10)) {
            Ok(Ok(MaxSatWatchdogServerEvent::Ready)) => Ok(MaxSatWatchdog {
                server: Arc::clone(self),
                campaign_lease,
                watch_id,
                target_pgid: i32::try_from(pid).ok(),
                terminal_outcome: None,
                terminal_error: None,
                receiver,
            }),
            Ok(Ok(_)) => bail!("MaxSAT RSS watchdog {watch_id} terminated before readiness"),
            Ok(Err(error)) => {
                bail!("MaxSAT RSS watchdog {watch_id} failed before readiness: {error}")
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {
                // Keep the sender registered until the server reports a
                // terminal event. The stopped target will be killed by the
                // caller; removing this ID early would poison other watches.
                bail!("MaxSAT RSS watchdog {watch_id} did not arm within 10 seconds")
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                bail!("MaxSAT RSS watchdog {watch_id} readiness channel disconnected")
            }
        }
    }

    fn heartbeat_is_fresh(&self) -> bool {
        if !self.healthy.load(Ordering::Acquire) {
            return false;
        }
        let Ok(now_ns) = maxsat_monotonic_time_ns() else {
            self.healthy.store(false, Ordering::Release);
            return false;
        };
        let last_ns = self.last_heartbeat_ns.load(Ordering::Acquire);
        if last_ns == 0
            || now_ns.saturating_sub(last_ns)
                > u64::try_from(MAXSAT_WATCHDOG_SERVER_HEARTBEAT_TIMEOUT.as_nanos())
                    .unwrap_or(u64::MAX)
        {
            self.healthy.store(false, Ordering::Release);
            return false;
        }
        true
    }

    fn is_healthy(&self) -> bool {
        if !self.heartbeat_is_fresh() {
            return false;
        }
        let Ok(now_ns) = maxsat_monotonic_time_ns() else {
            self.healthy.store(false, Ordering::Release);
            return false;
        };
        let interval_ns = u64::try_from(MAXSAT_WATCHDOG_SERVER_STATE_CHECK_INTERVAL.as_nanos())
            .unwrap_or(u64::MAX);
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
            .is_some_and(maxsat_watchdog_server_process_is_responsive);
        if !responsive {
            self.healthy.store(false, Ordering::Release);
        }
        responsive
    }

    #[cfg(test)]
    fn process_id(&self) -> Option<u32> {
        self.process
            .lock()
            .ok()
            .and_then(|process| process.as_ref().map(|server| server.child.id()))
    }

    #[cfg(test)]
    fn kill_process_for_test(&self) {
        if let Ok(mut process) = self.process.lock() {
            if let Some(server) = process.as_mut() {
                terminate_maxsat_process_group(&mut server.child);
            }
        }
    }
}

impl Drop for MaxSatWatchdogServer {
    fn drop(&mut self) {
        self.healthy.store(false, Ordering::Release);
        let process = match self.process.get_mut() {
            Ok(process) => process.take(),
            Err(poisoned) => poisoned.into_inner().take(),
        };
        let Some(mut server) = process else {
            return;
        };
        drop(server.stdin);
        let deadline = Instant::now() + Duration::from_secs(10);
        loop {
            match server.child.try_wait() {
                Ok(Some(_)) => return,
                Ok(None) if Instant::now() < deadline => {
                    std::thread::sleep(Duration::from_millis(5));
                }
                Ok(None) | Err(_) => {
                    terminate_maxsat_process_group(&mut server.child);
                    return;
                }
            }
        }
    }
}

fn maxsat_watchdog_server_reader(
    stdout: std::process::ChildStdout,
    registrations: Arc<
        Mutex<std::collections::HashMap<u64, mpsc::Sender<MaxSatWatchdogServerMessage>>>,
    >,
    healthy: Arc<AtomicBool>,
    last_heartbeat_ns: Arc<AtomicU64>,
    ready: mpsc::Sender<std::result::Result<(), String>>,
) {
    use std::io::{BufRead as _, Read as _};

    let result = (|| -> std::result::Result<(), String> {
        let mut reader = std::io::BufReader::new(stdout);
        let mut marker = vec![0_u8; MAXSAT_WATCHDOG_SERVER_READY.len()];
        reader
            .read_exact(&mut marker)
            .map_err(|error| format!("reading MaxSAT watchdog server readiness failed: {error}"))?;
        if marker != MAXSAT_WATCHDOG_SERVER_READY {
            return Err("invalid MaxSAT RSS watchdog server readiness marker".to_string());
        }
        last_heartbeat_ns.store(
            maxsat_monotonic_time_ns().map_err(|error| error.to_string())?,
            Ordering::Release,
        );
        healthy.store(true, Ordering::Release);
        let _ = ready.send(Ok(()));
        loop {
            let mut line = Vec::new();
            let read = (&mut reader)
                .take(MAXSAT_WATCHDOG_SERVER_MAX_LINE + 1)
                .read_until(b'\n', &mut line)
                .map_err(|error| {
                    format!("reading MaxSAT watchdog server response failed: {error}")
                })?;
            if read == 0 {
                return Err("MaxSAT RSS watchdog server closed its response pipe".to_string());
            }
            if line.len() > MAXSAT_WATCHDOG_SERVER_MAX_LINE as usize || !line.ends_with(b"\n") {
                return Err(
                    "MaxSAT RSS watchdog server response exceeds protocol limit".to_string()
                );
            }
            let line = std::str::from_utf8(&line[..line.len() - 1]).map_err(|error| {
                format!("MaxSAT RSS watchdog server emitted non-UTF-8: {error}")
            })?;
            if let Some(timestamp) = line.strip_prefix("HEARTBEAT ") {
                let timestamp = timestamp.parse::<u64>().map_err(|_| {
                    "MaxSAT RSS watchdog server heartbeat has invalid timestamp".to_string()
                })?;
                if timestamp == 0 {
                    return Err(
                        "MaxSAT RSS watchdog server heartbeat has zero timestamp".to_string()
                    );
                }
                last_heartbeat_ns.store(
                    maxsat_monotonic_time_ns().map_err(|error| error.to_string())?,
                    Ordering::Release,
                );
                continue;
            }
            let (watch_id, event, terminal) = parse_maxsat_watchdog_server_event(line)?;
            let sender = {
                let mut registrations = registrations
                    .lock()
                    .map_err(|_| "MaxSAT RSS watchdog registration mutex poisoned".to_string())?;
                if terminal {
                    registrations.remove(&watch_id)
                } else {
                    registrations.get(&watch_id).cloned()
                }
            }
            .ok_or_else(|| format!("MaxSAT RSS watchdog server reported unknown id {watch_id}"))?;
            // A local caller may time out and kill a stopped child before a
            // late response arrives. A dropped receiver is local, not a reason
            // to disarm the other campaign registrations.
            let _ = sender.send(event);
        }
    })();
    if !healthy.swap(false, Ordering::AcqRel) {
        let _ =
            ready.send(Err(result.as_ref().err().cloned().unwrap_or_else(|| {
                "MaxSAT RSS watchdog server stopped".to_string()
            })));
    }
    let failure = result
        .err()
        .unwrap_or_else(|| "MaxSAT RSS watchdog server stopped".to_string());
    if let Ok(mut registrations) = registrations.lock() {
        for (_, sender) in registrations.drain() {
            let _ = sender.send(Err(failure.clone()));
        }
    }
}

fn parse_maxsat_watchdog_server_event(
    line: &str,
) -> std::result::Result<(u64, MaxSatWatchdogServerMessage, bool), String> {
    let fields = line.split(' ').collect::<Vec<_>>();
    let watch_id = fields
        .get(1)
        .ok_or_else(|| "MaxSAT watchdog server response omitted id".to_string())?
        .parse::<u64>()
        .map_err(|_| "MaxSAT watchdog server response has invalid id".to_string())?;
    if watch_id == 0 {
        return Err("MaxSAT watchdog server response has zero id".to_string());
    }
    match fields.as_slice() {
        ["READY", _] => Ok((watch_id, Ok(MaxSatWatchdogServerEvent::Ready), false)),
        ["DONE", _] => Ok((watch_id, Ok(MaxSatWatchdogServerEvent::Done), true)),
        ["BREACH", _, timestamp] => {
            let timestamp = timestamp
                .parse::<u64>()
                .map_err(|_| "MaxSAT watchdog server breach has invalid timestamp".to_string())?;
            if timestamp == 0 {
                return Err("MaxSAT watchdog server breach has zero timestamp".to_string());
            }
            Ok((
                watch_id,
                Ok(MaxSatWatchdogServerEvent::Breach(timestamp)),
                true,
            ))
        }
        ["ERROR", _, encoded] => {
            if encoded.len() > 1024 || encoded.len() % 2 != 0 {
                return Err("MaxSAT watchdog server error has invalid encoding".to_string());
            }
            let mut bytes = Vec::with_capacity(encoded.len() / 2);
            for pair in encoded.as_bytes().as_chunks::<2>().0 {
                let pair = std::str::from_utf8(pair)
                    .map_err(|_| "MaxSAT watchdog server error has invalid encoding".to_string())?;
                bytes.push(u8::from_str_radix(pair, 16).map_err(|_| {
                    "MaxSAT watchdog server error has invalid encoding".to_string()
                })?);
            }
            let message = String::from_utf8(bytes)
                .map_err(|_| "MaxSAT watchdog server error is not UTF-8".to_string())?;
            Ok((watch_id, Err(message), true))
        }
        _ => Err("invalid MaxSAT RSS watchdog server response".to_string()),
    }
}

struct MaxSatWatchdog {
    server: Arc<MaxSatWatchdogServer>,
    campaign_lease: Option<Arc<MaxSatCampaignLease>>,
    watch_id: u64,
    target_pgid: Option<i32>,
    terminal_outcome: Option<MaxSatWatchdogOutcome>,
    terminal_error: Option<String>,
    receiver: mpsc::Receiver<MaxSatWatchdogServerMessage>,
}

impl MaxSatWatchdog {
    fn ensure_campaign_lease_alive(&mut self) -> Result<()> {
        let result = match self.campaign_lease.as_deref() {
            Some(lease) => lease.ensure_alive(),
            None => Ok(()),
        };
        if let Err(error) = result {
            self.kill_target();
            return Err(error).context("host-wide MaxSAT lease failed while child was guarded");
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

    fn decode_terminal_event(
        &self,
        event: MaxSatWatchdogServerMessage,
    ) -> Result<MaxSatWatchdogOutcome> {
        match event.map_err(|error| {
            anyhow::anyhow!("MaxSAT RSS watchdog {} failed: {error}", self.watch_id)
        })? {
            MaxSatWatchdogServerEvent::Done => Ok(MaxSatWatchdogOutcome {
                breached: false,
                breach_time_ns: None,
            }),
            MaxSatWatchdogServerEvent::Breach(breach_time_ns) => Ok(MaxSatWatchdogOutcome {
                breached: true,
                breach_time_ns: Some(breach_time_ns),
            }),
            MaxSatWatchdogServerEvent::Ready => {
                bail!(
                    "MaxSAT RSS watchdog {} emitted duplicate readiness",
                    self.watch_id
                )
            }
        }
    }

    /// Poll server and registration health while the guarded child is active.
    /// Any campaign-server failure kills the complete target process group.
    fn poll(&mut self) -> Result<Option<MaxSatWatchdogOutcome>> {
        self.ensure_campaign_lease_alive()?;
        if let Some(error) = &self.terminal_error {
            bail!("{error}");
        }
        if let Some(outcome) = self.terminal_outcome {
            return Ok(Some(outcome));
        }
        if !self.server.is_healthy() {
            self.kill_target();
            bail!("MaxSAT campaign RSS watchdog server stopped while a solver was active");
        }
        match self.receiver.try_recv() {
            Ok(message) => match self.decode_terminal_event(message) {
                Ok(outcome) => {
                    self.target_pgid = None;
                    self.terminal_outcome = Some(outcome);
                    Ok(Some(outcome))
                }
                Err(error) => {
                    self.kill_target();
                    let error = error.to_string();
                    self.terminal_error = Some(error.clone());
                    bail!("{error}")
                }
            },
            Err(mpsc::TryRecvError::Empty) => Ok(None),
            Err(mpsc::TryRecvError::Disconnected) => {
                self.kill_target();
                bail!(
                    "MaxSAT RSS watchdog {} response channel disconnected",
                    self.watch_id
                )
            }
        }
    }

    fn finish(mut self) -> Result<MaxSatWatchdogOutcome> {
        self.ensure_campaign_lease_alive()?;
        if let Some(error) = &self.terminal_error {
            bail!("{error}");
        }
        if let Some(outcome) = self.terminal_outcome {
            self.target_pgid = None;
            return Ok(outcome);
        }
        if !self.server.is_healthy() {
            self.kill_target();
            bail!("MaxSAT campaign RSS watchdog server stopped before reporting completion");
        }
        let message = match self.receiver.recv_timeout(Duration::from_secs(12)) {
            Ok(message) => message,
            Err(mpsc::RecvTimeoutError::Timeout) => {
                self.kill_target();
                bail!(
                    "MaxSAT RSS watchdog {} did not report completion within 12 seconds",
                    self.watch_id
                )
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                self.kill_target();
                bail!(
                    "MaxSAT RSS watchdog {} response channel disconnected",
                    self.watch_id
                )
            }
        };
        let outcome = self.decode_terminal_event(message)?;
        self.target_pgid = None;
        self.ensure_campaign_lease_alive()?;
        Ok(outcome)
    }

    fn detach_campaign_lease(&mut self) {
        self.campaign_lease = None;
    }

    /// The caller has already killed and reaped the target leader. Disarm the
    /// PGID before awaiting the terminal record so error-path Drop can never
    /// signal a subsequently reused process-group ID.
    fn finish_after_target_cleanup(mut self) -> Result<MaxSatWatchdogOutcome> {
        self.target_pgid = None;
        self.finish()
    }
}

impl Drop for MaxSatWatchdog {
    fn drop(&mut self) {
        self.kill_target();
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MaxSatUnreapedChildState {
    Running,
    Stopped,
    Exited,
}

#[cfg(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
))]
fn observe_maxsat_child_unreaped(
    child: &Child,
    include_stopped: bool,
    label: &str,
) -> Result<MaxSatUnreapedChildState> {
    use nix::sys::wait::{waitid, Id, WaitPidFlag, WaitStatus};

    let raw_pid = i32::try_from(child.id())
        .with_context(|| format!("{label}: child PID does not fit pid_t"))?;
    let mut flags = WaitPidFlag::WEXITED | WaitPidFlag::WNOHANG | WaitPidFlag::WNOWAIT;
    if include_stopped {
        flags |= WaitPidFlag::WSTOPPED;
    }
    match waitid(Id::Pid(nix::unistd::Pid::from_raw(raw_pid)), flags) {
        Ok(WaitStatus::Exited(..) | WaitStatus::Signaled(..)) => {
            Ok(MaxSatUnreapedChildState::Exited)
        }
        Ok(WaitStatus::Stopped(..)) if include_stopped => Ok(MaxSatUnreapedChildState::Stopped),
        Ok(WaitStatus::StillAlive | WaitStatus::Continued(..)) => {
            Ok(MaxSatUnreapedChildState::Running)
        }
        Ok(status) => bail!("{label}: unexpected unreaped child status: {status:?}"),
        Err(error) => bail!("{label}: observing child without reaping failed: {error}"),
    }
}

#[cfg(not(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
)))]
fn observe_maxsat_child_unreaped(
    _child: &Child,
    _include_stopped: bool,
    label: &str,
) -> Result<MaxSatUnreapedChildState> {
    bail!("{label}: safe unreaped child observation is unavailable on this platform")
}

#[cfg(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
))]
fn wait_for_maxsat_guard_stop(child: &Child, label: &str) -> Result<()> {
    use nix::sys::wait::{waitid, Id, WaitPidFlag, WaitStatus};

    let raw_pid = i32::try_from(child.id()).context("MaxSAT child PID does not fit pid_t")?;
    let pid = nix::unistd::Pid::from_raw(raw_pid);
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        match waitid(
            Id::Pid(pid),
            WaitPidFlag::WEXITED
                | WaitPidFlag::WSTOPPED
                | WaitPidFlag::WNOHANG
                | WaitPidFlag::WNOWAIT,
        ) {
            Ok(WaitStatus::Stopped(_, nix::sys::signal::Signal::SIGSTOP)) => return Ok(()),
            Ok(WaitStatus::StillAlive) if Instant::now() < deadline => {
                std::thread::sleep(Duration::from_millis(5));
            }
            Ok(WaitStatus::StillAlive) => {
                bail!("{label}: MaxSAT child did not enter its watchdog safety stop")
            }
            Ok(status) => bail!(
                "{label}: MaxSAT child exited or changed state before watchdog arming: {status:?}"
            ),
            Err(error) => bail!("{label}: observing stopped MaxSAT child failed: {error}"),
        }
    }
}

#[cfg(not(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
)))]
fn wait_for_maxsat_guard_stop(_child: &Child, label: &str) -> Result<()> {
    bail!("{label}: safe unreaped MaxSAT child observation is unavailable on this platform")
}

#[cfg(unix)]
fn isolate_maxsat_process_group(command: &mut Command) {
    use std::os::unix::process::CommandExt as _;
    command.process_group(0);
}

#[cfg(not(unix))]
fn isolate_maxsat_process_group(_command: &mut Command) {}

fn terminate_maxsat_process_group(child: &mut Child) {
    let _ = terminate_maxsat_process_group_with_status(child);
}

fn terminate_maxsat_process_group_with_status(
    child: &mut Child,
) -> Option<std::process::ExitStatus> {
    #[cfg(unix)]
    if let Ok(pid) = i32::try_from(child.id()) {
        let _ = nix::sys::signal::killpg(
            nix::unistd::Pid::from_raw(pid),
            nix::sys::signal::Signal::SIGKILL,
        );
    }
    #[cfg(not(unix))]
    let _ = child.kill();
    child.wait().ok()
}

const MAXSAT_CAPTURE_BYTES: usize = 32 * 1024 * 1024;

struct MaxSatCapture {
    receiver: mpsc::Receiver<(String, bool)>,
}

impl MaxSatCapture {
    fn start<R>(mut reader: R) -> Self
    where
        R: std::io::Read + Send + 'static,
    {
        let (sender, receiver) = mpsc::channel();
        std::thread::spawn(move || {
            let head_cap = MAXSAT_CAPTURE_BYTES / 2;
            let tail_cap = MAXSAT_CAPTURE_BYTES - head_cap;
            let mut head = Vec::with_capacity(head_cap);
            let mut tail = VecDeque::with_capacity(tail_cap);
            let mut total = 0usize;
            let mut chunk = [0u8; 8192];
            loop {
                let read = match reader.read(&mut chunk) {
                    Ok(0) | Err(_) => break,
                    Ok(read) => read,
                };
                total = total.saturating_add(read);
                let mut offset = 0;
                if head.len() < head_cap {
                    let keep = read.min(head_cap - head.len());
                    head.extend_from_slice(&chunk[..keep]);
                    offset = keep;
                }
                for byte in &chunk[offset..read] {
                    if tail.len() == tail_cap {
                        tail.pop_front();
                    }
                    tail.push_back(*byte);
                }
            }
            let truncated = total > MAXSAT_CAPTURE_BYTES;
            if !tail.is_empty() {
                if truncated {
                    head.extend_from_slice(b"\n[... output truncated ...]\n");
                }
                head.extend(tail);
            }
            let _ = sender.send((String::from_utf8_lossy(&head).into_owned(), truncated));
        });
        Self { receiver }
    }

    fn finish(self) -> (String, bool) {
        self.receiver
            .recv_timeout(Duration::from_secs(2))
            .unwrap_or_else(|_| (String::new(), true))
    }
}

/// MaxSAT solving commands.
#[derive(Subcommand)]
pub(crate) enum MaxSatCommand {
    /// Solve a WCNF/MaxSAT instance with competition output.
    Solve(MaxSatSolveArgs),
    /// Run a corpus of WCNF instances and score against reference data.
    Bench(MaxSatBenchArgs),
}

/// Arguments for `ay maxsat solve`.
#[derive(clap::Args)]
pub(crate) struct MaxSatSolveArgs {
    /// WCNF/MaxSAT input file.
    pub file: PathBuf,
    /// Wall-clock timeout in seconds (0 = none). On timeout, prints the best
    /// bound found and `s UNKNOWN`.
    #[arg(long, default_value_t = 0.0)]
    pub timeout: f64,
    /// EXPERIMENTAL: solve via the native ay-milp 0/1-ILP encoding instead of
    /// the OLL core-guided engine. Validation lane for LP-structured weighted
    /// families (facility-location / MPE / auctions) where OLL stalls.
    #[arg(long)]
    pub milp: bool,
}

/// Arguments for `ay maxsat bench`.
#[derive(clap::Args)]
pub(crate) struct MaxSatBenchArgs {
    /// Directory containing .wcnf instances (searched recursively).
    pub dir: PathBuf,
    /// Per-instance wall-clock timeout in seconds.
    #[arg(long, default_value_t = 60.0)]
    pub timeout: f64,
    /// Reference field CSV (columns: instance, o_value, then one column of
    /// per-instance runtimes per competing solver). Enables optimum
    /// verification and a retroactive leaderboard at the same timeout.
    #[arg(long)]
    pub field: Option<PathBuf>,
    /// Number of instances to run in parallel.
    #[arg(long)]
    pub jobs: Option<usize>,
    /// Run only the first N instances (sorted by name).
    #[arg(long)]
    pub limit: Option<usize>,
    /// Deterministically subsample: keep every Nth instance.
    #[arg(long)]
    pub stride: Option<usize>,
    /// Write detailed per-instance results to a JSON file.
    #[arg(long)]
    pub out: Option<PathBuf>,
    /// Skip re-verifying reported models against the instance.
    #[arg(long)]
    pub no_verify: bool,
    /// Benchmark an external solver instead of AY: "NAME=CMD" where CMD is
    /// a program plus arguments; "{file}" in CMD is replaced by the
    /// instance path (appended if absent). The same wall-clock timeout,
    /// kill policy, and model/optimum verification apply.
    #[arg(long)]
    pub solver: Option<String>,
}

/// Run a MaxSAT command and return the competition exit code.
pub(crate) fn run(cmd: &MaxSatCommand) -> Result<i32> {
    match cmd {
        MaxSatCommand::Solve(args) => solve(args),
        MaxSatCommand::Bench(args) => bench(args),
    }
}

// ---------------------------------------------------------------------------
// MILP race lane (#maxsat-milp-race)
// ---------------------------------------------------------------------------
// UWrMaxSat-SCIP architecture (ScipSolver.cc), implemented natively over
// ay-milp: on size-gated instances a second thread races the OLL engine with
// a 0/1-ILP encoding of the same instance, seeded with OLL's current
// incumbent as a strict cutoff row (objective <= UB-1). Outcomes:
//   - MILP Optimal below the cutoff  -> global optimum (exact rational proof)
//   - MILP Infeasible under a cutoff -> OLL's incumbent UB is PROVEN optimal
//     (nothing below it exists) — closes lb-race instances where OLL holds
//     the optimum but its core lower bound stalls
//   - MILP Infeasible with no cutoff -> hard clauses UNSAT
// Every win is fail-closed cross-checked against the OLL lane's state, and
// `ay maxsat bench` re-verifies the reported model + optimum independently.
// The bench harness runs each instance as a subprocess, so a still-computing
// race thread dies with the process — no cross-instance CPU leakage.

/// Size gates for MILP-race eligibility, mirroring UWrMaxSat's dispatch gate
/// (ScipSolver.cc:579-584): free vars < 100k, hard clauses < 600k, softs
/// < 100k, evaluated on the parsed instance.
const MILP_RACE_MAX_VARS: usize = 100_000;
/// Hard-clause gate. UWr allows up to 600k post-reduction, but our lane
/// encodes the RAW formula, and measured LP throughput on raw CNF rows makes
/// >150k-row models hopeless inside 60s (css-guardian 259k: never finished;
/// metro 875k: never finished) while every confirmed MILP win is small
/// (warehouses ~10-60k rows, auctions 11k). 150k matches CGSS2's own
/// optimizer gate (vars<100k AND clauses<150k, cgss2.cpp:2027) and sharply
/// cuts race-thread CPU contention at bench jobs=10.
const MILP_RACE_MAX_HARDS: usize = 150_000;
const MILP_RACE_MAX_SOFTS: usize = 100_000;
/// Numeric gate (MsSolver.cc:767): total soft weight must fit f64-coefficient
/// arithmetic with headroom (2^49 = 53-bit mantissa minus 4 safety bits).
const MILP_RACE_MAX_WEIGHT_SUM: u64 = 1 << 49;
/// Race launch delay: UWrMaxSat delays SCIP 120s of a 3600s budget (~3.3%);
/// at 60s the analog is ~2-3s. The delay lets OLL post a first incumbent
/// (the cutoff seed) and spares trivially-SAT-solvable instances the MILP
/// overhead entirely.
const MILP_RACE_DELAY_SECS: f64 = 3.0;
/// If no OLL incumbent has appeared by this point, launch unseeded anyway.
const MILP_RACE_UB_WAIT_SECS: f64 = 6.0;

/// Opt-in: `AY_AB_MAXSAT_MILP_RACE=1` enables the race lane. DEFAULT OFF for
/// the bench protocol: at `bench --jobs 10` on a 14-core box the extra
/// threads oversubscribe and cost ~7 borderline (20-50s) solves for ~2
/// MILP wins (full-track attribution legs, 2026-07-19: bundle3 296 with race
/// vs norace 298). In a competition setting (one instance per machine) the
/// second thread is free — enable it there.
fn maxsat_milp_race_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("AY_AB_MAXSAT_MILP_RACE").as_deref() == Ok("1"))
}

/// A race-lane verdict, produced by the MILP worker thread.
enum MilpRaceWin {
    /// MILP proved the exact optimum and holds a model achieving it.
    /// `model` is 1-based (`model[var]`), ready for `print_assignment`.
    Exact { cost: u64, model: Vec<bool> },
    /// MILP proved `objective <= optimum - 1` infeasible: the OLL incumbent
    /// equal to `optimum` is the proven global optimum.
    CutoffProof { optimum: u64 },
    /// MILP proved the hard clauses infeasible (no cutoff was applied).
    HardsUnsat,
}

/// Build the 0/1-ILP model for a MaxSAT instance. Returns the model plus the
/// objective offset and expression (needed for the cutoff row).
///
///   var x_v          -> binary col c_v
///   hard (l1..lk)    -> row  Σ lit >= 1        (¬x contributes 1 - c_v)
///   soft w unit (l)  -> objective on c_v directly (no relaxation var)
///   soft w (l1..lk)  -> binary r; row Σ lit + r >= 1; objective += w·r
fn build_maxsat_milp_model(
    hard: &[Vec<i32>],
    soft: &[(u64, Vec<i32>)],
    num_vars: usize,
) -> Option<(
    ay_milp::Model,
    Vec<ay_milp::Col>,
    f64,
    Vec<(ay_milp::Col, f64)>,
)> {
    use ay_milp::{Col, Model, Sense};
    let mut m = Model::new();
    let var_cols: Vec<Col> = (0..num_vars).map(|_| m.add_binary_col()).collect();

    let clause_row = |lits: &[i32]| -> (Vec<(Col, f64)>, f64) {
        let mut coeffs = Vec::with_capacity(lits.len() + 1);
        let mut rhs = 1.0_f64;
        for &l in lits {
            let c = var_cols[(l.unsigned_abs() as usize) - 1];
            if l > 0 {
                coeffs.push((c, 1.0));
            } else {
                coeffs.push((c, -1.0));
                rhs -= 1.0;
            }
        }
        (coeffs, rhs)
    };

    for cl in hard {
        if cl.is_empty() {
            return None; // trivially UNSAT — leave it to the OLL lane
        }
        let (coeffs, rhs) = clause_row(cl);
        m.add_row(rhs, f64::INFINITY, &coeffs);
    }

    let mut obj_map: std::collections::HashMap<Col, f64> = std::collections::HashMap::new();
    let mut offset = 0.0_f64;
    for (w, cl) in soft {
        let w = *w as f64;
        match cl.as_slice() {
            [] => offset += w,
            &[l] => {
                let c = var_cols[(l.unsigned_abs() as usize) - 1];
                if l > 0 {
                    *obj_map.entry(c).or_insert(0.0) -= w;
                    offset += w;
                } else {
                    *obj_map.entry(c).or_insert(0.0) += w;
                }
            }
            _ => {
                let r = m.add_binary_col();
                let (mut coeffs, rhs) = clause_row(cl);
                coeffs.push((r, 1.0));
                m.add_row(rhs, f64::INFINITY, &coeffs);
                *obj_map.entry(r).or_insert(0.0) += w;
            }
        }
    }
    let obj: Vec<(Col, f64)> = obj_map.into_iter().filter(|&(_, a)| a != 0.0).collect();
    m.set_objective(&obj, Sense::Minimize);
    if offset != 0.0 {
        m.set_objective_offset(offset);
    }
    Some((m, var_cols, offset, obj))
}

/// MILP race worker: delayed launch, cutoff-seeded exact solve, fail-closed
/// verdict publication. Runs on its own thread; never touches stdout.
#[allow(clippy::too_many_arguments)]
fn milp_race_worker(
    hard: Vec<Vec<i32>>,
    soft: Vec<(u64, Vec<i32>)>,
    num_vars: usize,
    deadline: Option<Instant>,
    shared_ub: Arc<AtomicU64>,
    milp_won: Arc<AtomicBool>,
    slot: Arc<Mutex<Option<MilpRaceWin>>>,
) {
    use ay_milp::{BabSession, Outcome, SolveOpts};
    use num_traits::ToPrimitive;

    // Delayed launch: give OLL a head start and wait (bounded) for a first
    // incumbent to use as the cutoff seed.
    let t0 = Instant::now();
    loop {
        let elapsed = t0.elapsed().as_secs_f64();
        if elapsed >= MILP_RACE_UB_WAIT_SECS {
            break;
        }
        if elapsed >= MILP_RACE_DELAY_SECS && shared_ub.load(Ordering::Relaxed) != u64::MAX {
            break;
        }
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return;
        }
        std::thread::sleep(Duration::from_millis(25));
    }

    let cutoff = shared_ub.load(Ordering::Relaxed);
    eprintln!(
        "c milp-race: launching (hards={} softs={} vars={} cutoff={})",
        hard.len(),
        soft.len(),
        num_vars,
        if cutoff == u64::MAX {
            "none".to_string()
        } else {
            cutoff.to_string()
        }
    );
    let Some((mut m, var_cols, offset, obj)) = build_maxsat_milp_model(&hard, &soft, num_vars)
    else {
        return;
    };
    // Strict cutoff row: objective expression <= cutoff - 1 (in offset-free
    // terms). Weights are integral so the -1 step is exact.
    let cutoff_applied = cutoff != u64::MAX && cutoff > 0;
    if cutoff_applied {
        let rhs = (cutoff as f64) - offset - 1.0;
        m.add_row(f64::NEG_INFINITY, rhs, &obj);
    }

    let mut opts = SolveOpts::new();
    // OOM guard (#maxsat-milp-race): the bench runs up to `jobs` solver
    // processes concurrently and each race thread would otherwise default to
    // ay-milp's 2 GiB open-set budget (10 × 2 GiB on a 24 GB box). 512 MiB
    // is ample for the ≤150k-row gated models (warehouses wins used far
    // less); exhausting it degrades to Feasible/Unknown, never a wrong
    // verdict.
    opts.memory_budget = Some(512 << 20);
    if let Some(d) = deadline {
        let now = Instant::now();
        if d <= now {
            return;
        }
        opts = opts.with_time_limit(d - now);
    }
    let sess = BabSession::new(m.clone(), &opts);
    let mut sess = match sess {
        Ok(s) => s,
        Err(e) => {
            eprintln!("c milp-race: session init failed: {e}");
            return;
        }
    };
    let outcome = match sess.check() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("c milp-race: solve failed: {e}");
            return;
        }
    };
    eprintln!(
        "c milp-race: outcome {} after launch",
        match &outcome {
            Outcome::Optimal { .. } => "Optimal",
            Outcome::Infeasible { .. } => "Infeasible",
            Outcome::Feasible { .. } => "Feasible(incumbent)",
            _ => "Unknown",
        }
    );

    let win = match outcome {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            let cost = value.to_integer().to_u64();
            match cost {
                // Guard: with a cutoff row the proven value must lie below it.
                Some(c) if !cutoff_applied || c < cutoff => {
                    let mut shifted = vec![false; num_vars + 1];
                    for (v, col) in var_cols.iter().enumerate().take(num_vars) {
                        let _ = col;
                        shifted[v + 1] = model_values
                            .get(v)
                            .and_then(ToPrimitive::to_f64)
                            .is_some_and(|f| f > 0.5);
                    }
                    Some(MilpRaceWin::Exact {
                        cost: c,
                        model: shifted,
                    })
                }
                _ => None, // fail closed on any numeric surprise
            }
        }
        Outcome::Infeasible { .. } => {
            if cutoff_applied {
                Some(MilpRaceWin::CutoffProof { optimum: cutoff })
            } else {
                Some(MilpRaceWin::HardsUnsat)
            }
        }
        _ => None,
    };

    if let Some(w) = win {
        *slot.lock().expect("milp race slot") = Some(w);
        milp_won.store(true, Ordering::Release);
    }
}

fn solve(args: &MaxSatSolveArgs) -> Result<i32> {
    if !args.timeout.is_finite() || args.timeout < 0.0 {
        bail!("--timeout must be finite and non-negative");
    }
    if args.milp {
        return milp_solve(args);
    }
    // The timeout covers total wall time including parsing, matching how
    // competition timeouts (and `ay maxsat bench`) measure solvers.
    let deadline =
        (args.timeout > 0.0).then(|| Instant::now() + Duration::from_secs_f64(args.timeout));

    // MILP-race clause capture: collect while all size gates hold; on the
    // first violation drop the buffers and stop collecting (the OLL engine
    // is unaffected).
    let race_wanted = maxsat_milp_race_enabled() && deadline.is_some();
    let mut race_hard: Vec<Vec<i32>> = Vec::new();
    let mut race_soft: Vec<(u64, Vec<i32>)> = Vec::new();
    let mut race_weight_sum: u64 = 0;
    let mut race_ok = race_wanted;

    let mut solver = MaxSatSolver::new();
    let summary = stream_wcnf_file(&args.file, &mut |weight, lits| {
        match weight {
            None => {
                if race_ok {
                    if race_hard.len() < MILP_RACE_MAX_HARDS {
                        race_hard.push(lits.to_vec());
                    } else {
                        race_ok = false;
                        race_hard = Vec::new();
                        race_soft = Vec::new();
                    }
                }
                solver.add_hard_clause(lits.to_vec());
            }
            Some(w) => {
                if race_ok {
                    race_weight_sum = race_weight_sum.saturating_add(w);
                    if race_soft.len() < MILP_RACE_MAX_SOFTS
                        && race_weight_sum < MILP_RACE_MAX_WEIGHT_SUM
                    {
                        race_soft.push((w, lits.to_vec()));
                    } else {
                        race_ok = false;
                        race_hard = Vec::new();
                        race_soft = Vec::new();
                    }
                }
                solver.add_soft_clause(lits.to_vec(), w);
            }
        }
        Ok(())
    })
    .with_context(|| format!("failed to parse '{}'", args.file.display()))?;
    let num_vars = summary.num_vars;
    if num_vars >= MILP_RACE_MAX_VARS {
        race_ok = false;
    }
    // Weighted instances only: on uniform-weight (unweighted-style) instances
    // the OLL engine's cardinality reasoning dominates any 0/1-LP relaxation
    // (the LP bound of a pure cardinality objective is weak), so the race
    // thread would only burn a core.
    if race_ok && (race_soft.is_empty() || race_soft.iter().all(|(w, _)| *w == race_soft[0].0)) {
        race_ok = false;
    }

    // Launch the race thread (detached; dies with the process).
    let shared_ub = Arc::new(AtomicU64::new(u64::MAX));
    let milp_won = Arc::new(AtomicBool::new(false));
    let race_slot: Arc<Mutex<Option<MilpRaceWin>>> = Arc::new(Mutex::new(None));
    if race_ok {
        let (h, s) = (
            std::mem::take(&mut race_hard),
            std::mem::take(&mut race_soft),
        );
        let (ub, won, slot) = (shared_ub.clone(), milp_won.clone(), race_slot.clone());
        std::thread::spawn(move || {
            milp_race_worker(h, s, num_vars, deadline, ub, won, slot);
        });
    }

    let milp_won_stop = milp_won.clone();
    let should_stop = move || {
        milp_won_stop.load(Ordering::Acquire) || deadline.is_some_and(|d| Instant::now() >= d)
    };
    let mut last_printed: Option<u64> = None;
    let shared_ub_cb = shared_ub.clone();
    let mut on_upper_bound = |cost: u64| {
        shared_ub_cb.fetch_min(cost, Ordering::Relaxed);
        if last_printed != Some(cost) {
            last_printed = Some(cost);
            println!("o {cost}");
        }
    };

    match solver.solve_interruptible(&should_stop, &mut on_upper_bound) {
        MaxSatResult::Optimal { model, cost } => {
            if last_printed != Some(cost) {
                println!("o {cost}");
            }
            println!("s OPTIMUM FOUND");
            print_assignment(num_vars, &model);
            Ok(30)
        }
        MaxSatResult::Unsatisfiable => {
            println!("s UNSATISFIABLE");
            Ok(20)
        }
        MaxSatResult::Unknown => {
            // Check the race lane before conceding. Every arm fail-closes to
            // the plain Unknown path on any cross-lane disagreement.
            let race_win = race_slot.lock().expect("milp race slot").take();
            match race_win {
                Some(MilpRaceWin::Exact { cost, model }) => {
                    // Sanity: OLL's incumbent (if any) cannot be better than
                    // a proven optimum.
                    let oll_better = solver.best_solution().is_some_and(|(c, _)| c < cost);
                    if oll_better {
                        eprintln!("c milp-race: DISCARDED Exact({cost}) — OLL incumbent is better");
                    } else {
                        if last_printed != Some(cost) {
                            println!("o {cost}");
                        }
                        println!("s OPTIMUM FOUND");
                        print_assignment(num_vars, &model);
                        eprintln!("c milp-race: optimum {cost} proven by MILP lane");
                        return Ok(30);
                    }
                }
                Some(MilpRaceWin::CutoffProof { optimum }) => {
                    if let Some((cost, model)) = solver.best_solution() {
                        if cost == optimum {
                            if last_printed != Some(cost) {
                                println!("o {cost}");
                            }
                            println!("s OPTIMUM FOUND");
                            print_assignment(num_vars, model);
                            eprintln!(
                                "c milp-race: OLL incumbent {cost} proven optimal by MILP cutoff"
                            );
                            return Ok(30);
                        }
                        eprintln!(
                            "c milp-race: DISCARDED CutoffProof({optimum}) — OLL incumbent is {cost}"
                        );
                    }
                }
                Some(MilpRaceWin::HardsUnsat) => {
                    if solver.best_solution().is_none() {
                        println!("s UNSATISFIABLE");
                        eprintln!("c milp-race: hard clauses proven UNSAT by MILP lane");
                        return Ok(20);
                    }
                    eprintln!("c milp-race: DISCARDED HardsUnsat — OLL holds a model");
                }
                None => {}
            }
            if let Some((cost, model)) = solver.best_solution() {
                if last_printed != Some(cost) {
                    println!("o {cost}");
                }
                println!("s UNKNOWN");
                print_assignment(num_vars, model);
            } else {
                println!("s UNKNOWN");
            }
            Ok(0)
        }
    }
}

fn print_assignment(num_vars: usize, model: &[bool]) {
    // MSE 2022+ format: `v` followed by one 0/1 per variable, one token.
    let mut line = String::with_capacity(num_vars + 2);
    line.push('v');
    line.push(' ');
    for var in 1..=num_vars {
        line.push(if model.get(var).copied().unwrap_or(false) {
            '1'
        } else {
            '0'
        });
    }
    println!("{line}");
}

/// EXPERIMENTAL native-MILP MaxSAT solver (validation lane for LP-structured
/// weighted families). Encodes the WCNF as an exact 0/1 ILP and solves it with
/// ay-milp's branch-and-bound:
///   var x_v          -> binary col c_v
///   hard (l1..lk)    -> row  Σ lit >= 1        (¬x contributes 1 - c_v)
///   soft w (l1..lk)  -> binary r; row Σ lit + r >= 1; objective += w·r
///   minimize Σ w·r   == weighted-MaxSAT cost.
/// ay-milp uses exact rational arithmetic, so a proven `Optimal` is the exact
/// optimum — safe to report (bench still re-verifies model + optimum).
fn milp_solve(args: &MaxSatSolveArgs) -> Result<i32> {
    use ay_milp::{BabSession, Outcome, SolveOpts};
    use num_traits::ToPrimitive;

    let start = Instant::now();
    let mut hard: Vec<Vec<i32>> = Vec::new();
    let mut soft: Vec<(u64, Vec<i32>)> = Vec::new();
    let mut max_var: usize = 0;
    let summary = stream_wcnf_file(&args.file, &mut |weight, lits| {
        for &l in lits {
            max_var = max_var.max(l.unsigned_abs() as usize);
        }
        match weight {
            None => hard.push(lits.to_vec()),
            Some(w) => soft.push((w, lits.to_vec())),
        }
        Ok(())
    })
    .with_context(|| format!("failed to parse '{}'", args.file.display()))?;
    let num_vars = summary.num_vars.max(max_var);

    let Some((m, _var_cols, _offset, _obj)) = build_maxsat_milp_model(&hard, &soft, num_vars)
    else {
        // An empty hard clause: trivially UNSAT.
        println!("s UNSATISFIABLE");
        return Ok(20);
    };

    let mut opts = SolveOpts::new();
    if args.timeout > 0.0 {
        opts = opts.with_time_limit(Duration::from_secs_f64(args.timeout));
    }
    let mut sess = BabSession::new(m.clone(), &opts).context("ay-milp session init failed")?;
    let outcome = sess.check().context("ay-milp solve failed")?;
    let elapsed = start.elapsed();

    match outcome {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            let cost = value.to_integer();
            println!("o {cost}");
            println!("s OPTIMUM FOUND");
            let mut shifted = vec![false; num_vars + 1];
            for v in 0..num_vars {
                shifted[v + 1] = model_values
                    .get(v)
                    .and_then(ToPrimitive::to_f64)
                    .is_some_and(|f| f > 0.5);
            }
            print_assignment(num_vars, &shifted);
            eprintln!(
                "milp: proved optimum {cost} in {:.2}s",
                elapsed.as_secs_f64()
            );
            Ok(30)
        }
        Outcome::Infeasible { .. } => {
            println!("s UNSATISFIABLE");
            Ok(20)
        }
        other => {
            println!("s UNKNOWN");
            eprintln!(
                "milp: no optimum in {:.2}s ({other:?})",
                elapsed.as_secs_f64()
            );
            Ok(0)
        }
    }
}

// ---------------------------------------------------------------------------
// Benchmarking
// ---------------------------------------------------------------------------

/// Reference data for one instance from a field CSV.
#[derive(Debug, Clone)]
struct FieldRow {
    /// Known optimum, if any solver proved one.
    o_value: Option<u64>,
    /// Per-solver runtime in seconds (absent = not solved within the
    /// evaluation's timeout).
    times: Vec<Option<f64>>,
}

#[derive(Debug, Default)]
struct FieldData {
    solvers: Vec<String>,
    rows: BTreeMap<String, FieldRow>,
}

/// Outcome status of one bench run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RunStatus {
    /// Proved optimum, model verified, matches reference optimum (if known).
    Optimum,
    /// Solver reported hard clauses unsatisfiable without an independently
    /// checked UNSAT proof. It is retained as evidence but never scored.
    Unvalidated,
    /// Exceeded the exact per-child RSS envelope.
    Memout,
    /// Timed out / unknown.
    Timeout,
    /// Reported optimum disagrees with reference or model verification.
    Wrong,
    /// Subprocess failed.
    Error,
}

impl RunStatus {
    fn as_str(self) -> &'static str {
        match self {
            RunStatus::Optimum => "OPTIMUM",
            RunStatus::Unvalidated => "UNVALIDATED",
            RunStatus::Memout => "MEMOUT",
            RunStatus::Timeout => "TIMEOUT",
            RunStatus::Wrong => "WRONG",
            RunStatus::Error => "ERROR",
        }
    }
}

#[derive(Debug, Clone)]
struct RunResult {
    instance: String,
    status: RunStatus,
    seconds: f64,
    cost: Option<u64>,
    detail: String,
    authority: String,
}

#[derive(Debug, Clone, Copy)]
struct BenchSummary {
    solved: usize,
    wrong: usize,
    errors: usize,
    memouts: usize,
    unvalidated: usize,
    par2: f64,
}

fn scoring_solved(status: RunStatus) -> bool {
    status == RunStatus::Optimum
}

fn summarize_bench(results: &[RunResult], timeout: f64) -> BenchSummary {
    let count = |status| {
        results
            .iter()
            .filter(|result| result.status == status)
            .count()
    };
    BenchSummary {
        solved: results
            .iter()
            .filter(|result| scoring_solved(result.status))
            .count(),
        wrong: count(RunStatus::Wrong),
        errors: count(RunStatus::Error),
        memouts: count(RunStatus::Memout),
        unvalidated: count(RunStatus::Unvalidated),
        par2: results
            .iter()
            .map(|result| {
                if scoring_solved(result.status) {
                    result.seconds
                } else {
                    2.0 * timeout
                }
            })
            .sum::<f64>()
            / results.len() as f64,
    }
}

fn bench_exit_code(summary: BenchSummary) -> i32 {
    i32::from(summary.wrong > 0 || summary.errors > 0 || summary.unvalidated > 0)
}

fn bench(args: &MaxSatBenchArgs) -> Result<i32> {
    if !args.timeout.is_finite() || args.timeout <= 0.0 {
        bail!("--timeout must be finite and positive for benchmarking");
    }
    if args.jobs == Some(0) {
        bail!("--jobs must be positive");
    }
    if args.stride == Some(0) {
        bail!("--stride must be positive");
    }
    let mut files = collect_wcnf_files(&args.dir)?;
    files.sort();
    if let Some(stride) = args.stride {
        if stride > 1 {
            files = files.into_iter().step_by(stride).collect();
        }
    }
    if let Some(limit) = args.limit {
        files.truncate(limit);
    }
    if files.is_empty() {
        bail!("no .wcnf files found under '{}'", args.dir.display());
    }

    let field = match &args.field {
        Some(path) => Some(parse_field_csv(path)?),
        None => auto_field_for(&files),
    };

    let requested_jobs = args
        .jobs
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|p| p.get().saturating_sub(1).max(1))
                .unwrap_or(1)
        })
        .max(1);
    let resources = MaxSatResources::plan(requested_jobs)?;
    let jobs = resources.plan.jobs;

    safe_println!(
        "ay maxsat bench: {} instances, timeout {}s, {} parallel jobs{}; memory={}MiB/child NBCORE={} headroom={}MiB enforcement={} aggregate={}",
        files.len(),
        args.timeout,
        jobs,
        match &field {
            Some(f) => format!(", field of {} reference solvers", f.solvers.len()),
            None => String::new(),
        },
        resources.plan.memlimit_mb_per_child,
        resources.plan.nbcore_per_child,
        resources.plan.headroom_mb,
        resources.plan.enforcement,
        resources.plan.aggregate_enforcement,
    );

    let external: Option<(String, Vec<String>)> = match &args.solver {
        Some(spec) => {
            let (name, cmd) = spec
                .split_once('=')
                .ok_or_else(|| anyhow::anyhow!("--solver expects NAME=CMD"))?;
            let words: Vec<String> = cmd.split_whitespace().map(str::to_string).collect();
            if words.is_empty() {
                bail!("--solver command is empty");
            }
            Some((name.to_string(), words))
        }
        None => None,
    };
    let solver_name = external
        .as_ref()
        .map(|(n, _)| n.clone())
        .unwrap_or_else(|| "AY".to_string());

    let exe = std::env::current_exe().context("cannot locate own executable")?;
    let queue: Mutex<Vec<(usize, PathBuf)>> =
        Mutex::new(files.iter().cloned().enumerate().rev().collect());
    let results: Mutex<Vec<RunResult>> = Mutex::new(Vec::with_capacity(files.len()));
    let done = std::sync::atomic::AtomicUsize::new(0);
    let total = files.len();

    // OOM guard (#bench-giant-gate): giant instances (multi-million-clause
    // families like abstraction-refinement) can push a single solver process
    // to several GB, and the name-sorted queue clusters same-family giants
    // onto concurrent workers. Cap concurrently-running giants; small
    // instances keep the remaining workers busy so wall-clock skew stays
    // negligible (~7% of the corpus is above the threshold).
    const GIANT_INSTANCE_BYTES: u64 = 80 * 1024 * 1024;
    const MAX_CONCURRENT_GIANTS: usize = 3;
    let giants_running = std::sync::atomic::AtomicUsize::new(0);

    std::thread::scope(|scope| {
        for _ in 0..jobs {
            scope.spawn(|| loop {
                let Some((_, file)) = queue.lock().expect("queue lock").pop() else {
                    return;
                };
                let is_giant = fs::metadata(&file)
                    .map(|m| m.len() > GIANT_INSTANCE_BYTES)
                    .unwrap_or(false);
                if is_giant {
                    loop {
                        let cur = giants_running.load(Ordering::Acquire);
                        if cur < MAX_CONCURRENT_GIANTS
                            && giants_running
                                .compare_exchange(cur, cur + 1, Ordering::AcqRel, Ordering::Acquire)
                                .is_ok()
                        {
                            break;
                        }
                        std::thread::sleep(Duration::from_millis(500));
                    }
                }
                let result = run_one(
                    &exe,
                    external.as_ref(),
                    &file,
                    args.timeout,
                    !args.no_verify,
                    field.as_ref(),
                    &resources,
                );
                if is_giant {
                    giants_running.fetch_sub(1, Ordering::AcqRel);
                }
                let idx = 1 + done.fetch_add(1, Ordering::Relaxed);
                safe_println!(
                    "[{idx}/{total}] {} {} {:.2}s{}{}",
                    result.instance,
                    result.status.as_str(),
                    result.seconds,
                    match result.cost {
                        Some(c) => format!(" o={c}"),
                        None => String::new(),
                    },
                    if result.detail.is_empty() {
                        String::new()
                    } else {
                        format!(" [{}]", result.detail)
                    }
                );
                results.lock().expect("results lock").push(result);
            });
        }
    });

    resources
        .ensure_campaign_lease()
        .context("host-wide MaxSAT lease exited during benchmark execution")?;

    let mut results = results.into_inner().expect("results lock");
    results.sort_by(|a, b| a.instance.cmp(&b.instance));

    // Only independently model-checked, reference-consistent optima count as
    // solved. Bare UNSAT claims have no proof path in this command and remain
    // explicit non-scoring failures.
    let summary = summarize_bench(&results, args.timeout);

    safe_println!("");
    safe_println!(
        "{}: solved {}/{} (PAR2 {:.2}), wrong {}, unvalidated {}, memout {}, errors {}",
        solver_name,
        summary.solved,
        results.len(),
        summary.par2,
        summary.wrong,
        summary.unvalidated,
        summary.memouts,
        summary.errors
    );

    if let Some(field) = &field {
        print_leaderboard(&solver_name, field, &results, args.timeout);
    }

    if let Some(out) = &args.out {
        write_json_report(out, args, &results, field.as_ref(), &resources.plan)?;
        safe_println!("wrote {}", out.display());
    }

    resources
        .ensure_campaign_lease()
        .context("host-wide MaxSAT lease exited before campaign completion")?;

    Ok(bench_exit_code(summary))
}

/// Score every reference solver on exactly the instances of this run at the
/// same timeout, insert the benched solver, and print the retroactive
/// leaderboard.
fn print_leaderboard(solver_name: &str, field: &FieldData, results: &[RunResult], timeout: f64) {
    struct Row {
        name: String,
        solved: usize,
        par2: f64,
    }

    let n = results.len();
    let mut rows: Vec<Row> = Vec::with_capacity(field.solvers.len() + 1);

    for (si, solver) in field.solvers.iter().enumerate() {
        let mut solved = 0usize;
        let mut par2_sum = 0.0f64;
        let mut covered = 0usize;
        for r in results {
            let Some(row) = field.rows.get(&r.instance) else {
                continue;
            };
            covered += 1;
            match row.times.get(si).copied().flatten() {
                Some(t) if t <= timeout => {
                    solved += 1;
                    par2_sum += t;
                }
                _ => par2_sum += 2.0 * timeout,
            }
        }
        if covered > 0 {
            rows.push(Row {
                name: solver.clone(),
                solved,
                par2: par2_sum / covered as f64,
            });
        }
    }

    let ay_solved = results
        .iter()
        .filter(|result| scoring_solved(result.status))
        .count();
    let ay_par2: f64 = results
        .iter()
        .map(|result| {
            if scoring_solved(result.status) {
                result.seconds
            } else {
                2.0 * timeout
            }
        })
        .sum::<f64>()
        / n as f64;
    rows.push(Row {
        name: format!("{solver_name} (this run)"),
        solved: ay_solved,
        par2: ay_par2,
    });

    rows.sort_by(|a, b| {
        b.solved.cmp(&a.solved).then(
            a.par2
                .partial_cmp(&b.par2)
                .unwrap_or(std::cmp::Ordering::Equal),
        )
    });

    safe_println!("");
    safe_println!(
        "Retroactive leaderboard on these {} instances at {}s timeout:",
        n,
        timeout
    );
    safe_println!(
        "  {:<4} {:<32} {:>7} {:>10}",
        "rank",
        "solver",
        "solved",
        "PAR2"
    );
    for (i, row) in rows.iter().enumerate() {
        let marker = if row.name.ends_with("(this run)") {
            " <=="
        } else {
            ""
        };
        safe_println!(
            "  {:<4} {:<32} {:>7} {:>10.2}{}",
            i + 1,
            row.name,
            row.solved,
            row.par2,
            marker
        );
    }
}

fn write_json_report(
    out: &Path,
    args: &MaxSatBenchArgs,
    results: &[RunResult],
    field: Option<&FieldData>,
    resource_plan: &MaxSatResourcePlan,
) -> Result<()> {
    let summary = summarize_bench(results, args.timeout);
    let items: Vec<serde_json::Value> = results
        .iter()
        .map(|r| {
            serde_json::json!({
                "instance": r.instance,
                "status": r.status.as_str(),
                "seconds": r.seconds,
                "cost": r.cost,
                "detail": r.detail,
                "authority": r.authority,
                "reference_optimum": field
                    .and_then(|f| f.rows.get(&r.instance))
                    .and_then(|row| row.o_value),
            })
        })
        .collect();
    let doc = serde_json::json!({
        "dir": args.dir.display().to_string(),
        "timeout": args.timeout,
        "solver": args
            .solver
            .as_deref()
            .map(|s| s.split('=').next().unwrap_or("external"))
            .unwrap_or("AY"),
        "summary": {
            "total": results.len(),
            "solved": summary.solved,
            "wrong": summary.wrong,
            "unvalidated": summary.unvalidated,
            "memout": summary.memouts,
            "errors": summary.errors,
            "par2": summary.par2,
            "exit_code": bench_exit_code(summary),
        },
        "results": items,
        "resource_plan": resource_plan,
    });
    let mut file =
        fs::File::create(out).with_context(|| format!("cannot create '{}'", out.display()))?;
    writeln!(file, "{}", serde_json::to_string_pretty(&doc)?)?;
    Ok(())
}

fn collect_wcnf_files(dir: &Path) -> Result<Vec<PathBuf>> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let entries =
            fs::read_dir(&d).with_context(|| format!("cannot read directory '{}'", d.display()))?;
        for entry in entries {
            let path = entry?.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "wcnf") {
                out.push(path);
            }
        }
    }
    Ok(out)
}

/// If no field CSV was given, look for the MSE reference CSVs shipped in
/// the repo relative to the instance directory's ancestors.
fn auto_field_for(files: &[PathBuf]) -> Option<FieldData> {
    let first = files.first()?;
    for ancestor in first.ancestors() {
        let base = ancestor.join("mse24");
        for name in ["field-exact-unweighted.csv", "field-exact-weighted.csv"] {
            let candidate = base.join(name);
            if candidate.is_file() {
                // Only use it if it actually covers these instances.
                if let Ok(field) = parse_field_csv(&candidate) {
                    let covered = files
                        .iter()
                        .filter(|f| field.rows.contains_key(&instance_key(f)))
                        .count();
                    if covered * 2 >= files.len() {
                        return Some(field);
                    }
                }
            }
        }
    }
    None
}

fn instance_key(path: &Path) -> String {
    path.file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default()
}

fn parse_field_csv(path: &Path) -> Result<FieldData> {
    let text = fs::read_to_string(path)
        .with_context(|| format!("cannot read field CSV '{}'", path.display()))?;
    let mut lines = text.lines();
    let header = lines.next().context("field CSV is empty")?;
    let cols: Vec<&str> = header.split(',').collect();
    if cols.len() < 3 || cols[0] != "instance" || cols[1] != "o_value" {
        bail!("field CSV must start with 'instance,o_value,<solver>...' columns");
    }
    let solvers: Vec<String> = cols[2..].iter().map(|s| s.to_string()).collect();
    let mut rows = BTreeMap::new();
    for line in lines {
        if line.trim().is_empty() {
            continue;
        }
        let cells: Vec<&str> = line.split(',').collect();
        if cells.len() != cols.len() {
            continue;
        }
        let times: Vec<Option<f64>> = cells[2..]
            .iter()
            .map(|c| c.trim().parse::<f64>().ok())
            .collect();
        rows.insert(
            cells[0].to_string(),
            FieldRow {
                o_value: cells[1].trim().parse::<u64>().ok(),
                times,
            },
        );
    }
    Ok(FieldData { solvers, rows })
}

/// Extra wall-clock slack before a child that ignored its own deadline is
/// killed by the bench harness.
const KILL_GRACE_SECS: f64 = 10.0;

fn classify_unsat_claim(
    field: Option<&FieldData>,
    instance: &str,
    external: bool,
) -> (RunStatus, String, String) {
    if let Some(expected) = field
        .and_then(|field| field.rows.get(instance))
        .and_then(|row| row.o_value)
    {
        return (
            RunStatus::Wrong,
            format!("UNSAT contradicts known feasible reference optimum {expected}"),
            "reference field".to_string(),
        );
    }
    (
        RunStatus::Unvalidated,
        "UNSAT claim not independently proof-checked".to_string(),
        if external {
            "external solver claim (unvalidated)"
        } else {
            "AY solver claim (unvalidated)"
        }
        .to_string(),
    )
}

/// Solve one instance in a subprocess and judge the outcome. When
/// `external` is given, its command runs instead of AY (with `{file}`
/// substituted), under the same wall-clock kill policy and verification.
fn run_one(
    exe: &Path,
    external: Option<&(String, Vec<String>)>,
    file: &Path,
    timeout: f64,
    verify: bool,
    field: Option<&FieldData>,
    resources: &MaxSatResources,
) -> RunResult {
    let instance = instance_key(file);
    let start = Instant::now();
    if let Err(error) = resources.ensure_campaign_lease() {
        return RunResult {
            instance,
            status: RunStatus::Error,
            seconds: start.elapsed().as_secs_f64(),
            cost: None,
            detail: format!("host-wide resource lease unavailable: {error}"),
            authority: "none".to_string(),
        };
    }
    let command = match external {
        Some((_, words)) => {
            let mut cmd = Command::new(&words[0]);
            let mut file_used = false;
            // `{file}` is the external-solver command template placeholder,
            // not a Rust formatting argument.
            #[allow(clippy::literal_string_with_formatting_args)]
            for w in &words[1..] {
                if w.contains("{file}") {
                    cmd.arg(w.replace("{file}", &file.to_string_lossy()));
                    file_used = true;
                } else {
                    cmd.arg(w);
                }
            }
            if !file_used {
                cmd.arg(file);
            }
            cmd
        }
        None => {
            let mut cmd = Command::new(exe);
            cmd.arg("maxsat")
                .arg("solve")
                .arg(file)
                .arg("--timeout")
                .arg(format!("{timeout}"));
            cmd
        }
    };
    let mut command = resources.wrap_stopped(&command);
    command.env("MEMLIMIT", resources.plan.memlimit_mb_per_child.to_string());
    command.env("NBCORE", resources.plan.nbcore_per_child.to_string());
    command.stdin(Stdio::null());
    command.stdout(Stdio::piped());
    command.stderr(Stdio::null());
    isolate_maxsat_process_group(&mut command);
    let child = command.spawn();

    let mut child = match child {
        Ok(c) => c,
        Err(e) => {
            return RunResult {
                instance,
                status: RunStatus::Error,
                seconds: start.elapsed().as_secs_f64(),
                cost: None,
                detail: format!("spawn failed: {e}"),
                authority: "none".to_string(),
            }
        }
    };

    // Drain concurrently, retaining a bounded head/tail. A noisy or hostile
    // external solver cannot OOM the parent benchmark process.
    let capture = child.stdout.take().map(MaxSatCapture::start);
    let mut watchdog = match resources.watch(&mut child, "ay maxsat bench") {
        Ok(watchdog) => watchdog,
        Err(error) => {
            if let Some(capture) = capture {
                let _ = capture.finish();
            }
            return RunResult {
                instance,
                status: RunStatus::Error,
                seconds: start.elapsed().as_secs_f64(),
                cost: None,
                detail: format!("failed to arm RSS watchdog: {error}"),
                authority: "none".to_string(),
            };
        }
    };

    let mut killed = false;
    let mut wait_error = None;
    let mut campaign_lease_error = None;
    let mut watchdog_poll_error = None;
    let mut terminal_trigger_ns = None;
    let mut watchdog_breach_observed = false;
    let completed_normally = loop {
        match observe_maxsat_child_unreaped(&child, false, "MaxSAT solver") {
            Ok(MaxSatUnreapedChildState::Exited) => match maxsat_monotonic_time_ns() {
                Ok(trigger_ns) => {
                    terminal_trigger_ns = Some(trigger_ns);
                    break true;
                }
                Err(error) => {
                    wait_error = Some(format!("cannot timestamp child completion: {error}"));
                    break false;
                }
            },
            Ok(MaxSatUnreapedChildState::Running) => {
                if let Err(error) = resources.ensure_campaign_lease() {
                    campaign_lease_error = Some(error.to_string());
                    break false;
                }
                match watchdog.poll() {
                    Ok(Some(outcome)) if outcome.breached => {
                        // The server already killed the group on breach. Reap
                        // the leader now; `finish_after_target_cleanup` retains
                        // the authenticated terminal classification.
                        watchdog_breach_observed = true;
                        break false;
                    }
                    Ok(Some(_)) => {
                        watchdog_poll_error =
                            Some("RSS watchdog stopped before the MaxSAT child".to_string());
                        break false;
                    }
                    Ok(None) => {}
                    Err(error) => {
                        match resources.ensure_campaign_lease() {
                            Ok(()) => watchdog_poll_error = Some(error.to_string()),
                            Err(lease_error) => {
                                campaign_lease_error = Some(lease_error.to_string());
                            }
                        }
                        break false;
                    }
                }
                if start.elapsed().as_secs_f64() > timeout + KILL_GRACE_SECS {
                    match maxsat_monotonic_time_ns() {
                        Ok(trigger_ns) => {
                            terminal_trigger_ns = Some(trigger_ns);
                            killed = true;
                        }
                        Err(error) => {
                            wait_error = Some(format!("cannot timestamp timeout trigger: {error}"));
                        }
                    }
                    break false;
                }
                std::thread::sleep(Duration::from_millis(20));
            }
            Ok(MaxSatUnreapedChildState::Stopped) => {
                wait_error = Some("MaxSAT solver stopped unexpectedly".to_string());
                break false;
            }
            Err(error) => {
                wait_error = Some(error.to_string());
                break false;
            }
        }
    };
    // Normal wrapper exit is not proof its descendants exited. Kill/reap the
    // complete isolated group before disarming the watchdog or collecting
    // output.
    let cleanup_status = terminate_maxsat_process_group_with_status(&mut child);
    let status = completed_normally.then_some(cleanup_status).flatten();
    let seconds = start.elapsed().as_secs_f64();
    if campaign_lease_error.is_none() {
        campaign_lease_error = resources
            .ensure_campaign_lease()
            .err()
            .map(|error| error.to_string());
    }
    if campaign_lease_error.is_some() {
        // The primary failure already proves that aggregate admission is
        // gone. Consume this registration's terminal event without rechecking
        // the same dead lease and obscuring the primary error.
        watchdog.detach_campaign_lease();
    }
    let watchdog_outcome = match watchdog.finish_after_target_cleanup() {
        Ok(outcome) => outcome,
        Err(error) => {
            if campaign_lease_error.is_none() {
                campaign_lease_error = resources
                    .ensure_campaign_lease()
                    .err()
                    .map(|lease_error| lease_error.to_string());
            }
            if let Some(capture) = capture {
                let _ = capture.finish();
            }
            let mut failures = Vec::new();
            if let Some(lease_error) = campaign_lease_error.as_deref() {
                failures.push(format!(
                    "host-wide resource lease exited early: {lease_error}"
                ));
            }
            if let Some(poll_error) = watchdog_poll_error.as_deref() {
                failures.push(format!(
                    "RSS watchdog failed while child was active: {poll_error}"
                ));
            }
            if let Some(error) = wait_error.as_deref() {
                failures.push(format!("wait failed: {error}"));
            }
            failures.push(format!("RSS watchdog terminal cleanup failed: {error}"));
            return RunResult {
                instance,
                status: RunStatus::Error,
                seconds,
                cost: None,
                detail: failures.join("; "),
                authority: "none".to_string(),
            };
        }
    };
    if watchdog_breach_observed && !watchdog_outcome.breached {
        if let Some(capture) = capture {
            let _ = capture.finish();
        }
        return RunResult {
            instance,
            status: RunStatus::Error,
            seconds,
            cost: None,
            detail: "RSS watchdog lost a previously observed breach".to_string(),
            authority: "none".to_string(),
        };
    }
    let memout = match terminal_trigger_ns {
        Some(trigger_ns) if !watchdog_breach_observed => {
            match maxsat_watchdog_breached_before(watchdog_outcome, trigger_ns) {
                Ok(memout) => memout,
                Err(error) => {
                    if let Some(capture) = capture {
                        let _ = capture.finish();
                    }
                    return RunResult {
                        instance,
                        status: RunStatus::Error,
                        seconds,
                        cost: None,
                        detail: format!("cannot attribute RSS watchdog breach: {error}"),
                        authority: "none".to_string(),
                    };
                }
            }
        }
        _ => watchdog_outcome.breached,
    };
    if campaign_lease_error.is_none() {
        campaign_lease_error = resources
            .ensure_campaign_lease()
            .err()
            .map(|error| error.to_string());
    }
    let exited_ok =
        status.is_some_and(|s| s.success() || s.code() == Some(30) || s.code() == Some(20));
    let (stdout, capture_truncated) = capture
        .map(MaxSatCapture::finish)
        .unwrap_or_else(|| (String::new(), true));
    if let Some(error) = campaign_lease_error {
        let detail = match watchdog_poll_error.as_deref() {
            Some(poll_error) => format!(
                "host-wide resource lease exited early: {error}; RSS watchdog failed while child was active: {poll_error}"
            ),
            None => format!("host-wide resource lease exited early: {error}"),
        };
        return RunResult {
            instance,
            status: RunStatus::Error,
            seconds,
            cost: None,
            detail,
            authority: "none".to_string(),
        };
    }
    if let Some(error) = watchdog_poll_error {
        return RunResult {
            instance,
            status: RunStatus::Error,
            seconds,
            cost: None,
            detail: format!("RSS watchdog failed while child was active: {error}"),
            authority: "none".to_string(),
        };
    }
    if memout {
        return RunResult {
            instance,
            status: RunStatus::Memout,
            seconds,
            cost: None,
            detail: format!(
                "process-group RSS exceeded {}MiB",
                resources.plan.memlimit_mb_per_child
            ),
            authority: "rss_watchdog(grace=0)".to_string(),
        };
    }
    if let Some(error) = wait_error {
        return RunResult {
            instance,
            status: RunStatus::Error,
            seconds,
            cost: None,
            detail: format!("wait failed: {error}"),
            authority: "none".to_string(),
        };
    }
    if capture_truncated {
        return RunResult {
            instance,
            status: RunStatus::Error,
            seconds,
            cost: None,
            detail: format!("solver stdout exceeded {MAXSAT_CAPTURE_BYTES} bytes"),
            authority: "none".to_string(),
        };
    }
    let mut status_line = "";
    let mut last_o: Option<u64> = None;
    let mut v_text = String::new();
    for line in stdout.lines() {
        if let Some(rest) = line.strip_prefix("o ") {
            last_o = rest.trim().parse::<u64>().ok();
        } else if let Some(rest) = line.strip_prefix("s ") {
            status_line = rest.trim();
        } else if let Some(rest) = line.strip_prefix("v ") {
            // Long models may wrap across several `v` lines; concatenate.
            v_text.push_str(rest);
            v_text.push(' ');
        } else if line == "v" {
            // tolerated: empty continuation
        }
    }
    let v_line: Option<&str> = if v_text.is_empty() {
        None
    } else {
        Some(v_text.as_str())
    };

    // Hold AY to the same wall-clock standard as the reference field:
    // a proof that lands after the timeout is a timeout.
    if matches!(status_line, "OPTIMUM FOUND" | "UNSATISFIABLE") && seconds > timeout {
        return RunResult {
            instance,
            status: RunStatus::Timeout,
            seconds,
            cost: last_o,
            detail: format!("finished late ({seconds:.2}s > {timeout}s)"),
            authority: "wall-clock harness".to_string(),
        };
    }

    match status_line {
        "OPTIMUM FOUND" => {
            let Some(cost) = last_o else {
                return RunResult {
                    instance,
                    status: RunStatus::Wrong,
                    seconds,
                    cost: None,
                    detail: "OPTIMUM without o-line".into(),
                    authority: "output parser".to_string(),
                };
            };
            // Reference optimum check.
            let expected_optimum = field
                .and_then(|f| f.rows.get(&instance))
                .and_then(|r| r.o_value);
            if let Some(expected) = expected_optimum {
                if expected != cost {
                    return RunResult {
                        instance,
                        status: RunStatus::Wrong,
                        seconds,
                        cost: Some(cost),
                        detail: format!("reference optimum {expected} != reported {cost}"),
                        authority: "reference field".to_string(),
                    };
                }
            }
            // Model verification: re-evaluate the reported model.
            if verify {
                if let Err(msg) = verify_model(file, v_line, cost) {
                    return RunResult {
                        instance,
                        status: RunStatus::Wrong,
                        seconds,
                        cost: Some(cost),
                        detail: msg,
                        authority: "model verifier".to_string(),
                    };
                }
            }
            RunResult {
                instance,
                status: RunStatus::Optimum,
                seconds,
                cost: Some(cost),
                detail: String::new(),
                authority: match (expected_optimum.is_some(), verify) {
                    (true, true) => "reference optimum + independently verified model",
                    (true, false) => "reference optimum; model verification disabled",
                    (false, true) => "solver optimality claim + independently verified model",
                    (false, false) => "solver claim; verification disabled",
                }
                .to_string(),
            }
        }
        "UNSATISFIABLE" => {
            let (status, detail, authority) =
                classify_unsat_claim(field, &instance, external.is_some());
            RunResult {
                instance,
                status,
                seconds,
                cost: None,
                detail,
                authority,
            }
        }
        _ => RunResult {
            instance,
            status: if killed || exited_ok {
                RunStatus::Timeout
            } else {
                RunStatus::Error
            },
            seconds,
            cost: last_o,
            detail: if killed {
                "killed".into()
            } else {
                String::new()
            },
            authority: if killed { "wall-clock harness" } else { "none" }.to_string(),
        },
    }
}

/// Re-scan the instance and confirm the reported model satisfies all hard
/// clauses and violates soft clauses of total weight exactly `cost`.
/// Streams the file: constant memory even on multi-GB instances.
fn verify_model(file: &Path, v_line: Option<&str>, cost: u64) -> std::result::Result<(), String> {
    let Some(v_line) = v_line else {
        return Err("OPTIMUM without v-line".into());
    };

    // Model bits. MSE 2022+ format: concatenated 0/1 values (whitespace
    // tolerated), possibly as one long token. Old format (some external
    // solvers): signed decimal literals ending in 0. Text such as `1 0` is
    // genuinely ambiguous until the instance variable count is known, so
    // evaluate both bounded candidates during the one streaming file pass and
    // retain the candidate whose assignment is complete. This avoids both a
    // second multi-GB file scan and the old one-variable misclassification.
    enum ParsedModel {
        Dense(Vec<bool>),
        Sparse(BTreeMap<usize, bool>),
    }

    struct ModelCandidate {
        model: ParsedModel,
        model_cost: Option<u64>,
        hard_violation: bool,
    }

    let parse_sparse = || -> std::result::Result<ParsedModel, String> {
        // Sparse until the independently parsed instance tells us its actual
        // variable count. A malicious huge literal must not size a Vec in the
        // parent verifier before that bound is known.
        let mut assignments = BTreeMap::new();
        for tok in v_line.split_whitespace() {
            let lit: i64 = tok
                .parse()
                .map_err(|_| format!("bad v-line literal '{tok}'"))?;
            if lit == 0 {
                continue;
            }
            let magnitude = lit
                .checked_abs()
                .ok_or_else(|| format!("v-line literal out of range '{tok}'"))?;
            let var = usize::try_from(magnitude)
                .map_err(|_| format!("v-line literal out of range '{tok}'"))?;
            if assignments.insert(var, lit > 0).is_some() {
                return Err(format!("duplicate v-line assignment for variable {var}"));
            }
        }
        Ok(ParsedModel::Sparse(assignments))
    };
    let parse_dense = || -> std::result::Result<ParsedModel, String> {
        let mut bits = Vec::new();
        for character in v_line.chars() {
            match character {
                '0' => bits.push(false),
                '1' => bits.push(true),
                c if c.is_whitespace() => {}
                other => return Err(format!("invalid character '{other}' in binary v-line")),
            }
        }
        Ok(ParsedModel::Dense(bits))
    };

    let old_format = v_line
        .split_whitespace()
        .any(|token| token.contains('-') || token.chars().any(|c| c.is_ascii_digit() && c > '1'));
    let mut candidates = Vec::with_capacity(2);
    if old_format {
        candidates.push(ModelCandidate {
            model: parse_sparse()?,
            model_cost: Some(0),
            hard_violation: false,
        });
    } else {
        candidates.push(ModelCandidate {
            model: parse_dense()?,
            model_cost: Some(0),
            hard_violation: false,
        });
        // Failure here only invalidates the alternate old-format reading. The
        // dense candidate remains authoritative if its length matches.
        if let Ok(model) = parse_sparse() {
            candidates.push(ModelCandidate {
                model,
                model_cost: Some(0),
                hard_violation: false,
            });
        }
    }

    let value = |model: &ParsedModel, lit: i32| -> bool {
        let variable = lit.unsigned_abs() as usize;
        let v = match model {
            ParsedModel::Dense(bits) => bits.get(variable - 1).copied().unwrap_or(false),
            ParsedModel::Sparse(assignments) => {
                assignments.get(&variable).copied().unwrap_or(false)
            }
        };
        if lit > 0 {
            v
        } else {
            !v
        }
    };

    let summary = stream_wcnf_file(file, &mut |weight, lits| {
        for candidate in &mut candidates {
            let satisfied = lits.iter().any(|&literal| value(&candidate.model, literal));
            match weight {
                None if !satisfied => candidate.hard_violation = true,
                Some(w) if !satisfied => {
                    candidate.model_cost = candidate
                        .model_cost
                        .and_then(|model_cost| model_cost.checked_add(w));
                }
                _ => {}
            }
        }
        Ok(())
    })
    .map_err(|e| format!("re-parse failed: {e}"))?;

    let complete = |model: &ParsedModel| match model {
        ParsedModel::Dense(bits) => bits.len() == summary.num_vars,
        ParsedModel::Sparse(assignments) => {
            assignments.len() == summary.num_vars
                && assignments
                    .keys()
                    .all(|variable| *variable <= summary.num_vars)
        }
    };
    let Some(candidate) = candidates
        .iter()
        .find(|candidate| complete(&candidate.model))
    else {
        return match &candidates[0].model {
            ParsedModel::Dense(bits) => Err(format!(
                "v-line has {} values for {} variables",
                bits.len(),
                summary.num_vars
            )),
            ParsedModel::Sparse(assignments) => Err(format!(
                "v-line assigns {} bounded variables for {} variables",
                assignments.len(),
                summary.num_vars
            )),
        };
    };
    if candidate.hard_violation {
        return Err("model violates a hard clause".into());
    }
    let model_cost = candidate
        .model_cost
        .ok_or_else(|| "model cost overflows u64".to_string())?;
    if model_cost != cost {
        return Err(format!("model cost {model_cost} != reported {cost}"));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Streaming WCNF parser
// ---------------------------------------------------------------------------

/// Summary of a streamed WCNF file.
struct WcnfSummary {
    /// Declared (old format) or maximum-seen (new format) variable count.
    num_vars: usize,
}

/// Stream a WCNF file (old `p wcnf` or MSE 2022+ format), invoking
/// `on_clause(weight, literals)` per clause with `weight == None` for hard
/// clauses. Old-format clauses with weight >= top are reported as hard.
///
/// Byte-level and buffered: peak memory is one clause, regardless of file
/// size, and parsing runs at buffer speed (no UTF-8 validation, no per-line
/// allocation).
fn stream_wcnf_file(
    path: &Path,
    on_clause: &mut dyn FnMut(Option<u64>, &[i32]) -> Result<()>,
) -> Result<WcnfSummary> {
    use std::io::{BufReader, Read as _};

    let file =
        fs::File::open(path).with_context(|| format!("failed to open '{}'", path.display()))?;
    let mut reader = BufReader::with_capacity(1 << 20, file);
    let mut buf = vec![0u8; 1 << 20];

    // Tokenizer state.
    let mut token: Vec<u8> = Vec::with_capacity(32);
    let mut in_comment = false;
    // p-line collection state ('p' token seen; consume rest of line).
    let mut in_pline = false;
    let mut pline: Vec<u8> = Vec::new();

    // Record state.
    let mut weight: Option<Option<u64>> = None; // None = expecting head
    let mut clause: Vec<i32> = Vec::new();

    // Header info.
    let mut declared_vars: Option<usize> = None;
    let mut old_top: Option<u64> = None;
    let mut max_var: usize = 0;

    let flush_token = |token: &mut Vec<u8>,
                       weight: &mut Option<Option<u64>>,
                       clause: &mut Vec<i32>,
                       old_top: &Option<u64>,
                       max_var: &mut usize,
                       on_clause: &mut dyn FnMut(Option<u64>, &[i32]) -> Result<()>|
     -> Result<()> {
        if token.is_empty() {
            return Ok(());
        }
        match *weight {
            None => {
                // Head of a clause record: 'h', or a numeric weight.
                if token.as_slice() == b"h" {
                    *weight = Some(None);
                } else {
                    let w = parse_u64(token)
                        .with_context(|| format!("invalid clause weight '{}'", lossy(token)))?;
                    let hard = old_top.is_some_and(|top| w >= top);
                    if !hard && w == 0 {
                        bail!("soft weight must be positive");
                    }
                    *weight = Some(if hard { None } else { Some(w) });
                }
            }
            Some(w) => {
                let lit = parse_i32(token)
                    .with_context(|| format!("invalid literal '{}'", lossy(token)))?;
                if lit == 0 {
                    on_clause(w, clause)?;
                    clause.clear();
                    *weight = None;
                } else {
                    *max_var = (*max_var).max(lit.unsigned_abs() as usize);
                    clause.push(lit);
                }
            }
        }
        token.clear();
        Ok(())
    };

    loop {
        let n = reader.read(&mut buf).context("read failed")?;
        if n == 0 {
            break;
        }
        for &byte in &buf[..n] {
            if in_comment {
                if byte == b'\n' {
                    in_comment = false;
                }
                continue;
            }
            if in_pline {
                if byte == b'\n' {
                    in_pline = false;
                    let text = String::from_utf8_lossy(&pline);
                    let fields: Vec<&str> = text.split_whitespace().collect();
                    if fields.len() < 3 || fields[0] != "wcnf" {
                        bail!("expected 'p wcnf <vars> <clauses> [top]'");
                    }
                    declared_vars = Some(fields[1].parse().context("invalid variable count")?);
                    if let Some(top) = fields.get(3) {
                        old_top = Some(top.parse().context("invalid top weight")?);
                    }
                    pline.clear();
                } else {
                    pline.push(byte);
                }
                continue;
            }
            if byte.is_ascii_whitespace() {
                flush_token(
                    &mut token,
                    &mut weight,
                    &mut clause,
                    &old_top,
                    &mut max_var,
                    on_clause,
                )?;
                continue;
            }
            // Comment / p-line markers are only valid at a record head with
            // an empty token.
            if token.is_empty() && weight.is_none() {
                if byte == b'c' {
                    in_comment = true;
                    continue;
                }
                if byte == b'p' {
                    in_pline = true;
                    continue;
                }
            }
            token.push(byte);
        }
    }
    flush_token(
        &mut token,
        &mut weight,
        &mut clause,
        &old_top,
        &mut max_var,
        on_clause,
    )?;

    if weight.is_some() {
        bail!("clause missing terminating 0");
    }

    let num_vars = declared_vars.unwrap_or(max_var).max(max_var);
    Ok(WcnfSummary { num_vars })
}

fn lossy(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

fn parse_u64(bytes: &[u8]) -> Result<u64> {
    if bytes.is_empty() {
        bail!("empty number");
    }
    let mut value: u64 = 0;
    for &b in bytes {
        if !b.is_ascii_digit() {
            bail!("not a number");
        }
        value = value
            .checked_mul(10)
            .and_then(|v| v.checked_add(u64::from(b - b'0')))
            .context("weight overflows u64")?;
    }
    Ok(value)
}

fn parse_i32(bytes: &[u8]) -> Result<i32> {
    let (negative, digits) = match bytes.split_first() {
        Some((b'-', rest)) => (true, rest),
        _ => (false, bytes),
    };
    if digits.is_empty() {
        bail!("empty literal");
    }
    let mut value: i64 = 0;
    for &b in digits {
        if !b.is_ascii_digit() {
            bail!("not a number");
        }
        value = value * 10 + i64::from(b - b'0');
        if value > i64::from(i32::MAX) {
            bail!("literal overflows i32");
        }
    }
    Ok(if negative {
        -value as i32
    } else {
        value as i32
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Read as _;

    /// Collect a WCNF text into (num_vars, hard, soft) via the streaming
    /// parser.
    #[allow(clippy::type_complexity)]
    fn parse_text(text: &str) -> (usize, Vec<Vec<i32>>, Vec<(u64, Vec<i32>)>) {
        let dir = std::env::temp_dir().join(format!(
            "ay-maxsat-parse-{}-{:p}",
            std::process::id(),
            text.as_ptr()
        ));
        fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("in.wcnf");
        fs::write(&path, text).expect("write");
        let mut hard = Vec::new();
        let mut soft = Vec::new();
        let summary = stream_wcnf_file(&path, &mut |weight, lits| {
            match weight {
                None => hard.push(lits.to_vec()),
                Some(w) => soft.push((w, lits.to_vec())),
            }
            Ok(())
        })
        .expect("parse");
        fs::remove_dir_all(&dir).ok();
        (summary.num_vars, hard, soft)
    }

    #[test]
    fn watchdog_registration_ids_advance_and_fail_closed_at_exhaustion() {
        let server = MaxSatWatchdogServer::new(OomGuardSource::Embedded);
        assert_eq!(server.reserve_watch_id().expect("reserve first ID"), 1);
        assert_eq!(server.next_id.load(Ordering::Relaxed), 2);

        server.next_id.store(u64::MAX, Ordering::Relaxed);
        assert!(server.reserve_watch_id().is_err());
        assert_eq!(server.next_id.load(Ordering::Relaxed), u64::MAX);
    }

    #[test]
    fn parses_new_maxsat_format() {
        let (num_vars, hard, soft) = parse_text("c new format\nh 1 2 0\n3 -1 0\n");
        assert_eq!(num_vars, 2);
        assert_eq!(hard, vec![vec![1, 2]]);
        assert_eq!(soft, vec![(3, vec![-1])]);
    }

    #[test]
    fn parses_old_wcnf_top_as_hard() {
        let (num_vars, hard, soft) = parse_text("p wcnf 2 2 10\n10 1 0\n2 -1 2 0\n");
        assert_eq!(num_vars, 2);
        assert_eq!(hard, vec![vec![1]]);
        assert_eq!(soft, vec![(2, vec![-1, 2])]);
    }

    #[test]
    fn parses_multiline_clauses_and_missing_newline() {
        let (num_vars, hard, soft) = parse_text("h 1\n 2 0\n5 -2\n-1 0");
        assert_eq!(num_vars, 2);
        assert_eq!(hard, vec![vec![1, 2]]);
        assert_eq!(soft, vec![(5, vec![-2, -1])]);
    }

    #[test]
    fn field_csv_roundtrip() {
        let dir = std::env::temp_dir().join(format!("ay-maxsat-field-{}", std::process::id()));
        fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("field.csv");
        fs::write(&path, "instance,o_value,S1,S2\na.wcnf,5,1.5,\nb.wcnf,,,\n").expect("write");
        let field = parse_field_csv(&path).expect("parse");
        assert_eq!(field.solvers, vec!["S1", "S2"]);
        let a = field.rows.get("a.wcnf").expect("row a");
        assert_eq!(a.o_value, Some(5));
        assert_eq!(a.times, vec![Some(1.5), None]);
        let b = field.rows.get("b.wcnf").expect("row b");
        assert_eq!(b.o_value, None);
        assert_eq!(b.times, vec![None, None]);
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn verify_model_accepts_both_v_line_formats() {
        let dir = std::env::temp_dir().join(format!("ay-maxsat-vfmt-{}", std::process::id()));
        fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("t.wcnf");
        fs::write(&path, "h 1 2 0\n3 -1 0\n2 2 0\n").expect("write");
        // New format: one long 0/1 token (UWrMaxSat -bm style).
        assert!(verify_model(&path, Some("11"), 3).is_ok());
        // New format: spaced bits.
        assert!(verify_model(&path, Some("1 1"), 3).is_ok());
        // Old format: signed decimal literals.
        assert!(verify_model(&path, Some("1 2 0"), 3).is_ok());
        // Model ¬1, 2 satisfies the hard clause and BOTH softs: cost 0.
        assert!(verify_model(&path, Some("-1 2 0"), 0).is_ok());
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn verify_model_disambiguates_one_variable_old_format() {
        let dir = std::env::temp_dir().join(format!("ay-maxsat-vone-{}", std::process::id()));
        fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("t.wcnf");
        fs::write(&path, "h 1 0\n").expect("write");
        // `1 0` used to be treated as two binary values and rejected even
        // though it is the canonical old-format assignment plus terminator.
        assert!(verify_model(&path, Some("1 0"), 0).is_ok());
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn verify_model_checks_cost() {
        let dir = std::env::temp_dir().join(format!("ay-maxsat-verify-{}", std::process::id()));
        fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("t.wcnf");
        fs::write(&path, "h 1 2 0\n3 -1 0\n2 2 0\n").expect("write");
        // Model 11: hard (1∨2) sat; soft ¬1 violated (3); soft 2 sat.
        assert!(verify_model(&path, Some("11"), 3).is_ok());
        assert!(verify_model(&path, Some("11"), 0).is_err());
        // Model 00 violates the hard clause.
        assert!(verify_model(&path, Some("00"), 3).is_err());
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn verify_model_rejects_malformed_binary_characters() {
        let dir = std::env::temp_dir().join(format!("ay-maxsat-vbad-{}", std::process::id()));
        fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("t.wcnf");
        fs::write(&path, "h 1 0\n").expect("write");
        let error = verify_model(&path, Some("10x1"), 0).expect_err("malformed model");
        assert!(error.contains("invalid character"), "{error}");
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn verify_model_rejects_extreme_old_format_literals_without_allocation() {
        let dir = std::env::temp_dir().join(format!("ay-maxsat-vhuge-{}", std::process::id()));
        fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("t.wcnf");
        fs::write(&path, "h 1 0\n").expect("write");
        let minimum = verify_model(&path, Some("-9223372036854775808"), 0)
            .expect_err("i64::MIN model literal");
        assert!(minimum.contains("out of range"), "{minimum}");
        let huge = verify_model(&path, Some("9223372036854775807"), 0)
            .expect_err("out-of-instance model literal");
        assert!(huge.contains("bounded variables"), "{huge}");
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn verify_model_rejects_objective_overflow() {
        let dir = std::env::temp_dir().join(format!("ay-maxsat-voverflow-{}", std::process::id()));
        fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("t.wcnf");
        fs::write(&path, format!("{} 1 0\n1 1 0\n", u64::MAX)).expect("write");
        let error = verify_model(&path, Some("0"), u64::MAX).expect_err("objective overflow");
        assert!(error.contains("overflows u64"), "{error}");
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn unvalidated_unsat_claims_never_score_or_succeed() {
        let mut field = FieldData::default();
        field.rows.insert(
            "case.wcnf".to_string(),
            FieldRow {
                o_value: Some(7),
                times: Vec::new(),
            },
        );
        let (status, detail, authority) = classify_unsat_claim(Some(&field), "case.wcnf", true);
        assert_eq!(status, RunStatus::Wrong);
        assert!(detail.contains("known feasible"));
        assert_eq!(authority, "reference field");

        let (status, detail, authority) = classify_unsat_claim(None, "case.wcnf", true);
        assert_eq!(status, RunStatus::Unvalidated);
        assert!(detail.contains("not independently proof-checked"));
        assert!(authority.contains("unvalidated"));

        let results = vec![RunResult {
            instance: "case.wcnf".to_string(),
            status,
            seconds: 0.01,
            cost: None,
            detail,
            authority,
        }];
        let summary = summarize_bench(&results, 10.0);
        assert_eq!(summary.solved, 0);
        assert_eq!(summary.unvalidated, 1);
        assert_eq!(summary.par2, 20.0);
        assert_eq!(bench_exit_code(summary), 1);
    }

    #[test]
    fn maxsat_stdout_capture_is_bounded() {
        let capture =
            MaxSatCapture::start(std::io::repeat(b'x').take((MAXSAT_CAPTURE_BYTES + 4096) as u64));
        let (output, truncated) = capture.finish();
        assert!(truncated);
        assert!(output.len() <= MAXSAT_CAPTURE_BYTES + 64);
    }

    #[test]
    fn maxsat_stdout_capture_does_not_modify_untruncated_output() {
        let input = vec![b'v'; MAXSAT_CAPTURE_BYTES / 2 + 4096];
        let capture = MaxSatCapture::start(std::io::Cursor::new(input.clone()));
        let (output, truncated) = capture.finish();
        assert!(!truncated);
        assert_eq!(output.as_bytes(), input);
    }

    #[cfg(unix)]
    #[test]
    fn maxsat_campaign_lease_excludes_second_campaign_until_drop() {
        fn acquire(lock_path: &Path, tmpdir: &Path, label: &str) -> Result<MaxSatCampaignLease> {
            let mut command = OomGuardSource::Embedded.command();
            command.env("TMPDIR", tmpdir);
            MaxSatCampaignLease::acquire_command(command, label, Stdio::null(), Some(lock_path))
        }

        let dir = std::env::temp_dir().join(format!(
            "ay-maxsat-lease-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&dir).expect("mkdir");
        let first_tmp = dir.join("first-tmp");
        let second_tmp = dir.join("second-tmp");
        fs::create_dir_all(&first_tmp).expect("first tmpdir");
        fs::create_dir_all(&second_tmp).expect("second tmpdir");
        let lock_path = dir.join("host-lease.lock");

        let first =
            acquire(&lock_path, &first_tmp, "MaxSAT lease regression first").expect("first lease");
        first.ensure_alive().expect("first lease stays alive");
        let error = acquire(&lock_path, &second_tmp, "MaxSAT lease regression blocked")
            .expect_err("a concurrent campaign must not acquire the same host lease");
        assert!(
            error.to_string().contains("lease"),
            "unexpected acquisition error: {error:#}"
        );

        drop(first);
        let replacement = acquire(
            &lock_path,
            &second_tmp,
            "MaxSAT lease regression replacement",
        )
        .expect("replacement lease");
        replacement
            .ensure_alive()
            .expect("replacement lease stays alive");
        drop(replacement);
        fs::remove_dir_all(&dir).ok();
    }

    #[cfg(unix)]
    #[test]
    fn maxsat_campaign_lease_detects_early_sidecar_exit() {
        let dir = std::env::temp_dir().join(format!(
            "ay-maxsat-lease-death-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&dir).expect("mkdir");
        let command = OomGuardSource::Embedded.command();
        let lock_path = dir.join("host-lease.lock");
        let lease = MaxSatCampaignLease::acquire_command(
            command,
            "MaxSAT lease death regression",
            Stdio::null(),
            Some(&lock_path),
        )
        .expect("lease");
        lease.kill_process_for_test();
        let error = lease
            .ensure_alive()
            .expect_err("a dead lease sidecar must fail the campaign closed");
        assert!(error.to_string().contains("exited early"), "{error:#}");
        drop(lease);
        fs::remove_dir_all(&dir).ok();
    }

    #[cfg(all(
        unix,
        any(
            target_os = "android",
            target_os = "freebsd",
            target_os = "haiku",
            all(target_os = "linux", not(target_env = "uclibc")),
        )
    ))]
    fn spawn_maxsat_watchdog_test_child(script: &str) -> Child {
        let mut command = OomGuardSource::Embedded.command();
        command
            .arg("exec-stopped")
            .arg("--")
            .arg("sh")
            .arg("-c")
            .arg(script)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        isolate_maxsat_process_group(&mut command);
        command.spawn().expect("spawn stopped watchdog target")
    }

    #[cfg(all(
        unix,
        any(
            target_os = "android",
            target_os = "freebsd",
            target_os = "haiku",
            all(target_os = "linux", not(target_env = "uclibc")),
        )
    ))]
    fn resume_maxsat_watchdog_test_child(child: &Child) {
        let pid = i32::try_from(child.id()).expect("child pid");
        nix::sys::signal::killpg(
            nix::unistd::Pid::from_raw(pid),
            nix::sys::signal::Signal::SIGCONT,
        )
        .expect("resume watchdog target");
    }

    #[cfg(all(
        unix,
        any(
            target_os = "android",
            target_os = "freebsd",
            target_os = "haiku",
            all(target_os = "linux", not(target_env = "uclibc")),
        )
    ))]
    #[test]
    fn maxsat_campaign_watchdog_server_is_shared_across_children() {
        let server = MaxSatWatchdogServer::new(OomGuardSource::Embedded);
        let mut first = spawn_maxsat_watchdog_test_child("sleep 60");
        let mut second = spawn_maxsat_watchdog_test_child("sleep 60");
        wait_for_maxsat_guard_stop(&first, "first shared-watchdog target").expect("first stopped");
        let first_watch = server
            .register(first.id(), 10_000, "first shared-watchdog target", None)
            .expect("first watch");
        let server_pid = server.process_id().expect("watch-server pid");
        wait_for_maxsat_guard_stop(&second, "second shared-watchdog target")
            .expect("second stopped");
        let second_watch = server
            .register(second.id(), 10_000, "second shared-watchdog target", None)
            .expect("second watch");
        assert_eq!(
            server.process_id(),
            Some(server_pid),
            "both registrations must use one campaign watch-server"
        );

        resume_maxsat_watchdog_test_child(&first);
        resume_maxsat_watchdog_test_child(&second);
        terminate_maxsat_process_group(&mut first);
        terminate_maxsat_process_group(&mut second);
        assert!(
            !first_watch
                .finish_after_target_cleanup()
                .expect("first terminal watch result")
                .breached
        );
        assert!(
            !second_watch
                .finish_after_target_cleanup()
                .expect("second terminal watch result")
                .breached
        );
    }

    #[cfg(all(
        unix,
        any(
            target_os = "android",
            target_os = "freebsd",
            target_os = "haiku",
            all(target_os = "linux", not(target_env = "uclibc")),
        )
    ))]
    #[test]
    fn maxsat_watchdog_server_death_kills_target_descendants() {
        let dir = std::env::temp_dir().join(format!(
            "ay-maxsat-watch-server-death-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&dir).expect("mkdir");
        let descendant_file = dir.join("descendant.pid");
        let script = format!("sleep 60 & echo $! > '{}'; wait", descendant_file.display());
        let server = MaxSatWatchdogServer::new(OomGuardSource::Embedded);
        let mut child = spawn_maxsat_watchdog_test_child(&script);
        wait_for_maxsat_guard_stop(&child, "watch-server death target").expect("target stopped");
        let mut watchdog = server
            .register(child.id(), 10_000, "watch-server death target", None)
            .expect("watch registered");
        resume_maxsat_watchdog_test_child(&child);
        for _ in 0..200 {
            if descendant_file.is_file() {
                break;
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        let descendant = fs::read_to_string(&descendant_file).expect("descendant pid");

        server.kill_process_for_test();
        let mut observed_error = None;
        for _ in 0..200 {
            match watchdog.poll() {
                Err(error) => {
                    observed_error = Some(error);
                    break;
                }
                Ok(_) => std::thread::sleep(Duration::from_millis(5)),
            }
        }
        let error = observed_error.expect("watch-server death must fail the active watch closed");
        assert!(error.to_string().contains("watchdog"), "{error:#}");
        terminate_maxsat_process_group(&mut child);
        let _ = watchdog.finish_after_target_cleanup();

        let proc_stat = PathBuf::from(format!("/proc/{}/stat", descendant.trim()));
        for _ in 0..100 {
            let dead_or_zombie = fs::read_to_string(&proc_stat)
                .map(|stat| {
                    stat.rsplit(')')
                        .nth(1)
                        .is_some_and(|rest| rest.trim().starts_with('Z'))
                })
                .unwrap_or(true);
            if dead_or_zombie {
                fs::remove_dir_all(&dir).ok();
                return;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        panic!(
            "descendant {} survived watch-server failure",
            descendant.trim()
        );
    }

    #[cfg(all(
        unix,
        any(
            target_os = "android",
            target_os = "freebsd",
            target_os = "haiku",
            all(target_os = "linux", not(target_env = "uclibc")),
        )
    ))]
    #[test]
    fn maxsat_missing_watchdog_heartbeat_kills_active_target() {
        let dir = std::env::temp_dir().join(format!(
            "ay-maxsat-watch-heartbeat-loss-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&dir).expect("mkdir");
        let fake_server = dir.join("watch-server.py");
        fs::write(
            &fake_server,
            "import sys\nsys.stdout.write('AY_OOM_WATCHDOG_SERVER_READY_V1\\n')\nsys.stdout.flush()\nfor line in sys.stdin.buffer:\n fields=line.decode('ascii').strip().split(' ')\n if len(fields)==5 and fields[0]=='WATCH':\n  print(f'READY {fields[1]}', flush=True)\n",
        )
        .expect("write fake watch server");
        let server = MaxSatWatchdogServer::new(OomGuardSource::Checkout(fake_server));
        let mut child = spawn_maxsat_watchdog_test_child("sleep 60");
        wait_for_maxsat_guard_stop(&child, "heartbeat-loss target").expect("target stopped");
        let mut watchdog = server
            .register(child.id(), 10_000, "heartbeat-loss target", None)
            .expect("watch registered");
        resume_maxsat_watchdog_test_child(&child);

        let started = Instant::now();
        let mut observed_error = None;
        for _ in 0..300 {
            match watchdog.poll() {
                Err(error) => {
                    observed_error = Some(error);
                    break;
                }
                Ok(_) => std::thread::sleep(Duration::from_millis(10)),
            }
        }
        let error = observed_error.expect("heartbeat loss must fail the active watch closed");
        assert!(started.elapsed() < Duration::from_secs(3), "{error:#}");
        assert!(error.to_string().contains("watchdog"), "{error:#}");
        terminate_maxsat_process_group(&mut child);
        let _ = watchdog.finish_after_target_cleanup();
        drop(server);
        fs::remove_dir_all(&dir).ok();
    }

    #[cfg(all(
        unix,
        any(
            target_os = "android",
            target_os = "freebsd",
            target_os = "haiku",
            all(target_os = "linux", not(target_env = "uclibc")),
        )
    ))]
    #[test]
    fn maxsat_campaign_lease_loss_kills_active_target_descendants() {
        let dir = std::env::temp_dir().join(format!(
            "ay-maxsat-active-lease-death-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&dir).expect("mkdir");
        let descendant_file = dir.join("descendant.pid");
        let lock_path = dir.join("host-lease.lock");
        let lease = Arc::new(
            MaxSatCampaignLease::acquire_command(
                OomGuardSource::Embedded.command(),
                "active MaxSAT lease death regression",
                Stdio::null(),
                Some(&lock_path),
            )
            .expect("campaign lease"),
        );
        let server = MaxSatWatchdogServer::new(OomGuardSource::Embedded);
        let script = format!("sleep 60 & echo $! > '{}'; wait", descendant_file.display());
        let mut child = spawn_maxsat_watchdog_test_child(&script);
        wait_for_maxsat_guard_stop(&child, "active lease-death target").expect("target stopped");
        let mut watchdog = server
            .register(
                child.id(),
                10_000,
                "active lease-death target",
                Some(Arc::clone(&lease)),
            )
            .expect("watch registered");
        resume_maxsat_watchdog_test_child(&child);
        for _ in 0..200 {
            if descendant_file.is_file() {
                break;
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        let descendant = fs::read_to_string(&descendant_file).expect("descendant pid");

        lease.kill_process_for_test();
        let mut observed_error = None;
        for _ in 0..200 {
            match watchdog.poll() {
                Err(error) => {
                    observed_error = Some(error);
                    break;
                }
                Ok(_) => std::thread::sleep(Duration::from_millis(5)),
            }
        }
        let error = observed_error.expect("lease death must fail the active watch closed");
        assert!(error.to_string().contains("lease"), "{error:#}");

        terminate_maxsat_process_group(&mut child);
        watchdog.detach_campaign_lease();
        let outcome = watchdog
            .finish_after_target_cleanup()
            .expect("consume terminal watch result after known lease death");
        assert!(!outcome.breached);

        let proc_stat = PathBuf::from(format!("/proc/{}/stat", descendant.trim()));
        for _ in 0..100 {
            let dead_or_zombie = fs::read_to_string(&proc_stat)
                .map(|stat| {
                    stat.rsplit(')')
                        .nth(1)
                        .is_some_and(|rest| rest.trim().starts_with('Z'))
                })
                .unwrap_or(true);
            if dead_or_zombie {
                fs::remove_dir_all(&dir).ok();
                return;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        panic!(
            "descendant {} survived aggregate lease failure",
            descendant.trim()
        );
    }

    #[test]
    fn maxsat_watchdog_breach_attribution_uses_monotonic_trigger() {
        let breach = MaxSatWatchdogOutcome {
            breached: true,
            breach_time_ns: Some(100),
        };
        assert!(maxsat_watchdog_breached_before(breach, 100).expect("equal timestamp"));
        assert!(maxsat_watchdog_breached_before(breach, 101).expect("earlier breach"));
        assert!(!maxsat_watchdog_breached_before(breach, 99).expect("later breach"));
        assert!(!maxsat_watchdog_breached_before(
            MaxSatWatchdogOutcome {
                breached: false,
                breach_time_ns: None,
            },
            100,
        )
        .expect("non-breach"));
        assert!(maxsat_watchdog_breached_before(
            MaxSatWatchdogOutcome {
                breached: true,
                breach_time_ns: None,
            },
            100,
        )
        .is_err());
    }

    #[test]
    fn maxsat_resource_plan_persists_versioned_enforcement_provenance() {
        let plan = MaxSatResourcePlan {
            schema: MAXSAT_RESOURCE_ENVELOPE_SCHEMA_V2,
            requested_jobs: 4,
            jobs: 2,
            memlimit_mb_per_child: 2048,
            nbcore_per_child: 3,
            headroom_mb: 16_000,
            planner: "embedded:scripts/_oom_guard.py".to_string(),
            planner_protocol: MAXSAT_RESOURCE_PLANNER_PROTOCOL_V1,
            enforcement: MAXSAT_CHILD_ENFORCEMENT_V1,
            solver_environment: MAXSAT_SOLVER_ENVIRONMENT_V1,
            aggregate_enforcement: MAXSAT_AGGREGATE_ENFORCEMENT_V1,
            lease_protocol: MAXSAT_LEASE_PROTOCOL_V1,
            lease_readiness: MAXSAT_LEASE_READINESS_V1,
            lease_location: MAXSAT_LEASE_LOCATION_V1,
        };
        let value = serde_json::to_value(plan).expect("serialize resource plan");
        assert_eq!(
            value["schema"],
            serde_json::json!("ay.maxsat-resource-envelope/v2")
        );
        assert_eq!(
            value["planner_protocol"],
            serde_json::json!("ay-oom-guard-plan/v1")
        );
        assert_eq!(
            value["enforcement"],
            serde_json::json!("ay-resource-v1:rss-watchdog-zero-grace")
        );
        assert_eq!(
            value["solver_environment"],
            serde_json::json!("ay-maxsat-solver-env/v1:MEMLIMIT+NBCORE")
        );
        assert_eq!(
            value["aggregate_enforcement"],
            serde_json::json!("ay-host-exclusive-flock-v1")
        );
        assert_eq!(
            value["lease_protocol"],
            serde_json::json!("ay-oom-guard-lease-sidecar/v1")
        );
        assert_eq!(
            value["lease_readiness"],
            serde_json::json!("AY_OOM_HARNESS_LEASE_READY_V1")
        );
        assert_eq!(
            value["lease_location"],
            serde_json::json!("ay-host-user-lock-path/v1:/tmp/ay-oom-guard-<uid>.lock")
        );
    }

    #[cfg(unix)]
    #[test]
    fn maxsat_runner_reaps_descendants_and_applies_core_envelope() {
        use std::os::unix::fs::PermissionsExt as _;

        let dir = std::env::temp_dir().join(format!(
            "ay-maxsat-runner-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&dir).expect("mkdir");
        let solver = dir.join("solver.sh");
        let pid_file = dir.join("descendant.pid");
        let env_file = dir.join("nbcore.txt");
        fs::write(
            &solver,
            format!(
                "#!/bin/sh\nsleep 60 &\necho $! > '{}'\necho \"${{NBCORE:-}}\" > '{}'\nprintf 's UNKNOWN\\n'\n",
                pid_file.display(),
                env_file.display()
            ),
        )
        .expect("write solver");
        let mut permissions = fs::metadata(&solver).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&solver, permissions).expect("chmod");
        let input = dir.join("case.wcnf");
        fs::write(&input, "h 1 0\n").expect("write input");
        let lease_command = OomGuardSource::Embedded.command();
        let lease_lock_path = dir.join("host-lease.lock");
        let campaign_lease = MaxSatCampaignLease::acquire_command(
            lease_command,
            "MaxSAT runner test",
            Stdio::null(),
            Some(&lease_lock_path),
        )
        .expect("campaign lease");
        let resources = MaxSatResources {
            plan: MaxSatResourcePlan {
                schema: MAXSAT_RESOURCE_ENVELOPE_SCHEMA_V2,
                requested_jobs: 1,
                jobs: 1,
                memlimit_mb_per_child: 10_000,
                nbcore_per_child: 3,
                headroom_mb: 16_000,
                planner: "test".to_string(),
                planner_protocol: MAXSAT_RESOURCE_PLANNER_PROTOCOL_V1,
                enforcement: MAXSAT_CHILD_ENFORCEMENT_V1,
                solver_environment: MAXSAT_SOLVER_ENVIRONMENT_V1,
                aggregate_enforcement: MAXSAT_AGGREGATE_ENFORCEMENT_V1,
                lease_protocol: MAXSAT_LEASE_PROTOCOL_V1,
                lease_readiness: MAXSAT_LEASE_READINESS_V1,
                lease_location: MAXSAT_LEASE_LOCATION_V1,
            },
            guard: OomGuardSource::Checkout(locate_oom_guard().expect("oom guard")),
            campaign_lease: Arc::new(campaign_lease),
            watchdog_server: MaxSatWatchdogServer::new(OomGuardSource::Checkout(
                locate_oom_guard().expect("oom guard"),
            )),
        };
        let external = ("fake".to_string(), vec![solver.display().to_string()]);
        let result = run_one(
            Path::new("unused-ay"),
            Some(&external),
            &input,
            5.0,
            false,
            None,
            &resources,
        );
        assert_eq!(result.status, RunStatus::Timeout, "{}", result.detail);
        assert_eq!(fs::read_to_string(env_file).unwrap().trim(), "3");
        let descendant = fs::read_to_string(pid_file).unwrap();
        let proc_stat = PathBuf::from(format!("/proc/{}/stat", descendant.trim()));
        for _ in 0..100 {
            let dead_or_zombie = fs::read_to_string(&proc_stat)
                .map(|stat| {
                    stat.rsplit(')')
                        .nth(1)
                        .is_some_and(|rest| rest.trim().starts_with('Z'))
                })
                .unwrap_or(true);
            if dead_or_zombie {
                fs::remove_dir_all(&dir).ok();
                return;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        panic!(
            "descendant {} survived process-group cleanup",
            descendant.trim()
        );
    }
}
