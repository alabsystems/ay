// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Local campaign restrictions. Neither these measurements nor the private
//! campaign flock confer a Targo/Host shared-machine resource claim.

use super::{BenchError, ResourcePlan, Result};

const MIB: usize = 1024 * 1024;
const CHILD_FLOOR_MIB: usize = 1024;
mod planning;

use ay_sys::supervisor::process_group::{process_groups_sample, ProcessIdentity};
use std::collections::BTreeMap;
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

// Preserve the existing watchdog's sampling cadence and health deadline.
const SAMPLE_INTERVAL: Duration = Duration::from_millis(20);
const HEARTBEAT_LIMIT: Duration = Duration::from_secs(1);

#[derive(Clone, Debug)]
enum Observation {
    Running,
    Complete,
    Breach(u64),
    Refused(String),
}

#[derive(Clone)]
struct Entry {
    identity: ProcessIdentity,
    bytes: u64,
    outcome: Arc<Mutex<Observation>>,
}

struct Census {
    entries: BTreeMap<u32, Entry>,
    heartbeat: Instant,
    refusal: Option<String>,
}

struct Shared {
    census: Mutex<Census>,
    changed: Condvar,
    stopped: AtomicBool,
}

/// One native sampler for all original children in a campaign. Observations
/// never authorize signals: the caller must retain the actual unreaped Child.
pub(super) struct Observer {
    shared: Arc<Shared>,
    thread: Option<std::thread::JoinHandle<()>>,
    jobs: usize,
}

pub(super) struct Watch {
    shared: Arc<Shared>,
    identity: ProcessIdentity,
    outcome: Arc<Mutex<Observation>>,
}

impl std::fmt::Debug for Observer {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Observer")
            .field("jobs", &self.jobs)
            .finish_non_exhaustive()
    }
}

impl std::fmt::Debug for Watch {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Watch")
            .field("identity", &self.identity)
            .finish_non_exhaustive()
    }
}

impl Observer {
    #[cfg(test)]
    pub(super) fn registered_children(&self) -> usize {
        self.shared.census.lock().unwrap().entries.len()
    }

    #[cfg(test)]
    fn stop_for_test(&self) {
        self.shared.stopped.store(true, Ordering::Release);
        self.shared.changed.notify_all();
    }

    pub(super) fn new(jobs: usize) -> Result<Self> {
        if jobs == 0 {
            return Err(BenchError::msg(
                "native observer requires positive concurrency",
            ));
        }
        let shared = Arc::new(Shared {
            census: Mutex::new(Census {
                entries: BTreeMap::new(),
                heartbeat: Instant::now(),
                refusal: None,
            }),
            changed: Condvar::new(),
            stopped: AtomicBool::new(false),
        });
        let worker = Arc::clone(&shared);
        let thread = std::thread::Builder::new()
            .name("ay-bench-rss".into())
            .spawn(move || observe(worker))?;
        Ok(Self {
            shared,
            thread: Some(thread),
            jobs,
        })
    }

    pub(super) fn register(&self, child: &std::process::Child, limit_mib: usize) -> Result<Watch> {
        let bytes = u64::try_from(limit_mib)
            .ok()
            .and_then(|value| value.checked_mul(MIB as u64))
            .filter(|value| *value > 0)
            .ok_or_else(|| BenchError::msg("invalid native RSS limit"))?;
        let identity = ay_sys::supervisor::process_group::process_identity(child.id())?
            .ok_or_else(|| BenchError::msg("native watch target vanished"))?;
        if identity.parent != std::process::id() || identity.group != child.id() {
            return Err(BenchError::msg(
                "native watch requires the original isolated child",
            ));
        }
        if !matches!(
            super::observe_child_unreaped(child, true, "native watch")?,
            super::UnreapedChildState::Stopped(nix::sys::signal::Signal::SIGSTOP)
        ) {
            return Err(BenchError::msg(
                "native watch requires the stopped launch barrier",
            ));
        }
        let mut census = self
            .shared
            .census
            .lock()
            .map_err(|_| BenchError::msg("native observer mutex poisoned"))?;
        check_census(&mut census)?;
        if census.entries.len() >= self.jobs || census.entries.contains_key(&identity.pid) {
            return Err(BenchError::msg("native campaign concurrency is exhausted"));
        }
        let outcome = Arc::new(Mutex::new(Observation::Running));
        census.entries.insert(
            identity.pid,
            Entry {
                identity,
                bytes,
                outcome: Arc::clone(&outcome),
            },
        );
        self.shared.changed.notify_all();
        Ok(Watch {
            shared: Arc::clone(&self.shared),
            identity,
            outcome,
        })
    }
}

fn check_census(census: &mut Census) -> Result<()> {
    if census.heartbeat.elapsed() > HEARTBEAT_LIMIT {
        census
            .refusal
            .get_or_insert_with(|| "native campaign observer heartbeat expired".into());
    }
    if let Some(reason) = &census.refusal {
        return Err(BenchError::msg(reason.clone()));
    }
    Ok(())
}

impl Watch {
    pub(super) fn identity(&self) -> ProcessIdentity {
        self.identity
    }

    pub(super) fn poll(&self) -> Result<Option<super::WatchdogOutcome>> {
        let mut census = self
            .shared
            .census
            .lock()
            .map_err(|_| BenchError::msg("native observer mutex poisoned"))?;
        let mut outcome = self
            .outcome
            .lock()
            .map_err(|_| BenchError::msg("native watch outcome mutex poisoned"))?;
        match &*outcome {
            Observation::Running => {
                if self.shared.stopped.load(Ordering::Acquire) {
                    return Err(BenchError::msg("native campaign observer owner was lost"));
                }
                if let Err(error) = check_census(&mut census) {
                    *outcome = Observation::Refused(error.to_string());
                    return Err(error);
                }
                Ok(None)
            }
            Observation::Complete => Ok(Some(super::WatchdogOutcome {
                breached: false,
                breach_time_ns: None,
            })),
            Observation::Breach(time) => Ok(Some(super::WatchdogOutcome {
                breached: true,
                breach_time_ns: Some(*time),
            })),
            Observation::Refused(reason) => Err(BenchError::msg(reason.clone())),
        }
    }
}

impl Drop for Watch {
    fn drop(&mut self) {
        if let Ok(mut census) = self.shared.census.lock() {
            // The immutable birth identity prevents an old handle removing a
            // later registration. Dropping an observer NEVER signals the group.
            if census
                .entries
                .get(&self.identity.pid)
                .is_some_and(|entry| entry.identity == self.identity)
            {
                census.entries.remove(&self.identity.pid);
            }
        }
    }
}

impl Drop for Observer {
    fn drop(&mut self) {
        self.shared.stopped.store(true, Ordering::Release);
        self.shared.changed.notify_all();
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

fn observe(shared: Arc<Shared>) {
    while !shared.stopped.load(Ordering::Acquire) {
        let entries = {
            let Ok(mut census) = shared.census.lock() else {
                return;
            };
            let _ = check_census(&mut census);
            census.entries.values().cloned().collect::<Vec<_>>()
        };
        let groups = entries
            .iter()
            .map(|entry| entry.identity.group)
            .collect::<Vec<_>>();
        // One existing native group census serves every registration. This
        // code observes only; the retained Child owner performs all cleanup.
        // No registration lock spans kernel observation: the actual Child
        // owner can still poll its deadline/heartbeat if a census is slow.
        let samples = process_groups_sample(&groups);
        let available = if groups.is_empty() {
            Some(usize::MAX)
        } else {
            ay_sys::observed_available_memory_bytes()
        };
        let now = super::monotonic_time_ns();
        let sample_error = samples.as_ref().err().filter(|error| {
            !ay_sys::supervisor::process_group::is_census_member_disappearance(error)
        });
        let refusal = if available.is_none() {
            Some("native available-memory observation failed".to_owned())
        } else if available.is_some_and(|bytes| bytes < CHILD_FLOOR_MIB * MIB) {
            Some("native campaign stopped for machine memory pressure".to_owned())
        } else if let Some(error) = sample_error {
            Some(format!("native group census failed: {error}"))
        } else if let Err(error) = &now {
            Some(error.to_string())
        } else {
            None
        };
        let Ok(mut census) = shared.census.lock() else {
            return;
        };
        let _ = check_census(&mut census);
        if let Some(reason) = refusal {
            census.refusal.get_or_insert(reason);
        }
        for entry in entries {
            if !census
                .entries
                .get(&entry.identity.pid)
                .is_some_and(|current| {
                    current.identity == entry.identity
                        && Arc::ptr_eq(&current.outcome, &entry.outcome)
                })
            {
                continue;
            }
            let Ok(mut outcome) = entry.outcome.lock() else {
                continue;
            };
            if !matches!(*outcome, Observation::Running) {
                continue;
            }
            if let Some(reason) = &census.refusal {
                *outcome = Observation::Refused(reason.clone());
                continue;
            }
            if let (Ok(samples), Ok(now)) = (&samples, &now) {
                let Some(sample) = samples.get(&entry.identity.group) else {
                    *outcome = Observation::Refused("native group sample missing".into());
                    continue;
                };
                if sample
                    .members
                    .iter()
                    .any(|member| member.pid == entry.identity.pid && *member != entry.identity)
                {
                    *outcome =
                        Observation::Refused("native original child identity changed".into());
                } else if sample.resident_bytes > entry.bytes {
                    *outcome = Observation::Breach(*now);
                } else if sample.live_members.is_empty() {
                    *outcome = Observation::Complete;
                }
            }
        }
        // A member exiting between the kernel's membership and identity reads
        // is incomplete evidence, not an empty-group witness or a fatal birth
        // mismatch. Retry at the same cadence without refreshing the last
        // complete-census heartbeat; persistent incompleteness still refuses.
        if samples.is_ok() {
            census.heartbeat = Instant::now();
        }
        let waited = shared.changed.wait_timeout(census, SAMPLE_INTERVAL);
        if waited.is_err() {
            return;
        }
    }
}

/// The SAME legacy host/user flock, held by the actual campaign instead of
/// a Python process. It excludes cooperating AY campaigns only; it is not a
/// shared-machine CPU or memory reservation.
#[cfg(unix)]
#[derive(Debug)]
pub(super) struct CampaignLease {
    file: std::fs::File,
    path: std::path::PathBuf,
    owner: ay_sys::supervisor::process_group::ProcessIdentity,
    refusal: std::sync::OnceLock<String>,
}

#[cfg(unix)]
impl CampaignLease {
    pub(super) fn acquire(path: &std::path::Path, label: &str) -> Result<Self> {
        use std::io::{Seek as _, Write as _};
        use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};
        if label.len() > 512 || label.chars().any(char::is_control) {
            return Err(BenchError::msg("invalid aggregate lease label"));
        }
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_CLOEXEC)
            .open(path)?;
        let metadata = file.metadata()?;
        if !metadata.is_file()
            || metadata.uid() != nix::unistd::getuid().as_raw()
            || metadata.nlink() != 1
            || metadata.mode() & 0o077 != 0
        {
            return Err(BenchError::msg("unsafe aggregate lease file metadata"));
        }
        let mut file = file;
        // Flock<T>::Drop calls LOCK_UN explicitly, which could unlock an
        // original parent's shared open-file-description from a forked child.
        // Close-only owned File retirement preserves the kernel's last-owner
        // release semantics; this local safe syscall wrapper is intentional.
        #[expect(
            deprecated,
            reason = "close-only file ownership must not issue foreign-process LOCK_UN on Drop"
        )]
        {
            use std::os::fd::AsRawFd as _;
            nix::fcntl::flock(
                file.as_raw_fd(),
                nix::fcntl::FlockArg::LockExclusiveNonblock,
            )
            .map_err(|error| {
                BenchError::msg(format!("aggregate campaign lease unavailable: {error}"))
            })?;
        }
        let owner = ay_sys::supervisor::process_group::process_identity(std::process::id())?
            .ok_or_else(|| BenchError::msg("campaign identity unavailable"))?;
        // No unlink/reclaim of somebody else's held inode: a surviving leaked
        // descriptor must refuse rather than split the host exclusion domain.
        file.set_len(0)?;
        file.rewind()?;
        let acquired = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|_| BenchError::msg("aggregate lease wall clock precedes epoch"))?
            .as_secs();
        // `start=-` is the legacy protocol's conservative PID-liveness form.
        // Do not put native birth units into its platform-specific start token:
        // an old Python reclaimer could otherwise mistake this LIVE owner for
        // a recycled PID. Native readers independently retain exact birth.
        writeln!(
            file,
            "pid={} acquired={acquired} start=- native_birth={} label={label}",
            owner.pid, owner.birth
        )?;
        file.flush()?;
        let lease = Self {
            file,
            path: path.to_owned(),
            owner,
            refusal: std::sync::OnceLock::new(),
        };
        lease.ensure_alive()?;
        Ok(lease)
    }

    pub(super) fn path(&self) -> &std::path::Path {
        &self.path
    }

    pub(super) fn ensure_alive(&self) -> Result<()> {
        use std::os::unix::fs::MetadataExt as _;
        if let Some(reason) = self.refusal.get() {
            return Err(BenchError::msg(reason.clone()));
        }
        let check = || -> Result<()> {
            // The private live owner cannot outlive this process and become
            // a reused PID; forked descendants have a different getpid. Keep
            // the authenticated acquisition birth without a new kernel birth
            // lookup on every child wait/poll.
            if std::process::id() != self.owner.pid {
                return Err(BenchError::msg("aggregate lease original process changed"));
            }
            let held = self.file.metadata()?;
            let visible = std::fs::symlink_metadata(&self.path)?;
            if !visible.is_file()
                || held.dev() != visible.dev()
                || held.ino() != visible.ino()
                || visible.nlink() != 1
                || visible.uid() != held.uid()
                || visible.mode() & 0o077 != 0
            {
                return Err(BenchError::msg("aggregate lease original file changed"));
            }
            Ok(())
        };
        if let Err(error) = check() {
            let reason = self.refusal.get_or_init(|| error.to_string());
            return Err(BenchError::msg(reason.clone()));
        }
        Ok(())
    }
}

/// Preserve the existing planner's headroom and child-floor policy using
/// checked native measurements. Unknown available memory is never idle RAM.
pub(super) fn plan(requested: usize, lease_path: &Path) -> Result<ResourcePlan> {
    planning::plan(requested, lease_path)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn campaign_watch_retains_sampler_until_actual_child_is_reaped() {
        let resources =
            super::super::PlannedResources::for_test(&crate::runner::repo_root_public(), 4096);
        let mut command = resources.external_command("/bin/sh");
        command.args(["-c", "exec sleep 0.05"]);
        let (mut child, watch) = resources
            .spawn_external_child(&mut command, "retained sampler")
            .unwrap();
        drop(resources);
        let outcome = super::super::wait_for_guarded_child(
            &mut child,
            watch,
            Duration::from_secs(5),
            "retained sampler",
        )
        .unwrap();
        assert!(outcome.status.is_some_and(|status| status.success()));
        assert!(!outcome.memout && !outcome.timed_out);
    }

    #[cfg(unix)]
    #[test]
    fn campaign_sampler_loss_reaps_the_guarded_child() {
        let resources =
            super::super::PlannedResources::for_test(&crate::runner::repo_root_public(), 4096);
        let mut command = resources.external_command("/bin/sh");
        command.args(["-c", "exec sleep 60"]);
        let (mut child, watch) = resources
            .spawn_external_child(&mut command, "sampler loss")
            .unwrap();
        resources.observer.stop_for_test();
        assert!(super::super::wait_for_guarded_child(
            &mut child,
            watch,
            Duration::from_secs(5),
            "sampler loss",
        )
        .is_err());
        assert!(child.try_wait().unwrap().is_some());
    }
    fn measured_plan(
        requested: usize,
        physical: usize,
        available: usize,
        cores: usize,
    ) -> Result<ResourcePlan> {
        planning::measured_plan(
            requested,
            physical,
            available,
            cores,
            &planning::Restrictions::default(),
        )
    }

    #[cfg(unix)]
    struct Target(std::process::Child);
    #[cfg(unix)]
    impl Drop for Target {
        fn drop(&mut self) {
            ay_sys::owned_child::terminate_process_group(&mut self.0);
        }
    }

    #[cfg(unix)]
    fn stopped_target() -> Target {
        use std::os::unix::process::CommandExt as _;
        let target = Target(
            std::process::Command::new("/bin/sh")
                .args(["-c", "kill -STOP $$; exec sleep 60"])
                .process_group(0)
                .spawn()
                .unwrap(),
        );
        let deadline = Instant::now() + Duration::from_secs(5);
        while !matches!(
            super::super::observe_child_unreaped(&target.0, true, "native test").unwrap(),
            super::super::UnreapedChildState::Stopped(_)
        ) {
            assert!(Instant::now() < deadline);
            std::thread::sleep(Duration::from_millis(2));
        }
        target
    }

    #[test]
    fn observed_peer_memory_reduces_concurrency_and_never_fabricates_a_child() {
        let ample = measured_plan(8, 64 * 1024, 60 * 1024, 16).unwrap();
        let occupied = measured_plan(8, 64 * 1024, 4 * 1024, 16).unwrap();
        assert_eq!(occupied.jobs, 3);
        assert!(occupied.jobs < ample.jobs);
        assert!(occupied.jobs * occupied.memlimit_mb_per_child <= 3 * 1024);
        assert!(measured_plan(8, 64 * 1024, 1024, 16).is_err());
        assert!(measured_plan(8, 64 * 1024, 0, 16).is_err());
        assert!(measured_plan(0, 64 * 1024, 60 * 1024, 16).is_err());
    }

    #[test]
    fn cpu_share_preserves_requested_memory_funded_parallelism() {
        let plan = measured_plan(3, 64 * 1024, 60 * 1024, 2).unwrap();
        assert_eq!(plan.jobs, 3);
        assert_eq!(plan.nbcore_per_child, 1);
    }

    #[cfg(unix)]
    #[test]
    fn native_lease_excludes_other_campaigns_and_releases_on_drop() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("lease");
        let first = CampaignLease::acquire(&path, "first").unwrap();
        assert!(CampaignLease::acquire(&path, "second").is_err());
        first.ensure_alive().unwrap();
        drop(first);
        CampaignLease::acquire(&path, "after original drop").unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn native_lease_contender_entry() {
        let args = std::env::args().collect::<Vec<_>>();
        if !args.iter().any(|arg| arg == "--exact") {
            return;
        }
        let Some(path) = std::env::var_os("AY_TEST_NATIVE_LEASE_PATH") else {
            return;
        };
        let expected = std::env::var("AY_TEST_NATIVE_LEASE_AVAILABLE").unwrap() == "yes";
        let acquired =
            CampaignLease::acquire(std::path::Path::new(&path), "independent native process");
        assert_eq!(acquired.is_ok(), expected);
    }

    #[cfg(unix)]
    #[test]
    fn native_lease_excludes_an_actual_other_process_until_original_drop() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("cross-process-lease");
        let lease = CampaignLease::acquire(&path, "original process").unwrap();
        let contender = |expected| {
            let mut command = std::process::Command::new(std::env::current_exe().unwrap());
            command
                .args([
                    "--exact",
                    "resource::native::tests::native_lease_contender_entry",
                    "--nocapture",
                ])
                .env("AY_TEST_NATIVE_LEASE_PATH", &path)
                .env("AY_TEST_NATIVE_LEASE_AVAILABLE", expected);
            let result = ay_sys::metadata_capture::capture(
                command,
                ay_sys::metadata_capture::CaptureLimits {
                    timeout: Duration::from_secs(5),
                    output_bytes: 64 * 1024,
                    resident_bytes: None,
                },
                "native lease contender",
            )
            .unwrap();
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
        };
        contender("no");
        lease.ensure_alive().unwrap();
        drop(lease);
        contender("yes");
    }

    #[cfg(unix)]
    #[test]
    fn restored_path_does_not_revive_an_invalidated_native_lease() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("lease");
        let saved = directory.path().join("original");
        let lease = CampaignLease::acquire(&path, "original").unwrap();
        std::fs::rename(&path, &saved).unwrap();
        assert!(lease.ensure_alive().is_err());
        std::fs::rename(saved, path).unwrap();
        assert!(lease.ensure_alive().is_err());
    }

    #[cfg(unix)]
    #[test]
    fn original_stopped_children_share_observer_and_concurrency_is_enforced() {
        use nix::sys::signal::{kill, Signal};
        use nix::unistd::Pid;
        use std::os::unix::process::CommandExt as _;
        let observer = Observer::new(1).unwrap();
        let target = Target(
            std::process::Command::new("/bin/sh")
                .args(["-c", "kill -STOP $$; exec sleep 0.05"])
                .process_group(0)
                .spawn()
                .unwrap(),
        );
        let child = &target.0;
        let deadline = Instant::now() + Duration::from_secs(5);
        while !matches!(
            super::super::observe_child_unreaped(&child, true, "native test").unwrap(),
            super::super::UnreapedChildState::Stopped(_)
        ) {
            assert!(Instant::now() < deadline);
            std::thread::sleep(Duration::from_millis(2));
        }
        let watch = observer.register(child, 4096).unwrap();
        assert!(observer.register(child, 4096).is_err());
        kill(
            Pid::from_raw(i32::try_from(child.id()).unwrap()),
            Signal::SIGCONT,
        )
        .unwrap();
        loop {
            if let Some(outcome) = watch.poll().unwrap() {
                assert!(!outcome.breached);
                break;
            }
            assert!(Instant::now() < deadline);
            std::thread::sleep(Duration::from_millis(2));
        }
    }

    #[cfg(unix)]
    #[test]
    fn native_rss_breach_is_zero_grace_and_survives_observer_owner_loss() {
        use std::os::unix::process::CommandExt as _;
        let observer = Observer::new(1).unwrap();
        let target = Target(
            std::process::Command::new("/bin/sh")
                .args(["-c", "kill -STOP $$; exec \"$@\"", "target"])
                .arg(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "resource::native::tests::native_rss_allocation_fixture",
                ])
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .process_group(0)
                .spawn()
                .unwrap(),
        );
        let deadline = Instant::now() + Duration::from_secs(5);
        while !matches!(
            super::super::observe_child_unreaped(&target.0, true, "native RSS").unwrap(),
            super::super::UnreapedChildState::Stopped(_)
        ) {
            assert!(Instant::now() < deadline);
            std::thread::sleep(Duration::from_millis(2));
        }
        let watch = observer.register(&target.0, 16).unwrap();
        nix::sys::signal::kill(
            nix::unistd::Pid::from_raw(i32::try_from(target.0.id()).unwrap()),
            nix::sys::signal::Signal::SIGCONT,
        )
        .unwrap();
        let first = loop {
            if let Some(outcome) = watch.poll().unwrap() {
                assert!(outcome.breached);
                break outcome.breach_time_ns;
            }
            assert!(Instant::now() < deadline);
            std::thread::sleep(Duration::from_millis(2));
        };
        assert!(first.is_some());
        drop(observer);
        assert_eq!(watch.poll().unwrap().unwrap().breach_time_ns, first);
    }

    #[test]
    fn native_rss_allocation_fixture() {
        // Use the maintained native_metadata_tests self-exec discrimination,
        // not a disabled test or an environment field mistaken for authority.
        let arguments = std::env::args().skip(1).collect::<Vec<_>>();
        if !arguments.iter().any(|argument| argument == "--exact")
            || !arguments.iter().any(|argument| {
                argument == "resource::native::tests::native_rss_allocation_fixture"
            })
        {
            return;
        }
        let payload = vec![0x7fu8; 32 * MIB];
        std::hint::black_box(&payload);
        std::thread::sleep(Duration::from_secs(60));
        std::hint::black_box(payload);
    }

    #[cfg(unix)]
    #[test]
    fn native_observer_owner_loss_refuses_without_signalling_the_original_child() {
        let observer = Observer::new(1).unwrap();
        let target = stopped_target();
        let watch = observer.register(&target.0, 4096).unwrap();
        drop(observer);
        assert!(watch.poll().is_err());
        assert!(watch.poll().is_err());
        assert!(matches!(
            super::super::observe_child_unreaped(&target.0, true, "owner loss").unwrap(),
            super::super::UnreapedChildState::Stopped(_)
        ));
    }
}
