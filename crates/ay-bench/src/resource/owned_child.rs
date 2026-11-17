// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Local solver custody. Pipes can be transferred; the Child/reaping authority
//! and watchdog stay together, including early return and unwinding.
use super::{BenchError, Child, Duration, GuardedChildOutcome, Result, RssWatchdog};
use ay_sys::child_pipe::ChildPipeWriter;
use std::process::{ChildStderr, ChildStdin, ChildStdout};
#[cfg(test)]
use wait_timeout::ChildExt as _;

pub(crate) struct LocalOwnedChild {
    child: Child,
    watchdog: Option<RssWatchdog>,
    #[cfg(unix)]
    identity: ay_sys::supervisor::process_group::ProcessIdentity,
    state: CleanupState,
    label: String,
}

pub(super) use ay_sys::owned_child::CleanupState;

impl LocalOwnedChild {
    pub(super) fn new(child: Child, watchdog: RssWatchdog, label: String) -> Self {
        Self {
            child,
            #[cfg(unix)]
            identity: watchdog.identity(),
            watchdog: Some(watchdog),
            state: CleanupState::Unwaited,
            label,
        }
    }

    pub(crate) fn take_stdout(&mut self) -> Option<ChildStdout> {
        self.child.stdout.take()
    }
    pub(crate) fn take_stderr(&mut self) -> Option<ChildStderr> {
        self.child.stderr.take()
    }
    pub(crate) fn take_stdin(&mut self) -> std::io::Result<ChildPipeWriter<ChildStdin>> {
        ChildPipeWriter::take_from(&mut self.child)
    }

    pub(crate) fn wait(self, timeout: Duration) -> Result<GuardedChildOutcome> {
        self.wait_with_limits(timeout, None, None)
    }

    pub(crate) fn wait_with_limits(
        mut self,
        timeout: Duration,
        file_limit: Option<(&std::path::Path, u64)>,
        abort: Option<&std::sync::atomic::AtomicBool>,
    ) -> Result<GuardedChildOutcome> {
        self.state = CleanupState::Waiting;
        let watchdog = self
            .watchdog
            .take()
            .ok_or_else(|| BenchError::msg("owned child has no watchdog"))?;
        let result = super::wait_for_guarded_child_with_limits(
            &mut self.child,
            watchdog,
            timeout,
            &self.label,
            file_limit,
            abort,
        );
        if result.is_ok() {
            self.state = CleanupState::Complete;
        }
        result
    }
    pub(crate) fn deadline(mut self) -> Result<GuardedChildOutcome> {
        self.state = CleanupState::Waiting;
        let watchdog = self
            .watchdog
            .take()
            .ok_or_else(|| BenchError::msg("owned child has no watchdog"))?;
        let result = super::terminate_after_deadline(&mut self.child, watchdog, &self.label);
        if result.is_ok() {
            self.state = CleanupState::Complete;
        }
        result
    }
    pub(crate) fn cancel(mut self) -> Result<()> {
        self.state = CleanupState::Waiting;
        let watchdog = self
            .watchdog
            .take()
            .ok_or_else(|| BenchError::msg("owned child has no watchdog"))?;
        let result = super::terminate_guarded_child(&mut self.child, watchdog, &self.label);
        if result.is_ok() {
            self.state = CleanupState::Complete;
        }
        result
    }

    fn recover_unreaped(&mut self) -> Result<()> {
        #[cfg(unix)]
        {
            recover_original_child(&mut self.child, &self.identity, &self.label).map_err(Into::into)
        }
        #[cfg(not(unix))]
        Err(BenchError::msg(
            "non-consuming child ownership unavailable; cleanup refused",
        ))
    }
}

#[cfg(unix)]
pub(super) use ay_sys::owned_child::{observe_original_unreaped, recover_original_child};

impl Drop for LocalOwnedChild {
    fn drop(&mut self) {
        if matches!(self.state, CleanupState::Complete) {
            return;
        }
        if let Some(watchdog) = self.watchdog.take() {
            // The private Child has never been handed to a consuming wait;
            // its unreaped leader still anchors all group cleanup authority.
            if super::terminate_guarded_child(&mut self.child, watchdog, &self.label).is_ok() {
                return;
            }
        }
        let _ = self.recover_unreaped();
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::process::CommandExt as _;

    #[test]
    fn changed_group_cleanup_kills_only_the_original_child() {
        use nix::sys::wait::{waitpid, WaitPidFlag, WaitStatus};
        use nix::unistd::Pid;
        const CHILD_GROUP: &str = "AY_TEST_OWNED_CHILD_JOIN_GROUP";
        if let Ok(group) = std::env::var(CHILD_GROUP) {
            let group = group.parse::<i32>().expect("owned sentinel group");
            assert!(group > 0);
            nix::unistd::setpgid(Pid::from_raw(0), Pid::from_raw(group))
                .expect("join the separate sentinel group");
            std::thread::sleep(Duration::from_secs(30));
            return;
        }

        // A wrong attempt to adopt the new group must hit only this owned
        // disposable sentinel, never the test runner or another machine job.
        struct Sentinel {
            child: Child,
            identity: ay_sys::supervisor::process_group::ProcessIdentity,
        }
        impl Drop for Sentinel {
            fn drop(&mut self) {
                let _ = recover_original_child(&mut self.child, &self.identity, "test sentinel");
            }
        }
        enum Cleanup {
            Drop,
            Wait,
        }
        let resources =
            super::super::PlannedResources::for_test(&crate::runner::repo_root_public(), 256);
        let test_name = std::thread::current()
            .name()
            .expect("libtest name")
            .to_owned();
        for cleanup in [Cleanup::Drop, Cleanup::Wait] {
            let sentinel = std::process::Command::new("/bin/sleep")
                .arg("30")
                .process_group(0)
                .spawn()
                .expect("spawn separate sentinel group");
            let identity = ay_sys::supervisor::process_group::process_identity(sentinel.id())
                .expect("sentinel identity")
                .expect("live sentinel");
            let mut sentinel = Sentinel {
                child: sentinel,
                identity,
            };
            let mut command =
                resources.external_command(std::env::current_exe().expect("test binary"));
            command
                .args(["--exact", &test_name, "--nocapture", "--test-threads=1"])
                .env(CHILD_GROUP, sentinel.child.id().to_string())
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null());
            let child = resources
                .spawn_owned_child(&mut command, "changed-group child")
                .expect("start original guarded child");
            let original = child.identity;
            let pid = Pid::from_raw(child.child.id() as i32);
            let started = std::time::Instant::now();
            let moved = loop {
                let actual = ay_sys::supervisor::process_group::process_identity(child.child.id())
                    .expect("observe original child group");
                if actual.is_some_and(|value| value.group == sentinel.child.id()) {
                    break true;
                }
                if started.elapsed() >= Duration::from_secs(3) {
                    break false;
                }
                std::thread::sleep(Duration::from_millis(5));
            };
            let wait_error = match cleanup {
                Cleanup::Drop => {
                    drop(child);
                    None
                }
                Cleanup::Wait => Some(
                    child
                        .wait(Duration::from_secs(1))
                        .expect_err("changed group refuses guarded result"),
                ),
            };
            let reaped = waitpid(pid, Some(WaitPidFlag::WNOHANG));
            // Clean up even if a regression left the exact original child
            // alive: a fresh kernel child observation plus matching birth and
            // parent grants only this direct-child cleanup, not a group kill.
            if matches!(reaped, Ok(WaitStatus::StillAlive)) {
                let actual = ay_sys::supervisor::process_group::process_identity(original.pid)
                    .expect("recover test child identity")
                    .expect("live test child");
                assert_eq!(
                    (actual.pid, actual.birth, actual.parent),
                    (original.pid, original.birth, original.parent)
                );
                nix::sys::signal::kill(pid, nix::sys::signal::Signal::SIGKILL)
                    .expect("clean up original test child");
                waitpid(pid, None).expect("reap original test child");
            }
            let sentinel_survived = sentinel
                .child
                .try_wait()
                .expect("sentinel status")
                .is_none();
            drop(sentinel);
            assert!(moved, "fixture did not enter the different group");
            assert_eq!(
                reaped,
                Err(nix::errno::Errno::ECHILD),
                "original child cleanup did not reap"
            );
            assert!(sentinel_survived, "cleanup signalled the adopted group");
            if let Some(error) = wait_error {
                assert!(
                    error.to_string().contains("group ownership mismatch"),
                    "{error}"
                );
            }
        }
    }

    #[test]
    fn cleanup_receipt_reaps_during_unwind_without_another_signal() {
        let mut child = std::process::Command::new("/bin/sleep")
            .arg("30")
            .process_group(0)
            .spawn()
            .expect("spawn owned group");
        let pid = nix::unistd::Pid::from_raw(child.id() as i32);
        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _cleanup = super::super::GroupCleanup::begin(&mut child)
                .expect("retain original unreaped child");
            panic!("interrupt between group cleanup and consuming reap");
        }));
        assert!(unwind.is_err());
        assert_eq!(
            nix::sys::wait::waitpid(pid, Some(nix::sys::wait::WaitPidFlag::WNOHANG)),
            Err(nix::errno::Errno::ECHILD)
        );
    }
    #[test]
    fn dropping_owned_local_child_kills_and_reaps_without_a_wait_call() {
        let resources =
            super::super::PlannedResources::for_test(&crate::runner::repo_root_public(), 64);
        let mut command = resources.external_command("/bin/sleep");
        command.arg("30");
        let child = resources
            .spawn_owned_child(&mut command, "owned child cancellation")
            .expect("spawn contained local child");
        let pid = nix::unistd::Pid::from_raw(child.child.id() as i32);
        drop(child);
        assert_eq!(
            nix::sys::wait::waitpid(pid, Some(nix::sys::wait::WaitPidFlag::WNOHANG)),
            Err(nix::errno::Errno::ECHILD),
            "owned child was already reaped"
        );
    }

    #[test]
    fn externally_reaped_child_is_an_ownership_error_not_signal_authority() {
        let resources =
            super::super::PlannedResources::for_test(&crate::runner::repo_root_public(), 64);
        let mut command = resources.external_command("/bin/sleep");
        command.arg("30");
        let mut child = resources
            .spawn_owned_child(&mut command, "external reaper control")
            .expect("spawn owned child");
        child.child.kill().expect("kill original owned child");
        let pid = nix::unistd::Pid::from_raw(child.child.id() as i32);
        nix::sys::wait::waitpid(pid, None).expect("consume status outside std Child cache");
        assert!(
            child.child.try_wait().is_err(),
            "std cache has no consumed status"
        );
        let error = child
            .wait(Duration::from_secs(1))
            .expect_err("lost parentage must fail closed");
        assert!(error.to_string().contains("observing child"), "{error}");
    }

    #[test]
    fn stale_birth_recovery_cannot_signal_another_live_owned_child() {
        let mut child = std::process::Command::new("/bin/sleep")
            .arg("30")
            .process_group(0)
            .spawn()
            .expect("spawn unrelated live group");
        let mut stale = ay_sys::supervisor::process_group::process_identity(child.id())
            .expect("observe live child")
            .expect("live birth");
        stale.birth = stale.birth.checked_add(1).expect("native birth has room");
        let result = recover_original_child(&mut child, &stale, "stale birth control");
        let survived = child
            .wait_timeout(Duration::from_millis(100))
            .expect("observe unrelated group");
        let _ = child.kill();
        let _ = child.wait();
        assert!(result.is_err(), "stale birth granted recovery authority");
        assert!(
            survived.is_none(),
            "recovery signalled the unrelated process"
        );
    }
}
