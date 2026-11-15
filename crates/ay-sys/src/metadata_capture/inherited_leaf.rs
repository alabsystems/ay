// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A bounded MD5 leaf under an existing outer process-group supervisor.
//!
//! This API grants no admission or memory policy. The caller MUST already run
//! under an admitted supervisor which owns its process group, bounds aggregate
//! RSS and wall time, and terminates the whole group on completion or failure.
//! The MD5 process inherits that group: this code never calls setpgid/setsid or
//! signals a process group. Local timeout/output cleanup signals and reaps only
//! the exact original child, retaining non-consuming parentage and birth checks.
//! Only the platform's known, non-spawning MD5 executable is exposed publicly.

use super::PipeCaptureEvidence;
use std::io;
use std::path::Path;
use std::process::ExitStatus;
use std::time::Duration;

/// A local failure remains evidence, never a successful digest observation.
pub struct InheritedLeafOutput {
    pub status: ExitStatus,
    pub timed_out: bool,
    pub output_limit_reached: bool,
    pub stdout: PipeCaptureEvidence,
    pub stderr: PipeCaptureEvidence,
}

/// Run only `/sbin/md5 -q` on macOS or `/usr/bin/md5sum --zero --` on Linux.
/// The caller supplies an absolute path and a finite local deadline; the
/// enclosing supervisor supplies memory enforcement and final group cleanup.
#[cfg(any(
    target_os = "macos",
    all(target_os = "linux", not(target_env = "uclibc"))
))]
pub fn capture_md5(path: &Path, timeout: Duration) -> io::Result<InheritedLeafOutput> {
    if !path.is_absolute() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "inherited MD5 path must be absolute",
        ));
    }
    #[cfg(target_os = "macos")]
    let mut command = std::process::Command::new("/sbin/md5");
    #[cfg(target_os = "macos")]
    command.arg("-q").arg(path);
    #[cfg(target_os = "linux")]
    let mut command = std::process::Command::new("/usr/bin/md5sum");
    #[cfg(target_os = "linux")]
    command.arg("--zero").arg("--").arg(path);
    capture_leaf(command, timeout, 4096, "official archive MD5")
}

#[cfg(not(any(
    target_os = "macos",
    all(target_os = "linux", not(target_env = "uclibc"))
)))]
pub fn capture_md5(_path: &Path, _timeout: Duration) -> io::Result<InheritedLeafOutput> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "bounded inherited MD5 capture unavailable on this platform",
    ))
}

#[cfg(any(
    target_os = "macos",
    all(target_os = "linux", not(target_env = "uclibc"))
))]
fn capture_leaf(
    mut command: std::process::Command,
    timeout: Duration,
    output_bytes: usize,
    label: &str,
) -> io::Result<InheritedLeafOutput> {
    use super::BoundedPipeCapture;
    use crate::owned_child::{
        observe_child_unreaped, ChildEvents, CleanupState, UnreapedChildState,
    };
    use std::process::Stdio;
    use std::time::Instant;

    if timeout.is_zero() || output_bytes == 0 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "inherited leaf restrictions must be positive",
        ));
    }
    let deadline = Instant::now().checked_add(timeout).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "inherited leaf deadline overflow",
        )
    })?;
    // Deliberately inherit the outer supervisor's group. A new group here
    // would let the hash process survive cancellation of its corpus worker.
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut owned = LeafChild {
        child: command.spawn()?,
        identity: None,
        state: CleanupState::Unwaited,
    };
    match crate::supervisor::process_group::process_identity(owned.child.id()) {
        Ok(Some(identity)) => owned.identity = Some(identity),
        observation => {
            if !matches!(
                observe_child_unreaped(&owned.child, ChildEvents::Exit, label)?,
                UnreapedChildState::Exited
            ) {
                return Err(match observation {
                    Err(error) => error,
                    _ => io::Error::other("inherited leaf original child identity unavailable"),
                });
            }
        }
    }
    let stdout = BoundedPipeCapture::with_limit(
        owned
            .child
            .stdout
            .take()
            .ok_or_else(|| io::Error::other("inherited leaf stdout missing"))?,
        output_bytes,
    )?;
    let stderr = BoundedPipeCapture::with_limit(
        owned
            .child
            .stderr
            .take()
            .ok_or_else(|| io::Error::other("inherited leaf stderr missing"))?,
        output_bytes,
    )?;
    let mut timed_out = false;
    let mut output_limit_reached = false;
    loop {
        if Instant::now() >= deadline {
            timed_out = true;
            break;
        }
        if stdout.limit_breached() || stderr.limit_breached() {
            output_limit_reached = true;
            break;
        }
        if matches!(owned.observe(label)?, UnreapedChildState::Exited) {
            break;
        }
        std::thread::sleep(Duration::from_millis(5));
    }
    let status = owned.finish(label)?;
    // Finite post-exit drainage preserves partial output on timeout/overflow.
    // An inherited writer can never leave a detached reader behind.
    let stdout = stdout.finish_evidence();
    let stderr = stderr.finish_evidence();
    output_limit_reached |= stdout.incomplete || stderr.incomplete;
    Ok(InheritedLeafOutput {
        status,
        timed_out,
        output_limit_reached,
        stdout,
        stderr,
    })
}

#[cfg(any(
    target_os = "macos",
    all(target_os = "linux", not(target_env = "uclibc"))
))]
struct LeafChild {
    child: std::process::Child,
    identity: Option<crate::supervisor::process_group::ProcessIdentity>,
    state: crate::owned_child::CleanupState,
}

#[cfg(any(
    target_os = "macos",
    all(target_os = "linux", not(target_env = "uclibc"))
))]
impl LeafChild {
    fn observe(&self, label: &str) -> io::Result<crate::owned_child::UnreapedChildState> {
        match &self.identity {
            Some(identity) => {
                crate::owned_child::observe_original_unreaped(&self.child, identity, label)
            }
            None => {
                let state = crate::owned_child::observe_child_unreaped(
                    &self.child,
                    crate::owned_child::ChildEvents::Exit,
                    label,
                )?;
                if !matches!(state, crate::owned_child::UnreapedChildState::Exited) {
                    return Err(io::Error::other(
                        "inherited leaf birth unavailable for live child; cleanup refused",
                    ));
                }
                Ok(state)
            }
        }
    }

    fn finish(&mut self, label: &str) -> io::Result<ExitStatus> {
        use crate::owned_child::{CleanupState, UnreapedChildState};
        use wait_timeout::ChildExt as _;
        if !matches!(self.observe(label)?, UnreapedChildState::Exited) {
            self.child.kill()?;
        }
        // After this consuming operation, a failure must never reuse the
        // terminal-visibility exception; Drop requires a fresh original birth.
        self.state = CleanupState::Waiting;
        let status = self
            .child
            .wait_timeout(Duration::from_secs(5))?
            .ok_or_else(|| {
                io::Error::other("inherited leaf cleanup did not reap within five seconds")
            })?;
        self.state = CleanupState::Complete;
        Ok(status)
    }
}

#[cfg(any(
    target_os = "macos",
    all(target_os = "linux", not(target_env = "uclibc"))
))]
impl Drop for LeafChild {
    fn drop(&mut self) {
        use crate::owned_child::CleanupState;
        match self.state {
            CleanupState::Complete => {}
            CleanupState::Unwaited => {
                let _ = self.finish("inherited leaf failure cleanup");
            }
            CleanupState::Waiting => {
                if let Some(identity) = self.identity {
                    let _ = crate::owned_child::recover_original_child(
                        &mut self.child,
                        &identity,
                        "inherited leaf consuming recovery",
                    );
                }
            }
        }
        // Refused custody or an uninterruptible child remains with the outer
        // group owner; this leaf helper never manufactures group authority.
    }
}

#[cfg(all(
    test,
    any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    )
))]
mod tests {
    use super::*;
    use std::process::Command;

    #[test]
    fn child_inherits_outer_group() {
        const PROBE: &str = "AY_INHERITED_LEAF_GROUP_PROBE";
        if std::env::var_os(PROBE).is_some() {
            // SAFETY: getpgrp takes no arguments, borrows no storage and only
            // observes this test process's current kernel process group.
            println!("inherited-leaf-group={}", unsafe { libc::getpgrp() });
            return;
        }
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args([
                "--exact",
                "metadata_capture::inherited_leaf::tests::child_inherits_outer_group",
                "--nocapture",
            ])
            .env(PROBE, "1");
        let output = capture_leaf(
            command,
            Duration::from_secs(5),
            8192,
            "inherited group probe",
        )
        .unwrap();
        assert!(output.status.success());
        assert!(!output.timed_out && !output.output_limit_reached);
        // SAFETY: getpgrp is a scalar read of the current process's group.
        let group = unsafe { libc::getpgrp() };
        assert!(output
            .stdout
            .text
            .contains(&format!("inherited-leaf-group={group}")));
    }

    #[test]
    fn local_timeout_is_retained_without_signalling_our_group() {
        let mut command = Command::new("/bin/sleep");
        command.arg("30");
        let output =
            capture_leaf(command, Duration::from_millis(20), 256, "inherited timeout").unwrap();
        assert!(output.timed_out);
        assert!(!output.status.success());
        assert!(!output.output_limit_reached);
    }

    #[test]
    fn output_limit_retains_partial_failure_evidence() {
        let output = capture_leaf(
            Command::new("/usr/bin/yes"),
            Duration::from_secs(5),
            256,
            "inherited output limit",
        )
        .unwrap();
        assert!(!output.status.success());
        assert!(!output.timed_out);
        assert!(output.output_limit_reached);
        assert!(!output.stdout.text.is_empty());
        assert!(output.stdout.text.len() <= 256);
        assert!(output.stdout.incomplete);
    }
}
