// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Local bounded metadata execution; observations and limits confer no shared
//! machine reservation or SolverHost authority. Cleanup retains the original
//! unreaped Child, never an arbitrary PID or a group it joined later.
#[cfg(unix)]
use crate::owned_child::{
    self, observe_child_unreaped, terminate_process_group, ChildEvents, GroupCleanup,
    UnreapedChildState,
};
use std::io;
#[cfg(unix)]
use std::process::{Child, Stdio};
use std::process::{Command, Output};
use std::time::Duration;
#[cfg(unix)]
use std::time::Instant;
pub mod inherited_leaf;
mod pipe;
pub use pipe::{BoundedPipeCapture, PipeCaptureEvidence, DEFAULT_OUTPUT_BYTES};

#[derive(Debug)]
struct ResidentLimitExceeded(String);

impl std::fmt::Display for ResidentLimitExceeded {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{}: exceeded metadata group RSS limit", self.0)
    }
}

impl std::error::Error for ResidentLimitExceeded {}

/// Whether capture itself stopped the original group at its RSS restriction.
/// An OS allocation/spawn error or matching error text is not this evidence.
pub fn is_resident_limit(error: &io::Error) -> bool {
    error
        .get_ref()
        .is_some_and(|cause| cause.is::<ResidentLimitExceeded>())
}

/// Restrictions only, never admission. RSS is sampled over the original
/// isolated group; a scalar here is not an installed kernel memory policy.
#[derive(Clone, Copy)]
pub struct CaptureLimits {
    pub timeout: Duration,
    pub output_bytes: usize,
    pub resident_bytes: Option<u64>,
}

/// Run one short native metadata command. Wall execution, retained output and
/// optional sampled group RSS are bounded. Cleanup can require up to five
/// additional seconds for an uninterruptible child; failure never yields data.
#[cfg(any(
    target_os = "macos",
    all(target_os = "linux", not(target_env = "uclibc"))
))]
pub fn capture(command: Command, limits: CaptureLimits, label: &str) -> io::Result<Output> {
    capture_with_group_sample(
        command,
        limits,
        label,
        crate::supervisor::process_group::process_group_sample,
    )
}

#[cfg(any(
    target_os = "macos",
    all(target_os = "linux", not(target_env = "uclibc"))
))]
fn capture_with_group_sample(
    mut command: Command,
    limits: CaptureLimits,
    label: &str,
    mut sample_group: impl FnMut(
        u32,
    )
        -> io::Result<crate::supervisor::process_group::ProcessGroupSample>,
) -> io::Result<Output> {
    use std::os::unix::process::CommandExt as _;
    if limits.timeout.is_zero() || limits.output_bytes == 0 || limits.resident_bytes == Some(0) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "metadata restrictions must be positive",
        ));
    }
    let deadline = Instant::now()
        .checked_add(limits.timeout)
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "metadata deadline overflow"))?;
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .process_group(0);
    let child = command.spawn().map_err(|error| {
        io::Error::new(
            error.kind(),
            format!("spawning owned metadata child for {label}: {error}"),
        )
    })?;
    let mut owned = MetadataChild {
        child,
        identity: None,
        state: owned_child::CleanupState::Unwaited,
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
                    _ => io::Error::other(format!(
                        "{label}: original metadata child birth unavailable"
                    )),
                });
            }
        }
    }
    let stdout = BoundedPipeCapture::with_limit(
        owned
            .child
            .stdout
            .take()
            .ok_or_else(|| io::Error::other("metadata stdout missing"))?,
        limits.output_bytes,
    )?;
    let stderr = BoundedPipeCapture::with_limit(
        owned
            .child
            .stderr
            .take()
            .ok_or_else(|| io::Error::other("metadata stderr missing"))?,
        limits.output_bytes,
    )?;
    loop {
        if Instant::now() >= deadline {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                format!("{label}: exceeded {:.3}s", limits.timeout.as_secs_f64()),
            ));
        }
        match observe_child_unreaped(&owned.child, ChildEvents::Exit, label)? {
            UnreapedChildState::Exited => break,
            UnreapedChildState::Running => {}
            UnreapedChildState::Stopped(_) => {
                return Err(io::Error::other(format!(
                    "{label}: metadata child stopped unexpectedly"
                )))
            }
        }
        if stdout.limit_breached() || stderr.limit_breached() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{label}: exceeded metadata output limit"),
            ));
        }
        if let Some(limit) = limits.resident_bytes {
            let original = owned
                .identity
                .ok_or_else(|| io::Error::other("metadata original identity unavailable"))?;
            if let Some(current) =
                crate::supervisor::process_group::process_identity(owned.child.id())?
            {
                if current.birth != original.birth
                    || current.parent != original.parent
                    || current.group != original.pid
                {
                    return Err(io::Error::other("metadata original group identity changed; RSS restriction cannot be proved"));
                }
            }
            match sample_group(original.pid) {
                Ok(sample) if sample.resident_bytes > limit => {
                    return Err(io::Error::new(
                        io::ErrorKind::OutOfMemory,
                        ResidentLimitExceeded(label.to_owned()),
                    ));
                }
                Ok(_) => {}
                Err(error)
                    if crate::supervisor::process_group::is_census_member_disappearance(&error) =>
                {
                    // A listed descendant may naturally exit before its birth
                    // query. Accept NO sample: the same unreaped original Child
                    // and deadline own the next observation. This grants no
                    // empty-group evidence; final native retirement remains
                    // mandatory before captured output can be returned.
                }
                Err(error) => return Err(error),
            }
        }
        std::thread::sleep(Duration::from_millis(5));
    }
    let cleanup = GroupCleanup::begin_until(&mut owned.child, deadline)?;
    owned.state = owned_child::CleanupState::Waiting;
    let status = cleanup.reap(label)?;
    owned.state = owned_child::CleanupState::Complete;
    let stdout = stdout.finish_bytes_until(label, "stdout", deadline)?;
    let stderr = stderr.finish_bytes_until(label, "stderr", deadline)?;
    if Instant::now() >= deadline {
        return Err(io::Error::new(
            io::ErrorKind::TimedOut,
            format!("{label}: metadata completion exceeded its original deadline"),
        ));
    }
    Ok(Output {
        status,
        stdout,
        stderr,
    })
}

#[cfg(not(any(
    target_os = "macos",
    all(target_os = "linux", not(target_env = "uclibc"))
)))]
pub fn capture(_command: Command, _limits: CaptureLimits, _label: &str) -> io::Result<Output> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "bounded native metadata capture unavailable on this platform",
    ))
}

#[cfg(unix)]
struct MetadataChild {
    child: Child,
    identity: Option<crate::supervisor::process_group::ProcessIdentity>,
    state: owned_child::CleanupState,
}

#[cfg(unix)]
impl Drop for MetadataChild {
    fn drop(&mut self) {
        use owned_child::CleanupState;
        match self.state {
            CleanupState::Complete => return,
            CleanupState::Waiting => {
                // A consuming wait may have failed after losing parentage.
                // Re-establish the original birth; never repeat a group kill
                // or grant a missing-birth terminal exemption on this path.
                if let Some(identity) = self.identity {
                    let _ = owned_child::recover_original_child(
                        &mut self.child,
                        &identity,
                        "metadata child after wait error",
                    );
                }
                return;
            }
            CleanupState::Unwaited => {}
        }
        // Group cleanup retains the original unreaped leader; it never adopts
        // a group the target joined later. A fresh birth/parentage check then
        // permits only the original child to be recovered if it moved groups.
        if let Some(identity) = self.identity {
            if let Ok(Some(current)) =
                crate::supervisor::process_group::process_identity(self.child.id())
            {
                if current.birth != identity.birth || current.parent != identity.parent {
                    return;
                }
                if current.group != identity.pid {
                    let result = GroupCleanup::begin(&mut self.child).and_then(|cleanup| {
                        cleanup.reap_moved_original(&current, "metadata child moved group")
                    });
                    if result.is_err() {
                        let _ = owned_child::recover_original_child(
                            &mut self.child,
                            &identity,
                            "metadata child recovery",
                        );
                    }
                    return;
                }
            }
        }
        terminate_process_group(&mut self.child);
        if let Some(identity) = self.identity {
            let _ = owned_child::recover_original_child(
                &mut self.child,
                &identity,
                "metadata child cleanup",
            );
        }
    }
}

#[cfg(all(
    test,
    any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    )
))]
mod tests;
