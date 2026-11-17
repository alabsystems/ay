// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original unreaped-child and group cleanup shared by local AY producers.
//! Observations never manufacture ownership: every signal is anchored by the
//! original Child's positive non-consuming kernel parentage. Recovery after a
//! consuming error additionally requires the original retained birth.
use std::io;
use std::process::{Child, ExitStatus};
use std::time::{Duration, Instant};
use wait_timeout::ChildExt as _;

/// Events observed without consuming the original child's wait status.
#[derive(Clone, Copy)]
pub enum ChildEvents {
    Exit,
    ExitOrStop,
}

pub fn observe_child_unreaped(
    child: &Child,
    events: ChildEvents,
    label: &str,
) -> io::Result<UnreapedChildState> {
    observe_child_unreaped_inner(child, matches!(events, ChildEvents::ExitOrStop), label)
}

/// The signal a `Stopped` observation carries.
///
/// `nix` is declared `[target.'cfg(unix)'.dependencies]`, so naming
/// `nix::sys::signal::Signal` in this enum unconditionally is what stopped
/// `ay-bench` compiling off Unix at all. Off Unix there is no
/// `waitid(..., WNOWAIT)` and no `nix`, and the only `observe_child_unreaped`
/// that compiles there fails closed without ever producing a state — so
/// `Infallible` is the accurate payload: it keeps the variant type-checked
/// while saying in the type system that nothing can construct it.
#[cfg(unix)]
type StopSignal = nix::sys::signal::Signal;
#[cfg(not(unix))]
type StopSignal = std::convert::Infallible;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnreapedChildState {
    Running,
    Stopped(StopSignal),
    Exited,
}

// On UNIX platforms without `waitid(..., WNOWAIT)`, observation fails closed
// before producing a state. Keep an exhaustive compile-time witness so all
// variants remain type-checked on those targets as well as on the supported
// ones. Off Unix the witness cannot exist — `Stopped` is uninhabited there, by
// construction — and it is not needed: the enum declaration alone type-checks
// every variant.
#[cfg(all(
    unix,
    not(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc")),
    ))
))]
const UNREAPED_CHILD_STATE_TYPE_WITNESS: [UnreapedChildState; 3] = [
    UnreapedChildState::Running,
    UnreapedChildState::Stopped(nix::sys::signal::Signal::SIGSTOP),
    UnreapedChildState::Exited,
];

#[derive(Clone, Copy)]
pub enum CleanupState {
    Unwaited,
    Waiting,
    Complete,
}

#[cfg(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
))]
fn observe_child_unreaped_inner(
    child: &Child,
    include_stopped: bool,
    label: &str,
) -> io::Result<UnreapedChildState> {
    use nix::sys::wait::{waitid, Id, WaitPidFlag, WaitStatus};
    use nix::unistd::Pid;

    let raw_pid = i32::try_from(child.id())
        .map_err(|_| io::Error::other(format!("{label}: child PID does not fit pid_t")))?;
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
        Ok(status) => Err(io::Error::other(format!(
            "{label}: unexpected unreaped child status: {status:?}"
        ))),
        Err(error) => Err(io::Error::other(format!(
            "{label}: observing child without reaping failed: {error}"
        ))),
    }
}

#[cfg(target_os = "macos")]
fn observe_child_unreaped_inner(
    child: &Child,
    include_stopped: bool,
    label: &str,
) -> io::Result<UnreapedChildState> {
    use crate::supervisor::UnreapedChildState as SystemChildState;

    match crate::supervisor::observe_child_unreaped(child, include_stopped) {
        Ok(SystemChildState::Running) => Ok(UnreapedChildState::Running),
        Ok(SystemChildState::Exited) => Ok(UnreapedChildState::Exited),
        Ok(SystemChildState::Stopped(signal)) if include_stopped => {
            let signal = nix::sys::signal::Signal::try_from(signal).map_err(|error| {
                io::Error::other(format!(
                    "{label}: child stopped with invalid signal {signal}: {error}"
                ))
            })?;
            Ok(UnreapedChildState::Stopped(signal))
        }
        Ok(SystemChildState::Stopped(signal)) => Err(io::Error::other(format!(
            "{label}: unexpectedly observed stopped child with signal {signal}"
        ))),
        Err(error) => Err(io::Error::other(format!(
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
fn observe_child_unreaped_inner(
    _child: &Child,
    _include_stopped: bool,
    label: &str,
) -> io::Result<UnreapedChildState> {
    // Unix-only: off Unix the witness does not exist (see its definition).
    #[cfg(unix)]
    let _ = UNREAPED_CHILD_STATE_TYPE_WITNESS;
    Err(io::Error::other(format!(
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
    let error = observe_child_unreaped_inner(&child, false, "target-policy regression")
        .expect_err("unsupported targets must fail closed");
    assert!(error
        .to_string()
        .contains("safe unreaped child observation is unavailable"));
    child.wait().expect("reap policy probe");
}

pub fn wait_for_child_exit_unreaped(
    child: &Child,
    timeout: Duration,
    label: &str,
) -> io::Result<bool> {
    let deadline = Instant::now()
        .checked_add(timeout)
        .ok_or_else(|| io::Error::other(format!("{label}: child wait deadline overflow")))?;
    loop {
        match observe_child_unreaped_inner(child, false, label)? {
            UnreapedChildState::Exited => return Ok(true),
            UnreapedChildState::Running => {}
            UnreapedChildState::Stopped(_) => {
                return Err(io::Error::other(format!(
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

pub fn kill_process_group(child: &mut Child) -> io::Result<()> {
    // A std Child with cached None may have lost parentage to another reaper.
    // Require a fresh non-consuming kernel child observation before signalling.
    let terminal = matches!(
        observe_child_unreaped_inner(child, true, "process-group cleanup")?,
        UnreapedChildState::Exited
    );
    #[cfg(not(target_os = "macos"))]
    let _ = terminal;
    #[cfg(unix)]
    {
        if let Ok(pid) = i32::try_from(child.id()) {
            let pgid = nix::unistd::Pid::from_raw(pid);
            match nix::sys::signal::killpg(pgid, nix::sys::signal::Signal::SIGKILL) {
                Ok(()) | Err(nix::errno::Errno::ESRCH) => {}
                Err(error) => {
                    #[cfg(target_os = "macos")]
                    if error == nix::errno::Errno::EPERM && terminal {
                        // Darwin denies signalling an empty zombie group.
                        // Only the original unreaped terminal child plus a
                        // complete, birth-checked census can establish that
                        // there is no live member left to signal. This grants
                        // reaping authority, never permission to ignore a
                        // live/unreadable member or signal another group.
                        let sample =
                            crate::supervisor::process_group::process_group_sample(child.id())?;
                        if sample.live_members.is_empty() {
                            return Ok(());
                        }
                    }
                    return Err(io::Error::other(format!(
                        "process-group cleanup failed: {error}"
                    )));
                }
            }
        }
    }
    #[cfg(not(unix))]
    {
        child.kill()?;
    }
    Ok(())
}

pub fn kill_process_group_and_reap(child: &mut Child, label: &str) -> io::Result<ExitStatus> {
    GroupCleanup::begin(child)?.reap(label)
}

/// Retains exclusive access to the original unreaped child after the one
/// authorised group signal. Darwin may stop exposing its BSD identity once
/// it exits; ordinary consumption only reaps. Moved-child recovery requires
/// fresh original-birth parentage before a direct-child signal.
pub struct GroupCleanup<'a> {
    child: Option<&'a mut Child>,
}

impl<'a> GroupCleanup<'a> {
    pub fn begin(child: &'a mut Child) -> io::Result<Self> {
        kill_process_group(child)?;
        Ok(Self { child: Some(child) })
    }

    /// Pending census turnover never grants a cleanup receipt. The caller's
    /// original deadline bounds resampling; each attempt re-establishes kernel
    /// parentage and only a complete native result permits reaping.
    #[cfg(unix)]
    pub(crate) fn begin_until(child: &'a mut Child, deadline: Instant) -> io::Result<Self> {
        Self::begin_until_with(child, deadline, kill_process_group)
    }

    #[cfg(unix)]
    fn begin_until_with(
        child: &'a mut Child,
        deadline: Instant,
        mut signal: impl FnMut(&mut Child) -> io::Result<()>,
    ) -> io::Result<Self> {
        loop {
            if Instant::now() >= deadline {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "original cleanup census deadline exceeded",
                ));
            }
            match signal(child) {
                Ok(()) => return Ok(Self { child: Some(child) }),
                Err(error)
                    if crate::supervisor::process_group::is_census_member_disappearance(&error) =>
                {
                    // No empty-group witness is inferred from a missing member.
                    std::thread::sleep(Duration::from_millis(5));
                }
                Err(error) => return Err(error),
            }
        }
    }

    #[cfg(unix)]
    pub fn reap_moved_original(
        mut self,
        identity: &crate::supervisor::process_group::ProcessIdentity,
        label: &str,
    ) -> io::Result<ExitStatus> {
        // Ownership revalidation is fallible. Disarm Drop before beginning:
        // an ECHILD, identity mismatch or visibility refusal must not cause a
        // consuming wait while unwinding this receipt.
        let child = self
            .child
            .take()
            .ok_or_else(|| io::Error::other("cleanup receipt already consumed"))?;
        // The group signal may have killed a child that moved back. This
        // receipt has never attempted a consuming wait: positive terminal
        // observation only grants reaping, even if Darwin withdrew BSD info.
        // A live original is signalled only after fresh birth/parent checks;
        // its current group is never adopted as cleanup authority.
        if child.id() != identity.pid {
            return Err(io::Error::other("moved-child PID ownership mismatch"));
        }
        let state = observe_child_unreaped_inner(child, true, label)?;
        let actual = crate::supervisor::process_group::process_identity(child.id())?;
        let (state, actual) =
            refresh_missing_terminal_transition(child, identity, state, actual, label)?;
        match actual {
            Some(current)
                if current.birth == identity.birth && current.parent == identity.parent => {}
            None if matches!(state, UnreapedChildState::Exited) => {}
            _ => {
                return Err(io::Error::other(
                    "moved-child birth/parent ownership mismatch",
                ))
            }
        }
        if !matches!(state, UnreapedChildState::Exited) {
            child.kill()?;
        }
        // Every path reaching this point has re-established original-child
        // authority. Re-arm only for the immediately following bounded reap,
        // which itself takes the reference before its consuming operation.
        self.child = Some(child);
        self.reap(label)
    }

    pub fn reap(mut self, label: &str) -> io::Result<ExitStatus> {
        // Disarm before the consuming operation: an error must never grant
        // Drop authority to retry against an unknown/reused numeric PID.
        let child = self
            .child
            .take()
            .ok_or_else(|| io::Error::other("cleanup receipt already consumed"))?;
        match child.wait_timeout(Duration::from_secs(5)) {
            Ok(Some(status)) => Ok(status),
            Ok(None) => Err(io::Error::other(format!(
                "{label}: process-group leader could not be reaped within 5 seconds after SIGKILL"
            ))),
            Err(error) => Err(io::Error::other(format!(
                "{label}: reaping process-group leader after SIGKILL failed: {error}"
            ))),
        }
    }
}

impl Drop for GroupCleanup<'_> {
    fn drop(&mut self) {
        if let Some(child) = self.child.take() {
            // No consuming wait has occurred since begin established kernel
            // parentage. Unwinding may only finish that wait, never signal.
            let _ = child.wait_timeout(Duration::from_secs(5));
        }
    }
}

pub fn terminate_process_group(child: &mut Child) {
    if kill_process_group(child).is_err() {
        return;
    }
    // SIGKILL does not wake an uninterruptible (D-state) task. Never let
    // cleanup turn a bounded harness deadline into an unbounded parent wait.
    let _ = child.wait_timeout(Duration::from_secs(5));
}

#[cfg(unix)]
pub fn recover_original_child(
    child: &mut Child,
    identity: &crate::supervisor::process_group::ProcessIdentity,
    label: &str,
) -> io::Result<()> {
    // Neither cached None nor a PID/birth snapshot grants authority after a
    // failed consuming wait. Require both positive WNOWAIT parentage and the
    // original birth before any recovery signal or consuming wait.
    if child.id() != identity.pid {
        return Err(io::Error::other(
            "original child PID mismatch; cleanup refused",
        ));
    }
    let state = observe_child_unreaped_inner(child, true, label)?;
    let actual =
        crate::supervisor::process_group::process_identity(child.id())?.ok_or_else(|| {
            io::Error::other("child identity unavailable after consuming wait; cleanup refused")
        })?;
    if actual.pid != identity.pid
        || actual.birth != identity.birth
        || actual.parent != identity.parent
    {
        return Err(io::Error::other(
            "original child birth/parent ownership mismatch; cleanup refused",
        ));
    }
    // An original child may change its process group. Fresh kernel parentage
    // and the original birth still authorize killing that exact child, never
    // adopting its new group or claiming custody of escaped descendants.
    if !matches!(state, UnreapedChildState::Exited) {
        child.kill()?;
    }
    child
        .wait_timeout(Duration::from_secs(5))?
        .ok_or_else(|| io::Error::other("owned child recovery did not reap within five seconds"))?;
    Ok(())
}

#[cfg(unix)]
pub fn observe_original_unreaped(
    child: &Child,
    identity: &crate::supervisor::process_group::ProcessIdentity,
    label: &str,
) -> io::Result<UnreapedChildState> {
    observe_original_with_identity(child, identity, label, || {
        crate::supervisor::process_group::process_identity(child.id())
    })
}

#[cfg(unix)]
fn observe_original_with_identity(
    child: &Child,
    identity: &crate::supervisor::process_group::ProcessIdentity,
    label: &str,
    mut read_identity: impl FnMut() -> io::Result<
        Option<crate::supervisor::process_group::ProcessIdentity>,
    >,
) -> io::Result<UnreapedChildState> {
    if child.id() != identity.pid {
        return Err(io::Error::other(format!("{label}: original child PID mismatch; cleanup refused: child_pid={}, expected={identity:?}", child.id())));
    }
    let state = observe_child_unreaped_inner(child, true, label)?;
    let actual = read_identity().map_err(|error| io::Error::new(error.kind(), format!("{label}: original child identity observation failed; cleanup refused: child_pid={}, expected={identity:?}, unreaped_state={state:?}, error={error}", child.id())))?;
    let (state, actual) =
        refresh_missing_original_observation(identity, state, actual, label, || {
            Ok((
                observe_child_unreaped_inner(child, true, label)?,
                read_identity()?,
            ))
        })?;
    classify_original_observation(identity, state, actual, label)
}

/// Refresh one missing observation. Continued absence is pending under the
/// original caller's deadline, never a new local timer/count or signal grant.
#[cfg(unix)]
fn refresh_missing_original_observation(
    identity: &crate::supervisor::process_group::ProcessIdentity,
    initial: UnreapedChildState,
    actual: Option<crate::supervisor::process_group::ProcessIdentity>,
    label: &str,
    observe: impl FnOnce() -> io::Result<(
        UnreapedChildState,
        Option<crate::supervisor::process_group::ProcessIdentity>,
    )>,
) -> io::Result<(
    UnreapedChildState,
    Option<crate::supervisor::process_group::ProcessIdentity>,
)> {
    if actual.is_some() || !matches!(initial, UnreapedChildState::Running) {
        return Ok((initial, actual));
    }
    let (state, actual) = observe().map_err(|error| io::Error::new(error.kind(), format!("{label}: disappeared original child lacks fresh parentage; cleanup refused: expected={identity:?}, initial_state={initial:?}, refresh_error={error}")))?;
    match actual {
        Some(observed) if observed != *identity => Err(io::Error::other(format!("{label}: original child identity changed during visibility refresh; cleanup refused: expected={identity:?}, actual={actual:?}, refreshed_state={state:?}"))),
        None if matches!(state, UnreapedChildState::Stopped(_)) => Err(io::Error::other(format!("{label}: disappeared original child is not running or exited; cleanup refused: expected={identity:?}, actual=None, refreshed_state={state:?}"))),
        _ => Ok((state, actual)),
    }
}

#[cfg(unix)]
fn refresh_missing_terminal_transition(
    child: &Child,
    identity: &crate::supervisor::process_group::ProcessIdentity,
    initial: UnreapedChildState,
    actual: Option<crate::supervisor::process_group::ProcessIdentity>,
    label: &str,
) -> io::Result<(
    UnreapedChildState,
    Option<crate::supervisor::process_group::ProcessIdentity>,
)> {
    refresh_missing_original_observation(identity, initial, actual, label, || {
        Ok((
            observe_child_unreaped_inner(child, true, label)?,
            crate::supervisor::process_group::process_identity(child.id())?,
        ))
    })
}

#[cfg(unix)]
fn classify_original_observation(
    identity: &crate::supervisor::process_group::ProcessIdentity,
    state: UnreapedChildState,
    actual: Option<crate::supervisor::process_group::ProcessIdentity>,
    label: &str,
) -> io::Result<UnreapedChildState> {
    match actual {
        Some(actual) if actual == *identity => Ok(state),
        // Darwin can hide an exited unreaped leader from libproc. WNOWAIT
        // still proves parentage; callers holding the original unconsumed
        // Child may finish that wait. Recovery after a consuming error is
        // stricter and refuses any action without the original birth above.
        None if matches!(state, UnreapedChildState::Exited) => Ok(state),
        None if matches!(state, UnreapedChildState::Running) => Err(io::Error::new(io::ErrorKind::WouldBlock, format!("{label}: original child identity is pending; cleanup refused until fresh identity/exit: expected={identity:?}, actual=None, unreaped_state={state:?}"))),
        _ => Err(io::Error::other(format!(
            "{label}: original child birth/group ownership mismatch; cleanup refused: expected={identity:?}, actual={actual:?}, unreaped_state={state:?}"
        ))),
    }
}

#[cfg(all(test, unix))]
mod observation_diagnostics_tests {
    use super::*;
    use crate::supervisor::process_group::ProcessIdentity;
    fn identity() -> ProcessIdentity {
        ProcessIdentity {
            pid: 101,
            parent: 100,
            group: 101,
            birth: 12_345_678,
        }
    }
    #[cfg(any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    #[test]
    fn moved_cleanup_refusal_does_not_reap_in_drop() {
        use std::os::unix::process::CommandExt as _;
        let mut command = std::process::Command::new("/bin/sleep");
        command.arg("30").process_group(0);
        let mut child = command.spawn().unwrap();
        // A wrong original PID causes immediate refusal. Before this fix,
        // dropping the still-armed receipt consumed this child's wait status.
        let foreign = ProcessIdentity {
            pid: child.id().wrapping_add(1),
            parent: std::process::id(),
            group: child.id(),
            birth: 0,
        };
        let observation = (|| -> io::Result<()> {
            let receipt = GroupCleanup::begin(&mut child)?;
            let refused = receipt.reap_moved_original(&foreign, "foreign cleanup");
            if refused.is_ok() {
                return Err(io::Error::other("foreign identity was accepted"));
            }
            if !wait_for_child_exit_unreaped(&child, Duration::from_secs(2), "unconsumed refusal")?
            {
                return Err(io::Error::other(
                    "original child did not exit after group kill",
                ));
            }
            Ok(())
        })();
        let _ = child.kill();
        let reaped = child.wait();
        observation.unwrap();
        reaped.unwrap();
    }

    #[test]
    fn mismatched_identity_never_gains_authority_even_after_exit() {
        let expected = identity();
        for actual in [
            ProcessIdentity {
                pid: 102,
                ..expected
            },
            ProcessIdentity {
                parent: 99,
                ..expected
            },
            ProcessIdentity {
                group: 102,
                ..expected
            },
            ProcessIdentity {
                birth: 12_345_679,
                ..expected
            },
        ] {
            for state in [UnreapedChildState::Running, UnreapedChildState::Exited] {
                let error = classify_original_observation(
                    &expected,
                    state,
                    Some(actual),
                    "ownership-probe",
                )
                .unwrap_err();
                let diagnostic = error.to_string();
                assert!(diagnostic.contains(&format!("expected={expected:?}")));
                assert!(diagnostic.contains(&format!("actual=Some({actual:?})")));
                assert!(diagnostic.contains(&format!("unreaped_state={state:?}")));
                assert!(diagnostic.contains("cleanup refused"));
            }
        }
    }

    #[test]
    fn absent_identity_preserves_existing_terminal_only_rule() {
        let expected = identity();
        assert_eq!(
            classify_original_observation(&expected, UnreapedChildState::Exited, None, "probe")
                .unwrap(),
            UnreapedChildState::Exited
        );
        let diagnostic =
            classify_original_observation(&expected, UnreapedChildState::Running, None, "probe")
                .unwrap_err()
                .to_string();
        assert!(diagnostic.contains("actual=None"));
        assert!(diagnostic.contains("unreaped_state=Running"));
        assert!(classify_original_observation(
            &expected,
            UnreapedChildState::Running,
            Some(expected),
            "probe"
        )
        .is_ok());
    }

    #[test]
    fn missing_identity_requires_fresh_parentage_then_pending_or_terminal() {
        let expected = identity();
        for fresh in [
            UnreapedChildState::Running,
            UnreapedChildState::Stopped(nix::sys::signal::Signal::SIGSTOP),
            UnreapedChildState::Exited,
        ] {
            let result = refresh_missing_original_observation(
                &expected,
                UnreapedChildState::Running,
                None,
                "transition",
                || Ok((fresh, None)),
            )
            .and_then(|(state, actual)| {
                classify_original_observation(&expected, state, actual, "transition")
            });
            match fresh {
                UnreapedChildState::Exited => {
                    assert_eq!(result.unwrap(), UnreapedChildState::Exited)
                }
                UnreapedChildState::Running => {
                    assert_eq!(result.unwrap_err().kind(), io::ErrorKind::WouldBlock)
                }
                _ => assert!(result.unwrap_err().to_string().contains("cleanup refused")),
            }
        }
        let error = refresh_missing_original_observation(
            &expected,
            UnreapedChildState::Running,
            None,
            "transition",
            || Err(io::Error::from_raw_os_error(libc::ECHILD)),
        )
        .unwrap_err();
        assert!(error.to_string().contains("refresh_error="));
        assert!(error.to_string().contains("cleanup refused"));
    }

    #[test]
    fn present_identity_never_uses_the_disappearance_exception() {
        let expected = identity();
        for actual in [
            expected,
            ProcessIdentity {
                birth: expected.birth + 1,
                ..expected
            },
            ProcessIdentity {
                group: expected.group + 1,
                ..expected
            },
        ] {
            let (state, actual) = refresh_missing_original_observation(
                &expected,
                UnreapedChildState::Running,
                Some(actual),
                "present",
                || panic!("present identity must not be replaced"),
            )
            .unwrap();
            assert_eq!(
                classify_original_observation(&expected, state, actual, "present").is_ok(),
                actual == Some(expected)
            );
        }
        let (state, actual) = refresh_missing_original_observation(
            &expected,
            UnreapedChildState::Exited,
            None,
            "terminal",
            || panic!("already positively exited"),
        )
        .unwrap();
        assert_eq!((state, actual), (UnreapedChildState::Exited, None));
    }

    #[test]
    fn pending_visibility_has_no_local_abandonment_quota() {
        let expected = identity();
        for fresh in [
            UnreapedChildState::Running,
            UnreapedChildState::Running,
            UnreapedChildState::Exited,
        ] {
            let result = refresh_missing_original_observation(
                &expected,
                UnreapedChildState::Running,
                None,
                "pending",
                || Ok((fresh, None)),
            )
            .unwrap();
            let observed = classify_original_observation(&expected, result.0, result.1, "pending");
            if fresh == UnreapedChildState::Exited {
                assert_eq!(observed.unwrap(), fresh);
            } else {
                assert_eq!(observed.unwrap_err().kind(), io::ErrorKind::WouldBlock);
            }
        }
    }

    #[test]
    fn visibility_refresh_requires_exact_reappearance_and_never_hides_mismatch() {
        let expected = identity();
        let result = refresh_missing_original_observation(
            &expected,
            UnreapedChildState::Running,
            None,
            "reappeared",
            || Ok((UnreapedChildState::Running, Some(expected))),
        )
        .unwrap();
        assert_eq!(result, (UnreapedChildState::Running, Some(expected)));
        for changed in [
            ProcessIdentity {
                parent: 0,
                ..expected
            },
            ProcessIdentity {
                group: 0,
                ..expected
            },
            ProcessIdentity {
                birth: 0,
                ..expected
            },
        ] {
            assert!(refresh_missing_original_observation(
                &expected,
                UnreapedChildState::Running,
                None,
                "mismatch",
                || Ok((UnreapedChildState::Exited, Some(changed)))
            )
            .is_err());
        }
    }
    #[cfg(target_os = "macos")]
    #[test]
    fn native_darwin_exit_between_observations_keeps_original_parentage() {
        use std::os::unix::process::CommandExt as _;
        let mut command = std::process::Command::new("/bin/sleep");
        command.arg("30").process_group(0);
        let mut child = command.spawn().unwrap();
        // Always reap before asserting, including when a host refuses one of
        // the read-only observations. Only this test's child is signalled.
        let observed = (|| -> io::Result<_> {
            let expected = crate::supervisor::process_group::process_identity(child.id())?
                .ok_or_else(|| io::Error::other("live child identity unavailable"))?;
            let initial = observe_child_unreaped_inner(&child, true, "native transition")?;
            if initial != UnreapedChildState::Running {
                return Err(io::Error::other(
                    "fixture exited before initial observation",
                ));
            }
            child.kill()?;
            if !wait_for_child_exit_unreaped(&child, Duration::from_secs(2), "native transition")? {
                return Err(io::Error::other("fixture did not exit after SIGKILL"));
            }
            let actual = crate::supervisor::process_group::process_identity(child.id())?;
            let (state, refreshed_actual) = refresh_missing_terminal_transition(
                &child,
                &expected,
                initial,
                actual,
                "native transition",
            )?;
            Ok((expected, actual, refreshed_actual, state))
        })();
        let _ = child.kill();
        let reaped = child.wait();
        let (expected, actual, refreshed_actual, state) = observed.unwrap();
        reaped.unwrap();
        if actual.is_none() {
            assert!(classify_original_observation(
                &expected,
                UnreapedChildState::Running,
                None,
                "old stale observation"
            )
            .is_err());
            assert_eq!(state, UnreapedChildState::Exited);
        } else {
            // Some Darwin revisions retain the BSD record for zombies. They
            // keep the ordinary exact-identity path and need no exception.
            assert_eq!(state, UnreapedChildState::Running);
        }
        classify_original_observation(&expected, state, refreshed_actual, "native transition")
            .unwrap();
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn native_darwin_fast_exit_stress_retains_original_custody() {
        use std::os::unix::process::CommandExt as _;
        for _ in 0..32 {
            let mut command = std::process::Command::new("/bin/sleep");
            command.arg("30").process_group(0);
            let mut child = command.spawn().unwrap();
            let outcome = (|| -> io::Result<()> {
                let expected = crate::supervisor::process_group::process_identity(child.id())?
                    .ok_or_else(|| io::Error::other("live stress child unavailable"))?;
                child.kill()?;
                let deadline = Instant::now() + Duration::from_secs(2);
                loop {
                    match observe_original_unreaped(&child, &expected, "fast-exit stress") {
                        Ok(UnreapedChildState::Exited) => return Ok(()),
                        Ok(_) => {}
                        Err(error) if error.kind() == io::ErrorKind::WouldBlock => {}
                        Err(error) => return Err(error),
                    }
                    if Instant::now() >= deadline {
                        return Err(io::Error::other("fast-exit stress timed out"));
                    }
                    std::thread::sleep(Duration::from_millis(1));
                }
            })();
            let _ = child.kill();
            let reaped = child.wait();
            outcome.unwrap();
            reaped.unwrap();
        }
    }
}

#[cfg(all(test, target_os = "macos"))]
#[test]
fn original_child_exit_between_wait_and_identity_retains_terminal_custody() {
    use std::os::unix::process::CommandExt as _;
    let mut child = std::process::Command::new("/bin/cat")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .process_group(0)
        .spawn()
        .unwrap();
    let mut input = Some(child.stdin.take().unwrap());
    let identity = crate::supervisor::process_group::process_identity(child.id())
        .unwrap()
        .unwrap();
    let pending =
        observe_original_with_identity(&child, &identity, "missing live identity", || Ok(None))
            .expect_err("missing live identity provides no authority");
    assert_eq!(pending.kind(), io::ErrorKind::WouldBlock);
    assert_eq!(
        observe_original_unreaped(&child, &identity, "same original recovers").unwrap(),
        UnreapedChildState::Running
    );
    let mut wrong_birth = identity;
    wrong_birth.birth += 1;
    assert!(observe_original_with_identity(
        &child,
        &wrong_birth,
        "wrong original identity",
        || Ok(Some(identity))
    )
    .is_err());
    let until = Instant::now() + Duration::from_secs(5);
    let result = observe_original_with_identity(&child, &identity, "exit observation race", || {
        drop(input.take());
        while observe_child_unreaped_inner(&child, true, "exit observation race")?
            != UnreapedChildState::Exited
        {
            if Instant::now() >= until {
                return Err(io::Error::other("owned cat did not exit"));
            }
            std::thread::yield_now();
        }
        Ok(None)
    });
    if result.is_err() {
        let _ = child.kill();
    }
    let status = child.wait().unwrap();
    assert_eq!(result.unwrap(), UnreapedChildState::Exited);
    assert!(status.success());
}

#[cfg(all(
    test,
    any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    )
))]
struct CensusTestChild(Child);

#[cfg(all(
    test,
    any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    )
))]
impl Drop for CensusTestChild {
    fn drop(&mut self) {
        terminate_process_group(&mut self.0);
    }
}

#[cfg(all(
    test,
    any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    )
))]
#[test]
fn original_cleanup_census_pending_retains_receipt_until_native_signal_and_reap() {
    use std::os::unix::process::CommandExt as _;
    let mut child = CensusTestChild(
        std::process::Command::new("/bin/sleep")
            .arg("30")
            .process_group(0)
            .spawn()
            .unwrap(),
    );
    let mut attempts = 0;
    let receipt = GroupCleanup::begin_until_with(
        &mut child.0,
        Instant::now() + Duration::from_secs(2),
        |original| {
            attempts += 1;
            if attempts == 1 {
                return Err(crate::supervisor::process_group::census_member_disappeared());
            }
            kill_process_group(original)
        },
    )
    .unwrap();
    let status = receipt.reap("same original after census turnover").unwrap();
    assert!(attempts >= 2);
    assert!(!status.success());
    assert!(child.0.try_wait().unwrap().is_some());
}

#[cfg(all(
    test,
    any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    )
))]
#[test]
fn original_cleanup_census_refusal_and_persistent_turnover_cannot_mint_a_receipt() {
    use std::os::unix::process::CommandExt as _;
    let mut child = CensusTestChild(
        std::process::Command::new("/bin/sleep")
            .arg("30")
            .process_group(0)
            .spawn()
            .unwrap(),
    );
    let mut attempts = 0;
    let error = match GroupCleanup::begin_until_with(
        &mut child.0,
        Instant::now() + Duration::from_secs(2),
        |_| {
            attempts += 1;
            Err(io::Error::other("group member disappeared during census"))
        },
    ) {
        Ok(_) => panic!("matching text minted a cleanup receipt"),
        Err(error) => error,
    };
    assert_eq!(attempts, 1);
    assert_eq!(error.kind(), io::ErrorKind::Other);
    assert!(child.0.try_wait().unwrap().is_none());
    let error = match GroupCleanup::begin_until_with(
        &mut child.0,
        Instant::now() + Duration::from_millis(50),
        |_| Err(crate::supervisor::process_group::census_member_disappeared()),
    ) {
        Ok(_) => panic!("incomplete census minted a cleanup receipt"),
        Err(error) => error,
    };
    assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    assert!(child.0.try_wait().unwrap().is_none());
    GroupCleanup::begin(&mut child.0)
        .unwrap()
        .reap("refused cleanup control")
        .unwrap();
}
