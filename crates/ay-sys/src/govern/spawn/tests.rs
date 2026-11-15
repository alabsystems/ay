// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual final-image governor controls; no taskpolicy or probe surrogate.
use std::io::{self, Read as _, Write as _};
use std::os::unix::process::{CommandExt as _, ExitStatusExt as _};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt as _;

use crate::govern::{self, ARMED_ENV, BUDGET_ENV, ROOT_PID_ENV, SHARED_BUDGET_ENV};
use crate::supervisor::process_group::{process_identity, ProcessIdentity};

const PAYLOAD: &str = "AY_TEST_NATIVE_GOVERN_PAYLOAD";
const BEFORE: &str = "AY_TEST_NATIVE_GOVERN_BEFORE";
const COMPLETED: &str = "AY_TEST_NATIVE_GOVERN_COMPLETED";

fn identity() -> io::Result<ProcessIdentity> {
    process_identity(std::process::id())?.ok_or_else(|| io::Error::other("own birth unavailable"))
}

fn record(value: ProcessIdentity) -> String {
    format!(
        "{} {} {} {}",
        value.pid, value.parent, value.group, value.birth
    )
}

fn payload() -> io::Result<()> {
    let before = std::env::var_os(BEFORE)
        .ok_or_else(|| io::Error::other("missing initial identity path"))?;
    if !govern::is_armed() {
        // Parent retains the original Child and captures its birth before
        // releasing this private protected pipe. No process-global env change.
        io::stdin().read_exact(&mut [0_u8])?;
        std::fs::write(&before, record(identity()?))?;
        govern::arm();
        return Err(io::Error::other("native SETEXEC unexpectedly returned"));
    }
    let actual = identity()?;
    assert_eq!(std::fs::read_to_string(&before)?, record(actual));
    assert_eq!(govern::root_pid(), actual.pid);
    assert_eq!(
        govern::active_budget_bytes(),
        usize::try_from(govern::budget_mb())
            .ok()
            .and_then(|mib| mib.checked_mul(1024 * 1024))
    );
    let mut pages = vec![0_u8; 128 * 1024 * 1024];
    for page in pages.chunks_mut(4096) {
        page[0] = 1;
    }
    std::hint::black_box(&pages);
    std::thread::sleep(Duration::from_millis(250));
    let completed =
        std::env::var_os(COMPLETED).ok_or_else(|| io::Error::other("missing completion path"))?;
    std::fs::write(completed, record(actual))?;
    Ok(())
}

fn bounded_wait(child: &mut Child, original: ProcessIdentity) -> io::Result<ExitStatus> {
    match child.wait_timeout(Duration::from_secs(10))? {
        Some(status) => Ok(status),
        None => {
            // A timeout is a failed control, never a successful fatal-policy
            // observation. Reauthenticate the exact original unreaped child;
            // a failed consuming wait above never reaches this signal path.
            let observed =
                crate::darwin_child::observe(child, crate::darwin_child::Events::ExitOnly)?;
            if matches!(
                observed,
                Some(
                    crate::darwin_child::Event::Exited(_)
                        | crate::darwin_child::Event::Killed(_)
                        | crate::darwin_child::Event::Dumped(_)
                )
            ) {
                let _ = child.wait_timeout(Duration::from_secs(5));
            } else if process_identity(child.id())? == Some(original) {
                child.kill()?;
                child
                    .wait_timeout(Duration::from_secs(5))?
                    .ok_or_else(|| io::Error::other("original control child did not reap"))?;
            }
            Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "native governor control exceeded ten seconds",
            ))
        }
    }
}

#[test]
fn native_final_exec_preserves_identity_and_enforces_budget() -> io::Result<()> {
    if std::env::var_os(PAYLOAD).is_some() {
        return payload();
    }
    let test_name = std::thread::current()
        .name()
        .ok_or_else(|| io::Error::other("missing libtest name"))?
        .to_owned();
    for (budget, expected_signal, expected_code) in [
        (256_u64, None, Some(0)),
        (64, Some(libc::SIGKILL), None),
        (u64::MAX, None, Some(govern::EXIT_UNGOVERNED)),
    ] {
        let directory = tempfile::tempdir()?;
        let before = directory.path().join("before");
        let completed = directory.path().join("completed");
        let mut child = Command::new(std::env::current_exe()?)
            .args(["--exact", &test_name, "--nocapture", "--test-threads=1"])
            .env(PAYLOAD, "1")
            .env(BEFORE, &before)
            .env(COMPLETED, &completed)
            .env(BUDGET_ENV, budget.to_string())
            .env_remove(ARMED_ENV)
            .env_remove(ROOT_PID_ENV)
            .env_remove(SHARED_BUDGET_ENV)
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::inherit())
            .process_group(0)
            .spawn()?;
        let original = process_identity(child.id())?
            .ok_or_else(|| io::Error::other("original child birth unavailable"))?;
        let mut writer = crate::child_pipe::ChildPipeWriter::take_from(&mut child)?;
        writer.write_all(&[1])?;
        writer.flush()?;
        drop(writer);
        let status = bounded_wait(&mut child, original)?;
        assert_eq!(
            status.signal(),
            expected_signal,
            "budget {budget}: {status}"
        );
        assert_eq!(status.code(), expected_code, "budget {budget}: {status}");
        assert_eq!(std::fs::read_to_string(&before)?, record(original));
        if status.success() {
            assert_eq!(std::fs::read_to_string(&completed)?, record(original));
        } else {
            assert!(!completed.exists(), "refused/killed payload completed");
        }
    }
    Ok(())
}
