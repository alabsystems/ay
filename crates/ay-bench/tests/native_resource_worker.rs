// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(unix)]

use ay_sys::owned_child::{observe_child_unreaped, ChildEvents, UnreapedChildState};
use ay_sys::supervisor::process_group::process_identity;
use std::os::unix::process::CommandExt as _;
use std::process::{Child, Command};
use std::time::{Duration, Instant};

struct Target(Child, bool);
impl Drop for Target {
    fn drop(&mut self) {
        if self.1 {
            ay_sys::owned_child::terminate_process_group(&mut self.0);
        }
    }
}

fn await_stop(target: &Target) {
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        let state =
            observe_child_unreaped(&target.0, ChildEvents::ExitOrStop, "packaged worker").unwrap();
        if matches!(
            state,
            UnreapedChildState::Stopped(nix::sys::signal::Signal::SIGSTOP)
        ) {
            return;
        }
        assert!(matches!(state, UnreapedChildState::Running), "{state:?}");
        assert!(Instant::now() < deadline);
        std::thread::sleep(Duration::from_millis(2));
    }
}

#[test]
fn packaged_worker_stops_before_target_and_preserves_original_identity_through_exec() {
    let directory = tempfile::tempdir().unwrap();
    let marker = directory.path().join("target-ran");
    let mut target = Target(
        Command::new(env!("CARGO_BIN_EXE_ay-bench-resource"))
            .arg("--")
            .arg("/bin/sh")
            .args(["-c", "printf ran > \"$1\"; exec sleep 60", "target"])
            .arg(&marker)
            .process_group(0)
            .spawn()
            .unwrap(),
        true,
    );
    let deadline = Instant::now() + Duration::from_secs(5);
    await_stop(&target);
    let identity = process_identity(target.0.id()).unwrap().unwrap();
    assert_eq!(identity.parent, std::process::id());
    assert_eq!(identity.group, identity.pid);
    assert!(
        !marker.exists(),
        "target ran before the parent's arm barrier"
    );
    nix::sys::signal::kill(
        nix::unistd::Pid::from_raw(i32::try_from(identity.pid).unwrap()),
        nix::sys::signal::Signal::SIGCONT,
    )
    .unwrap();
    loop {
        // Shell redirection creates the file before printf writes its bytes.
        // Existence is not the target's completed observation.
        match std::fs::read_to_string(&marker) {
            Ok(contents) if contents == "ran" => break,
            Ok(contents) => assert!("ran".starts_with(&contents), "{contents:?}"),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => panic!("target marker read failed: {error}"),
        }
        assert!(Instant::now() < deadline);
        std::thread::sleep(Duration::from_millis(2));
    }
    let after = process_identity(target.0.id()).unwrap().unwrap();
    assert_eq!(after, identity);
    assert_eq!(std::fs::read_to_string(marker).unwrap(), "ran");
    // Disarm before the consuming cleanup: even an error cannot grant a
    // second attempt against an unknown/reused numeric process identity.
    target.1 = false;
    ay_sys::owned_child::kill_process_group_and_reap(&mut target.0, "worker test").unwrap();
}

#[test]
fn packaged_worker_installs_file_ceiling_before_the_launch_barrier() {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("bounded");
    let mut target = Target(
        Command::new(env!("CARGO_BIN_EXE_ay-bench-resource"))
            .args([
                "--fsize-bytes",
                "1024",
                "--",
                "/bin/sh",
                "-c",
                "dd if=/dev/zero of=\"$1\" bs=4096 count=1",
                "target",
            ])
            .arg(&file)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .process_group(0)
            .spawn()
            .unwrap(),
        true,
    );
    await_stop(&target);
    assert!(!file.exists());
    nix::sys::signal::kill(
        nix::unistd::Pid::from_raw(i32::try_from(target.0.id()).unwrap()),
        nix::sys::signal::Signal::SIGCONT,
    )
    .unwrap();
    let deadline = Instant::now() + Duration::from_secs(5);
    while !matches!(
        observe_child_unreaped(&target.0, ChildEvents::Exit, "file ceiling").unwrap(),
        UnreapedChildState::Exited
    ) {
        assert!(Instant::now() < deadline);
        std::thread::sleep(Duration::from_millis(2));
    }
    assert!(std::fs::metadata(file).unwrap().len() <= 1024);
    target.1 = false;
    let status =
        ay_sys::owned_child::kill_process_group_and_reap(&mut target.0, "file ceiling").unwrap();
    assert!(!status.success());
}
