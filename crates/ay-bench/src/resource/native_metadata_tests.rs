// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Whether this process is the payload child: the driver tests re-exec
/// this test binary with `--exact <full test path>` (see
/// [`payload_arguments`]). In a plain suite run the payload tests return
/// at once instead of acting. Deliberately no `#[ignore]`: disabled tests
/// are banned workspace-wide, so payload discrimination is by argv, the
/// same shape as the self-re-exec guards in `owned_child`'s tests.
fn payload_test_path(name: &str) -> String {
    format!("resource::native_metadata_tests::{name}")
}

fn invoked_as_payload(name: &str) -> bool {
    let exact = payload_test_path(name);
    let mut has_exact = false;
    let mut has_name = false;
    for arg in std::env::args().skip(1) {
        has_exact |= arg == "--exact";
        has_name |= arg == exact;
    }
    has_exact && has_name
}

#[test]
fn successful_payload() {
    if !invoked_as_payload("successful_payload") {
        return;
    }
    println!("native-metadata-stdout");
    eprintln!("native-metadata-stderr");
}

#[test]
fn sleeping_payload() {
    if !invoked_as_payload("sleeping_payload") {
        return;
    }
    if let Ok(group) = std::fs::read_to_string("join-group") {
        nix::unistd::setpgid(
            nix::unistd::Pid::from_raw(0),
            nix::unistd::Pid::from_raw(group.trim().parse().unwrap()),
        )
        .unwrap();
    }
    let identity = ay_sys::supervisor::process_group::process_identity(std::process::id())
        .unwrap()
        .unwrap();
    std::fs::write(
        "metadata-child",
        format!("{} {}", identity.pid, identity.birth),
    )
    .unwrap();
    std::thread::sleep(Duration::from_secs(60));
}

fn payload_arguments(name: &str) -> Vec<String> {
    vec![
        payload_test_path(name),
        "--exact".into(),
        "--nocapture".into(),
    ]
}

#[test]
fn captures_native_executable_without_an_interpreter() {
    let output = capture_local_output(
        std::env::current_exe().unwrap(),
        payload_arguments("successful_payload"),
        Duration::from_secs(5),
        "native metadata success",
    )
    .unwrap();
    assert!(output.status.success());
    assert!(output.stdout.contains("native-metadata-stdout"));
    assert!(output.stderr.contains("native-metadata-stderr"));
}

#[test]
fn metadata_timeout_terminates_and_reaps_the_original_child() {
    check_timeout(Placement::OriginalGroup);
}

#[test]
fn moved_metadata_child_does_not_transfer_cleanup_to_its_new_group() {
    check_timeout(Placement::JoinSentinel);
}

enum Placement {
    OriginalGroup,
    JoinSentinel,
}

fn check_timeout(placement: Placement) {
    use std::os::unix::process::CommandExt as _;
    struct Sentinel {
        child: Child,
        identity: ay_sys::supervisor::process_group::ProcessIdentity,
    }
    impl Drop for Sentinel {
        fn drop(&mut self) {
            let _ = owned_child::recover_original_child(
                &mut self.child,
                &self.identity,
                "metadata test sentinel",
            );
        }
    }
    let directory = tempfile::tempdir().unwrap();
    let mut sentinel = matches!(placement, Placement::JoinSentinel).then(|| {
        let child = Command::new("/bin/sleep")
            .arg("30")
            .process_group(0)
            .spawn()
            .unwrap();
        let identity = ay_sys::supervisor::process_group::process_identity(child.id())
            .unwrap()
            .unwrap();
        std::fs::write(directory.path().join("join-group"), child.id().to_string()).unwrap();
        Sentinel { child, identity }
    });
    let error = capture_local_output_in(
        std::env::current_exe().unwrap(),
        payload_arguments("sleeping_payload"),
        Duration::from_secs(1),
        "native metadata timeout",
        Some(directory.path()),
    )
    .err()
    .expect("sleeping metadata must time out");
    assert!(error.to_string().contains("exceeded"), "{error}");
    let identity = std::fs::read_to_string(directory.path().join("metadata-child")).unwrap();
    let mut fields = identity.split_whitespace();
    let pid = fields.next().unwrap().parse().unwrap();
    let birth: u128 = fields.next().unwrap().parse().unwrap();
    assert!(
        ay_sys::supervisor::process_group::process_identity(pid)
            .unwrap()
            .is_none_or(|current| current.birth != birth),
        "the original child must be gone after timeout cleanup"
    );
    if let Some(sentinel) = sentinel.as_mut() {
        assert!(sentinel.child.try_wait().unwrap().is_none());
        assert_eq!(
            ay_sys::supervisor::process_group::process_identity(sentinel.child.id())
                .unwrap()
                .unwrap()
                .birth,
            sentinel.identity.birth,
            "cleanup must never adopt the joined group"
        );
    }
}

#[test]
fn missing_metadata_program_reports_spawn_failure() {
    let directory = tempfile::tempdir().unwrap();
    let error = capture_local_output(
        directory.path().join("absent-program"),
        std::iter::empty::<&str>(),
        Duration::from_secs(1),
        "missing native metadata",
    )
    .err()
    .expect("missing metadata executable must fail");
    assert!(error.to_string().contains("spawning owned metadata child"));
}
