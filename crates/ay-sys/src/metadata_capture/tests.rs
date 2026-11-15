// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use std::io::{Read, Write};
use std::path::Path;
#[test]
fn moved_child_returning_to_original_group_is_reaped_from_the_signal_receipt() {
    use std::os::unix::process::CommandExt as _;
    let directory = tempfile::tempdir().unwrap();
    let sentinel = Command::new("/bin/sleep")
        .arg("30")
        .process_group(0)
        .spawn()
        .unwrap();
    let sentinel_identity = crate::supervisor::process_group::process_identity(sentinel.id())
        .unwrap()
        .unwrap();
    let mut sentinel = MetadataChild {
        child: sentinel,
        identity: Some(sentinel_identity),
        state: owned_child::CleanupState::Unwaited,
    };
    std::fs::write(
        directory.path().join("join-group"),
        sentinel.child.id().to_string(),
    )
    .unwrap();
    std::fs::write(directory.path().join("return-after-observation"), b"ready").unwrap();
    let child = command("sleeping_payload")
        .current_dir(directory.path())
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .process_group(0)
        .spawn()
        .unwrap();
    let mut original = MetadataChild {
        child,
        identity: None,
        state: owned_child::CleanupState::Unwaited,
    };
    wait_for_file(&directory.path().join("metadata-child"));
    let moved = crate::supervisor::process_group::process_identity(original.child.id())
        .unwrap()
        .unwrap();
    original.identity = Some(moved);
    assert_eq!(moved.group, sentinel.child.id());
    std::fs::write(directory.path().join("return-now"), b"ready").unwrap();
    wait_for_file(&directory.path().join("returned-to-original-group"));
    let cleanup = GroupCleanup::begin(&mut original.child).unwrap();
    original.state = owned_child::CleanupState::Waiting;
    let status = cleanup
        .reap_moved_original(&moved, "returned metadata child")
        .unwrap();
    original.state = owned_child::CleanupState::Complete;
    assert!(!status.success());
    assert!(original.child.try_wait().unwrap().is_some());
    assert!(sentinel.child.try_wait().unwrap().is_none());
}

fn payload(name: &str) -> bool {
    let expected = format!("metadata_capture::tests::{name}");
    let args: Vec<_> = std::env::args().collect();
    args.iter().any(|arg| arg == "--exact") && args.iter().any(|arg| arg == &expected)
}
fn command(name: &str) -> Command {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command.args([
        "--exact",
        &format!("metadata_capture::tests::{name}"),
        "--nocapture",
    ]);
    command
}
fn limits() -> CaptureLimits {
    CaptureLimits {
        timeout: Duration::from_secs(2),
        output_bytes: 4096,
        resident_bytes: None,
    }
}

#[test]
fn resident_budget_stop_has_typed_evidence_without_accepting_matching_text() {
    let mut command = Command::new("/bin/sleep");
    command.arg("10");
    let error = capture(
        command,
        CaptureLimits {
            resident_bytes: Some(1),
            ..limits()
        },
        "resident restriction control",
    )
    .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::OutOfMemory);
    assert!(is_resident_limit(&error));
    assert!(!is_resident_limit(&io::Error::new(
        io::ErrorKind::OutOfMemory,
        error.to_string(),
    )));
    assert!(!is_resident_limit(&io::Error::from_raw_os_error(
        libc::ENOMEM
    )));
}

#[test]
fn native_output_payload() {
    if !payload("native_output_payload") {
        return;
    }
    println!("retained-native-output");
    eprintln!("retained-native-error");
}
#[test]
fn oversized_output_payload() {
    if !payload("oversized_output_payload") {
        return;
    }
    io::stdout().write_all(&[b'x'; 8192]).unwrap();
}
#[test]
fn sleeping_payload() {
    if !payload("sleeping_payload") {
        return;
    }
    if let Ok(group) = std::fs::read_to_string("join-group") {
        nix::unistd::setpgid(
            nix::unistd::Pid::from_raw(0),
            nix::unistd::Pid::from_raw(group.trim().parse().unwrap()),
        )
        .unwrap();
    }
    let identity = crate::supervisor::process_group::process_identity(std::process::id())
        .unwrap()
        .unwrap();
    std::fs::write(
        "metadata-child",
        format!("{} {}", identity.pid, identity.birth),
    )
    .unwrap();
    if Path::new("return-after-observation").exists() {
        wait_for_file(Path::new("return-now"));
        nix::unistd::setpgid(nix::unistd::Pid::from_raw(0), nix::unistd::Pid::from_raw(0)).unwrap();
        std::fs::write("returned-to-original-group", b"ready").unwrap();
    }
    std::thread::sleep(Duration::from_secs(30));
}

fn wait_for_file(path: &Path) {
    let deadline = Instant::now() + Duration::from_secs(5);
    while !path.is_file() {
        assert!(Instant::now() < deadline, "waiting for {}", path.display());
        std::thread::sleep(Duration::from_millis(5));
    }
}

#[test]
fn native_metadata_output_is_complete_and_excess_is_refused() {
    let output = capture(command("native_output_payload"), limits(), "native output").unwrap();
    assert!(output.status.success());
    assert!(String::from_utf8(output.stdout)
        .unwrap()
        .contains("retained-native-output"));
    assert!(String::from_utf8(output.stderr)
        .unwrap()
        .contains("retained-native-error"));
    let error = capture(
        command("oversized_output_payload"),
        limits(),
        "bounded output",
    )
    .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
}

#[test]
fn native_metadata_deadline_and_sampled_rss_are_actual_restrictions() {
    let directory = tempfile::tempdir().unwrap();
    let mut wall_command = command("sleeping_payload");
    wall_command.current_dir(directory.path());
    let mut wall = limits();
    wall.timeout = Duration::from_millis(100);
    assert_eq!(
        capture(wall_command, wall, "wall").unwrap_err().kind(),
        io::ErrorKind::TimedOut
    );
    let mut resident = limits();
    resident.resident_bytes = Some(1);
    let mut resident_command = command("sleeping_payload");
    resident_command.current_dir(directory.path());
    let error = capture(resident_command, resident, "resident").unwrap_err();
    assert!(error.to_string().contains("RSS"), "{error}");
}

#[test]
fn dropping_capture_closes_reader_even_while_the_writer_is_retained() {
    let (reader, mut writer) = std::os::unix::net::UnixStream::pair().unwrap();
    writer
        .set_read_timeout(Some(Duration::from_secs(1)))
        .unwrap();
    let capture = BoundedPipeCapture::with_limit(reader, 64).unwrap();
    drop(capture);
    // Drop joined the reader and released the original endpoint. A detached
    // blocking reader would leave this peer open until the bounded read fails.
    assert_eq!(writer.read(&mut [0u8; 1]).unwrap(), 0);
}

#[test]
fn completed_pipe_data_cannot_renew_an_expired_deadline() {
    let (reader, mut writer) = std::os::unix::net::UnixStream::pair().unwrap();
    let capture = BoundedPipeCapture::with_limit(reader, 64).unwrap();
    writer.write_all(b"already complete").unwrap();
    drop(writer);
    let expired = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
    assert_eq!(
        capture
            .finish_bytes_until("expired", "stdout", expired)
            .unwrap_err()
            .kind(),
        io::ErrorKind::TimedOut
    );
    assert!(
        BoundedPipeCapture::with_limit(tempfile::tempfile().unwrap(), 64).is_err(),
        "a regular file is not a bounded native pipe"
    );
}

#[test]
fn census_turnover_payload() {
    if !payload("census_turnover_payload") {
        return;
    }
    let deadline = Instant::now() + Duration::from_secs(2);
    while !Path::new("release-census-payload").exists() {
        if Instant::now() >= deadline {
            panic!("original capture did not release its payload");
        }
        std::thread::sleep(Duration::from_millis(2));
    }
    println!("retained-after-census-turnover");
}

#[test]
fn disappeared_census_is_pending_until_a_real_sample_and_original_retirement() {
    let directory = tempfile::tempdir().unwrap();
    let mut command = command("census_turnover_payload");
    command.current_dir(directory.path());
    let mut observations = 0;
    let output = capture_with_group_sample(
        command,
        CaptureLimits {
            resident_bytes: Some(u64::MAX),
            ..limits()
        },
        "transient census",
        |group| {
            observations += 1;
            if observations == 1 {
                return Err(crate::supervisor::process_group::census_member_disappeared());
            }
            let sample = crate::supervisor::process_group::process_group_sample(group)?;
            std::fs::write(directory.path().join("release-census-payload"), b"ready")?;
            Ok(sample)
        },
    )
    .unwrap();
    assert!(observations >= 2);
    assert!(output.status.success(), "{:?}", output);
    assert!(String::from_utf8(output.stdout)
        .unwrap()
        .contains("retained-after-census-turnover"));
}

#[test]
fn matching_census_error_text_does_not_make_a_failed_observation_pending() {
    let mut command = Command::new("/bin/sleep");
    command.arg("30");
    let mut observations = 0;
    let error = capture_with_group_sample(
        command,
        CaptureLimits {
            resident_bytes: Some(u64::MAX),
            ..limits()
        },
        "genuine census refusal",
        |_| {
            observations += 1;
            Err(io::Error::other("group member disappeared during census"))
        },
    )
    .unwrap_err();
    assert_eq!(observations, 1);
    assert_eq!(error.kind(), io::ErrorKind::Other);
    assert!(!crate::supervisor::process_group::is_census_member_disappearance(&error));
}

#[test]
fn persistent_census_turnover_keeps_the_original_deadline_and_returns_no_output() {
    let mut command = Command::new("/bin/sleep");
    command.arg("30");
    let mut observations = 0;
    let error = capture_with_group_sample(
        command,
        CaptureLimits {
            timeout: Duration::from_millis(100),
            resident_bytes: Some(u64::MAX),
            ..limits()
        },
        "persistent census turnover",
        |_| {
            observations += 1;
            Err(crate::supervisor::process_group::census_member_disappeared())
        },
    )
    .unwrap_err();
    assert!(observations > 0);
    assert_eq!(error.kind(), io::ErrorKind::TimedOut);
}
