// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
#[cfg(unix)]
fn incomplete_capture_retains_bounded_prefix_and_error() {
    use std::io::Write as _;
    let (reader, writer) = std::os::unix::net::UnixStream::pair().unwrap();
    let capture = crate::resource::BoundedPipeCapture::start(reader).unwrap();
    let writer = std::thread::spawn(move || {
        let mut writer = ay_sys::child_pipe::ChildPipeWriter::new(writer).unwrap();
        writer.write_all(&vec![b'x'; 70 * 1024]).unwrap();
    });
    writer.join().unwrap();
    let evidence = capture.finish_evidence();
    assert_eq!(evidence.text, "x".repeat(64 * 1024));
    assert!(evidence.incomplete);
    assert!(evidence.error.as_ref().unwrap().contains("truncated=true"));
    let mut assessment = checked("sat\n", &stats("sat", 4 * 1024 * 1024 * 1024), Some(0));
    let output = super::super::execution::Output {
        stdout: evidence.text,
        stderr: String::new(),
        terminal: SmtCliTerminal {
            exit_code: Some(0),
            timed_out: false,
            memory_limit_exceeded: false,
            original_deadline_expired: false,
            stdout_complete: !evidence.incomplete,
            stderr_complete: true,
            errors: evidence.error.into_iter().collect(),
        },
    };
    output.refuse_incomplete(&mut assessment);
    assert!(!assessment.checked);
    assert!(assessment
        .blockers
        .contains(&SmtCliBlocker::OutputIncomplete));
}

#[test]
fn elapsed_terminal_failure_retains_output_argv_binary_and_input() {
    let directory = tempfile::tempdir().unwrap();
    let output = super::super::execution::Output {
        stdout: "sat\npartial".into(),
        stderr: "deadline diagnostic".into(),
        terminal: SmtCliTerminal {
            exit_code: None,
            timed_out: true,
            memory_limit_exceeded: false,
            original_deadline_expired: true,
            stdout_complete: false,
            stderr_complete: true,
            errors: vec!["truncated output".into()],
        },
    };
    let mut record = SmtCliRecord {
        case: case(SmtMemoryVariant::Serial4GiB),
        binary: serde_json::to_value(binary()).unwrap(),
        terminal: Some(output.terminal.clone()),
        argv: vec![
            "/private/ay".into(),
            "--self-check".into(),
            "/private/input.smt2".into(),
        ],
        environment: BTreeMap::new(),
        observed_status: "sat".into(),
        in_tree_self_check_passed: true,
        independent_replay_passed: false,
        observed_solver_memory_bytes: Some(4 * 1024 * 1024 * 1024),
        default_observation: None,
        tree_memory_bytes: 4 * 1024 * 1024 * 1024,
        execution_envelope: "test-only".into(),
        elapsed_ns: 10,
        deadline_from_run_start_ns: 1,
        stdout_sha256: super::super::snapshot::hash(output.stdout.as_bytes()),
        stderr_sha256: super::super::snapshot::hash(output.stderr.as_bytes()),
        blockers: vec![SmtCliBlocker::OutputIncomplete],
        promotable_for_ask_closure: false,
    };
    let expired = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
    super::super::execution::retain_output(directory.path(), "solve", &output).unwrap();
    super::super::execution::publish_record(directory.path(), &mut record, expired).unwrap();
    assert!(!record.in_tree_self_check_passed);
    let retained: serde_json::Value =
        serde_json::from_slice(&std::fs::read(directory.path().join("record.json")).unwrap())
            .unwrap();
    assert_eq!(retained["case"]["sha256"], record.case.sha256);
    assert_eq!(retained["binary"]["sha256"], binary().sha256);
    assert_eq!(retained["argv"][0], "/private/ay");
    assert_eq!(retained["terminal"]["timed_out"], true);
    assert_eq!(retained["terminal"]["stdout_complete"], false);
    assert_eq!(retained["in_tree_self_check_passed"], false);
    assert!(record.blockers.contains(&SmtCliBlocker::Deadline));
    assert_eq!(
        std::fs::read_to_string(directory.path().join("solve.stdout")).unwrap(),
        output.stdout
    );
}
