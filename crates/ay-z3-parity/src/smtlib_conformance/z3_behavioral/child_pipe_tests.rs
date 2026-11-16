// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The live `-in` stream driver against a target that stops reading.
//!
//! This binary is built with the `unix_hardened` Trust profile, whose `main`
//! runs with SIGPIPE at `SIG_DFL`: the next phase written through a plain
//! `ChildStdin` to a target that had closed its stdin killed the driver with
//! exit 141, where it is written to record `phase_complete: false` and report.
//! The scenario runs alone ([`run_alone`]), where a bypass of
//! `ChildPipeWriter` is a SIGPIPE death named as one.

use super::*;
use ay_test_support::sigpipe::run_alone;

/// Runs of the scenario before it counts as never having reached its write.
const ATTEMPTS: usize = 5;

#[test]
fn authenticated_children_scrub_loader_environment_and_bound_artifact_files() {
    let _resource_guard = resource_test_lock();
    if !ay_test_support::sigpipe::run_alone_with(
        module_path!(),
        "authenticated_children_scrub_loader_environment_and_bound_artifact_files",
        |command| {
            command
                .env("LIBPATH", "ay-untrusted-library-path")
                .env("SHLIB_PATH", "ay-untrusted-library-path")
                .env("AY_BEHAVIORAL_ENV_CONTROL", "retained");
        },
    )
    .expect("run environment scenario in its own process")
    {
        return;
    }
    assert_eq!(
        std::env::var("LIBPATH").unwrap(),
        "ay-untrusted-library-path"
    );
    let resources = PlannedResources::plan(
        &locate_repo_root().unwrap(),
        1,
        "behavioral child environment control",
    )
    .unwrap();
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("input.smt2");
    let bytes = b"(check-sat)\n";
    fs::write(&input, bytes).unwrap();
    let driver = std::env::current_exe().unwrap();
    let args = vec!["-c".to_string(), "test -z \"${LIBPATH+x}\" && test -z \"${SHLIB_PATH+x}\" && test \"$AY_BEHAVIORAL_ENV_CONTROL\" = retained && printf 'environment-ok\\n'".to_string()];
    for style in [RunStyle::Batch, RunStyle::File] {
        let captured = run_target(
            &resources,
            &driver,
            Path::new("/bin/sh"),
            &args,
            bytes,
            style,
            (style == RunStyle::File).then_some(directory.path()),
            (style == RunStyle::File).then_some(Path::new("input.smt2")),
            Duration::from_secs(5),
            "authenticated environment control",
        )
        .unwrap();
        assert_eq!(captured.exit_code, Some(0));
        assert_eq!(captured.stdout, b"environment-ok\n");
        assert_eq!(captured.stderr.as_slice(), &[] as &[u8]);
    }
    let args = vec![
        "if=/dev/zero".to_string(),
        "of=artifact".to_string(),
        "bs=1048576".to_string(),
        "count=17".to_string(),
    ];
    let captured = run_target(
        &resources,
        &driver,
        Path::new("/bin/dd"),
        &args,
        bytes,
        RunStyle::File,
        Some(directory.path()),
        Some(Path::new("input.smt2")),
        Duration::from_secs(5),
        "kernel artifact output ceiling",
    )
    .unwrap();
    assert_ne!(captured.exit_code, Some(0));
    assert!(!captured.timed_out && !captured.memout);
    assert!(
        fs::metadata(directory.path().join("artifact"))
            .unwrap()
            .len()
            <= ARTIFACT_BYTE_LIMIT
    );
}

#[test]
fn stream_driver_survives_a_target_that_stops_reading() {
    use std::os::unix::fs::PermissionsExt as _;

    if !run_alone(
        module_path!(),
        "stream_driver_survives_a_target_that_stops_reading",
    )
    .expect("re-exec this test alone")
    {
        return;
    }
    let directory = tempfile::tempdir().expect("tempdir");
    let target = directory.path().join("target.sh");
    // Reads the first phase, closes its stdin, THEN answers it: a driver that
    // got the answer writes its next phase into a pipe with no reader. Reading
    // first orders the close after the driver's first write, so that write can
    // never be the one that fails, however the two processes are scheduled.
    fs::write(
        &target,
        "#!/bin/sh\nread -r request\nexec 0<&-\necho phase-one\nsleep 1\n",
    )
    .expect("write stream target");
    fs::set_permissions(&target, fs::Permissions::from_mode(0o755))
        .expect("make stream target executable");
    let args = vec!["--target".to_string(), target.display().to_string()];
    // A target that has not answered within the driver's phase timeout (a
    // loaded host can take that long to start a shell) ends the run before
    // that write, and a pass would then prove nothing. Such a run is retried;
    // the test requires a run whose write failed.
    for _ in 0..ATTEMPTS {
        let (report, stdin_write_failed) =
            drive_stream_target(&args).expect("the driver reports the incomplete stream");
        assert!(!report.phase_complete, "the stream is recorded incomplete");
        if stdin_write_failed {
            assert_eq!(report.stdout, "phase-one\n", "the one phase it answered");
            return;
        }
    }
    panic!(
        "in {ATTEMPTS} runs the target never answered phase one within the driver's \
         timeout, so no write reached its closed stdin: the scenario did not run"
    );
}
