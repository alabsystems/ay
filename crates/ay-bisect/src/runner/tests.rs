// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_parse_result_sat() {
    assert_eq!(parse_result("sat\n", true), SolveResult::Sat);
}

#[test]
fn test_parse_result_unsat() {
    assert_eq!(parse_result("unsat\n", true), SolveResult::Unsat);
}

#[test]
fn test_parse_result_last_verdict_wins() {
    assert_eq!(parse_result("unknown\nsat\n", true), SolveResult::Sat);
}

#[test]
fn test_parse_result_unknown() {
    assert_eq!(parse_result("unknown\n", true), SolveResult::Unknown);
}

#[test]
fn test_parse_result_no_verdict_exit_ok() {
    assert_eq!(parse_result("", true), SolveResult::Error);
}

#[test]
fn test_parse_result_no_verdict_exit_fail() {
    assert_eq!(parse_result("garbage\n", false), SolveResult::Error);
}

#[test]
fn test_parse_result_rejects_verdict_from_crashed_process() {
    assert_eq!(parse_result("sat\n", false), SolveResult::Error);
}

#[test]
fn test_solveresult_matches() {
    assert!(SolveResult::Sat.matches(Expected::Sat));
    assert!(SolveResult::Unsat.matches(Expected::Unsat));
    assert!(!SolveResult::Unknown.matches(Expected::Sat));
    assert!(!SolveResult::Timeout.matches(Expected::Sat));
    assert!(!SolveResult::Sat.matches(Expected::Unsat));
}

#[test]
fn bounded_capture_preserves_output_below_limit() {
    let input = vec![b'x'; CAPTURE_HEAD_BYTES + 4096];
    let capture = PipeCapture::start(std::io::Cursor::new(input.clone()));
    assert_eq!(capture.finish().as_bytes(), input);
}

/// Run a trial, tolerating a transient `ETXTBSY` from the freshly written
/// fake-solver script.
///
/// The unix tests below write a small shell script and immediately `execve`
/// it. `std::fs::write` closes its own descriptor, but any *other* test
/// thread in this same binary that forks in that window (there are several
/// process-spawning tests here) hands the forked child an inherited copy of
/// the still-open write descriptor. Until that child reaches its own
/// `execve` the kernel sees a writable descriptor on the script and refuses
/// our exec with `ETXTBSY` — reported as
/// `SpawnFailed { ExecutableFileBusy }`. The race is inherent to
/// fork/exec (rust-lang/rust#97590, golang/go#22315); the standard remedy
/// is to retry the exec, which observes exactly the same run and therefore
/// weakens no assertion below.
#[cfg(unix)]
fn run_trial_tolerating_text_busy(runner: &CliRunner, flags: &[&str]) -> SolveResult {
    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        match runner.run(flags) {
            Err(BisectError::SpawnFailed { source, .. })
                if source.kind() == std::io::ErrorKind::ExecutableFileBusy
                    && Instant::now() < deadline =>
            {
                thread::sleep(Duration::from_millis(20));
            }
            other => return other.expect("fake solver trial must run"),
        }
    }
}

#[cfg(unix)]
#[test]
fn cli_runner_bounds_noisy_output_and_keeps_trailing_verdict() {
    use std::os::unix::fs::PermissionsExt as _;

    let dir = tempfile::tempdir().expect("tempdir");
    let solver = dir.path().join("noisy-ay");
    std::fs::write(
        &solver,
        "#!/bin/sh\nhead -c 4194304 /dev/zero | tr '\\000' x\nprintf '\\nsat\\n'\nhead -c 4194304 /dev/zero | tr '\\000' y >&2\n",
    )
    .expect("write solver");
    let mut permissions = std::fs::metadata(&solver).unwrap().permissions();
    permissions.set_mode(0o755);
    std::fs::set_permissions(&solver, permissions).expect("chmod");
    let input = dir.path().join("case.smt2");
    std::fs::write(&input, "(check-sat)\n").expect("write input");
    let runner = CliRunner::new(solver, input, Duration::from_secs(10), false);
    assert_eq!(
        run_trial_tolerating_text_busy(&runner, &[]),
        SolveResult::Sat
    );
}

#[cfg(unix)]
#[test]
fn cli_runner_applies_planned_memory_and_core_envelope() {
    use std::os::unix::fs::PermissionsExt as _;

    let dir = tempfile::tempdir().expect("tempdir");
    let argv_file = dir.path().join("argv.txt");
    let env_file = dir.path().join("env.txt");
    let solver = dir.path().join("fake-ay");
    std::fs::write(
        &solver,
        format!(
            "#!/bin/sh\nprintf '%s\\n' \"$@\" > '{}'\nprintf '%s\\n' \"${{NBCORE:-}}\" > '{}'\nprintf 'sat\\n'\n",
            argv_file.display(),
            env_file.display(),
        ),
    )
    .expect("write solver");
    let mut permissions = std::fs::metadata(&solver).unwrap().permissions();
    permissions.set_mode(0o755);
    std::fs::set_permissions(&solver, permissions).expect("chmod");
    let input = dir.path().join("case.smt2");
    std::fs::write(&input, "(check-sat)\n").expect("write input");
    let plan = crate::ResourcePlan {
        requested_jobs: 4,
        jobs: 2,
        memlimit_mb_per_child: 321,
        nbcore_per_child: 3,
        headroom_mb: 16000,
        planner: "scripts/_oom_guard.py".to_string(),
    };
    let runner = CliRunner::new(solver, input.clone(), Duration::from_secs(5), false)
        .with_resource_plan(&plan);

    assert_eq!(
        run_trial_tolerating_text_busy(&runner, &["--no-bve"]),
        SolveResult::Sat
    );
    let argv = std::fs::read_to_string(argv_file).expect("read argv");
    assert!(argv.contains("--memory\n321\n"), "{argv:?}");
    assert!(argv.contains("--no-bve\n"), "{argv:?}");
    assert!(argv.contains(input.to_string_lossy().as_ref()), "{argv:?}");
    assert_eq!(std::fs::read_to_string(env_file).unwrap().trim(), "3");
}
