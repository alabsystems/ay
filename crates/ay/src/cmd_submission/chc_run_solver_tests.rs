// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The command line the CHC-COMP 2026 `run_solver.sh` gives ay (AY-SMT-9).

use super::*;

/// Run the generated CHC runner against a fake `ay` that records its argv:
/// the package must start a `--chc` solve with the proof cycle shed
/// (`--no-proof`), the timeout derived from the job limit minus its reserve,
/// and the benchmark last. A plain `--chc` solve strict-certifies every UNSAT
/// of the CHC engines' internal queries and withheld answers ay had computed
/// (sum01_bug02: `unknown` at 51 s plain, `unsat` in 1.4 s shed).
#[cfg(unix)]
#[test]
fn generated_chc_runner_sheds_the_proof_cycle() {
    use std::os::unix::fs::PermissionsExt;

    let dir = tempfile::tempdir().expect("tempdir");
    write_chc_run_solver(dir.path()).expect("write CHC run_solver.sh");
    let record = dir.path().join("record.txt");
    let fake_ay = dir.path().join("ay");
    fs::write(
        &fake_ay,
        "#!/usr/bin/env bash\nprintf '%s\\n' \"$@\" >\"$ARGV_RECORD\"\nprintf 'sat\\n'\n",
    )
    .expect("write fake ay");
    fs::set_permissions(&fake_ay, fs::Permissions::from_mode(0o755)).expect("chmod fake ay");
    let benchmark = dir.path().join("tiny.smt2");
    fs::write(&benchmark, "(set-logic HORN)\n(check-sat)\n").expect("write benchmark");

    let output = Command::new("bash")
        .arg(dir.path().join("run_solver.sh"))
        .arg(&benchmark)
        .env("ARGV_RECORD", &record)
        .env("TIMELIMIT", "60")
        .env_remove("AY_CHC_TIMEOUT_MS")
        .env_remove("AY_TIMEOUT_MS")
        .output()
        .expect("run generated run_solver.sh");
    assert!(
        output.status.success(),
        "run_solver.sh exited {}",
        output.status
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "sat\n");

    let recorded = fs::read_to_string(&record).expect("read argv record");
    let benchmark = benchmark.display().to_string();
    assert_eq!(
        recorded.lines().collect::<Vec<_>>(),
        [
            "--chc",
            "--no-proof",
            "--timeout",
            "54000",
            benchmark.as_str()
        ],
    );
}
