// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `smt_alethe_external_replay` proof-inventory row.
//!
//! The row claims a proof "accepted by an external checker", so it passes only
//! on the checker's literal `valid`. It used to pass on the exit status alone,
//! and pinned Carcara exits 0 on a `holey` document: every step re-derived
//! except a `hole` step (or a `trust` step under `--allowed-rules trust`).
//! Measured with carcara 1.1.0 [git 9a352ee]: a proof "refuting" the
//! SATISFIABLE `(assert (> x 0))` through `(step t1 (cl (not (> x 0))) :rule
//! hole)` exits 0 and prints `holey`, which that read counted as a replay.
//!
//! Nor is every `valid` a replay: pinned Carcara misjudges some `evaluate`
//! steps and misreads some `:named`/`define-fun` binders
//! (`ay_core::pinned_carcara`), and prints `valid` for a refutation of a
//! satisfiable problem resting on either. Such a pair is refused before the
//! checker runs, by the same scan every other Carcara gate uses.

use super::{
    resolve_repo_path, resolve_work_dir, run_command_capture, tail_text, ProofInventoryRow,
    Z3AuditArgs,
};
use std::fs;
use std::path::Path;

const ID: &str = "smt_alethe_external_replay";
const SURFACE: &str = "SMT Alethe external replay";
const GOAL: &str = "1/1 SMT Alethe proof emitted and accepted by an external checker";

pub(super) fn alethe_replay_row(
    args: &Z3AuditArgs,
    repo_root: &Path,
    ay: &Path,
    run: bool,
) -> ProofInventoryRow {
    let command = format!(
        "{} solve --proof <work-dir>/smt-alethe-proof.alethe {} && {} check <work-dir>/smt-alethe-proof.alethe {}",
        ay.display(),
        args.alethe_problem.display(),
        args.alethe_checker,
        args.alethe_problem.display()
    );
    let fail = |current: &str, finding: String| {
        ProofInventoryRow::fail(ID, SURFACE, current, GOAL, command.clone(), finding)
    };
    if !run {
        return ProofInventoryRow::not_run(
            ID,
            SURFACE,
            "0/1 external Alethe replay command run by this audit",
            GOAL,
            command,
            "inventory-only mode suppressed execution; default z3-audit emits and externally replays this Alethe proof; --run-alethe-replay re-enables this row with --inventory-only".to_string(),
        );
    }

    let work_dir = resolve_work_dir(repo_root, args.proof_work_dir.as_deref());
    let problem = resolve_repo_path(repo_root, &args.alethe_problem);
    let proof = work_dir.join("smt-alethe-proof.alethe");
    if let Err(error) = fs::create_dir_all(&work_dir) {
        return fail(
            "0/1 proof work directory created",
            format!("failed to create {}: {error}", work_dir.display()),
        );
    }

    let proof_arg = proof.to_string_lossy().into_owned();
    let problem_arg = problem.to_string_lossy().into_owned();
    let emit = match run_command_capture(
        repo_root,
        ay,
        &["solve", "--proof", &proof_arg, &problem_arg],
    ) {
        Ok(output) => output,
        Err(error) => {
            return fail(
                "0/1 SMT Alethe proof emitted",
                format!("failed to run proof emission command: {error}"),
            );
        }
    };
    if !emit.status.success() || !proof.is_file() {
        return fail(
            "0/1 SMT Alethe proof emitted",
            format!(
                "proof emission failed: status={:?} proof_exists={} stdout_tail={:?} stderr_tail={:?}",
                emit.status.code(),
                proof.is_file(),
                tail_text(&String::from_utf8_lossy(&emit.stdout)),
                tail_text(&String::from_utf8_lossy(&emit.stderr))
            ),
        );
    }

    if let Err(finding) = pinned_carcara_can_judge_files(&problem, &proof) {
        return fail("0/1 SMT Alethe proof externally replayed", finding);
    }
    let replay = run_command_capture(
        repo_root,
        Path::new(&args.alethe_checker),
        &["check", &proof_arg, &problem_arg],
    );
    match replay {
        Ok(replay) if external_replay_verified(replay.status.success(), &replay.stdout) => {
            ProofInventoryRow::pass(
                ID,
                SURFACE,
                "1/1 SMT Alethe proof emitted and externally replayed",
                GOAL,
                command,
                format!("external replay verified (`valid`); proof={}", proof.display()),
            )
        }
        Ok(replay) => fail(
            "0/1 SMT Alethe proof externally replayed",
            format!(
                "external replay did not verify (only `valid` does; `holey` carries an unchecked step): status={:?} stdout_tail={:?} stderr_tail={:?}",
                replay.status.code(),
                tail_text(&String::from_utf8_lossy(&replay.stdout)),
                tail_text(&String::from_utf8_lossy(&replay.stderr))
            ),
        ),
        Err(error) => fail(
            "0/1 SMT Alethe proof externally replayed",
            format!("failed to run external checker: {error}"),
        ),
    }
}

/// `Ok` when pinned Carcara's verdict on the exact problem and proof files can
/// count at all; otherwise why not (a read failure fails closed too).
fn pinned_carcara_can_judge_files(problem: &Path, proof: &Path) -> Result<(), String> {
    let read = |path: &Path| {
        fs::read_to_string(path).map_err(|error| {
            format!(
                "failed to read {} for the pinned-Carcara scan: {error}",
                path.display()
            )
        })
    };
    ay_core::pinned_carcara::pinned_carcara_can_judge(&read(problem)?, &read(proof)?)
        .map_err(|misjudged| format!("{misjudged}; proof={}", proof.display()))
}

/// External verification: a successful exit AND the literal verdict `valid`.
/// Carcara's `holey` also exits 0; any other or extra output fails closed.
fn external_replay_verified(status_success: bool, stdout: &[u8]) -> bool {
    status_success && String::from_utf8_lossy(stdout).trim() == "valid"
}

#[cfg(test)]
mod tests {
    #[cfg(unix)]
    use super::super::CheckStatus;
    use super::external_replay_verified;
    #[cfg(unix)]
    use super::{alethe_replay_row, Z3AuditArgs};

    #[test]
    fn only_a_successful_literal_valid_is_an_external_replay() {
        assert!(external_replay_verified(true, b"valid\n"));
        assert!(!external_replay_verified(true, b"holey\n"));
        assert!(!external_replay_verified(false, b"valid\n"));
        assert!(!external_replay_verified(false, b"invalid\n"));
        assert!(!external_replay_verified(true, b""));
        assert!(!external_replay_verified(true, b"valid\nholey\n"));
    }

    /// The row end to end, with an `ay` stub that writes `proof` and a checker
    /// stub that always prints `valid`: `(status, finding)`.
    #[cfg(unix)]
    fn row_with_valid_checker(problem: &str, proof: &str) -> (CheckStatus, String) {
        use clap::Parser;
        use std::os::unix::fs::PermissionsExt;

        #[derive(Parser)]
        struct Cli {
            #[command(flatten)]
            args: Z3AuditArgs,
        }
        let dir = tempfile::tempdir().expect("temporary directory");
        let executable = |name: &str, body: String| {
            let path = dir.path().join(name);
            std::fs::write(&path, body).expect("write stub");
            let mut permissions = std::fs::metadata(&path).expect("stub").permissions();
            permissions.set_mode(0o755);
            std::fs::set_permissions(&path, permissions).expect("chmod stub");
            path
        };
        let proof_source = dir.path().join("source.alethe");
        std::fs::write(&proof_source, proof).expect("write proof");
        std::fs::write(dir.path().join("problem.smt2"), problem).expect("write problem");
        // `ay solve --proof OUT PROBLEM`: copy the fixed proof to OUT.
        let ay = executable(
            "ay",
            format!("#!/bin/sh\ncp '{}' \"$3\"\n", proof_source.display()),
        );
        let checker = executable("carcara", "#!/bin/sh\necho valid\n".to_string());
        let work = dir.path().join("work");
        let cli = Cli::parse_from([
            "z3-audit".to_string(),
            format!("--alethe-checker={}", checker.display()),
            format!(
                "--alethe-problem={}",
                dir.path().join("problem.smt2").display()
            ),
            format!("--proof-work-dir={}", work.display()),
        ]);
        let row = alethe_replay_row(&cli.args, dir.path(), &ay, true);
        (row.status, row.finding)
    }

    /// NEGATIVE CONTROL: the pair pinned Carcara prints `valid` for only
    /// through its `evaluate` defect is refused even though the checker says
    /// `valid`; the positive twin (a clean pair, same checker) passes.
    #[cfg(unix)]
    #[test]
    fn a_valid_replay_of_a_document_pinned_carcara_misjudges_is_refused() {
        use ay_core::pinned_carcara::{FALSE_VALID_CONTROL_PROBLEM, FALSE_VALID_CONTROL_PROOF};
        let (status, finding) =
            row_with_valid_checker(FALSE_VALID_CONTROL_PROBLEM, FALSE_VALID_CONTROL_PROOF);
        assert_eq!(status, CheckStatus::Fail, "{finding}");
        assert!(finding.contains("is not evidence"), "{finding}");

        let clean = "(assume t0 (bvsge #xf #xe))\n(step t1 (cl) :rule hole :premises (t0))\n";
        let (status, finding) = row_with_valid_checker(FALSE_VALID_CONTROL_PROBLEM, clean);
        assert_eq!(status, CheckStatus::Pass, "{finding}");
    }
}
