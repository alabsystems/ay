// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A REFUSED certificate artifact must leave a greppable record.
//!
//! There are two entirely different reasons a run prints no
//! `c ay.proof.certificate` line, and until `c ay.proof.artifact-refused`
//! existed they were indistinguishable from outside the process:
//!
//!  1. nothing was ever offered — the UNSAT had no reconstructable proof, so
//!     the mint produced no artifact to publish; and
//!  2. an artifact WAS produced and was then refused — by the renderer, by the
//!     writer, or by the publication authority check — and the verdict went
//!     out anyway with only prose on stderr.
//!
//! A corpus evidence census filed both under "no evidence artifact at all",
//! which reads as *AY never tried*. These tests pin the marker that separates
//! them, and pin that `--rigor strict` withholds the verdict on the same
//! event while still recording it.
//!
//! The refusal driven here is the WRITE stage, provoked by a pre-existing
//! `<input>.alethe` — the exact filesystem trap that makes an in-place corpus
//! scan under-report evidence. It is used instead of a corpus file because the
//! benchmark corpus is gitignored and the real render-stage reproducers take
//! seconds each; the marker is emitted from one shared helper, so the stage
//! label is the only thing that differs between them.

use std::process::Command;

use tempfile::TempDir;

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

/// A propositional contradiction: UNSAT, with a proof the default posture
/// renders and publishes.
const UNSAT_SCRIPT: &str = r"
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
";

struct Run {
    stdout: String,
    stderr: String,
}

/// Solve `UNSAT_SCRIPT` in a private directory. When `block_artifact` is set,
/// the default `<input>.alethe` pathname is occupied first, so publication of
/// the rendered certificate is refused.
fn solve(rigor: &str, block_artifact: bool) -> Run {
    let dir = TempDir::new().expect("tempdir");
    let input = dir.path().join("problem.smt2");
    std::fs::write(&input, UNSAT_SCRIPT).expect("write problem");
    if block_artifact {
        std::fs::write(dir.path().join("problem.smt2.alethe"), "occupied\n")
            .expect("occupy the default artifact pathname");
    }
    let out = Command::new(ay_binary())
        .arg(&input)
        .arg("--rigor")
        .arg(rigor)
        .output()
        .expect("run ay");
    Run {
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

fn marker_line(stderr: &str) -> Option<&str> {
    stderr
        .lines()
        .find(|line| line.starts_with("c ay.proof.artifact-refused "))
}

/// The control: with the pathname free, the certificate publishes and NO
/// refusal is claimed. Without this, a marker that fired unconditionally would
/// pass every assertion below.
#[test]
fn a_published_certificate_is_not_reported_as_refused() {
    let run = solve("standard", false);
    assert!(
        run.stdout.contains("unsat"),
        "the control run must decide the contradiction; stdout={}\nstderr={}",
        run.stdout,
        run.stderr
    );
    assert!(
        run.stderr.contains("c ay.proof.certificate"),
        "a published certificate must disclose itself; stderr={}",
        run.stderr
    );
    assert!(
        marker_line(&run.stderr).is_none(),
        "nothing was refused, so nothing may be marked refused; stderr={}",
        run.stderr
    );
}

/// Default posture: the verdict still publishes — that is the deliberate
/// trade — but it can no longer publish SILENTLY.
#[test]
fn a_refused_artifact_is_marked_when_the_verdict_still_publishes() {
    let run = solve("standard", true);
    assert!(
        run.stdout.contains("unsat"),
        "the default posture keeps the verdict; stdout={}\nstderr={}",
        run.stdout,
        run.stderr
    );
    assert!(
        !run.stderr.contains("c ay.proof.certificate"),
        "no certificate was published, so none may be disclosed; stderr={}",
        run.stderr
    );
    let marker = marker_line(&run.stderr).unwrap_or_else(|| {
        panic!(
            "a refused artifact must leave a greppable marker; stderr={}",
            run.stderr
        )
    });
    assert!(
        marker.contains("stage=write"),
        "the marker must name which stage refused; marker={marker}"
    );
    assert!(
        marker.contains("path=") && marker.contains("problem.smt2.alethe"),
        "the marker must name the artifact it refused; marker={marker}"
    );
    assert!(
        marker.contains(" rejections=") && marker.contains(" nested_rejections="),
        "the marker must carry the publication-rejection accounting; marker={marker}"
    );
    assert!(
        marker.contains("reason="),
        "the marker must name why; marker={marker}"
    );
}

/// Strict posture: the same refusal, and the verdict is withheld. The marker
/// is a record of the event, not of the posture, so it is printed here too.
#[test]
fn strict_withholds_the_verdict_on_a_refused_artifact_and_still_marks_it() {
    let run = solve("strict", true);
    assert!(
        run.stdout.contains("unknown"),
        "strict must not publish a verdict whose artifact was refused; stdout={}\nstderr={}",
        run.stdout,
        run.stderr
    );
    assert!(
        !run.stdout.contains("unsat"),
        "strict must not also emit the withheld verdict; stdout={}",
        run.stdout
    );
    let marker = marker_line(&run.stderr).unwrap_or_else(|| {
        panic!(
            "the refusal is the same event under strict and must still be recorded; stderr={}",
            run.stderr
        )
    });
    assert!(
        marker.contains("stage=write"),
        "marker={marker}; stderr={}",
        run.stderr
    );
}

/// The occupied pathname is left exactly as it was found: a refusal must never
/// clobber the file it could not replace.
#[test]
fn a_refused_publication_leaves_the_occupying_file_untouched() {
    let dir = TempDir::new().expect("tempdir");
    let input = dir.path().join("problem.smt2");
    std::fs::write(&input, UNSAT_SCRIPT).expect("write problem");
    let occupied = dir.path().join("problem.smt2.alethe");
    std::fs::write(&occupied, "occupied\n").expect("occupy");
    let out = Command::new(ay_binary())
        .arg(&input)
        .arg("--rigor")
        .arg("standard")
        .output()
        .expect("run ay");
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(
        marker_line(&stderr).is_some(),
        "precondition: the run must have refused the artifact; stderr={stderr}"
    );
    assert_eq!(
        std::fs::read_to_string(&occupied).expect("read occupying file"),
        "occupied\n",
        "a refused publication must leave the pre-existing file byte-identical"
    );
}
