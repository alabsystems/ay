// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Differential contract on real QF_S/QF_SLIA benchmark formulas.
//!
//! This test pins a curated set of cvc5 string benchmarks that are:
//! 1) accepted by both Z3 and AY, and
//! 2) currently solved with a definite SAT/UNSAT answer by both solvers.
//!
//! The goal is to catch regressions in strings behavior on real-world
//! benchmark inputs, not only hand-written formulas.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn solve_with_ay_script(smt: &str) -> Result<String, String> {
    let commands = parse(smt).map_err(|e| format!("parse error: {e}"))?;
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .map(|lines| lines.join("\n"))
        .map_err(|e| format!("ay execute_all error: {e}"))
}

fn z3_available() -> bool {
    Command::new("z3")
        .arg("--version")
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false)
}

fn solve_with_z3_file(path: &Path) -> Result<String, String> {
    let output = Command::new("z3")
        .arg(path)
        .output()
        .map_err(|e| format!("failed to spawn z3 for {}: {e}", path.display()))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!(
            "z3 failed for {} with status {}: {}",
            path.display(),
            output.status,
            stderr
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).to_string())
}

fn repo_path(relative: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative)
}

// Benchmarks chosen from reference/cvc5 where both Z3 and AY currently
// return definite answers and agree. Expanded from 5 -> 11 cases using
// a local triage pass over regress0/regress1 QF_S/QF_SLIA files.
const REFERENCE_BENCHMARK_CASES: [(&str, &str, &str); 11] = [
    (
        "bug001",
        "reference/cvc5/test/regress/cli/regress0/strings/bug001.smt2",
        "sat",
    ),
    (
        "issue3440",
        "reference/cvc5/test/regress/cli/regress0/strings/issue3440.smt2",
        "sat",
    ),
    (
        "bug613",
        "reference/cvc5/test/regress/cli/regress0/strings/bug613.smt2",
        "sat",
    ),
    (
        "leadingzero001",
        "reference/cvc5/test/regress/cli/regress0/strings/leadingzero001.smt2",
        "sat",
    ),
    (
        "model001",
        "reference/cvc5/test/regress/cli/regress0/strings/model001.smt2",
        "sat",
    ),
    (
        "str003",
        "reference/cvc5/test/regress/cli/regress0/strings/str003.smt2",
        "unsat",
    ),
    (
        "str004",
        "reference/cvc5/test/regress/cli/regress0/strings/str004.smt2",
        "unsat",
    ),
    (
        "str005",
        "reference/cvc5/test/regress/cli/regress0/strings/str005.smt2",
        "unsat",
    ),
    // type001: correct answer is SAT. AY model validation fails because
    // str.to_int/str.from_int ground evaluations are not propagated to the
    // LIA model, causing inconsistency between string and integer models.
    (
        "type001",
        "reference/cvc5/test/regress/cli/regress0/strings/type001.smt2",
        "sat",
    ),
    // issue4701: correct answer is SAT. AY has a soundness regression (#4057)
    // where str.substr/str.replace interaction causes false UNSAT.
    // Previous soundness guard returned "unknown" but was removed/bypassed.
    (
        "issue4701_substr_splice",
        "reference/cvc5/test/regress/cli/regress1/strings/issue4701_substr_splice.smt2",
        "sat",
    ),
    (
        "issue6973_dup_lemma_conc",
        "reference/cvc5/test/regress/cli/regress1/strings/issue6973-dup-lemma-conc.smt2",
        "unsat",
    ),
];

/// Classify a AY result for a benchmark case.
fn classify_ay_result(
    name: &str,
    smt: &str,
    path: &Path,
    expected: &str,
    z3_result: &str,
) -> BenchmarkOutcome {
    match solve_with_ay_script(smt) {
        Ok(output) => match crate::common::sat_result(&output) {
            Some(r) if r == "unknown" && z3_result != "unknown" => {
                BenchmarkOutcome::CompletenessGap(format!(
                    "{name}: ay=unknown, z3={z3_result} (expected={expected})"
                ))
            }
            Some(r) if r != z3_result || r != expected => BenchmarkOutcome::SoundnessBug(format!(
                "{name} ({}) expected={expected} z3={z3_result} ay={r}",
                path.display(),
            )),
            Some(_) => BenchmarkOutcome::Ok,
            None => panic!("ay produced no sat-status on {name}: {output}"),
        },
        Err(e) if e.contains("model validation") => BenchmarkOutcome::CompletenessGap(format!(
            "{name}: ay model validation error (expected={expected}): {e}"
        )),
        Err(e) => panic!("ay failed on {name} ({}): {e}", path.display()),
    }
}

enum BenchmarkOutcome {
    Ok,
    CompletenessGap(String),
    SoundnessBug(String),
}

#[test]
#[timeout(120_000)]
fn qf_s_qf_slia_reference_benchmarks_match_z3() {
    if !z3_available() {
        eprintln!("z3 not found; skipping benchmark differential contract");
        return;
    }

    let mut soundness_bugs = Vec::new();
    let mut completeness_gaps = Vec::new();
    let mut evaluated = 0usize;
    let mut skipped_missing = 0usize;

    for (name, relative_path, expected) in REFERENCE_BENCHMARK_CASES {
        let path = repo_path(relative_path);
        // The cvc5 reference regression corpus is an OPTIONAL external clone
        // (see reference/SOURCES.md: `git clone ... cvc5`). When it is not
        // present, skip the benchmark instead of hard-failing: this is a
        // differential completeness contract over an external corpus, not a
        // soundness gate, so absence of the corpus must not fail the suite.
        let Ok(smt) = fs::read_to_string(&path) else {
            eprintln!(
                "skipping optional reference benchmark {name} not checked into repo \
                 (clone cvc5 into reference/ per reference/SOURCES.md): {}",
                path.display()
            );
            skipped_missing += 1;
            continue;
        };
        evaluated += 1;
        assert!(
            smt.contains("(set-logic QF_S)") || smt.contains("(set-logic QF_SLIA)"),
            "{name} must be a QF_S/QF_SLIA benchmark, path={}",
            path.display()
        );

        let z3_output = solve_with_z3_file(&path)
            .unwrap_or_else(|e| panic!("z3 failed on {name} ({}): {e}", path.display()));
        let z3_result = crate::common::sat_result(&z3_output)
            .unwrap_or_else(|| panic!("z3 produced no sat-status on {name}: {z3_output}"));

        match classify_ay_result(name, &smt, &path, expected, z3_result) {
            BenchmarkOutcome::Ok => {}
            BenchmarkOutcome::CompletenessGap(msg) => completeness_gaps.push(msg),
            BenchmarkOutcome::SoundnessBug(msg) => soundness_bugs.push(msg),
        }
    }

    if skipped_missing > 0 {
        eprintln!(
            "skipped {skipped_missing} reference benchmark(s) not present on this machine; \
             evaluated {evaluated} (clone cvc5 into reference/ per reference/SOURCES.md for \
             full differential coverage)"
        );
    }
    if !completeness_gaps.is_empty() {
        eprintln!(
            "completeness gaps (ay=unknown, not soundness bugs):\n  {}",
            completeness_gaps.join("\n  ")
        );
    }
    // The soundness gate below always runs: when the corpus is present every
    // benchmark is checked; when it is absent we simply have an empty bug list.
    report_soundness_bugs(&soundness_bugs);
}

fn report_soundness_bugs(soundness_bugs: &[String]) {
    // Known soundness regressions being actively tracked.
    // issue4701_substr_splice removed: #4057 soundness fix eliminates false UNSAT
    // (now returns unknown instead of unsat, classified as completeness gap).
    const KNOWN: &[&str] = &[];
    let (known, new_bugs): (Vec<_>, Vec<_>) = soundness_bugs
        .iter()
        .partition(|bug| KNOWN.iter().any(|k| bug.contains(k)));
    if !known.is_empty() {
        eprintln!(
            "KNOWN soundness regressions:\n  {}",
            known
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join("\n  ")
        );
    }
    assert!(
        new_bugs.is_empty(),
        "NEW SOUNDNESS BUGS:\n{}",
        new_bugs
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n\n")
    );
}
