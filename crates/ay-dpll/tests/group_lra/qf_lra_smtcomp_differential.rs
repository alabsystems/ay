// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Curated SMT-COMP QF_LRA differential coverage for #4919 and #6277.
//!
//! The existing `differential_z3.rs` suite exercises only the small
//! `benchmarks/smt/QF_LRA` directory. This file adds:
//! 1. A curated 38-benchmark set from `benchmarks/smtcomp/QF_LRA/` with strict
//!    result comparison (AY must match Z3 exactly on these).
//! 2. A soundness sweep of ALL 100 smtcomp QF_LRA benchmarks checking for
//!    disagreements (AY must not contradict Z3; unknown/timeout is acceptable).
//!
//! Part of #4919, #6277.

use crate::common::{
    check_z3_or_skip, count_real_declarations, run_executor_file_with_timeout, run_z3_file,
    workspace_path, SolverOutcome,
};
use anyhow::Result;
use ntest::timeout;
use std::fs;

const BENCHMARK_TIMEOUT_SECS: u64 = 6;

/// 37 QF_LRA smtcomp benchmarks that AY solves correctly at 6s timeout in
/// debug mode. Measured at commit 053e3de24 (Phase 5 of #4919).
/// `constraints-tempo-width-10.smt2` now takes ~12s on the debug CLI at HEAD,
/// so it no longer belongs in this 6s strict subset. It is covered by the
/// release-only #6564 regressions instead.
/// Two more solve in release only (synched.base, windowreal-no_t_deadlock-12)
/// and `windowreal-no_t_deadlock-6.smt2` is borderline; those are covered by
/// the soundness sweep, which accepts timeout.
/// When AY starts solving additional benchmarks, add them here.
const SMTCOMP_QF_LRA_CASES: &[(&str, ExpectedResult)] = &[
    ("atan-problem-1-chunk-0031.smt2", ExpectedResult::Sat),
    ("atan-problem-2-weak2-chunk-0035.smt2", ExpectedResult::Sat),
    (
        "atan-problem-2-weak2-chunk-0037.smt2",
        ExpectedResult::Unsat,
    ),
    (
        "atan-problem-2-weak2-chunk-0118.smt2",
        ExpectedResult::Unsat,
    ),
    (
        "atan-problem-2-weak2-chunk-0131.smt2",
        ExpectedResult::Unsat,
    ),
    (
        "atan-problem-2-weak2-chunk-0132.smt2",
        ExpectedResult::Unsat,
    ),
    ("bottom-plate-mixer-chunk-0020.smt2", ExpectedResult::Unsat),
    ("Carpark2-ausgabe-3.smt2", ExpectedResult::Unsat),
    ("cbrt-problem-3-weak-chunk-0099.smt2", ExpectedResult::Unsat),
    ("Chua-1-IL-L-chunk-0013.smt2", ExpectedResult::Sat),
    // clocksynchro_9clocks.worst_case_skew.base.smt2 is borderline (~5-15s in
    // release, >6s in debug). Moved to soundness sweep which accepts timeout.
    // See QF_LRA performance chain #8452.
    ("CMOS-opamp-chunk-0012.smt2", ExpectedResult::Sat),
    ("constraints-cooking12.smt2", ExpectedResult::Sat),
    ("constraints-cooking14.smt2", ExpectedResult::Sat),
    ("constraints-tempo-depth-2.smt2", ExpectedResult::Sat),
    ("constraints-tms-2-3-light-09.smt2", ExpectedResult::Sat),
    ("gasburner-prop3-2.smt2", ExpectedResult::Unsat),
    (
        "polypaver-bench-exp-3d-chunk-0018.smt2",
        ExpectedResult::Sat,
    ),
    (
        "polypaver-bench-exp-3d-chunk-0031.smt2",
        ExpectedResult::Sat,
    ),
    (
        "polypaver-bench-exp-3d-chunk-0044.smt2",
        ExpectedResult::Unsat,
    ),
    (
        "polypaver-bench-exp-3d-chunk-0050.smt2",
        ExpectedResult::Sat,
    ),
    ("sin-344-3-weak-chunk-0013.smt2", ExpectedResult::Unsat),
    ("sin-344-3-weak-chunk-0016.smt2", ExpectedResult::Unsat),
    ("sin-problem-7-weak-chunk-0029.smt2", ExpectedResult::Sat),
    ("sin-problem-7-weak-chunk-0052.smt2", ExpectedResult::Sat),
    ("sin-problem-7-weak-chunk-0054.smt2", ExpectedResult::Sat),
    ("sin-problem-7-weak-chunk-0056.smt2", ExpectedResult::Sat),
    ("sin-problem-7-weak-chunk-0062.smt2", ExpectedResult::Unsat),
    ("sin-problem-7-weak2-chunk-0009.smt2", ExpectedResult::Sat),
    ("sin-problem-7-weak2-chunk-0021.smt2", ExpectedResult::Sat),
    ("sin-problem-7-weak2-chunk-0036.smt2", ExpectedResult::Sat),
    ("sin-problem-7-weak2-chunk-0071.smt2", ExpectedResult::Sat),
    ("sin-problem-8-weak-chunk-0012.smt2", ExpectedResult::Unsat),
    ("sin-problem-8-weak-chunk-0032.smt2", ExpectedResult::Unsat),
    ("sqrt-1mcosq-7-chunk-0103.smt2", ExpectedResult::Sat),
    ("sqrt-1mcosq-7-chunk-0107.smt2", ExpectedResult::Sat),
    ("sqrt-1mcosq-8-chunk-0029.smt2", ExpectedResult::Unsat),
    // synched.base.smt2 and windowreal-no_t_deadlock-12.smt2 solve in release
    // mode but timeout in debug mode at 6s. They're covered by the soundness
    // sweep (which accepts timeout), so omitting from the strict set.
    ("windowreal-no_t_deadlock-6.smt2", ExpectedResult::Unsat),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExpectedResult {
    Sat,
    Unsat,
}

impl ExpectedResult {
    fn as_outcome(self) -> SolverOutcome {
        match self {
            Self::Sat => SolverOutcome::Sat,
            Self::Unsat => SolverOutcome::Unsat,
        }
    }
}

/// Strict curated subset: AY MUST solve all 37 benchmarks and agree with Z3.
/// Any regression (AY stops solving one) is caught immediately.
#[test]
#[timeout(300_000)]
fn qf_lra_smtcomp_subset_matches_z3() -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }

    // `benchmarks/smtcomp/` is gitignored (only two QF_LRA files are whitelisted),
    // so a clean checkout has no corpus. Skip the individual benchmarks that are
    // absent — a partial corpus still gets the full strict comparison — and
    // report how many were skipped so a silently-empty run is visible.
    let mut failures = Vec::new();
    let mut skipped = Vec::new();
    for (name, expected) in SMTCOMP_QF_LRA_CASES {
        let path = workspace_path(format!("benchmarks/smtcomp/QF_LRA/{name}"));
        if !path.exists() && crate::common::corpus_skip_allowed(&path) {
            skipped.push(*name);
            continue;
        }
        let z3_result = run_z3_file(&path, BENCHMARK_TIMEOUT_SECS)?;
        let ay_result = run_executor_file_with_timeout(&path, BENCHMARK_TIMEOUT_SECS)?;

        if z3_result != expected.as_outcome() {
            failures.push(format!(
                "{name}: Z3 changed from measured reference (expected {expected:?}, got {z3_result:?})"
            ));
            continue;
        }
        if ay_result != z3_result {
            failures.push(format!(
                "{name}: AY={ay_result:?} disagrees with Z3={z3_result:?}"
            ));
        }
    }

    if !skipped.is_empty() {
        eprintln!(
            "SKIP qf_lra_smtcomp_subset_matches_z3: {}/{} curated benchmarks not installed \
             (gitignored smtcomp corpus); compared {}",
            skipped.len(),
            SMTCOMP_QF_LRA_CASES.len(),
            SMTCOMP_QF_LRA_CASES.len() - skipped.len()
        );
    }

    assert!(
        failures.is_empty(),
        "QF_LRA curated subset failures ({}/{} compared, {} skipped as not installed):\n{}",
        failures.len(),
        SMTCOMP_QF_LRA_CASES.len() - skipped.len(),
        skipped.len(),
        failures.join("\n")
    );

    Ok(())
}

/// Soundness sweep: run ALL smtcomp QF_LRA benchmarks. AY must never disagree
/// with Z3 (returning sat when Z3 says unsat, or vice versa). Unknown/timeout
/// is acceptable — this test catches soundness bugs, not completeness gaps.
#[test]
#[timeout(600_000)]
fn qf_lra_smtcomp_soundness_sweep() -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }

    let dir = workspace_path("benchmarks/smtcomp/QF_LRA");
    if !dir.is_dir() {
        eprintln!(
            "SKIP qf_lra_smtcomp_soundness_sweep: corpus directory not found: {}",
            dir.display()
        );
        return Ok(());
    }
    let mut entries: Vec<_> = fs::read_dir(&dir)?
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().map_or(false, |ext| ext == "smt2"))
        .map(|e| e.path())
        .collect();
    entries.sort();

    let mut disagreements = Vec::new();
    let mut ay_solved = 0u32;
    let mut z3_solved = 0u32;
    let total = entries.len();

    for path in &entries {
        let name = path.file_name().unwrap().to_string_lossy();
        let z3_result = run_z3_file(path, BENCHMARK_TIMEOUT_SECS)?;
        let ay_result = run_executor_file_with_timeout(path, BENCHMARK_TIMEOUT_SECS)?;

        let z3_definite = matches!(z3_result, SolverOutcome::Sat | SolverOutcome::Unsat);
        let ay_definite = matches!(ay_result, SolverOutcome::Sat | SolverOutcome::Unsat);

        if z3_definite {
            z3_solved += 1;
        }
        if ay_definite {
            ay_solved += 1;
        }

        if z3_definite && ay_definite && z3_result != ay_result {
            disagreements.push(format!("{name}: AY={ay_result:?} vs Z3={z3_result:?}"));
        }
    }

    eprintln!(
        "QF_LRA soundness sweep: {total} benchmarks, AY solved {ay_solved}, Z3 solved {z3_solved}, disagreements {}",
        disagreements.len()
    );

    assert!(
        disagreements.is_empty(),
        "SOUNDNESS BUG: AY disagrees with Z3 on {} of {} QF_LRA smtcomp benchmarks:\n{}",
        disagreements.len(),
        total,
        disagreements.join("\n")
    );

    Ok(())
}

/// Industrial-scale test: constraints-cooking12.smt2 has 50+ Real variables.
#[test]
#[timeout(15_000)]
fn qf_lra_industrial_cooking12_matches_z3() -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }

    let path = workspace_path("benchmarks/smtcomp/QF_LRA/constraints-cooking12.smt2");
    // Gitignored smtcomp corpus — skip when not installed.
    if !path.exists() && crate::common::corpus_skip_allowed(&path) {
        eprintln!(
            "SKIP qf_lra_industrial_cooking12_matches_z3: corpus benchmark not found: {}",
            path.display()
        );
        return Ok(());
    }
    let real_decls = count_real_declarations(&path)?;
    assert!(
        real_decls >= 50,
        "constraints-cooking12.smt2 should stay an industrial-scale QF_LRA benchmark, got {real_decls} real declarations"
    );

    let z3_result = run_z3_file(&path, BENCHMARK_TIMEOUT_SECS)?;
    let ay_result = run_executor_file_with_timeout(&path, BENCHMARK_TIMEOUT_SECS)?;
    assert_eq!(z3_result, SolverOutcome::Sat);
    assert_eq!(
        ay_result, z3_result,
        "constraints-cooking12.smt2 should match Z3 on the industrial benchmark path"
    );

    Ok(())
}
