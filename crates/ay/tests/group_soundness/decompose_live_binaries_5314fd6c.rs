// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-COMP 2026 5314fd6c, shrunk: decompose read binary watch entries of
//! garbage clauses (fixed 2026-09-14 in 01ccc94e4).
//!
//! The solver sometimes learns a binary it already holds. Eager subsumption
//! marks the older copy garbage without unlinking it, and the targeted watch
//! flush removes stale entries one list at a time. So a half-removed binary
//! reached decompose as an implication without its contrapositive. The SCC
//! lost skew symmetry and chained the representative map, and the rewrite and
//! the reconstruction then lost constraints. With `--sat-congruence-bounded-occs
//! true`, the unfixed release build failed its own model check on this UNSAT
//! fixture (FINALIZE_SAT_FAIL) after about 16 s. Its fail-closed rescue retry
//! then answered `s UNKNOWN` at the 90 s budget.
//!
//! The fixture is a sub-miter of 5314fd6c. It keeps 3,018 of the 9,688
//! difference literals under the flattened output OR, with their cones of
//! influence and the original variable numbers: 441,144 clauses, UNSAT like
//! the instance, and the smallest failing subset delta debugging reached.
//!
//! Both tests run the shipped SAT-COMP posture under
//! `--sat-deterministic-inproc`, so the search does not depend on machine load,
//! and each names the switch: `true` (the default since 2026-09-15) or `false`.
//! They require no model-check failure, no chained representative map, and
//! never `s SATISFIABLE`. The fixed release build proves the fixture UNSAT with
//! the switch in about 41 s. Without the switch, the unbounded
//! congruence closure runs out of memory in preprocessing within seconds,
//! before any decompose, in both builds.
//!
//! A debug build runs about 18 times slower, so its budget ends the search long
//! before the old failure point: the pin needs `--release`.

use crate::corpus::optional_corpus_file;
use crate::spawn::OutputTimeout;
use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;
use tempfile::TempDir;

/// The solve budget: in release, well past the unfixed build's failure point.
fn budget_ms() -> u64 {
    if cfg!(debug_assertions) {
        30_000
    } else {
        90_000
    }
}

/// The fixture, unpacked from its zip archive into `dir`, or `None` where the
/// tree does not carry it: `publish/manifest.txt` keeps `benchmarks/sat/regression`
/// out of the public export and the SAT-COMP archive (owner decision, 2026-09-14).
/// That absence is a skip, announced on stderr, and a failure under
/// `AY_REQUIRE_CORPUS=1` — never a pass that checked something.
fn unpack_fixture(dir: &TempDir) -> Option<PathBuf> {
    let archive = optional_corpus_file(
        "decompose_live_binaries_5314fd6c",
        "benchmarks/sat/regression/5314fd6c-decompose-shrunk.cnf.zip",
    )?;
    let file =
        std::fs::File::open(&archive).unwrap_or_else(|e| panic!("open {}: {e}", archive.display()));
    let mut zip = zip::ZipArchive::new(file).expect("read fixture archive");
    let mut entry = zip.by_index(0).expect("fixture archive entry");
    let cnf = dir.path().join("5314fd6c-decompose-shrunk.cnf");
    let mut out = std::fs::File::create(&cnf).expect("create fixture CNF");
    std::io::copy(&mut entry, &mut out).expect("unpack fixture CNF");
    Some(cnf)
}

fn solve(bounded_occs: bool) -> Option<(String, String)> {
    let dir = tempfile::tempdir().expect("tempdir");
    let fixture = unpack_fixture(&dir)?;
    let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
    command
        .args(["solve", "--sat-variant", "default"])
        .args(["--sat-deterministic-inproc", "true", "--stats-json"])
        .arg(format!("--timeout={}", budget_ms()));
    // Both postures are named: the switch is ON by default since 2026-09-15.
    command.args([
        "--sat-congruence-bounded-occs",
        if bounded_occs { "true" } else { "false" },
    ]);
    let output = command
        .arg(&fixture)
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .env(
            "AY_INTERNAL_SATCOMP_WRAPPER",
            "main-regular-default-veripb-v1",
        )
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_SAT_VARIANT", "default")
        .env("AY_COMPETITION_JIT_MODE", "off")
        .env_remove("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT")
        .output_timeout(Duration::from_millis(budget_ms() + 120_000))
        .expect("spawn ay solve");
    Some((
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    ))
}

fn assert_no_model_check_failure(bounded_occs: bool) {
    let Some((stdout, stderr)) = solve(bounded_occs) else {
        return;
    };
    let verdict = stdout
        .lines()
        .find(|line| line.starts_with("s "))
        .unwrap_or("-");
    assert!(
        matches!(verdict, "s UNSATISFIABLE" | "s UNKNOWN"),
        "bounded_occs={bounded_occs}: verdict {verdict} on an UNSAT fixture\n{stderr}"
    );
    assert!(
        !stderr.contains("FINALIZE_SAT_FAIL"),
        "bounded_occs={bounded_occs}: the model check failed\n{stderr}"
    );
    // A memory-out prints no stats line. Without the switch that is the expected
    // end: the unbounded congruence closure runs out of memory in preprocessing.
    let stats = stderr
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .find(|value| value.get("mode").is_some());
    let Some(stats) = stats else {
        assert!(!bounded_occs, "missing stats JSON object\n{stderr}");
        return;
    };
    assert_eq!(
        stats
            .get("sat.decomp_chained_reprs")
            .and_then(serde_json::Value::as_u64),
        Some(0),
        "bounded_occs={bounded_occs}: a chained representative map"
    );
}

#[test]
#[timeout(300_000)]
fn shrunk_5314fd6c_with_bounded_occs_passes_its_model_check() {
    assert_no_model_check_failure(true);
}

#[test]
#[timeout(300_000)]
fn shrunk_5314fd6c_without_bounded_occs_passes_its_model_check() {
    assert_no_model_check_failure(false);
}
