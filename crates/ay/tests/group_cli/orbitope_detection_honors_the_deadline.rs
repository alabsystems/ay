// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The orbitope route honors the `--timeout` deadline (2026-09-15, owner).
//!
//! On latin_square_10.15 its detection runs about 130 s, and before this fix it
//! never looked at the deadline: a timeout inside it went unanswered until the
//! watchdog's hard exit, 2 s later. The formula below is the same shape, a
//! colouring with only at-least-one columns: its detection runs about 44 s in
//! release. A short timeout must end the solve inside the route, cleanly: the
//! route says it stopped, the verdict is `s UNKNOWN`, and no proof is left.
//! The watchdog's hard exit also prints `s UNKNOWN` and discards the proof, but
//! not the stats: only the solve's own stop path prints `--stats-json`.

use crate::spawn::OutputTimeout;
use ntest::timeout;
use std::io::Write;
use std::process::Command;
use std::time::{Duration, Instant};

/// A 3-colouring of a 2,000-vertex graph with about 166,000 edges, with no
/// per-vertex at-most-one clauses (the latin_square shape): 500,000 clauses.
fn write_colouring(path: &std::path::Path) {
    const VERTICES: u64 = 2_000;
    const COLOURS: u64 = 3;
    let edges: Vec<(u64, u64)> = (0..VERTICES)
        .flat_map(|u| ((u + 1)..VERTICES).map(move |v| (u, v)))
        .filter(|&(u, v)| ((u.wrapping_mul(2_654_435_761) ^ v.wrapping_mul(40_503)) >> 7) % 12 == 0)
        .collect();
    let var = |v: u64, c: u64| 1 + COLOURS * v + c;
    let mut out = std::io::BufWriter::new(std::fs::File::create(path).expect("create CNF"));
    let clauses = VERTICES + COLOURS * edges.len() as u64;
    writeln!(out, "p cnf {} {clauses}", VERTICES * COLOURS).expect("write CNF");
    for v in 0..VERTICES {
        writeln!(out, "{} {} {} 0", var(v, 0), var(v, 1), var(v, 2)).expect("write CNF");
    }
    for &(u, v) in &edges {
        for c in 0..COLOURS {
            writeln!(out, "-{} -{} 0", var(u, c), var(v, c)).expect("write CNF");
        }
    }
    out.flush().expect("flush CNF");
}

#[test]
#[timeout(600_000)]
fn a_timeout_inside_orbitope_detection_ends_the_solve_cleanly() {
    let dir = tempfile::tempdir().expect("tempdir");
    let cnf = dir.path().join("colouring-2000x3.cnf");
    write_colouring(&cnf);
    let proof = dir.path().join("proof.pbp");
    // Well inside detection in both builds: release reaches the route in about
    // a second. The workspace dev/test profile is `opt-level = 1`, so a debug
    // build is NOT the unoptimized build the old 60 s assumed: measured
    // 2026-09-23 on a GB10 pinned to one core, detection of this fixture ends at
    // 61.9 s on a Cortex-X925 and 122.4 s on a Cortex-A725, so 60 s sat 2 s from
    // the end of detection and the test flipped with load. 10 s and 20 s both
    // stop inside the route on both core types, so 20 s keeps a 2x margin to
    // reaching the route and a 3x margin to the end of detection.
    let timeout_ms: u64 = if cfg!(debug_assertions) {
        20_000
    } else {
        5_000
    };
    let started = Instant::now();
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["solve", "--sat-variant", "default"])
        .args(["--sat-deterministic-inproc", "true"])
        .arg(format!("--timeout={timeout_ms}"))
        .arg("--proof")
        .arg(&proof)
        .args([
            "--proof-format",
            "veripb",
            "--proof-checker",
            "veripb",
            "--no-verify-proof",
        ])
        .arg("--stats-json")
        .arg(&cnf)
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .env(
            "AY_INTERNAL_SATCOMP_WRAPPER",
            "main-regular-default-veripb-v1",
        )
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_SAT_VARIANT", "default")
        .env("AY_COMPETITION_JIT_MODE", "off")
        .output_timeout(Duration::from_millis(timeout_ms + 240_000))
        .expect("spawn ay solve");
    let elapsed = started.elapsed();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let context = format!("after {elapsed:?}\nstdout:\n{stdout}\nstderr tail:\n{}", {
        let lines: Vec<&str> = stderr.lines().collect();
        lines[lines.len().saturating_sub(20)..].join("\n")
    });
    assert!(
        stderr.contains("c symmetry: orbitope route stopped: DeadlineExceeded"),
        "the deadline did not stop the orbitope route; {context}"
    );
    assert!(
        !stderr.contains("c symmetry: orbitope 3x2000 matrix"),
        "detection ran to the end despite the deadline; {context}"
    );
    assert!(
        stdout.lines().any(|line| line == "s UNKNOWN"),
        "expected s UNKNOWN; {context}"
    );
    assert!(!proof.exists(), "a proof was left behind; {context}");
    assert!(
        stderr
            .lines()
            .any(|line| line.starts_with('{') && line.contains("\"conflicts\"")),
        "no stats JSON: the watchdog's hard exit ended the solve, not its own stop; {context}"
    );
}
