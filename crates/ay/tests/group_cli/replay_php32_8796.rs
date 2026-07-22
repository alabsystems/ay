// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Phase-2 integration test for `ay_replay::drat::SequentialReplayer` (#8796).
//!
//! Drives a fresh ay cold solve on PHP(3,2) to emit a DRAT proof, replays
//! the proof with the sequential RUP-only replayer, and asserts both agree.
//! Prints wall-clock numbers to stderr via `--nocapture` so the main-loop
//! can paste them into the #8796 progress comment.

use ay_replay::drat::{DratReplayInput, SequentialReplayer};
use ntest::timeout;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use crate::spawn::OutputTimeout;

/// PHP(3,2) — 3 pigeons, 2 holes. UNSAT, requires real CDCL.
const PHP_3_2_CNF: &str = "p cnf 6 9\n\
1 2 0\n\
3 4 0\n\
5 6 0\n\
-1 -3 0\n\
-1 -5 0\n\
-3 -5 0\n\
-2 -4 0\n\
-2 -6 0\n\
-4 -6 0\n";

struct CleanupGuard(PathBuf);
impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn temp_path(stem: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_replay_8796_{}_{}_{}.{}",
        std::process::id(),
        stem,
        id,
        extension
    ));
    (path.clone(), CleanupGuard(path))
}

#[test]
#[timeout(60_000)]
fn php_3_2_drat_replay_matches_cold_solve() {
    let ay_bin = env!("CARGO_BIN_EXE_ay");
    let (cnf_path, _cnf_cleanup) = temp_path("cnf", "cnf");
    let (proof_path, _proof_cleanup) = temp_path("proof", "drat");
    {
        let mut f = std::fs::File::create(&cnf_path).expect("create cnf");
        f.write_all(PHP_3_2_CNF.as_bytes()).expect("write cnf");
    }

    // Stage 1: fresh cold solve, emitting DRAT.
    let cold_start = Instant::now();
    let out = Command::new(ay_bin)
        .arg("--drat")
        .arg(&proof_path)
        .arg(&cnf_path)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay");
    let cold_wall = cold_start.elapsed();
    assert_eq!(
        out.status.code(),
        Some(20),
        "expected ay exit 20 (UNSAT): stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );

    let proof_bytes = std::fs::read(&proof_path).expect("read proof");
    assert!(!proof_bytes.is_empty(), "DRAT proof must be non-empty");

    // Stage 2: sequential DRAT replay.
    let replayer = SequentialReplayer::new();
    let plan = replayer
        .load(&DratReplayInput {
            cnf: PHP_3_2_CNF.as_bytes(),
            proof: &proof_bytes,
        })
        .expect("load replay plan");

    // Warm cache: run once, discard timing (ensures allocator / page faults
    // don't dominate the measured replay). Then the measured run is the
    // steady-state replay cost.
    let _ = replayer.replay(&plan).expect("warm replay");
    let replay_start = Instant::now();
    let outcome = replayer.replay(&plan).expect("replay");
    let replay_wall = replay_start.elapsed();

    assert!(
        outcome.is_verified(),
        "replay of PHP(3,2) DRAT must verify: {outcome} (reason={:?})",
        outcome.failure_reason
    );

    // Timing is informational — PHP(3,2) is microseconds in both paths, so
    // noise dominates for an instance this small. The comparison is
    // load-bearing on deeper BMC unrollings (Phase 3 follow-up). We still
    // print the numbers so the main-loop can paste them into #8796.
    eprintln!(
        "#8796 PHP(3,2) timing: cold_solve_incl_process_spawn={:?} \
         in_process_replay={:?} proof_bytes={} steps={} adds_ok={} dels={}",
        cold_wall,
        replay_wall,
        proof_bytes.len(),
        plan.step_count(),
        outcome.add_steps_verified,
        outcome.delete_steps_applied
    );
    eprintln!(
        "#8796 speedup_factor_vs_process_spawn={:.1}x \
         (replay avoids process start + DIMACS parse in solver + CDCL)",
        cold_wall.as_nanos() as f64 / replay_wall.as_nanos().max(1) as f64
    );
}
