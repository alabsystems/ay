// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-deterministic-inproc` is clock-free (2026-09-14): runs of one build
//! write byte-identical proofs, and count the same work, however loaded the
//! machine is.
//!
//! Before this, the flag replaced only the round, backbone and sweep walls
//! with counted work. The per-round inprocessing overhead behind
//! `adaptive_tick_scale` (buckets at 1, 3 and 8 ms) still read the clock, as
//! did the arena-compaction bias, lookahead's 500 ms wall, the 2 s BVE
//! cascade, gate extraction, the lucky and GF(p) probes and the indep_enum
//! schedule. On a 14-core Mac with 28 spinning processes, the flagged solve
//! of the formula below wrote a different proof in 2 of 3 loaded runs.
//!
//! A test binary of its own: it saturates every core, and cargo runs test
//! binaries one at a time, so the load never overlaps other tests.

use ntest::timeout;
use serde_json::{Map, Value};
use std::num::NonZero;
use std::path::Path;
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread::JoinHandle;
use std::time::Duration;

#[path = "common/random_3sat.rs"]
mod random_3sat;
#[path = "common/spawn.rs"]
mod spawn;

use random_3sat::random_3sat;
use spawn::OutputTimeout;

/// Busy threads that contend for every core until dropped.
struct CpuLoad {
    stop: Arc<AtomicBool>,
    threads: Vec<JoinHandle<()>>,
}

impl CpuLoad {
    fn start(threads: usize) -> Self {
        let stop = Arc::new(AtomicBool::new(false));
        let threads = (0..threads)
            .map(|seed| {
                let stop = Arc::clone(&stop);
                std::thread::spawn(move || {
                    let mut state = seed as u64 | 1;
                    while !stop.load(Ordering::Relaxed) {
                        for _ in 0..4096 {
                            state = std::hint::black_box(
                                state
                                    .wrapping_mul(6_364_136_223_846_793_005)
                                    .wrapping_add(1),
                            );
                        }
                    }
                })
            })
            .collect();
        Self { stop, threads }
    }
}

impl Drop for CpuLoad {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Relaxed);
        for thread in self.threads.drain(..) {
            let _ = thread.join();
        }
    }
}

/// One flagged solve in the SAT-COMP posture.
struct Run {
    verdict: String,
    proof: Vec<u8>,
    stats: Map<String, Value>,
}

fn solve(input: &Path, proof: &Path, extra: &[&str]) -> Run {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args([
            "solve",
            "--sat-variant",
            "default",
            "--sat-deterministic-inproc",
            "true",
            "--timeout=240000",
            "--proof",
        ])
        .arg(proof)
        .args([
            "--proof-format",
            "veripb",
            "--proof-checker",
            "veripb",
            "--no-verify-proof",
            "--stats-json",
        ])
        .args(extra)
        .arg(input)
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
        .output_timeout(Duration::from_secs(280))
        .expect("spawn ay solve");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let verdict = stdout
        .lines()
        .find(|line| line.starts_with("s "))
        .unwrap_or("no verdict")
        .to_string();
    let stats = stderr
        .lines()
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .find_map(|value| match value {
            Value::Object(map) if map.contains_key("conflicts") => Some(map),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no stats JSON on stderr:\n{stderr}"));
    Run {
        verdict,
        proof: std::fs::read(proof).unwrap_or_default(),
        stats,
    }
}

/// Stats keys that measure time or the host rather than work: they may
/// differ between runs whatever the search did. Rates (`*_per_sec`,
/// `*_mpps_*`) divide by wall time; `resource.*` reads the process and the
/// memory limit.
fn measures_time(key: &str) -> bool {
    ["_ms", "_us", "_ns", "_per_sec", "_pct_x100"]
        .iter()
        .any(|suffix| key.ends_with(suffix))
        || key.contains("_mpps")
        || key.starts_with("time.")
        || key.starts_with("resource.")
        || key.contains("rss")
}

/// The counted stats on which two runs differ.
fn counted_differences(a: &Map<String, Value>, b: &Map<String, Value>) -> Vec<String> {
    let mut keys: Vec<&String> = a.keys().chain(b.keys()).collect();
    keys.sort();
    keys.dedup();
    keys.into_iter()
        .filter(|key| !measures_time(key) && a.get(*key) != b.get(*key))
        .map(|key| format!("{key}: {:?} vs {:?}", a.get(key), b.get(key)))
        .collect()
}

/// Where two proofs first part, for the failure message.
fn first_difference(a: &[u8], b: &[u8]) -> String {
    let lines = a
        .split(|&byte| byte == b'\n')
        .zip(b.split(|&byte| byte == b'\n'));
    for (index, (x, y)) in lines.enumerate() {
        if x != y {
            return format!(
                "line {}: {:?} vs {:?}",
                index + 1,
                String::from_utf8_lossy(x),
                String::from_utf8_lossy(y)
            );
        }
    }
    format!(
        "one is a prefix of the other ({} vs {} bytes)",
        a.len(),
        b.len()
    )
}

/// Runs under CPU load write the unloaded run's proof, byte for byte, and
/// count the same work.
#[test]
#[timeout(900_000)]
fn deterministic_inproc_proofs_are_identical_under_cpu_load() {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("random-3sat-240.cnf");
    std::fs::write(&input, random_3sat(240, 1_128, 5)).expect("write CNF");

    let reference = solve(&input, &dir.path().join("unloaded.pbp"), &[]);
    assert_eq!(reference.verdict, "s UNSATISFIABLE");
    assert!(
        reference
            .proof
            .starts_with(b"pseudo-Boolean proof version 3.0"),
        "the unloaded run wrote no VeriPB proof"
    );

    // The test is only as strong as the timing decisions the solve reaches:
    // several inprocessing rounds (each sets the adaptive tick scale for the
    // next), the passes that scale gates, and reductions with compactions
    // (the compaction bias).
    let count = |key: &str| {
        reference
            .stats
            .get(key)
            .and_then(Value::as_u64)
            .unwrap_or(0)
    };
    let passes = [
        "backbone",
        "congruence",
        "probe",
        "subsume",
        "sweep",
        "vivify",
    ];
    let passes_run = passes
        .iter()
        .filter(|pass| count(&format!("sat.inproc_{pass}_runs")) >= 1)
        .count();
    assert!(
        count("conflicts") >= 20_000
            && count("sat.inproc_rounds") >= 3
            && passes_run >= 5
            && count("sat.reductions") >= 5
            && count("sat.arena_compactions") >= 1,
        "the formula no longer exercises the timing decisions this test is for; \
         conflicts {}, inprocessing rounds {}, passes run {passes_run} of {}, \
         reductions {}, compactions {}",
        count("conflicts"),
        count("sat.inproc_rounds"),
        passes.len(),
        count("sat.reductions"),
        count("sat.arena_compactions"),
    );

    let cores = std::thread::available_parallelism().map_or(4, NonZero::get);
    for (index, threads) in [2 * cores, 2 * cores, 3 * cores].into_iter().enumerate() {
        let run = {
            let _load = CpuLoad::start(threads);
            solve(&input, &dir.path().join(format!("loaded-{index}.pbp")), &[])
        };
        let label = format!("loaded run {index} ({threads} busy threads on {cores} cores)");
        assert_eq!(run.verdict, reference.verdict, "{label}");
        assert!(
            run.proof == reference.proof,
            "{label} wrote a different proof ({} vs {} bytes); first difference at {}",
            run.proof.len(),
            reference.proof.len(),
            first_difference(&run.proof, &reference.proof)
        );
        let differences = counted_differences(&run.stats, &reference.stats);
        assert!(
            differences.is_empty(),
            "{label} counted different work: {differences:?}"
        );
    }
}

/// `--sat-conflict-cap` stops the flagged search at a counted point: a capped
/// run answers UNKNOWN at its N-th conflict, and a loaded run stops at the same
/// place having counted the same work. The formula needs more than 20,000
/// conflicts (the test above), so the cap binds.
#[test]
#[timeout(600_000)]
fn conflict_cap_stops_loaded_and_unloaded_runs_at_the_same_point() {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("random-3sat-240.cnf");
    std::fs::write(&input, random_3sat(240, 1_128, 5)).expect("write CNF");
    let cap = ["--sat-conflict-cap", "5000"];
    let unloaded = solve(&input, &dir.path().join("capped.pbp"), &cap);
    let cores = std::thread::available_parallelism().map_or(4, NonZero::get);
    let loaded = {
        let _load = CpuLoad::start(2 * cores);
        solve(&input, &dir.path().join("capped-loaded.pbp"), &cap)
    };
    for (label, run) in [("unloaded", &unloaded), ("loaded", &loaded)] {
        assert_eq!(run.verdict, "s UNKNOWN", "{label}");
        assert_eq!(
            run.stats.get("conflicts").and_then(Value::as_u64),
            Some(5_000),
            "{label}"
        );
    }
    let differences = counted_differences(&loaded.stats, &unloaded.stats);
    assert!(
        differences.is_empty(),
        "the loaded capped run counted different work: {differences:?}"
    );
}

/// The flag refuses the routes that decide by timing: a parallel portfolio
/// (the first finisher wins), cube-and-conquer workers and a fallback stage
/// cut by the clock. Without the flag they are not refused.
#[test]
#[timeout(240_000)]
fn deterministic_inproc_refuses_the_routes_that_decide_by_timing() {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("random-3sat-60.cnf");
    std::fs::write(&input, random_3sat(60, 258, 3)).expect("write CNF");
    let routes: [&[&str]; 3] = [
        &["--parallel", "2"],
        &["--cube-and-conquer", "2"],
        &[
            "--fallback-solver",
            "/usr/bin/true",
            "--timeout=20000",
            "--fallback-after=10000",
        ],
    ];
    for route in routes {
        for flagged in [true, false] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
            command.arg("solve");
            if flagged {
                command.args(["--sat-deterministic-inproc", "true"]);
            }
            let output = command
                .args(route)
                .arg(&input)
                .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
                .output_timeout(Duration::from_secs(60))
                .expect("spawn ay solve");
            let stderr = String::from_utf8_lossy(&output.stderr);
            let refused = stderr.contains("--sat-deterministic-inproc is incompatible with");
            if flagged {
                assert!(
                    refused && output.status.code() == Some(1),
                    "{route:?} with the flag was not refused: exit {:?}\n{stderr}",
                    output.status.code()
                );
            } else {
                assert!(
                    !refused,
                    "{route:?} without the flag was refused:\n{stderr}"
                );
            }
        }
    }
}
