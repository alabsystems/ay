// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bench-1 (lia-hot-loop plan): end-to-end DRAGON_3 depth-0/1 BMC checks.
//!
//! Reconstructs the exact persistent-executor transition-system BMC script
//! (`solve_transition_system_incremental`) for
//! `vmt-chc-benchmarks/lustre/DRAGON_3_e7_3211_000.smt2` and times the
//! per-depth `(check-sat)`s on one `ay_dpll::Executor`, in both lanes:
//!
//! - incremental lane: init@0, `(push 1)` query@0 `(check-sat)`, `(pop 1)`
//!   transition@0, `(push 1)` query@1 `(check-sat)` — this shape is ALL CHC
//!   BMC/PDR/Houdini traffic, routed to the eager BCP-interleaved arm by
//!   Fix B1 (`AY_DPLL_LIA_INCREMENTAL_EAGER`, default ON);
//! - standalone lane: init@0 + transition@0 + query@1 flat, one
//!   `(check-sat)` — the eager arm's original lane, as the reference point.
//!
//! Ground truth (z3 4.x, 13ms total): depth-0 is **unsat** (no
//! counterexample of 0 transitions), depth-1 is **sat** (a depth-1
//! counterexample exists; it is exactly what makes DRAGON_3's CHC verdict
//! `unsat`).
//!
//! Measured on this machine (release, 2026-06): the depth-0 incremental
//! check is the B1 gate — lazy arm times out at 30s, eager arm answers
//! unsat in ~30ms (>1000x). The depth-1 SAT-type query livelocks under
//! default LRA theory propagation (>300s; sat-side-model-search diagnosis)
//! and answers `sat` in ~1-3s with propagation off. Both lanes therefore
//! mirror the production TS lane's executor setup
//! (`set_no_lra_theory_propagation(true)`, Fix 1); the test reports
//! verdict/time under a 10s budget and fails on an `unsat` soundness flip.
//!
//! `#[ignore]`d perf gate: run explicitly with
//! `cargo test -p ay-chc --test group_misc --release -- --ignored perf_dragon --nocapture`.
//! The benchmark corpus lives outside the repo for most checkouts; set
//! `AY_CHC_BENCH_ROOT` to the `benchmarks/` root (the test skips when the
//! instance file is absent).

use std::time::{Duration, Instant};

const DRAGON_3: &str =
    "chc/chc-comp26-benchmarks/vmt-chc-benchmarks/lustre/DRAGON_3_e7_3211_000.smt2";

fn dragon3_path() -> Option<std::path::PathBuf> {
    let root = std::env::var("AY_CHC_BENCH_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("..")
                .join("benchmarks")
        });
    let path = root.join(DRAGON_3);
    path.exists().then_some(path)
}

fn dragon3_segments(depth: usize) -> Option<Vec<String>> {
    let path = dragon3_path()?;
    let text = std::fs::read_to_string(&path).expect("benchmark should be readable");
    let problem = ay_chc::ChcParser::parse(&text).expect("DRAGON_3 should parse as CHC");
    let segments = ay_chc::BmcSolver::ts_incremental_script_segments_for_test(problem, depth)
        .expect("DRAGON_3 should be a supported transition system");
    Some(segments)
}

fn exec_segment(exec: &mut ay_dpll::Executor, segment: &str) -> Vec<String> {
    let commands = ay_frontend::parse(segment).expect("segment should parse");
    let mut outputs = Vec::new();
    for cmd in &commands {
        if let Some(out) = exec.execute(cmd).expect("segment should execute") {
            outputs.push(out);
        }
    }
    outputs
}

fn verdict(outputs: &[String]) -> String {
    outputs
        .iter()
        .map(|s| s.trim())
        .find(|s| matches!(*s, "sat" | "unsat" | "unknown"))
        .unwrap_or("unknown")
        .to_string()
}

/// Utility: dump the depth-1 script segments to the directory named by
/// `AY_DUMP_TS_SCRIPT_DIR` for CLI-level iteration (no solving).
#[test]
#[ignore = "utility; set AY_DUMP_TS_SCRIPT_DIR and AY_CHC_BENCH_ROOT"]
fn dump_dragon_depth1_segments() {
    let Ok(dir) = std::env::var("AY_DUMP_TS_SCRIPT_DIR") else {
        eprintln!("SKIP: AY_DUMP_TS_SCRIPT_DIR not set");
        return;
    };
    let Some(segments) = dragon3_segments(1) else {
        eprintln!("SKIP: DRAGON_3 instance not found (set AY_CHC_BENCH_ROOT)");
        return;
    };
    for (i, seg) in segments.iter().enumerate() {
        let p = std::path::Path::new(&dir).join(format!("segment_{i}.smt2"));
        std::fs::write(&p, seg).expect("segment should write");
        eprintln!("wrote {}", p.display());
    }
}

#[test]
#[ignore = "perf gate; needs the chc-comp26 benchmark corpus (AY_CHC_BENCH_ROOT)"]
fn perf_dragon_bmc_depth1_incremental_lane() {
    let Some(segments) = dragon3_segments(1) else {
        eprintln!("SKIP: DRAGON_3 instance not found (set AY_CHC_BENCH_ROOT)");
        return;
    };
    // [init@0, push+query@0+check, pop+transition@0, push+query@1+check]
    assert_eq!(segments.len(), 4, "depth-1 script should have 4 segments");

    let mut exec = ay_dpll::Executor::new();
    exec.set_timeout(Some(Duration::from_secs(10)));
    // Mirror the production TS lane (Fix 1): LRA propagation off.
    exec.set_no_lra_theory_propagation(true);
    exec_segment(&mut exec, &segments[0]);

    // Depth 0 (unsat): THE B1 gate. Lazy arm: 30s timeout; eager: ~30ms.
    let d0_start = Instant::now();
    let d0 = verdict(&exec_segment(&mut exec, &segments[1]));
    let d0_secs = d0_start.elapsed().as_secs_f64();

    exec_segment(&mut exec, &segments[2]);

    // Depth 1 (sat per z3): answers sat in ~1-3s with propagation off
    // (Fix 1); livelocked (>300s) under default propagation.
    let d1_start = Instant::now();
    let d1 = verdict(&exec_segment(&mut exec, &segments[3]));
    let d1_secs = d1_start.elapsed().as_secs_f64();
    let round_trips = exec.statistics().get_int("dpll.round_trips").unwrap_or(0);

    eprintln!(
        "perf_dragon_bmc_depth1 incremental lane: depth0={d0} {d0_secs:.3}s \
         depth1={d1} {d1_secs:.3}s round_trips={round_trips}"
    );

    assert_eq!(d0, "unsat", "DRAGON_3 depth-0 must be unsat");
    // Generous regression tripwire: pre-B1 the lazy arm burned the whole 10s
    // budget on depth 0 without an answer; the eager-routed check answers in
    // well under this even in debug builds.
    assert!(
        d0_secs < 8.0,
        "depth-0 incremental check took {d0_secs:.3}s (tripwire 8s; \
         the lazy arm times out here — did B1 routing regress?)"
    );
    // Depth 1 has a counterexample (z3: sat in 9ms). `unsat` would be a
    // soundness bug; `unknown` is the current known gap (SAT-type model
    // search on DRAGON-class is the next frontier after B1).
    assert_ne!(
        d1, "unsat",
        "DRAGON_3 depth-1 is sat (z3); unsat is unsound"
    );
}

#[test]
#[ignore = "perf gate; needs the chc-comp26 benchmark corpus (AY_CHC_BENCH_ROOT)"]
fn perf_dragon_bmc_depth1_standalone_lane() {
    let Some(segments) = dragon3_segments(1) else {
        eprintln!("SKIP: DRAGON_3 instance not found (set AY_CHC_BENCH_ROOT)");
        return;
    };
    assert_eq!(segments.len(), 4, "depth-1 script should have 4 segments");

    // Flat lane: init@0 + transition@0 + query@1 + one check-sat, no push/pop
    // framing. Strip the framing lines from the incremental segments so the
    // asserted conjunction is exactly the depth-1 query.
    let mut flat = String::new();
    flat.push_str(&segments[0]);
    for line in segments[2].lines().chain(segments[3].lines()) {
        if line == "(push 1)" || line == "(pop 1)" {
            continue;
        }
        flat.push_str(line);
        flat.push('\n');
    }

    let mut exec = ay_dpll::Executor::new();
    exec.set_timeout(Some(Duration::from_secs(10)));
    // Mirror the production TS-lane confirmation re-solve (Fix 1):
    // LRA propagation off on the flat depth-1 query.
    exec.set_no_lra_theory_propagation(true);
    let start = Instant::now();
    let d1 = verdict(&exec_segment(&mut exec, &flat));
    let secs = start.elapsed().as_secs_f64();
    let round_trips = exec.statistics().get_int("dpll.round_trips").unwrap_or(0);

    eprintln!(
        "perf_dragon_bmc_depth1 standalone lane: depth1={d1} {secs:.3}s \
         round_trips={round_trips}"
    );

    // Depth 1 has a counterexample (z3: sat in 9ms). See the incremental
    // lane: `unknown` is the current known gap, `unsat` would be unsound.
    assert_ne!(
        d1, "unsat",
        "DRAGON_3 depth-1 is sat (z3); unsat is unsound"
    );
}
