// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Depth-0/1 transition-system BMC script-shape regression.
//!
//! Reconstructs the exact persistent-executor transition-system BMC script
//! (`solve_transition_system_incremental`) for a bounded counter fixture and
//! checks the per-depth `(check-sat)`s on one `ay_dpll::Executor`, in both
//! lanes:
//!
//! - incremental lane: init@0, `(push 1)` query@0 `(check-sat)`, `(pop 1)`
//!   transition@0, `(push 1)` query@1 `(check-sat)` — this shape is ALL CHC
//!   BMC/PDR/Houdini traffic, routed to the eager BCP-interleaved arm by
//!   Fix B1 (`AY_DPLL_LIA_INCREMENTAL_EAGER`, default ON);
//! - standalone lane: init@0 + transition@0 + query@1 flat, one
//!   `(check-sat)` — the eager arm's original lane, as the reference point.
//!
//! Ground truth: depth-0 is **unsat** (no counterexample of 0 transitions);
//! depth-1 is **sat**.
//!
//! The fixture preserves the script protocol diagnosed on DRAGON_3 while
//! remaining hermetic. External benchmark exports use `ts_script_export`;
//! bounded solver campaigns use `chc_corpus_campaign`.

use std::time::{Duration, Instant};

fn script_segments(text: &str, depth: usize) -> Vec<String> {
    let problem = ay_chc::ChcParser::parse(text).expect("fixture should parse as CHC");
    ay_chc::BmcSolver::ts_incremental_script_segments_for_test(problem, depth)
        .expect("fixture should be a supported transition system")
}

fn builtin_segments(depth: usize) -> Vec<String> {
    const BUILTIN: &str = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (xp Int))
    (=> (and (inv x) (= xp (+ x 1))) (inv xp))))
(assert (forall ((x Int)) (=> (and (inv x) (= x 1)) false)))
(check-sat)
"#;

    script_segments(BUILTIN, depth)
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

/// Round-trip the depth-1 script segments through a temporary directory.
#[test]
fn bounded_depth1_segments_round_trip() {
    let segments = builtin_segments(1);
    let temporary = tempfile::tempdir().expect("temporary segment directory");
    let dir = temporary.path();
    assert_eq!(segments.len(), 4, "depth-1 script should have 4 segments");
    for (i, seg) in segments.iter().enumerate() {
        let p = dir.join(format!("segment_{i}.smt2"));
        std::fs::write(&p, seg).expect("segment should write");
        assert_eq!(
            std::fs::read_to_string(&p).expect("segment should read"),
            *seg,
            "exported segment must round-trip"
        );
    }
}

#[test]
fn bounded_depth1_incremental_lane() {
    let segments = builtin_segments(1);
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

    // Depth 1 is satisfiable; production uses the same propagation setting.
    let d1_start = Instant::now();
    let d1 = verdict(&exec_segment(&mut exec, &segments[3]));
    let d1_secs = d1_start.elapsed().as_secs_f64();
    let round_trips = exec.statistics().get_int("dpll.round_trips").unwrap_or(0);

    eprintln!(
        "bounded_depth1 incremental lane: depth0={d0} {d0_secs:.3}s \
         depth1={d1} {d1_secs:.3}s round_trips={round_trips}"
    );

    assert_eq!(d0, "unsat", "bounded fixture depth-0 must be unsat");
    // Generous regression tripwire: pre-B1 the lazy arm burned the whole 10s
    // budget on depth 0 without an answer; the eager-routed check answers in
    // well under this even in debug builds.
    assert!(
        d0_secs < 8.0,
        "depth-0 incremental check took {d0_secs:.3}s (tripwire 8s; \
         the lazy arm times out here — did B1 routing regress?)"
    );
    // Depth 1 has a counterexample; `unsat` would be a soundness bug.
    assert_ne!(
        d1, "unsat",
        "bounded fixture depth-1 is sat; unsat is unsound"
    );
    assert_eq!(d1, "sat", "built-in depth-1 counterexample must be found");
}

#[test]
fn bounded_depth1_standalone_lane() {
    let segments = builtin_segments(1);
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
        "bounded_depth1 standalone lane: depth1={d1} {secs:.3}s \
         round_trips={round_trips}"
    );

    // Depth 1 has a counterexample; `unsat` would be unsound.
    assert_ne!(
        d1, "unsat",
        "bounded fixture depth-1 is sat; unsat is unsound"
    );
    assert_eq!(d1, "sat", "built-in depth-1 counterexample must be found");
}
