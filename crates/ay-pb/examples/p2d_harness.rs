// P2d complete-engine profiling harness (see the development design notes §P2d).
//
// Runs the NATIVE CDCL engine (`PbCdclSolver`) directly on one OPB instance —
// the exact code path `ay-pb pb solve --native` (decision) and the portfolio's
// `solve_optimization_native` arm (optimization) exercise — with a wall-clock
// deadline. Single-threaded and deterministic, so wall-clock A/B comparisons
// and `sample`-based profiles attribute time to the propagation / conflict
// analysis hot loop without portfolio noise.
//
// Usage: cargo run --release --example p2d_harness -- <file.opb> [timeout_ms] [--no-eq-dp]
//
// `--no-eq-dp` disables the single-equality knapsack DP special case
// (A/B baseline arm; the default keeps it on, matching production).
//
// Output (one line, machine-readable):
//   P2D <verdict> obj=<objective|-> wall_s=<secs> conflicts=<n> propagations=<n> decisions=<n> restarts=<n>

use std::time::{Duration, Instant};

use ay_pb::{parse_opb, PbCdclResult, PbCdclSolver};

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: p2d_harness <file.opb> [timeout_ms]");
    let mut timeout_ms: u64 = 10_000;
    let mut eq_dp_enabled = true;
    for arg in args {
        if arg == "--no-eq-dp" {
            eq_dp_enabled = false;
        } else {
            timeout_ms = arg.parse().expect("timeout_ms must be an integer");
        }
    }

    let text = std::fs::read_to_string(&path).expect("failed to read instance");
    let instance = parse_opb(&text).expect("failed to parse OPB");

    let start = Instant::now();
    let deadline = start + Duration::from_millis(timeout_ms);
    let should_stop = || Instant::now() >= deadline;

    let mut solver = PbCdclSolver::new_interruptible(&instance, should_stop);
    solver.set_eq_knapsack_dp_enabled(eq_dp_enabled);
    // Thread the wall-clock deadline so internal sub-budgets (root LP bound)
    // are sized proportionally to the remaining time — the same wiring the
    // production callers (portfolio / ay CLI) use.
    solver.set_solve_deadline(Some(deadline));
    let result = match instance.objective.as_ref() {
        Some(objective) => solver.solve_optimize_interruptible(objective, None, should_stop),
        None => solver.solve_interruptible(should_stop),
    };
    let wall = start.elapsed().as_secs_f64();

    let (verdict, obj) = match &result {
        PbCdclResult::Satisfiable(_) => ("SATISFIABLE", None),
        PbCdclResult::Unsatisfiable => ("UNSATISFIABLE", None),
        PbCdclResult::Unknown => ("UNKNOWN", None),
        PbCdclResult::Optimal(_, value) => ("OPTIMUM", Some(*value)),
        PbCdclResult::Feasible(_, value) => ("FEASIBLE", Some(*value)),
        _ => ("OTHER", None),
    };
    let stats = solver.stats();
    println!(
        "P2D {verdict} obj={} wall_s={wall:.3} conflicts={} propagations={} decisions={} restarts={}",
        obj.map_or_else(|| "-".to_string(), |v| v.to_string()),
        stats.conflicts,
        stats.propagations,
        stats.decisions,
        stats.restarts,
    );
    // Extended P2e diagnostics (second line so P2D consumers stay compatible):
    // learnt-DB composition + reduce/restart split + conflict-analysis mix.
    let (db_active, db_glue, db_avg_terms, db_max_terms) = solver.learned_db_diag();
    println!(
        "P2E learned={} deleted={} reduce_calls={} avg_lbd={:.2} db_active={db_active} \
         db_glue={db_glue} db_avg_terms={db_avg_terms:.1} db_max_terms={db_max_terms} \
         glucose_restarts={} luby_restarts={} proven_r2o={} heur_r2o={} card_fallback={}",
        stats.learned,
        stats.learned_deletions,
        stats.reduce_db_calls,
        stats.avg_lbd,
        stats.glucose_restarts,
        stats.luby_restarts,
        stats.proven_round_to_one_count,
        stats.round_to_one_count + stats.round_to_one_fallback_count,
        stats.reduce_to_cardinality_count,
    );
    println!(
        "P2E2 event_backlog={} eq_dp={}",
        solver.propagation_event_backlog(),
        stats.eq_knapsack_dp,
    );
}
