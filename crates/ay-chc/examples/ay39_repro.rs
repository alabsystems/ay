// ay39 repro harness: replicate model-checker-consumer-driver's native CHC lane phase-by-phase.
// Phases (mirrors model-checker-consumer-driver/src/call_ay/chc/native.rs try_ay_chc_solver):
//   A: acyclic BMC lane  — BmcConfig::default + max_depth=#preds + acyclic_safe + 15s budget
//   B: adaptive portfolio — AdaptiveConfig::with_budget(15s), strict_proofs=true
//   C: BMC cross-check   — BmcConfig::cross_check + 15s budget (runs only when B is Safe in
//      the driver; run unconditionally here to time it)
use std::time::{Duration, Instant};

use ay_chc::{engines, AdaptiveConfig, AdaptivePortfolio, BmcConfig, ChcParser};

fn per_depth(total: Duration) -> Duration {
    let floor = total.min(Duration::from_secs(1));
    (total / 4).min(Duration::from_secs(10)).max(floor)
}

fn variant(r: &ay_chc::VerifiedChcResult) -> &'static str {
    use ay_chc::VerifiedChcResult::*;
    match r {
        Safe(_) => "Safe",
        Unsafe(_) => "Unsafe",
        _ => "Unknown/Other",
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: ay39_repro <file.smt2> [phases e.g. ABC]");
    let phases = args.next().unwrap_or_else(|| "ABC".to_string());
    let smt = std::fs::read_to_string(&path).expect("read smt2");
    let budget = Duration::from_secs(15);

    let t = Instant::now();
    let mut problem = ChcParser::parse(&smt).expect("parse CHC");
    problem.expand_nullary_fail_queries(false);
    let preds = problem.predicates().len();
    println!(
        "parsed: {} preds, {} clauses ({:?})",
        preds,
        problem.clauses().len(),
        t.elapsed()
    );

    if phases.contains('A') {
        let cfg = BmcConfig::default()
            .with_max_depth(preds.max(1))
            .with_acyclic_safe(true)
            .with_time_budget(budget)
            .with_per_depth_timeout(per_depth(budget))
            .with_verbose(false);
        let t = Instant::now();
        let r = engines::solve_bmc_only(problem.clone(), cfg);
        println!(
            "phase A (acyclic BMC lane):  {:>8.1?}  -> {}",
            t.elapsed(),
            variant(&r)
        );
    }

    if phases.contains('B') {
        let mut acfg = AdaptiveConfig::with_budget(budget, false);
        acfg.strict_proofs = true;
        let solver = AdaptivePortfolio::new(problem.clone(), acfg);
        let t = Instant::now();
        let r = solver.solve();
        println!(
            "phase B (adaptive portfolio):{:>8.1?}  -> {}",
            t.elapsed(),
            variant(&r)
        );
    }

    if phases.contains('C') {
        let cfg = BmcConfig::cross_check()
            .with_time_budget(budget.min(Duration::from_secs(30)))
            .with_per_depth_timeout(per_depth(budget))
            .with_verbose(false);
        let t = Instant::now();
        let r = engines::solve_bmc_only(problem.clone(), cfg);
        println!(
            "phase C (BMC cross-check):   {:>8.1?}  -> {}",
            t.elapsed(),
            variant(&r)
        );
    }
}
