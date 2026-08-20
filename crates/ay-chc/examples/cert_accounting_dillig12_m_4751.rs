// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #cert-accounting item 6: the on-demand cost attribution for #4751.
//!
//! `dillig12_m_deadline_4751` says only *that* the benchmark misses its
//! deadline. This binary says *where the time went*, using the standing
//! counters in `ay_dpll::CertificationAccounting` instead of a throwaway
//! hand-instrumented build.
//!
//! An EXAMPLE, not a test, and deliberately so: it re-runs the same ~20 s
//! benchmark the deadline guard already runs, so making it part of the default
//! suite would double that cost to restate a fact no assertion depends on. It
//! used to be an `#[ignore]`d test, but the quality gate bans disabled tests in
//! owned source outright (there is no waiver kind for them) — and an `#[ignore]`
//! that never runs is exactly the "dead rather than green" shape that ban
//! exists to catch. As an example it stays compiled by `cargo build
//! --examples`, so it cannot silently rot, without costing the suite anything.
//!
//! Run it when the question is "what is certification costing this benchmark":
//!
//! ```text
//! cargo run --release -p ay-chc --example cert_accounting_dillig12_m_4751
//! ```
//!
//! What the output answers, in the order the #4751 investigation needed it:
//!   * `decisions_internal_lemma` — how many sub-queries the CHC search
//!     channel issued (attribution: is this cost even ours?);
//!   * `mints` / `mint_ms` — the certificate-minting hypothesis, which a
//!     controlled A/B has already REFUTED as the critical path: removing all
//!     of it left the benchmark failing at 27.9 s;
//!   * `decisions_proof_tracked_internal_lemma` and `proof_steps_recorded` —
//!     the surviving hypothesis: per-step proof RECORDING during search on a
//!     channel whose verdicts are consumed only as search guidance;
//!   * `nested_corroboration_solves` / `_ms` — the two fresh-`Executor`
//!     whole-problem re-solves inside each mint, measured at 97.4% of mint
//!     cost, so mint cost is really re-solve cost wearing a different name.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser};
use ay_dpll::CertificationAccounting;
use std::time::Duration;

const DILLIG12_M_BENCHMARK_4751: &str =
    include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/dillig12_m_000.smt2");

fn main() {
    let Ok(problem) = ChcParser::parse(DILLIG12_M_BENCHMARK_4751) else {
        eprintln!("dillig12_m benchmark should parse");
        std::process::exit(2);
    };

    let budget = if cfg!(debug_assertions) {
        Duration::from_secs(90)
    } else {
        Duration::from_secs(20)
    };

    let before = CertificationAccounting::snapshot();
    let wall = std::time::Instant::now();
    let solver = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(budget),
    );
    let result = solver.solve();
    let wall = wall.elapsed();
    let delta = CertificationAccounting::snapshot().since(before);

    let pct = |nanos: u64| (nanos as f64) / wall.as_nanos().max(1) as f64 * 100.0;
    eprintln!("dillig12_m verdict      : {result:?}");
    eprintln!("dillig12_m wall         : {:.2}s", wall.as_secs_f64());
    eprintln!("{delta}");
    eprintln!(
        "  decision time          : {:.2}s ({:.1}% of wall)",
        delta.decision_nanos as f64 / 1e9,
        pct(delta.decision_nanos)
    );
    eprintln!(
        "  certificate minting    : {:.2}s ({:.1}% of wall) over {} mints",
        delta.mint_nanos as f64 / 1e9,
        pct(delta.mint_nanos),
        delta.mints
    );
    eprintln!(
        "  ... of which nested    : {:.2}s ({:.1}% of mint) over {} re-solves",
        delta.nested_corroboration_nanos as f64 / 1e9,
        delta.nested_corroboration_nanos as f64 / (delta.mint_nanos.max(1)) as f64 * 100.0,
        delta.nested_corroboration_solves
    );
    eprintln!(
        "  search-channel share   : {}/{} decisions, {}/{} mints, {}/{} proof-tracked",
        delta.decisions_internal_lemma,
        delta.decisions,
        delta.mints_internal_lemma,
        delta.mints,
        delta.decisions_proof_tracked_internal_lemma,
        delta.decisions_proof_tracked
    );

    // The only check: the counters were actually wired to this run. The numbers
    // themselves are load-dependent and are deliberately NOT gated on — this
    // project's own seeded-control methodology treats unseeded wall ratios as
    // incumbent luck, so a threshold here would flake rather than inform.
    if delta.decisions < 1 {
        eprintln!("FAIL: the certification accounting must observe this run: {delta}");
        std::process::exit(1);
    }
}
