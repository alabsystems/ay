// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay-nra-oracle` — the differential oracle for AY's exact univariate and
//! real-algebraic layer.
//!
//! It drives the real libz3's `Z3_algebraic_*` family and
//! `Z3_polynomial_subresultants` against AY's `UniPoly` / `RealAlgebraic`
//! primitives on seeded random and adversarial polynomials, and reports the
//! ACTUAL number of comparisons executed together with the ACTUAL number of
//! divergences. It exists so that the nlsat-class math substrate has a
//! bug-detector standing BEFORE any of it is written.
//!
//! ```text
//! ay-nra-oracle golden --no-z3 [--heavy]          # path-free fixtures
//! ay-nra-oracle probe --z3 /path/to/libz3         # sanity-check the binding
//! ay-nra-oracle fuzz --z3 /path/to/libz3 --seed 1 --cases 1000000
//! ay-nra-oracle repro --z3 /path/to/libz3 --seed 1 --case 12345
//! ```
//!
//! Every case is a pure function of `(seed, case index)`, so a divergence
//! printed on one machine replays exactly on another. `--start` selects an
//! arbitrary window without replaying what came before, and the work budget
//! changes only WHICH cases run, never which polynomials they draw.
//!
//! ## Long campaigns must be sharded
//!
//! Roughly one case in `10^5` sends AY's exact univariate layer into a
//! computation that has been observed to run past twenty minutes, and nothing
//! inside this process can interrupt it: the work is a straight-line
//! `BigRational` Sturm computation with no yield point. The cheap static
//! [`polygen::work_cost`] guard bounds the INPUT size, which removes the bulk
//! of the tail but cannot bound a cost that only materialises in derived
//! polynomials (a cross-point resultant multiplies the operand degrees).
//!
//! Run long campaigns through the maintained resource-enveloped shard driver:
//!
//! ```text
//! python3 scripts/nra_oracle_shards.py \
//!   --binary target/release/ay-nra-oracle \
//!   --z3 /trusted/z3/lib/libz3.so \
//!   --seed S --cases 1000000 --shard-cases 2000 \
//!   --jobs J --timeout 1200 --out-dir the development design notes
//! ```
//!
//! The driver refuses concurrent Rust builds, retains one aggregate resource
//! lease, caps concurrency to the admitted plan, and puts every child behind a
//! process-group RSS watchdog and wall timeout. It persists binary/reference
//! provenance and the exact memory/core envelope. Timeout, memory breach,
//! cancellation, truncated output, an invalid exit code, or an inconsistent
//! terminal summary marks that shard's complete range as abandoned rather than
//! silently dropping it.

mod anum;
mod checks;
mod cli;
mod explain;
mod golden;
mod ialg;
mod mpbq;
mod mv;
mod pmgr;
mod polygen;
mod subres;
mod upoly;
mod z3;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

use checks::{Check, Outcome, ALL_CHECKS};
use cli::Command;
use polygen::Rng;
use z3::Z3;

fn emit_stdout(message: std::fmt::Arguments<'_>) {
    println!("{message}");
}

fn emit_stderr(message: std::fmt::Arguments<'_>) {
    eprintln!("{message}");
}

/// How many cases run before the z3 context is torn down and rebuilt. The
/// non-refcounted context accumulates every AST it has ever built, so a long
/// run needs periodic recycling; this is not a correctness knob.
const RECYCLE_EVERY: u64 = 400;

/// Derive a case's seed from the run seed and the case index, so any case is
/// reachable directly without replaying the ones before it.
fn case_seed(seed: u64, index: u64) -> u64 {
    let mut z = seed
        .wrapping_mul(0x9E37_79B9_7F4A_7C15)
        .wrapping_add(index.wrapping_mul(0xD1B5_4A32_D192_ED03));
    z ^= z >> 33;
    z = z.wrapping_mul(0xFF51_AFD7_ED55_8CCD);
    z ^= z >> 33;
    z
}

#[derive(Default)]
struct Tally {
    cases: u64,
    comparisons: u64,
    matched: u64,
    declined: u64,
    skipped: u64,
    diverged: u64,
}

struct Report {
    per_check: BTreeMap<&'static str, Tally>,
    total: Tally,
    reference_comparisons: u64,
    decline_reasons: BTreeMap<String, u64>,
    skip_reasons: BTreeMap<String, u64>,
    shape_counts: BTreeMap<&'static str, u64>,
    slowest_ms: u128,
    slowest_case: u64,
}

impl Report {
    fn new() -> Self {
        Self {
            per_check: BTreeMap::new(),
            total: Tally::default(),
            reference_comparisons: 0,
            decline_reasons: BTreeMap::new(),
            skip_reasons: BTreeMap::new(),
            shape_counts: BTreeMap::new(),
            slowest_ms: 0,
            slowest_case: 0,
        }
    }

    fn record(&mut self, check: Check, outcome: &Outcome, shapes: &[&'static str]) {
        let entry = self.per_check.entry(check.name()).or_default();
        entry.cases += 1;
        self.total.cases += 1;
        for s in shapes {
            *self.shape_counts.entry(s).or_default() += 1;
        }
        match outcome {
            Outcome::Match(n) => {
                entry.matched += 1;
                entry.comparisons += n;
                self.total.matched += 1;
                self.total.comparisons += n;
                if check.uses_z3() {
                    self.reference_comparisons += n;
                }
            }
            Outcome::Declined(r) => {
                entry.declined += 1;
                self.total.declined += 1;
                *self.decline_reasons.entry((*r).to_string()).or_default() += 1;
            }
            Outcome::Skipped(r) => {
                entry.skipped += 1;
                self.total.skipped += 1;
                *self.skip_reasons.entry((*r).to_string()).or_default() += 1;
            }
            Outcome::Diverged(d) => {
                entry.comparisons += 1;
                entry.diverged += 1;
                self.total.comparisons += 1;
                self.total.diverged += 1;
                self.reference_comparisons += u64::from(d.reference == "z3");
            }
        }
    }

    fn print(&self, seed: u64, elapsed_s: f64, reference_failures: u64) {
        println!("\n=== ay-nra-oracle: differential run ===");
        println!("seed                 {seed}");
        println!("wall clock           {elapsed_s:.1}s");
        println!("cases executed       {}", self.total.cases);
        println!("differential asserts {}", self.total.comparisons);
        println!("reference comparisons {}", self.reference_comparisons);
        println!("reference failures   {reference_failures}");
        println!("  matched            {}", self.total.matched);
        println!("  AY declined        {}", self.total.declined);
        println!("  skipped / n/a      {}", self.total.skipped);
        println!("DIVERGENCES          {}", self.total.diverged);
        println!(
            "throughput           {:.0} cases/s",
            f64::from(u32::try_from(self.total.cases.min(u64::from(u32::MAX))).unwrap_or(0))
                / elapsed_s.max(1e-9)
        );
        println!(
            "slowest case         {} ms (case #{})",
            self.slowest_ms, self.slowest_case
        );

        println!("\n-- per check --");
        println!(
            "{:<20} {:>9} {:>11} {:>8} {:>9} {:>7} {:>6}",
            "check", "cases", "asserts", "matched", "declined", "skip", "DIVRG"
        );
        for (name, t) in &self.per_check {
            println!(
                "{name:<20} {:>9} {:>11} {:>8} {:>9} {:>7} {:>6}",
                t.cases, t.comparisons, t.matched, t.declined, t.skipped, t.diverged
            );
        }

        println!("\n-- generated shape coverage --");
        for (shape, n) in &self.shape_counts {
            println!("{shape:<24} {n:>10}");
        }

        if !self.decline_reasons.is_empty() {
            println!("\n-- AY declines (fail-closed `None`, NOT divergences) --");
            let mut v: Vec<_> = self.decline_reasons.iter().collect();
            v.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
            for (r, n) in v {
                println!("{r:<40} {n:>10}");
            }
        }
        if !self.skip_reasons.is_empty() {
            println!("\n-- skipped / inapplicable inputs --");
            let mut v: Vec<_> = self.skip_reasons.iter().collect();
            v.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
            for (r, n) in v {
                println!("{r:<40} {n:>10}");
            }
        }
    }
}

include!("main/probe.rs");
include!("main/commands.rs");
include!("main/growth.rs");
include!("main/declines.rs");
include!("main/entry.rs");
