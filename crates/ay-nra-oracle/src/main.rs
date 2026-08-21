// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(unsafe_code)] // Dedicated C-ABI boundary to libz3; sites carry local invariants.

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
//! ay-nra-oracle golden [--heavy]                 # z3's own tests, transliterated
//! ay-nra-oracle probe                            # sanity-check the z3 binding
//! ay-nra-oracle fuzz --seed 1 --cases 1000000    # the campaign
//! ay-nra-oracle repro --seed 1 --case 12345      # one case, verbosely
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
//! So a `10^6`-case run is driven as independent shards with a per-shard wall
//! clock, e.g.
//!
//! ```text
//! for start in 0 2000 4000 ...; do
//!   ay-nra-oracle fuzz --seed S --start $start --cases 2000 --progress 0 &
//!   # kill the shard if it exceeds the cap; its range counts as NOT executed
//! done
//! ```
//!
//! A killed shard is reported as an abandoned range rather than silently
//! dropped, which turns each stall into a located interval to investigate.

mod anum;
mod checks;
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
use std::path::PathBuf;
use std::time::Instant;

use checks::{Check, Outcome, ALL_CHECKS};
use polygen::Rng;
use z3::Z3;

/// Where the reference libz3 sits, RELATIVE TO `$HOME`, when neither `--z3`
/// nor `AY_NRA_ORACLE_Z3` names one.
///
/// This was an absolute path with a username baked into it, which made the
/// default dead on every machine but one — including this one — and leaked a
/// personal home directory into the public snapshot.
const DEFAULT_Z3_UNDER_HOME: &str = "ay/reference/z3/5.0.0/bin/libz3.dylib";

/// Resolve the reference libz3: `AY_NRA_ORACLE_Z3` wins, else
/// `$HOME/{DEFAULT_Z3_UNDER_HOME}`. `--z3` overrides both.
fn default_z3() -> PathBuf {
    match std::env::var("AY_NRA_ORACLE_Z3") {
        Ok(path) if !path.is_empty() => PathBuf::from(path),
        _ => PathBuf::from(std::env::var("HOME").unwrap_or_default()).join(DEFAULT_Z3_UNDER_HOME),
    }
}

/// Default per-case work budget (see `polygen::work_cost`): roughly
/// `(degree + 1) * widest coefficient in bits`.
///
/// AY's Sturm sequences use plain Euclidean remainder over `Q`, so a
/// high-degree polynomial with 128-bit coefficients costs tens of SECONDS per
/// case and would consume the whole campaign for a handful of comparisons.
/// The default keeps the common band fast; `--max-cost 0` disables the bound
/// (`0` is read as "unbounded") for a deliberate heavy-tail campaign.
const DEFAULT_MAX_COST: usize = 420;

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
            Outcome::Diverged(_) => {
                entry.diverged += 1;
                self.total.diverged += 1;
            }
        }
    }

    fn print(&self, seed: u64, elapsed_s: f64) {
        println!("\n=== ay-nra-oracle: differential run ===");
        println!("seed                 {seed}");
        println!("wall clock           {elapsed_s:.1}s");
        println!("cases executed       {}", self.total.cases);
        println!("differential asserts {}", self.total.comparisons);
        println!("  matched            {}", self.total.matched);
        println!("  AY declined        {}", self.total.declined);
        println!("  inapplicable       {}", self.total.skipped);
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
            "check", "cases", "asserts", "matched", "declined", "n/a", "DIVRG"
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
            println!("\n-- inapplicable inputs --");
            let mut v: Vec<_> = self.skip_reasons.iter().collect();
            v.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
            for (r, n) in v {
                println!("{r:<40} {n:>10}");
            }
        }
    }
}

fn dump_divergence(
    seed: u64,
    index: u64,
    check: Check,
    d: &checks::Divergence,
    out_dir: Option<&PathBuf>,
) {
    let inputs: serde_json::Map<String, serde_json::Value> = d
        .inputs
        .iter()
        .map(|(k, v)| (k.clone(), serde_json::Value::String(v.clone())))
        .collect();
    let blob = serde_json::json!({
        "seed": seed,
        "case": index,
        "check": check.name(),
        "reference": d.reference,
        "detail": d.detail,
        "inputs": inputs,
        // The check-set size is part of the reproducer. `index % checks` is
        // what selects the check, so this command replays THIS case only
        // against a binary with the same number of checks.
        "reproduce": format!(
            "ay-nra-oracle repro --seed {seed} --case {index}   # checks={}",
            checks::ALL_CHECKS.len()
        ),
    });
    let text =
        serde_json::to_string_pretty(&blob).unwrap_or_else(|e| format!("{{\"error\":\"{e}\"}}"));
    eprintln!(
        "\n!!! DIVERGENCE ({} vs {}) !!!\n{text}",
        d.check, d.reference
    );
    if let Some(dir) = out_dir {
        let _ = std::fs::create_dir_all(dir);
        let path = dir.join(format!("divergence-{seed}-{index}.json"));
        if let Err(e) = std::fs::write(&path, &text) {
            eprintln!("(could not write reproducer to {}: {e})", path.display());
        } else {
            eprintln!("(reproducer written to {})", path.display());
        }
    }
}

fn open_z3(path: &PathBuf) -> Z3 {
    match Z3::open(path) {
        Ok(z) => {
            println!("reference libz3: {} ({})", path.display(), z.version);
            z
        }
        Err(e) => {
            eprintln!("FATAL: could not load the reference libz3: {e}");
            eprintln!("The oracle refuses to report a clean run without a reference.");
            std::process::exit(2);
        }
    }
}

/// Sanity-check the z3 binding itself before trusting any verdict it produces.
/// If this fails, every "0 divergences" result downstream is worthless.
fn cmd_probe(z3_path: &PathBuf) -> i32 {
    let z = open_z3(z3_path);
    let mut failures = 0;

    // x^2 - 2 has two real roots, bracketing +-sqrt(2).
    match z.roots(&checks::ipoly(&[-2, 0, 1])) {
        Some(r) if r.len() == 2 => {
            let (lo, hi) = z
                .bracket(r[1], 40)
                .unwrap_or((checks::rat(0, 1), checks::rat(0, 1)));
            println!("probe roots(x^2-2): 2 roots, upper root in ({lo}, {hi})");
            let want_lo = checks::rat(1_414_213, 1_000_000);
            let want_hi = checks::rat(1_414_214, 1_000_000);
            if lo < want_lo || hi > want_hi {
                println!("  (bracket wider than 1e-6; not a failure, just coarse)");
            }
        }
        other => {
            println!(
                "probe roots(x^2-2): FAILED ({:?} roots)",
                other.map(|v| v.len())
            );
            failures += 1;
        }
    }

    // Sign of x^2 - 3 at sqrt(2) must be negative; x^2 - 2 must be zero.
    if let Some(r) = z.roots(&checks::ipoly(&[-2, 0, 1])) {
        let alpha = r[1];
        let s0 = z.eval_sign(&checks::ipoly(&[-2, 0, 1]), alpha);
        let s1 = z.eval_sign(&checks::ipoly(&[-3, 0, 1]), alpha);
        let s2 = z.eval_sign(&checks::ipoly(&[-1, 1]), alpha);
        println!("probe eval_sign at sqrt(2): x^2-2 -> {s0:?}, x^2-3 -> {s1:?}, x-1 -> {s2:?}");
        if s0 != Some(0) || s1 != Some(-1) || s2 != Some(1) {
            failures += 1;
        }
    }

    // Algebraic arithmetic: sqrt(2) * sqrt(2) == 2.
    if let Some(r) = z.roots(&checks::ipoly(&[-2, 0, 1])) {
        let sq = z.mul(r[1], r[1]);
        let two = z.rational(&checks::rat(2, 1));
        let ok = z.eq(sq, two);
        println!("probe sqrt(2)*sqrt(2) == 2: {ok}");
        if !ok {
            failures += 1;
        }
        println!(
            "probe defining poly of sqrt(2): {:?}, root index {}",
            z.defining_poly(r[1])
                .map(|v| v.iter().map(ToString::to_string).collect::<Vec<_>>()),
            z.root_index(r[1])
        );
    }

    // The subresultant mapping: p = x+1, q = x+2 must give a single psc
    // (z3's own `src/test/api_polynomial.cpp` asserts exactly this).
    for (name, p, q) in [
        ("x+1 vs x+2", checks::ipoly(&[1, 1]), checks::ipoly(&[2, 1])),
        (
            "x^2-2 vs x^2-3",
            checks::ipoly(&[-2, 0, 1]),
            checks::ipoly(&[-3, 0, 1]),
        ),
        (
            "x^2-2 vs x^2-11",
            checks::ipoly(&[-2, 0, 1]),
            checks::ipoly(&[-11, 0, 1]),
        ),
        (
            "x^2-1 vs x-1",
            checks::ipoly(&[-1, 0, 1]),
            checks::ipoly(&[-1, 1]),
        ),
        (
            "x^2+3x+2 vs 2x+3",
            checks::ipoly(&[2, 3, 1]),
            checks::ipoly(&[3, 2]),
        ),
        (
            "x^3-2 vs x^2-2",
            checks::ipoly(&[-2, 0, 0, 1]),
            checks::ipoly(&[-2, 0, 1]),
        ),
        (
            "x^3-2 vs 3x^2",
            checks::ipoly(&[-2, 0, 0, 1]),
            checks::ipoly(&[0, 0, 3]),
        ),
        // Reversed argument order: z3 sorts by degree internally, so this
        // pins whether the sign convention survives the swap.
        (
            "x^2-2 vs x^3-2 (swapped)",
            checks::ipoly(&[-2, 0, 1]),
            checks::ipoly(&[-2, 0, 0, 1]),
        ),
        (
            "x-1 vs x^3-2 (swapped)",
            checks::ipoly(&[-1, 1]),
            checks::ipoly(&[-2, 0, 0, 1]),
        ),
        (
            "x^3-2 vs x-1",
            checks::ipoly(&[-2, 0, 0, 1]),
            checks::ipoly(&[-1, 1]),
        ),
        // Non-unit content: does z3's polynomial manager rescale?
        (
            "2x^2-4 vs x-1",
            checks::ipoly(&[-4, 0, 2]),
            checks::ipoly(&[-1, 1]),
        ),
        (
            "6x^2-12 vs 3x-3",
            checks::ipoly(&[-12, 0, 6]),
            checks::ipoly(&[-3, 3]),
        ),
        // Shared factor of degree 1: psc_0 = 0 and z3 skips it.
        (
            "(x-1)(x-2)(x-3) vs (x-1)(x-5)",
            checks::ipoly(&[-6, 11, -6, 1]),
            checks::ipoly(&[5, -6, 1]),
        ),
        // Shared factor of degree 2.
        (
            "(x-1)^2(x-3) vs (x-1)^2(x-5)",
            checks::ipoly(&[-3, 7, -5, 1]),
            checks::ipoly(&[-5, 11, -7, 1]),
        ),
    ] {
        let ay = ay_nra::oracle_api::resultant(
            &ay_nra::oracle_api::OPoly::from_coeffs(p.clone()),
            &ay_nra::oracle_api::OPoly::from_coeffs(q.clone()),
        );
        match z.subresultants(&p, &q) {
            None => {
                println!("probe psc {name}: z3 declined");
                failures += 1;
            }
            Some(chain) => {
                let rendered: Vec<String> = chain
                    .iter()
                    .map(|a| {
                        z.numeral_value(*a)
                            .map_or_else(|| z.ast_string(*a), |v| v.to_string())
                    })
                    .collect();
                println!(
                    "probe psc {name}: z3 = [{}]   AY resultant = {}",
                    rendered.join(", "),
                    ay.map_or_else(|| "None".to_string(), |v| v.to_string())
                );
            }
        }
    }

    if failures == 0 {
        println!("\nprobe: z3 binding behaves as documented.");
        0
    } else {
        println!("\nprobe: {failures} FAILURES — do not trust downstream results.");
        1
    }
}

/// Dump both sides' view of one polynomial, given its coefficients low-to-high.
/// Used to triage a divergence down to the primitive that produced it.
fn cmd_dbg(z3_path: &PathBuf, spec: &str) -> i32 {
    let z = open_z3(z3_path);
    let coeffs: Vec<num_rational::BigRational> = spec
        .split(',')
        .filter_map(|t| z3::parse_rational(t.trim()))
        .collect();
    println!("p = {}", polygen::render(&coeffs));
    let p = ay_nra::oracle_api::OPoly::from_coeffs(coeffs.clone());
    println!("AY degree: {:?}", p.degree());
    match p.square_free_part() {
        None => println!("AY square_free_part: declined"),
        Some(sf) => println!("AY square_free_part: {}", polygen::render(&sf.coeffs())),
    }
    match p.square_free_part().and_then(|sf| sf.isolate_roots()) {
        None => println!("AY isolate_roots: declined"),
        Some(ms) => {
            println!("AY markers ({}):", ms.len());
            for (i, m) in ms.iter().enumerate() {
                println!("  #{i}: {m:?}");
            }
        }
    }
    let show = |label: &str, cs: &[num_rational::BigRational]| match z.roots(cs) {
        None => println!("z3 roots of {label}: declined"),
        Some(rs) => {
            println!("z3 roots of {label} ({}), in returned order:", rs.len());
            for (i, r) in rs.iter().enumerate() {
                let b = z.bracket(*r, 40).map_or_else(
                    || "?".to_string(),
                    |(lo, hi)| format!("{:.9} .. {:.9}", ratio_f64(&lo), ratio_f64(&hi)),
                );
                println!("  #{i}: {b}");
            }
            println!("  pairwise lt matrix:");
            for a in &rs {
                let row: Vec<&str> = rs
                    .iter()
                    .map(|b| {
                        if z.lt(*a, *b) {
                            "<"
                        } else if z.lt(*b, *a) {
                            ">"
                        } else {
                            "="
                        }
                    })
                    .collect();
                println!("    {}", row.join(" "));
            }
        }
    };
    show("p", &coeffs);
    if let Some(sf) = p.square_free_part() {
        show("sf", &sf.coeffs());
        // Now the interleaved order the checks actually use: fetch BOTH root
        // lists first, then compare. If this disagrees with the sequential
        // dump above, the fault is in the harness's lifetime handling, not in
        // either implementation.
        println!("interleaved (both lists fetched before any comparison):");
        if let (Some(rp), Some(rs)) = (z.roots(&coeffs), z.roots(&sf.coeffs())) {
            for (i, (a, b)) in rp.iter().zip(rs.iter()).enumerate() {
                let ba = z.bracket(*a, 40).map_or(f64::NAN, |(lo, _)| ratio_f64(&lo));
                let bb = z.bracket(*b, 40).map_or(f64::NAN, |(lo, _)| ratio_f64(&lo));
                println!("  #{i}: p {ba:.9}   sf {bb:.9}   eq={}", z.eq(*a, *b));
            }
        }
    }
    0
}

/// Decimal rendering for the debug dump only.
fn ratio_f64(r: &num_rational::BigRational) -> f64 {
    let n = r.numer().to_string().parse::<f64>().unwrap_or(f64::NAN);
    let d = r.denom().to_string().parse::<f64>().unwrap_or(f64::NAN);
    n / d
}

fn cmd_golden(z3_path: &PathBuf, heavy: bool, live: bool) -> i32 {
    let z = if live { Some(open_z3(z3_path)) } else { None };
    let results = golden::run_all(z.as_ref(), heavy);
    let mut failed = 0;
    for r in &results {
        if r.passed {
            if r.detail.is_empty() {
                println!("  ok   {}", r.name);
            } else {
                println!("  ok   {}   [{}]", r.name, r.detail);
            }
        } else {
            failed += 1;
            println!("  FAIL {}   {}", r.name, r.detail);
        }
    }
    println!(
        "\ngolden fixtures: {} run, {} passed, {failed} failed",
        results.len(),
        results.len() - failed
    );
    i32::from(failed > 0)
}

fn cmd_fuzz(
    z3_path: &PathBuf,
    seed: u64,
    cases: u64,
    start: u64,
    dump_dir: Option<PathBuf>,
    progress_every: u64,
    max_cost: usize,
) -> i32 {
    let mut z = open_z3(z3_path);
    // The check-set size is part of a case's identity, not decoration: the
    // driver picks with `ALL_CHECKS[i % len]`, so the SAME (seed, case) names a
    // DIFFERENT check under a different `len`. Five lanes believed appending
    // preserved case numbering; it never did. See `ALL_CHECKS`.
    println!(
        "seed {seed}, cases {cases} (starting at index {start}), work budget {max_cost}, \
         checks {}",
        ALL_CHECKS.len()
    );
    let mut report = Report::new();
    let begin = Instant::now();
    let mut last_progress = Instant::now();

    for i in start..start + cases {
        if (i - start) % RECYCLE_EVERY == RECYCLE_EVERY - 1 {
            z.recycle();
        }
        let check = ALL_CHECKS[usize::try_from(i % (ALL_CHECKS.len() as u64)).unwrap_or(0)];
        let mut rng = Rng::new(case_seed(seed, i));
        let t0 = Instant::now();
        let result = checks::run_case(&z, check, &mut rng, max_cost, checks::Sabotage::Off);
        let ms = t0.elapsed().as_millis();
        if ms > report.slowest_ms {
            report.slowest_ms = ms;
            report.slowest_case = i;
        }
        report.record(check, &result.outcome, &result.shapes);
        if let Outcome::Diverged(d) = &result.outcome {
            dump_divergence(seed, i, check, d, dump_dir.as_ref());
        }
        if progress_every > 0
            && (i - start + 1) % progress_every == 0
            && last_progress.elapsed().as_secs_f64() > 0.0
        {
            let done = i - start + 1;
            let el = begin.elapsed().as_secs_f64();
            eprintln!(
                "  [{done}/{cases}] {:.0} cases/s, {} asserts, {} divergences, {:.0}s elapsed",
                done as f64 / el.max(1e-9),
                report.total.comparisons,
                report.total.diverged,
                el
            );
            last_progress = Instant::now();
        }
    }

    report.print(seed, begin.elapsed().as_secs_f64());
    i32::from(report.total.diverged > 0)
}
/// The catch rate below which a check is reported DEGRADED and `selftest`
/// fails, even though the check still catches something.
///
/// The old gate was `hits > 0`. A verifier proved what that permits: hardwiring
/// `Zp::is_irreducible` to `Some(true)` dropped `up-zp-factor` from 39 of 39
/// caught to 17 of 39, and `selftest` still printed "detects sabotage" and
/// exited 0. Detection can collapse by more than half and the gate stays green,
/// which makes a clean selftest much weaker evidence than it reads as.
///
/// 0.80 is chosen against the MEASURED floor of the honest checks, not picked
/// for roundness: at `--cases 1100` the lowest legitimate rates are `gcd`
/// 28/29 = 96.6%, `pm-representation` 48/50 = 96.0% and `square-free`
/// 34/35 = 97.1%. Those misses are real — a saboteur can multiply by a factor
/// that happens to preserve the property under test — so 100% is not
/// achievable. 0.80 leaves each of them ~16 points of sampling headroom while
/// still failing the 43.6% collapse above decisively.
const MIN_CATCH_RATE: f64 = 0.80;

/// Prove the oracle can fail.
///
/// A clean run only means something if a dirty one would have been caught, so
/// this replays ordinary cases with [`checks::Sabotage::On`] — AY's answer is
/// minimally corrupted right at the comparison — and requires EVERY check to
/// report divergences. A check that stays silent under sabotage is not
/// checking anything, and the command exits non-zero.
fn cmd_selftest(z3_path: &PathBuf, seed: u64, cases: u64, max_cost: usize) -> i32 {
    let mut z = open_z3(z3_path);
    println!("selftest: {cases} sabotaged cases at seed {seed}\n");
    let mut caught: BTreeMap<&'static str, (u64, u64)> = BTreeMap::new();
    for i in 0..cases {
        if i % RECYCLE_EVERY == RECYCLE_EVERY - 1 {
            z.recycle();
        }
        let check = ALL_CHECKS[usize::try_from(i % (ALL_CHECKS.len() as u64)).unwrap_or(0)];
        let mut rng = Rng::new(case_seed(seed, i));
        let result = checks::run_case(&z, check, &mut rng, max_cost, checks::Sabotage::On);
        let e = caught.entry(check.name()).or_insert((0, 0));
        match result.outcome {
            Outcome::Diverged(_) => {
                e.0 += 1;
                e.1 += 1;
            }
            Outcome::Match(_) => e.1 += 1,
            // Declined / inapplicable cases never reached a comparison, so they
            // are not evidence either way.
            Outcome::Declined(_) | Outcome::Skipped(_) => {}
        }
    }
    println!(
        "{:<22} {:>10} {:>10} {:>7}  {}",
        "check", "compared", "caught", "rate", "verdict"
    );
    let mut blind = 0;
    let mut degraded = 0;
    for (name, (hits, compared)) in &caught {
        #[allow(clippy::cast_precision_loss)]
        let rate = if *compared == 0 {
            0.0
        } else {
            *hits as f64 / *compared as f64
        };
        let verdict = if *hits == 0 {
            blind += 1;
            "BLIND"
        } else if rate < MIN_CATCH_RATE {
            degraded += 1;
            "DEGRADED"
        } else {
            "detects sabotage"
        };
        println!(
            "{name:<22} {compared:>10} {hits:>10} {:>6.1}%  {verdict}",
            rate * 100.0
        );
    }
    for c in ALL_CHECKS {
        if !caught.contains_key(c.name()) {
            blind += 1;
            println!("{:<22} {:>10} {:>10} {:>7}  NEVER RAN", c.name(), 0, 0, "-");
        }
    }
    if blind == 0 && degraded == 0 {
        println!("\nselftest: every check detects a corrupted AY answer.");
        0
    } else {
        if blind > 0 {
            println!(
                "\nselftest: {blind} check(s) cannot fail — a clean run proves nothing for them."
            );
        }
        if degraded > 0 {
            println!(
                "selftest: {degraded} check(s) caught sabotage at under {:.0}% — detection has \
                 COLLAPSED even though they still catch something.",
                MIN_CATCH_RATE * 100.0
            );
        }
        1
    }
}

fn cmd_repro(z3_path: &PathBuf, seed: u64, index: u64, max_cost: usize) -> i32 {
    let z = open_z3(z3_path);
    let check = ALL_CHECKS[usize::try_from(index % (ALL_CHECKS.len() as u64)).unwrap_or(0)];
    let mut rng = Rng::new(case_seed(seed, index));
    // `checks N` is required to replay this: `index % N` is what selected the
    // check, so a case number without it is ambiguous across commits.
    println!(
        "case #{index} of seed {seed} (checks {}): check `{}`",
        ALL_CHECKS.len(),
        check.name()
    );
    let result = checks::run_case(&z, check, &mut rng, max_cost, checks::Sabotage::Off);
    println!("shapes: {}", result.shapes.join(", "));
    match &result.outcome {
        Outcome::Match(n) => {
            println!("MATCH ({n} assertions held)");
            0
        }
        Outcome::Declined(r) => {
            println!("AY DECLINED at `{r}` (fail-closed; not a divergence)");
            0
        }
        Outcome::Skipped(r) => {
            println!("inapplicable: {r}");
            0
        }
        Outcome::Diverged(d) => {
            dump_divergence(seed, index, check, d, None);
            1
        }
    }
}

/// `growth`: MEASURE what each GCD implementation does to the coefficients.
///
/// Not a differential check — there is nothing to compare against. It exists
/// because "the naive one blows up" is a claim, and the campaign rule is that
/// claims come with numbers. It builds an increasingly ill-conditioned planted
/// GCD and prints, per depth, the widest coefficient on each implementation's
/// path together with the wall time and whether the two agreed.
fn cmd_growth(max_depth: usize) -> i32 {
    println!("coefficient growth: planted trivariate gcd, `depth` cofactors per side");
    println!("widest coefficient, in BITS, reached on each path (* = chain aborted)");
    println!("`terms` columns are the peak TERM COUNT on the same chain\n");
    println!(
        "{:>5} {:>8} {:>12} {:>8} {:>12} {:>8} {:>10} {:>9} {:>9} {:>6} {:>10}",
        "depth",
        "in",
        "naive prem",
        "terms",
        "subres PRS",
        "terms",
        "mod answer",
        "prs us",
        "mod us",
        "agree",
        "mod certif"
    );
    let mut worst_naive = 0f64;
    let mut worst_prs = 0f64;
    for depth in 1..=max_depth {
        let r = pmgr::measure_growth(depth);
        println!(
            "{:>5} {:>8} {:>11}{} {:>8} {:>11}{} {:>8} {:>10} {:>9} {:>9} {:>6} {:>10}",
            r.depth,
            r.input_bits,
            r.naive_peak_bits,
            if r.naive_aborted { "*" } else { " " },
            r.naive_peak_terms,
            r.prs_peak_bits,
            if r.prs_aborted { "*" } else { " " },
            r.prs_peak_terms,
            r.mod_ans_bits,
            r.prs_us,
            r.mod_us,
            r.agreed,
            r.modular_certified
        );
        if r.input_bits > 0 {
            #[allow(clippy::cast_precision_loss)]
            let (n, p) = (
                r.naive_peak_bits as f64 / r.input_bits as f64,
                r.prs_peak_bits as f64 / r.input_bits as f64,
            );
            worst_naive = worst_naive.max(n);
            worst_prs = worst_prs.max(p);
        }
        if !r.agreed && r.modular_certified {
            eprintln!("DIVERGENCE: the two gcd implementations disagreed at depth {depth}");
            return 1;
        }
    }
    println!("\nworst peak / input coefficient width:");
    println!("  naive pseudo-remainder chain : {worst_naive:.1}x");
    println!("  subresultant PRS             : {worst_prs:.1}x");
    println!("  modular answer               : bounded by the primes consumed, by construction");

    // The second table. The one above walks a chain that is univariate in x
    // with y/z coefficients, where everything finishes in microseconds and the
    // coefficient ratio is the whole story. A verifier showed that is not where
    // the cost lives: on genuinely multivariate inputs the PRS runs for SECONDS
    // and returns a narrow answer. Coefficient width cannot show that.
    //
    // `mod_gcd` used to decline on precisely those inputs — 3 of the 5 shapes —
    // which made the fast path unavailable exactly where it was needed. The
    // `decline cause` column exists because that fact was recorded for a long
    // time with no mechanism attached to it, and the `speedup` column exists
    // because a decline is not free: it costs `mod us` and then pays the PRS
    // anyway.
    println!("\nmultivariate cost: planted gcd, terms and WALL TIME (not coefficient width)");
    println!("this is the table to read before any layer depends on gcd latency\n");
    println!(
        "{:>22} {:>8} {:>8} {:>6} {:>8} {:>9} {:>9} {:>9} {:>9} {:>9} {:>6} {:>9} {:>7} {:>7} {:>7} {:>7}  {}",
        "shape",
        "u terms",
        "v terms",
        "deg x",
        "in bits",
        "prs ms",
        "ans terms",
        "ans bits",
        "mod us",
        "mod cert",
        "agree",
        "speedup",
        "primes",
        "points",
        "gcd us",
        "gcd=prs",
        "decline cause"
    );
    let mut worst_prs_ms = 0u128;
    let mut declines = 0usize;
    let mut total_prs_us = 0u128;
    let mut total_gcd_us = 0u128;
    for i in 0..pmgr::mv_shape_count() {
        let r = pmgr::measure_mv_cost(i);
        // What a caller above this layer actually pays. This used to MODEL a
        // dispatching caller as `mod_us`, or `mod_us + prs_us` on a decline.
        // `PolyManager::gcd` now really does dispatch, so the model is replaced
        // by the measurement: `gcd_us` is that entry point, timed. A decline
        // still scores honestly — it pays the modular attempt and then the PRS
        // anyway, which lands the row below 1.0x.
        let effective_us = r.gcd_us;
        total_prs_us += r.prs_us;
        total_gcd_us += effective_us;
        #[allow(clippy::cast_precision_loss)]
        let speedup = r.prs_us as f64 / (effective_us.max(1)) as f64;
        println!(
            "{:>22} {:>8} {:>8} {:>6} {:>8} {:>9} {:>9} {:>9} {:>9} {:>9} {:>6} {:>8.1}x {:>7} {:>7} {:>7} {:>7}  {}",
            r.label,
            r.u_terms,
            r.v_terms,
            r.deg_x,
            r.input_bits,
            r.prs_ms,
            r.prs_ans_terms,
            r.prs_ans_bits,
            r.mod_us,
            r.mod_certified,
            r.agreed,
            speedup,
            r.primes_used,
            r.eval_points,
            r.gcd_us,
            r.gcd_agrees,
            r.decline_reason
        );
        worst_prs_ms = worst_prs_ms.max(r.prs_ms);
        if !r.mod_certified {
            declines += 1;
        }
        if !r.agreed {
            eprintln!(
                "DIVERGENCE: the two gcd implementations disagreed on shape {}",
                r.label
            );
            return 1;
        }
        // Preferring a CERTIFIED fast path must not change any answer, only the
        // time taken to reach it. If this ever fires, the dispatch in
        // `PolyManager::gcd` is wrong and the speedup is worthless.
        if !r.gcd_agrees {
            eprintln!(
                "DIVERGENCE: the dispatching `gcd` disagreed with the PRS-only path on shape {}",
                r.label
            );
            return 1;
        }
    }
    let n = pmgr::mv_shape_count();
    println!("\n  slowest subresultant PRS     : {worst_prs_ms} ms");
    println!("  modular declines             : {declines} of {n} shapes");
    println!("  total PRS-only               : {total_prs_us} us");
    println!("  total modular-first + fallback: {total_gcd_us} us");
    #[allow(clippy::cast_precision_loss)]
    let overall = total_prs_us as f64 / (total_gcd_us.max(1)) as f64;
    println!("  overall speedup              : {overall:.1}x");
    println!(
        "  `speedup` scores a DECLINE honestly: a declining shape pays `mod us + prs us`, \
         so it is below 1.0x. Only a certification is a win."
    );
    println!(
        "  NOTE: a decline is `None`, never a wrong answer — `gcd` stays on the PRS. The cost \
         is that the modular path is unavailable on the inputs that most need it."
    );
    println!("  `decline cause` comes from the same counters `ay-nra-oracle declines` histograms.");
    0
}

/// `declines`: WHY the modular GCD gives up.
///
/// Not a differential check and not a timing run — a census. It reports the
/// MECHANISM behind each decline, per shape and over a pool of random cases
/// drawn from exactly the generator the `pm-mod-gcd` check uses. It exists
/// because tuning a prime list or a budget without knowing which of them is
/// binding is guessing, and a fix aimed at the wrong cause is worse than none.
///
/// It was built to answer "the modular path declines on 3 of 5 multivariate
/// shapes and 21.93% of random cases — WHY?", and the answer it gave was that
/// no prime, no budget and no certificate was involved: 415,232 of the
/// rejections came from a single trial division inside the `Z_p` recursion, and
/// 315,728 of those would have passed had the interpolant's `Z_p[x]` content
/// been removed instead of its `Z_p[Y]` content. Both rates are now 0. The
/// command stays because a regression is invisible without it.
/// `bq-growth`: MEASURE what a long refinement does to the denominator.
///
/// Not a differential check. It exists because "the dyadic layer keeps
/// denominators small" is a claim, and the campaign rule is that claims come
/// with numbers. Two implementations of the SAME bisection — one over
/// `mpbq::Bq`, one over `num_rational::BigRational` — run side by side on
/// `x^2 - 2` and must stay numerically identical throughout (`agree`), so the
/// comparison is of cost, not of answers.
///
/// The depths deliberately SWEEP PAST POWERS OF TWO. The previous cost harness
/// in this crate measured 8/16/32/.../256 and missed a capability cliff at
/// 335-512; the analogue here would be a refinement whose behaviour changes
/// once `k` crosses a limb boundary, so 100, 335, 500, 700 and 1000 are
/// measured alongside the powers of two.
fn cmd_bq_growth() -> i32 {
    const DEPTHS: [u32; 16] = [
        1, 2, 4, 8, 16, 32, 64, 100, 128, 200, 256, 335, 500, 512, 700, 1000,
    ];
    println!("dyadic denominator growth: bisecting an isolating interval of x^2 - 2");
    println!("`k` is the denominator EXPONENT (a/2^k); `bits` is total stored bits\n");
    println!(
        "{:>7} {:>8} {:>10} {:>14} {:>11} {:>12} {:>9} {:>8} {:>7}",
        "steps",
        "k",
        "bq bits",
        "rational bits",
        "bq us",
        "rational us",
        "select k",
        "mid k",
        "agree"
    );
    let rows = mpbq::measure_growth(&DEPTHS);
    let mut bad = 0;
    for r in &rows {
        println!(
            "{:>7} {:>8} {:>10} {:>14} {:>11} {:>12} {:>9} {:>8} {:>7}",
            r.steps,
            r.dyadic_k,
            r.dyadic_bits,
            r.rational_bits,
            r.dyadic_us,
            r.rational_us,
            r.select_k,
            r.mid_k,
            r.agree
        );
        // The property the module exists for: exactly one bit of denominator
        // per bisection, never two. A refine loop that DOUBLES k every step is
        // correct and useless, and this is where that would show.
        if r.dyadic_k != r.steps {
            println!(
                "  !! k = {} after {} steps, expected exactly {}",
                r.dyadic_k, r.steps, r.steps
            );
            bad += 1;
        }
        if !r.agree {
            println!("  !! the two implementations DIVERGED at depth {}", r.steps);
            bad += 1;
        }
    }
    if bad == 0 {
        println!("\nk grows by exactly 1 per bisection at every depth, and both");
        println!("implementations agree on the interval throughout.");
        0
    } else {
        println!("\n{bad} anomaly/anomalies, see the `!!` lines above.");
        1
    }
}

/// The system load average, so a timing table cannot be read as if the machine
/// were idle. `None` when `uptime` is unavailable.
fn load_average() -> Option<String> {
    let out = std::process::Command::new("uptime").output().ok()?;
    let s = String::from_utf8_lossy(&out.stdout);
    let idx = s.find("load average")?;
    Some(s[idx..].trim().to_string())
}

/// Degree and coefficient growth across CHAINS of `anum` operations.
///
/// Resultant-based arithmetic MULTIPLIES degrees: `add` of a degree-`m` and a
/// degree-`n` number gives degree `m*n`, so a chain of `k` operations from a
/// degree-`d` base reaches `d^(k+1)`. Measuring a single operation says nothing
/// about that; this measures every step of every chain.
fn cmd_anum_growth(budget_ms: u128) -> i32 {
    println!("anum operation-CHAIN growth");
    println!("base operand j: the real root of x^d - p_j in the dyadic interval (1, 2)");
    println!("chain: acc := acc OP base_{{step}}, alternating + and *\n");
    println!(
        "load average: {}",
        load_average().unwrap_or_else(|| "<unavailable>".to_string())
    );
    println!("per-step budget: {budget_ms} ms (a step over budget ends its chain)\n");
    println!(
        "{:>5} {:>5} {:>3} {:>8} {:>11} {:>10} {:>12} {:>9}",
        "base", "step", "op", "degree", "coeff bits", "interval k", "step us", "outcome"
    );
    let rows = anum::measure_chain_growth(budget_ms);
    let mut declines = 0usize;
    let mut worst_degree = 0usize;
    let mut worst_bits = 0u64;
    for r in &rows {
        println!(
            "{:>5} {:>5} {:>3} {:>8} {:>11} {:>10} {:>12} {:>9}",
            r.base_degree,
            r.step,
            r.op,
            r.degree,
            r.coeff_bits,
            r.interval_k,
            r.elapsed_us,
            if r.declined { "DECLINED" } else { "ok" }
        );
        if r.declined {
            declines += 1;
        } else {
            worst_degree = worst_degree.max(r.degree);
            worst_bits = worst_bits.max(r.coeff_bits);
        }
    }
    println!(
        "\n{} steps, {declines} declined; largest degree reached {worst_degree}, \
         largest coefficient {worst_bits} bits",
        rows.len()
    );
    println!(
        "load average after: {}",
        load_average().unwrap_or_else(|| "<unavailable>".to_string())
    );
    0
}

fn cmd_declines(seed: u64, cases: u64) -> i32 {
    println!("mod_gcd DECLINE CENSUS");
    println!("a decline is a fail-closed `None`; `PolyManager::gcd` falls back to the PRS\n");

    println!("-- the {} shapes of MV_SHAPES --", pmgr::mv_shape_count());
    println!(
        "{:>22} {:>6} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7}  {}",
        "shape",
        "cert",
        "primes",
        "badcof",
        "recdec",
        "lcgate",
        "inner",
        "budget",
        "lc_H!=",
        "trialdv",
        "points",
        "maxpts",
        "degbnd",
        "primary cause"
    );
    for i in 0..pmgr::mv_shape_count() {
        let r = pmgr::diagnose_mv(i);
        println!(
            "{:>22} {:>6} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7}  {}",
            r.label,
            r.certified,
            r.primes_used,
            r.prime_bad_coeff,
            r.prime_rec_declined,
            r.lc_gate_rejected,
            r.rec_inner_declined,
            r.rec_budget_exhausted,
            r.rec_lch_mismatch,
            r.rec_trialdiv_reject,
            r.rec_points_tried,
            r.rec_max_points_at_level,
            r.rec_max_deg_bound,
            r.reason
        );
    }

    println!("\n-- {cases} random cases, seed {seed} (the `pm-mod-gcd` generator) --");
    let mut rng = Rng::new(case_seed(seed, 0));
    let mut by_reason: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut by_shape: BTreeMap<&'static str, (u64, u64)> = BTreeMap::new(); // (cases, declines)
    let mut by_shape_reason: BTreeMap<(&'static str, &'static str), u64> = BTreeMap::new();
    let mut totals = [0u64; 14];
    let mut n = 0u64;
    let mut declined = 0u64;
    // How far past `deg_bound + 1` the interpolation ran before giving up.
    let mut pts_over_bound: BTreeMap<i64, u64> = BTreeMap::new();
    for _ in 0..cases {
        let Some(r) = pmgr::diagnose_random(&mut rng) else {
            continue;
        };
        n += 1;
        let e = by_shape.entry(r.label).or_default();
        e.0 += 1;
        if !r.certified {
            declined += 1;
            e.1 += 1;
            *by_reason.entry(r.reason).or_default() += 1;
            *by_shape_reason.entry((r.label, r.reason)).or_default() += 1;
            totals[0] += u64::from(r.prime_bad_coeff);
            totals[1] += u64::from(r.prime_bad_lcg);
            totals[2] += u64::from(r.prime_rec_declined);
            totals[3] += u64::from(r.lc_gate_rejected);
            totals[4] += u64::from(r.cert_reject_u);
            totals[5] += u64::from(r.cert_reject_v);
            totals[6] += u64::from(r.rec_inner_declined);
            totals[7] += u64::from(r.rec_budget_exhausted);
            totals[8] += u64::from(r.rec_lch_mismatch);
            totals[9] += u64::from(r.rec_trialdiv_reject);
            totals[10] += u64::from(r.rec_unlucky_degree);
            totals[11] += u64::from(r.rec_base_failed + r.rec_content_failed);
            totals[12] += u64::from(r.rec_reset_smaller);
            totals[13] += u64::from(r.rec_points_tried);
            let over = i64::from(r.rec_max_points_at_level) - (i64::from(r.rec_max_deg_bound) + 1);
            *pts_over_bound.entry(over.clamp(-4, 8)).or_default() += 1;
        }
    }
    #[allow(clippy::cast_precision_loss)]
    let pct = |k: u64| -> f64 { 100.0 * k as f64 / (n.max(1)) as f64 };
    println!("cases   {n}");
    println!("declines {declined}  ({:.2}%)", pct(declined));

    println!(
        "\n{:<52} {:>8} {:>8}",
        "primary cause of decline", "count", "% of all"
    );
    let mut v: Vec<_> = by_reason.iter().collect();
    v.sort_by_key(|(_, k)| std::cmp::Reverse(**k));
    for (r, k) in v {
        println!("{r:<52} {k:>8} {:>7.2}%", pct(*k));
    }

    println!(
        "\n{:<16} {:>8} {:>10} {:>8}",
        "generated shape", "cases", "declines", "rate"
    );
    for (s, (c, d)) in &by_shape {
        #[allow(clippy::cast_precision_loss)]
        let rate = 100.0 * *d as f64 / (*c).max(1) as f64;
        println!("{s:<16} {c:>8} {d:>10} {rate:>7.2}%");
    }

    println!("\n-- shape x cause --");
    for ((s, r), k) in &by_shape_reason {
        println!("{s:<16} {k:>6}  {r}");
    }

    println!("\n-- raw event totals over declining cases (a case can log several) --");
    for (label, k) in [
        ("prime rejected: coefficient vanished", totals[0]),
        ("prime rejected: lc_g vanished", totals[1]),
        ("prime rejected: recursion declined", totals[2]),
        ("lc gate rejected the CRA candidate", totals[3]),
        ("EXACT certificate rejected on u", totals[4]),
        ("EXACT certificate rejected on v", totals[5]),
        ("recursion: inner call at a point declined", totals[6]),
        ("recursion: budget exhausted", totals[7]),
        ("recursion: lc_H != lc_g (needs more points)", totals[8]),
        ("recursion: trial division rejected", totals[9]),
        ("recursion: unlucky point (degree too high)", totals[10]),
        ("recursion: base/content refused", totals[11]),
        (
            "recursion: Newton form reset (smaller image deg)",
            totals[12],
        ),
        ("recursion: evaluation points consumed", totals[13]),
    ] {
        println!("{label:<48} {k:>10}");
    }

    println!(
        "\n-- how far the interpolation ran past `deg_bound + 1` before giving up --\n\
         (a value > 0 means MORE points than the degree bound can require were supplied \
         and the trial division STILL rejected: more budget is not the fix)"
    );
    for (over, k) in &pts_over_bound {
        println!("{over:>+4} points   {k:>8}");
    }
    0
}

fn usage() -> i32 {
    eprintln!(
        "ay-nra-oracle — differential oracle for AY's exact univariate / real-algebraic layer

  ay-nra-oracle probe                       sanity-check the libz3 binding
  ay-nra-oracle golden [--heavy] [--no-z3]  z3's own tests, transliterated
  ay-nra-oracle selftest [--cases n]        prove every check can fail (sabotage)
  ay-nra-oracle fuzz   [options]            the differential campaign
  ay-nra-oracle repro  --seed S --case I    replay a single case verbosely
  ay-nra-oracle dbg    --coeffs a,b,c,...   dump both sides' view of one poly
  ay-nra-oracle growth [--cases n]          MEASURE gcd coefficient growth
  ay-nra-oracle bq-growth                   MEASURE dyadic denominator growth
  ay-nra-oracle declines [--seed S --cases n]  WHY the modular gcd declines

fuzz/repro options:
  --seed <u64>        run seed (default 1)
  --cases <u64>       number of cases (default 100000)
  --start <u64>       first case index (default 0), for sharding a long run
  --dump <dir>        write each divergence as JSON here
  --progress <n>      progress line every n cases (0 = silent, default 50000)
  --max-cost <n>      per-case work budget, 0 = unbounded (default {DEFAULT_MAX_COST})
  --z3 <path>         reference libz3 ($AY_NRA_ORACLE_Z3, else $HOME/{DEFAULT_Z3_UNDER_HOME})

A case is a pure function of (seed, index): `repro --seed S --case I` replays
exactly what `fuzz --seed S` did at index I, on any machine. The work budget
changes only WHICH cases run, never which polynomials they draw."
    );
    64
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        std::process::exit(usage());
    }
    let mut seed: u64 = 1;
    let mut cases: u64 = 100_000;
    let mut start: u64 = 0;
    let mut index: u64 = 0;
    let mut heavy = false;
    let mut live = true;
    let mut progress: u64 = 50_000;
    let mut dump: Option<PathBuf> = None;
    let mut z3_path = default_z3();
    let mut coeffs_spec = String::new();
    let mut max_cost: usize = DEFAULT_MAX_COST;

    let mut i = 1;
    while i < args.len() {
        let need = |i: usize| -> String {
            args.get(i + 1).cloned().unwrap_or_else(|| {
                eprintln!("missing value for {}", args[i]);
                std::process::exit(64);
            })
        };
        match args[i].as_str() {
            "--seed" => {
                seed = need(i).parse().unwrap_or(1);
                i += 2;
            }
            "--cases" => {
                cases = need(i).parse().unwrap_or(100_000);
                i += 2;
            }
            "--start" => {
                start = need(i).parse().unwrap_or(0);
                i += 2;
            }
            "--case" => {
                index = need(i).parse().unwrap_or(0);
                i += 2;
            }
            "--progress" => {
                progress = need(i).parse().unwrap_or(50_000);
                i += 2;
            }
            "--dump" => {
                dump = Some(PathBuf::from(need(i)));
                i += 2;
            }
            "--max-cost" => {
                // 0 means "no bound" — the heavy-tail campaign.
                let v: usize = need(i).parse().unwrap_or(DEFAULT_MAX_COST);
                max_cost = if v == 0 { usize::MAX } else { v };
                i += 2;
            }
            "--coeffs" => {
                coeffs_spec = need(i);
                i += 2;
            }
            "--z3" => {
                z3_path = PathBuf::from(need(i));
                i += 2;
            }
            "--heavy" => {
                heavy = true;
                i += 1;
            }
            "--no-z3" => {
                live = false;
                i += 1;
            }
            other => {
                eprintln!("unknown option {other}");
                std::process::exit(usage());
            }
        }
    }

    let code = match args[0].as_str() {
        "probe" => cmd_probe(&z3_path),
        "golden" => cmd_golden(&z3_path, heavy, live),
        "fuzz" => cmd_fuzz(&z3_path, seed, cases, start, dump, progress, max_cost),
        "repro" => cmd_repro(&z3_path, seed, index, max_cost),
        "selftest" => cmd_selftest(&z3_path, seed, cases, max_cost),
        "dbg" => cmd_dbg(&z3_path, &coeffs_spec),
        "growth" => cmd_growth(usize::try_from(cases).unwrap_or(6).clamp(1, 12)),
        "anum-growth" => cmd_anum_growth(u128::from(cases.clamp(1, 600_000))),
        "factor-cost" => cmd_factor_cost(usize::try_from(cases).unwrap_or(64).clamp(8, 512)),
        "bq-growth" => cmd_bq_growth(),
        "declines" => cmd_declines(seed, cases),
        _ => usage(),
    };
    std::process::exit(code);
}

/// `factor-cost`: MEASURE what `Z_p` factorization costs on adversarial input.
///
/// Not a differential check. It exists because a factorizer that is correct on
/// every test and exponential on real input passes every correctness gate this
/// oracle has, and because the previous lane shipped a correct multivariate GCD
/// that took 20 seconds on a 25-term input — nobody noticed, because the growth
/// harness only measured coefficient width.
///
/// Three families, each the worst case for a different stage:
///   * `split-linear`       — `prod (x - i)`: one distinct-degree bucket
///                            holding every factor, so Cantor-Zassenhaus must
///                            perform `n - 1` random splits. This is where an
///                            exponential would live.
///   * `irreducible`        — the distinct-degree loop cannot exit early and
///                            runs its full `n/2` iterations.
///   * `power-of-quadratic` — `(x^2 + 1)^k`, so the square-free decomposition
///                            iterates `k` times before factoring starts.
///
/// The `ok` column is the product identity re-checked at measurement time: a
/// cost number attached to a wrong answer is worse than no number at all.
fn cmd_factor_cost(max_n: usize) -> i32 {
    println!("Z_p factorization cost on ADVERSARIAL input (degrees up to {max_n})\n");
    println!(
        "{:>20} {:>8} {:>7} {:>8} {:>10} {:>7} {:>7} {:>7} {:>9} {:>11} {:>5}",
        "family",
        "p",
        "degree",
        "factors",
        "wall us",
        "ddf it",
        "edf try",
        "splits",
        "powmods",
        "powmod mul",
        "ok"
    );
    let rows = upoly::measure_cost(max_n);
    let mut bad = 0;
    let mut worst_us = 0u128;
    for r in &rows {
        println!(
            "{:>20} {:>8} {:>7} {:>8} {:>10} {:>7} {:>7} {:>7} {:>9} {:>11} {:>5}",
            r.family,
            r.p,
            r.degree,
            r.factors,
            r.us,
            r.ddf_iters,
            r.edf_attempts,
            r.edf_splits,
            r.powmods,
            r.powmod_mults,
            r.ok
        );
        if !r.ok {
            bad += 1;
        }
        worst_us = worst_us.max(r.us);
    }
    println!("\nworst wall time observed: {worst_us} us");
    println!(
        "splits vs factors: equal-degree performs exactly `factors - buckets` splits, so the\n\
         `splits` column is LINEAR in the answer size by construction, not merely small here."
    );
    if bad > 0 {
        eprintln!("{bad} row(s) FAILED the product identity — the cost numbers are meaningless");
        return 1;
    }
    0
}
