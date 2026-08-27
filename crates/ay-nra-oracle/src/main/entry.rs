// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the binary root; command ordering remains source-stable.

fn usage() -> i32 {
    eprintln!("{}", cli::usage());
    64
}

fn main() {
    // #govern: kernel-held memory bound, armed by the IMAGE (see
    // crates/ay-sys/src/govern.rs). This oracle drives z3 and AY's exact
    // real-algebraic primitives over generated polynomials — unbounded degree
    // growth is exactly the shape that took the box down on 2026-08-02.
    ay_sys::govern::arm();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let command = match cli::parse_args(&args) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("error: {error}");
            std::process::exit(usage());
        }
    };
    let code = match command {
        Command::Probe { z3 } => cmd_probe(&z3),
        Command::Golden { z3, heavy } => cmd_golden(z3.as_deref(), heavy),
        Command::Selftest {
            z3,
            seed,
            cases,
            max_cost,
        } => cmd_selftest(&z3, seed, cases, max_cost),
        Command::Fuzz {
            z3,
            seed,
            cases,
            start,
            dump,
            progress,
            max_cost,
        } => cmd_fuzz(&z3, seed, cases, start, dump, progress, max_cost),
        Command::Repro {
            z3,
            seed,
            index,
            max_cost,
        } => cmd_repro(&z3, seed, index, max_cost),
        Command::Dbg { z3, coeffs } => cmd_dbg(&z3, &coeffs),
        Command::Growth { cases } => cmd_growth(usize::try_from(cases).unwrap_or(6).clamp(1, 12)),
        Command::AnumGrowth { cases } => cmd_anum_growth(u128::from(cases.clamp(1, 600_000))),
        Command::FactorCost { cases } => {
            cmd_factor_cost(usize::try_from(cases).unwrap_or(64).clamp(8, 512))
        }
        Command::BqGrowth => cmd_bq_growth(),
        Command::Declines { seed, cases } => cmd_declines(seed, cases),
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
/// * `split-linear` — `prod (x - i)`: one distinct-degree bucket holding every
///   factor, so Cantor-Zassenhaus must perform `n - 1` random splits. This is
///   where an exponential would live.
/// * `irreducible` — the distinct-degree loop cannot exit early and runs its
///   full `n/2` iterations.
/// * `power-of-quadratic` — `(x^2 + 1)^k`, so the square-free decomposition
///   iterates `k` times before factoring starts.
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
