// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the binary root; command ordering remains source-stable.

/// `growth`: MEASURE what each GCD implementation does to the coefficients.
///
/// Not a differential check — there is nothing to compare against. It exists
/// because "the naive one blows up" is a claim, and the campaign rule is that
/// claims come with numbers. It builds an increasingly ill-conditioned planted
/// GCD and prints, per depth, the widest coefficient on each implementation's
/// path together with the wall time and whether the two agreed.
struct CoefficientGrowth {
    worst_naive: f64,
    worst_prs: f64,
}

fn print_coefficient_growth(max_depth: usize) -> Result<CoefficientGrowth, ()> {
    println!("coefficient growth: planted trivariate gcd, `depth` cofactors per side");
    println!("widest coefficient, in BITS, reached on each path (* = chain aborted)");
    println!("`terms` columns are the peak TERM COUNT on the same chain\n");
    println!(
        "{:>5} {:>8} {:>12} {:>8} {:>12} {:>8} {:>10} {:>9} {:>9} {:>6} mod certif",
        "depth",
        "in",
        "naive prem",
        "terms",
        "subres PRS",
        "terms",
        "mod answer",
        "prs us",
        "mod us",
        "agree"
    );
    let mut summary = CoefficientGrowth {
        worst_naive: 0.0,
        worst_prs: 0.0,
    };
    for depth in 1..=max_depth {
        let row = pmgr::measure_growth(depth);
        println!(
            "{:>5} {:>8} {:>11}{} {:>8} {:>11}{} {:>8} {:>10} {:>9} {:>9} {:>6} {:>10}",
            row.depth,
            row.input_bits,
            row.naive_peak_bits,
            if row.naive_aborted { "*" } else { " " },
            row.naive_peak_terms,
            row.prs_peak_bits,
            if row.prs_aborted { "*" } else { " " },
            row.prs_peak_terms,
            row.mod_ans_bits,
            row.prs_us,
            row.mod_us,
            row.agreed,
            row.modular_certified
        );
        if row.input_bits > 0 {
            #[allow(clippy::cast_precision_loss)]
            let (naive, prs) = (
                row.naive_peak_bits as f64 / row.input_bits as f64,
                row.prs_peak_bits as f64 / row.input_bits as f64,
            );
            summary.worst_naive = summary.worst_naive.max(naive);
            summary.worst_prs = summary.worst_prs.max(prs);
        }
        if !row.agreed && row.modular_certified {
            eprintln!("DIVERGENCE: the two gcd implementations disagreed at depth {depth}");
            return Err(());
        }
    }
    println!("\nworst peak / input coefficient width:");
    println!(
        "  naive pseudo-remainder chain : {:.1}x",
        summary.worst_naive
    );
    println!("  subresultant PRS             : {:.1}x", summary.worst_prs);
    println!("  modular answer               : bounded by the primes consumed, by construction");
    Ok(summary)
}

struct MultivariateGrowth {
    worst_prs_ms: u128,
    declines: usize,
    total_prs_us: u128,
    total_gcd_us: u128,
}

fn print_multivariate_growth() -> Result<MultivariateGrowth, ()> {
    println!("\nmultivariate cost: planted gcd, terms and WALL TIME (not coefficient width)");
    println!("this is the table to read before any layer depends on gcd latency\n");
    println!(
        "{:>22} {:>8} {:>8} {:>6} {:>8} {:>9} {:>9} {:>9} {:>9} {:>9} {:>6} {:>9} {:>7} {:>7} {:>7} {:>7}  decline cause",
        "shape", "u terms", "v terms", "deg x", "in bits", "prs ms", "ans terms",
        "ans bits", "mod us", "mod cert", "agree", "speedup", "primes", "points",
        "gcd us", "gcd=prs"
    );
    let mut summary = MultivariateGrowth {
        worst_prs_ms: 0,
        declines: 0,
        total_prs_us: 0,
        total_gcd_us: 0,
    };
    for index in 0..pmgr::mv_shape_count() {
        let row = pmgr::measure_mv_cost(index);
        let effective_us = row.gcd_us;
        summary.total_prs_us += row.prs_us;
        summary.total_gcd_us += effective_us;
        #[allow(clippy::cast_precision_loss)]
        let speedup = row.prs_us as f64 / effective_us.max(1) as f64;
        println!(
            "{:>22} {:>8} {:>8} {:>6} {:>8} {:>9} {:>9} {:>9} {:>9} {:>9} {:>6} {:>8.1}x {:>7} {:>7} {:>7} {:>7}  {}",
            row.label, row.u_terms, row.v_terms, row.deg_x, row.input_bits, row.prs_ms,
            row.prs_ans_terms, row.prs_ans_bits, row.mod_us, row.mod_certified, row.agreed,
            speedup, row.primes_used, row.eval_points, row.gcd_us, row.gcd_agrees,
            row.decline_reason
        );
        summary.worst_prs_ms = summary.worst_prs_ms.max(row.prs_ms);
        summary.declines += usize::from(!row.mod_certified);
        if !row.agreed {
            eprintln!(
                "DIVERGENCE: the two gcd implementations disagreed on shape {}",
                row.label
            );
            return Err(());
        }
        if !row.gcd_agrees {
            eprintln!(
                "DIVERGENCE: the dispatching `gcd` disagreed with the PRS-only path on shape {}",
                row.label
            );
            return Err(());
        }
    }
    Ok(summary)
}

fn print_multivariate_summary(summary: &MultivariateGrowth) {
    let shape_count = pmgr::mv_shape_count();
    println!(
        "\n  slowest subresultant PRS     : {} ms",
        summary.worst_prs_ms
    );
    println!(
        "  modular declines             : {} of {shape_count} shapes",
        summary.declines
    );
    println!(
        "  total PRS-only               : {} us",
        summary.total_prs_us
    );
    println!(
        "  total modular-first + fallback: {} us",
        summary.total_gcd_us
    );
    #[allow(clippy::cast_precision_loss)]
    let overall = summary.total_prs_us as f64 / summary.total_gcd_us.max(1) as f64;
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
}

fn cmd_growth(max_depth: usize) -> i32 {
    if print_coefficient_growth(max_depth).is_err() {
        return 1;
    }
    let summary = match print_multivariate_growth() {
        Ok(summary) => summary,
        Err(()) => return 1,
    };
    print_multivariate_summary(&summary);
    0
}

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

fn print_decline_shapes() {
    println!("-- the {} shapes of MV_SHAPES --", pmgr::mv_shape_count());
    println!(
        "{:>22} {:>6} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7}  primary cause",
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
        "degbnd"
    );
    for index in 0..pmgr::mv_shape_count() {
        let row = pmgr::diagnose_mv(index);
        println!(
            "{:>22} {:>6} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7}  {}",
            row.label,
            row.certified,
            row.primes_used,
            row.prime_bad_coeff,
            row.prime_rec_declined,
            row.lc_gate_rejected,
            row.rec_inner_declined,
            row.rec_budget_exhausted,
            row.rec_lch_mismatch,
            row.rec_trialdiv_reject,
            row.rec_points_tried,
            row.rec_max_points_at_level,
            row.rec_max_deg_bound,
            row.reason
        );
    }
}
