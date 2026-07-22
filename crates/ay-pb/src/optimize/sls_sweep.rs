// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SLS A/B sweep harness (Task V4). Measures the unified NuPBO-class SLS and the
//! candidate feasibility-wall levers against the two-phase baseline on synthetic
//! hard families (market_split / Cornuéjols-Dawande equality systems, plus
//! covering / cardinality / partition shapes). Gated behind the `AY_SLS_SWEEP`
//! env var so it is a no-op in normal `cargo test`; run with:
//!
//! ```text
//! AY_SLS_SWEEP=1 cargo test -p ay-pb --lib optimize::sls_sweep -- --nocapture
//! ```
//!
//! Every reported incumbent is re-verified by `verify_all_constraints`, so this
//! harness ALSO functions as a 0-wrong soundness check across all families.

#![cfg(test)]

use std::time::{Duration, Instant};

use crate::eval::verify_all_constraints;
use crate::optimize::lns::SplitMix64;
use crate::optimize::sls::{search_unified, search_with_options, up_seed};
use crate::solver::eval_objective;
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}
fn term(coeff: i128, l: PbLit) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![l],
    }
}
fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}
fn eq(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Eq,
        rhs,
    }
}

fn finalize(
    constraints: Vec<PbConstraint>,
    objective: PbObjective,
    n: u32,
) -> (PbInstance, PbObjective) {
    let instance = PbInstance {
        num_vars: n,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: Some(objective.clone()),
    };
    (instance, objective)
}

/// Cornuéjols–Dawande market split: `m` equality rows over `n = 10*(m-1)` 0/1
/// vars, coefficients uniform in [0,99], rhs_i = floor(sum_i / 2). A trivial
/// objective (minimize Σ x) is attached only so the optimization SLS will run;
/// the whole difficulty is finding ANY feasible point.
fn market_split(m: usize, rng: &mut SplitMix64) -> (PbInstance, PbObjective) {
    let n = (10 * (m.saturating_sub(1))).max(2);
    let mut constraints = Vec::with_capacity(m);
    for _ in 0..m {
        let mut terms = Vec::with_capacity(n);
        let mut sum: i128 = 0;
        for v in 1..=n {
            let c = rng.below(100) as i128; // [0,99]
            sum += c;
            terms.push(term(c, lit(v as u32)));
        }
        constraints.push(eq(terms, sum / 2));
    }
    let objective = PbObjective {
        terms: (1..=n as u32).map(|v| term(1, lit(v))).collect(),
    };
    finalize(constraints, objective, n as u32)
}

/// Subset-sum / balanced-partition equality: a SINGLE equality `Σ w_i x_i = T`
/// with T = (Σ w)/2, weights uniform in [1,50]; minimize Σ x_i. Equality-heavy
/// but only one row — a softer equality wall than full market split.
fn subset_sum(n: usize, rng: &mut SplitMix64) -> (PbInstance, PbObjective) {
    let mut terms = Vec::with_capacity(n);
    let mut total: i128 = 0;
    for v in 1..=n {
        let w = 1 + rng.below(50) as i128;
        total += w;
        terms.push(term(w, lit(v as u32)));
    }
    let constraints = vec![eq(terms, total / 2)];
    let objective = PbObjective {
        terms: (1..=n as u32).map(|v| term(1, lit(v))).collect(),
    };
    finalize(constraints, objective, n as u32)
}

/// Random set-cover: `rows` covering constraints over `n` vars, each row a random
/// subset (size ~k) requiring at-least-one; minimize Σ cost_i x_i.
fn set_cover(n: usize, rows: usize, k: usize, rng: &mut SplitMix64) -> (PbInstance, PbObjective) {
    let mut constraints = Vec::with_capacity(rows);
    for _ in 0..rows {
        let mut chosen = Vec::new();
        let kk = (1 + rng.below(k)).min(n);
        while chosen.len() < kk {
            let v = 1 + rng.below(n) as u32;
            if !chosen.contains(&v) {
                chosen.push(v);
            }
        }
        constraints.push(ge(chosen.iter().map(|&v| term(1, lit(v))).collect(), 1));
    }
    let objective = PbObjective {
        terms: (1..=n as u32)
            .map(|v| term(1 + rng.below(10) as i128, lit(v)))
            .collect(),
    };
    finalize(constraints, objective, n as u32)
}

/// Knapsack-cover: a few Ge rows `Σ w_i x_i >= R` (must buy enough), minimize cost.
fn knapsack_cover(n: usize, rows: usize, rng: &mut SplitMix64) -> (PbInstance, PbObjective) {
    let mut constraints = Vec::with_capacity(rows);
    for _ in 0..rows {
        let mut terms = Vec::with_capacity(n);
        let mut sum: i128 = 0;
        for v in 1..=n {
            let w = rng.below(20) as i128;
            sum += w;
            terms.push(term(w, lit(v as u32)));
        }
        constraints.push(ge(terms, sum / 2 + 1));
    }
    let objective = PbObjective {
        terms: (1..=n as u32)
            .map(|v| term(1 + rng.below(10) as i128, lit(v)))
            .collect(),
    };
    finalize(constraints, objective, n as u32)
}

/// Cardinality choose-exactly-k: `Σ x = k`, minimize Σ cost_i x_i.
fn cardinality(n: usize, k: i128, rng: &mut SplitMix64) -> (PbInstance, PbObjective) {
    let constraints = vec![eq((1..=n as u32).map(|v| term(1, lit(v))).collect(), k)];
    let objective = PbObjective {
        terms: (1..=n as u32)
            .map(|v| term(1 + rng.below(50) as i128, lit(v)))
            .collect(),
    };
    finalize(constraints, objective, n as u32)
}

#[derive(Clone, Copy, Default)]
struct Outcome {
    feasible: usize,
    instances: usize,
    wrong: usize,
}

fn run_one(
    instance: &PbInstance,
    objective: &PbObjective,
    budget: Duration,
    mode: &str,
) -> (bool, i128, bool) {
    let stop = || false;
    let deadline = Some(Instant::now() + budget);
    let mut wrong = false;
    let mut best: Option<i128> = None;
    {
        let mut on_improve = |obj: i128, model: &[bool]| {
            if !verify_all_constraints(&instance.constraints, model)
                || eval_objective(objective, model) != obj
            {
                wrong = true;
            }
        };
        let result = match mode {
            "baseline" => {
                search_with_options(instance, objective, deadline, &stop, &mut on_improve, true)
            }
            "unified" => {
                search_unified(instance, objective, deadline, &stop, &mut on_improve, None)
            }
            "unified_up" => {
                let seed = up_seed(instance);
                search_unified(
                    instance,
                    objective,
                    deadline,
                    &stop,
                    &mut on_improve,
                    seed.as_deref(),
                )
            }
            "combined" => {
                // Feasibility-first hybrid: spend a slice on the two-phase
                // feasibility hunt (breaks the equality wall), then hand its best
                // feasible point to the unified loop as a warm start for objective
                // descent (crosses the equality ridge). Mirrors the shippable
                // portfolio lever.
                let frac: f64 = std::env::var("AY_SLS_FEAS_FRAC")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(0.5);
                let feas = budget.mul_f64(frac);
                let rest = budget.saturating_sub(feas);
                let feas_deadline = Some(Instant::now() + feas);
                let r1 = search_with_options(
                    instance,
                    objective,
                    feas_deadline,
                    &stop,
                    &mut on_improve,
                    true,
                );
                let warm = r1.as_ref().map(|r| r.assignment.clone());
                let uni_deadline = Some(Instant::now() + rest);
                let r2 = search_unified(
                    instance,
                    objective,
                    uni_deadline,
                    &stop,
                    &mut on_improve,
                    warm.as_deref(),
                );
                // Best of the two (lowest objective).
                match (r1, r2) {
                    (Some(a), Some(b)) => Some(if b.objective <= a.objective { b } else { a }),
                    (a, b) => a.or(b),
                }
            }
            "both" => {
                // Union of the two complementary trajectories, keep best: a
                // feasibility-first two-phase pass (breaks the equality wall) AND
                // the unified objective-as-soft pass from scratch (best descent),
                // each on half the budget. The global best-incumbent aggregation
                // gives feasibility = either-found, objective = min — strictly
                // dominating either pass alone.
                let frac: f64 = std::env::var("AY_SLS_FEAS_FRAC")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(0.34);
                let feas = budget.mul_f64(frac);
                let rest = budget.saturating_sub(feas);
                let r1 = search_with_options(
                    instance,
                    objective,
                    Some(Instant::now() + feas),
                    &stop,
                    &mut on_improve,
                    true,
                );
                let r2 = search_unified(
                    instance,
                    objective,
                    Some(Instant::now() + rest),
                    &stop,
                    &mut on_improve,
                    None,
                );
                match (r1, r2) {
                    (Some(a), Some(b)) => Some(if b.objective <= a.objective { b } else { a }),
                    (a, b) => a.or(b),
                }
            }
            _ => unreachable!(),
        };
        if let Some(r) = result {
            if !verify_all_constraints(&instance.constraints, &r.assignment)
                || eval_objective(objective, &r.assignment) != r.objective
            {
                wrong = true;
            }
            best = Some(r.objective);
        }
    }
    (best.is_some(), best.unwrap_or(0), wrong)
}

/// Planted-FEASIBLE market split: choose a random 0/1 vector `x*`, draw random
/// coefficients per row, and set each `rhs_i = Σ_j a_ij x*_j`. By construction `x*`
/// is feasible, so a feasibility hit-rate of 0 is a genuine search failure (not an
/// infeasible instance). This is the honest controlled measurement of whether the
/// 2-flip SWAP lever cracks the multi-row equality wall: the unplanted
/// `market_split` generator uses `rhs = sum/2`, which is almost never
/// simultaneously satisfiable across rows, so its 0/5 says nothing about the lever.
fn market_split_planted(m: usize, rng: &mut SplitMix64) -> (PbInstance, PbObjective) {
    let n = (10 * (m.saturating_sub(1))).max(2);
    // Plant a balanced random feasible assignment.
    let planted: Vec<bool> = (0..n).map(|_| rng.below(2) == 1).collect();
    let mut constraints = Vec::with_capacity(m);
    for _ in 0..m {
        let mut terms = Vec::with_capacity(n);
        let mut rhs: i128 = 0;
        for v in 1..=n {
            let c = rng.below(100) as i128; // [0,99]
            if planted[v - 1] {
                rhs += c;
            }
            terms.push(term(c, lit(v as u32)));
        }
        constraints.push(eq(terms, rhs));
    }
    let objective = PbObjective {
        terms: (1..=n as u32).map(|v| term(1, lit(v))).collect(),
    };
    finalize(constraints, objective, n as u32)
}

/// Gated controlled measurement: planted-feasible market split, endgame-swap A/B.
/// Run with e.g.
/// ```text
/// AY_SLS_PLANTED=1 cargo test -p ay-pb --lib \
///   optimize::sls_sweep::market_split_planted_swap_ab -- --nocapture
/// ```
/// (default endgame swap on) and again with `AY_PB_SLS_ENDGAME_THRESHOLD=0` for the
/// swap-off (single-flip) baseline. The test asserts 0-wrong (VIG) always; it never
/// asserts a feasibility count (the lever's value is measured, not required, since
/// some draws can still be hard).
#[test]
fn market_split_planted_swap_ab() {
    if std::env::var_os("AY_SLS_PLANTED").is_none() {
        return; // gated: no-op in normal test runs
    }
    let budget = Duration::from_millis(
        std::env::var("AY_SLS_SWEEP_MS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(1000),
    );
    let threshold = std::env::var("AY_PB_SLS_ENDGAME_THRESHOLD")
        .ok()
        .unwrap_or_else(|| "(default)".into());
    println!(
        "\n=== planted-feasible market split (budget {} ms, endgame_threshold={}) ===",
        budget.as_millis(),
        threshold
    );
    println!(
        "{:>6} {:>5} {:>10} {:>10} {:>10}",
        "m", "n", "baseline", "combined", "both"
    );
    let count: usize = std::env::var("AY_SLS_PLANTED_COUNT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(8);
    let m_list: Vec<usize> = std::env::var("AY_SLS_PLANTED_M")
        .ok()
        .map(|s| s.split(',').filter_map(|t| t.trim().parse().ok()).collect())
        .unwrap_or_else(|| vec![3usize, 4, 5, 6]);
    for &m in &m_list {
        let (mut b_feas, mut c_feas, mut t_feas) = (0, 0, 0);
        for inst_i in 0..count {
            let mut rng = SplitMix64::new(0xF00D_5EED + m as u64 * 104_729 + inst_i as u64);
            let (instance, objective) = market_split_planted(m, &mut rng);
            for (mode, acc) in [
                ("baseline", &mut b_feas),
                ("combined", &mut c_feas),
                ("both", &mut t_feas),
            ] {
                let (f, _o, w) = run_one(&instance, &objective, budget, mode);
                assert!(
                    !w,
                    "planted market split mode {mode} reported a WRONG incumbent"
                );
                if f {
                    *acc += 1;
                }
            }
        }
        let n = (10 * (m - 1)).max(2);
        println!("{m:>6} {n:>5} {b_feas:>10} {c_feas:>10} {t_feas:>10}");
    }
}

#[test]
fn sls_feasibility_wall_sweep() {
    if std::env::var_os("AY_SLS_SWEEP").is_none() {
        return; // gated: no-op in normal test runs
    }
    let budget = Duration::from_millis(
        std::env::var("AY_SLS_SWEEP_MS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(1000),
    );
    let modes = ["baseline", "unified", "combined", "both"];
    let nmodes = modes.len();

    // (family-name, count, generator)
    type Gen = Box<dyn Fn(&mut SplitMix64) -> (PbInstance, PbObjective)>;
    let families: Vec<(&str, usize, Gen)> = vec![
        ("market_split_m3", 5, Box::new(|r| market_split(3, r))),
        ("market_split_m4", 5, Box::new(|r| market_split(4, r))),
        ("market_split_m5", 3, Box::new(|r| market_split(5, r))),
        ("subset_sum_30", 5, Box::new(|r| subset_sum(30, r))),
        ("subset_sum_60", 5, Box::new(|r| subset_sum(60, r))),
        ("set_cover_80", 5, Box::new(|r| set_cover(80, 120, 6, r))),
        ("knapsack_cover", 5, Box::new(|r| knapsack_cover(50, 4, r))),
        ("cardinality_40", 5, Box::new(|r| cardinality(40, 15, r))),
    ];

    println!(
        "\n=== SLS feasibility-wall sweep (budget {} ms/instance) ===",
        budget.as_millis()
    );
    print!("{:>18}", "family");
    for m in &modes {
        print!(" {:>12}", format!("{}_feas", m));
    }
    for m in &modes {
        print!(" {:>12}", format!("{}_obj", m));
    }
    println!();

    let mut totals: Vec<Outcome> = vec![Outcome::default(); nmodes];
    for (name, count, make) in &families {
        // Deterministic per-family seed so every mode sees the SAME instances.
        let mut feas = vec![0usize; nmodes];
        let mut objs = vec![0i128; nmodes];
        let mut wrongs = vec![0usize; nmodes];
        for inst_i in 0..*count {
            let mut rng =
                SplitMix64::new(0xA53F_1000 + (*name).len() as u64 * 7919 + inst_i as u64);
            let (instance, objective) = make(&mut rng);
            for (mi, mode) in modes.iter().enumerate() {
                let (f, o, w) = run_one(&instance, &objective, budget, mode);
                if f {
                    feas[mi] += 1;
                    objs_add(&mut objs[mi], o);
                }
                if w {
                    wrongs[mi] += 1;
                }
                totals[mi].instances += 1;
                if f {
                    totals[mi].feasible += 1;
                }
                totals[mi].wrong += w as usize;
            }
        }
        print!("{:>18}", name);
        for mi in 0..nmodes {
            print!(" {:>12}", feas[mi]);
        }
        for mi in 0..nmodes {
            print!(" {:>12}", objs[mi]);
        }
        println!();
        for mi in 0..nmodes {
            assert_eq!(
                wrongs[mi], 0,
                "{} mode {} reported a WRONG incumbent",
                name, modes[mi]
            );
        }
    }
    println!("\n--- totals (feasible / instances), 0-wrong required ---");
    for mi in 0..nmodes {
        println!(
            "{:>12}: feasible {}/{}  wrong {}",
            modes[mi], totals[mi].feasible, totals[mi].instances, totals[mi].wrong
        );
        assert_eq!(totals[mi].wrong, 0);
    }
}

fn objs_add(acc: &mut i128, v: i128) {
    *acc = acc.saturating_add(v);
}
