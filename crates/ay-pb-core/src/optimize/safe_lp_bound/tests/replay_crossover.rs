// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MEASUREMENT HARNESS (ignored by default): replay REAL box-LP models and
//! race the primal form against the transposed form, paired back-to-back, to
//! locate the transpose crossover on production shapes instead of synthetic
//! ones. This is the harness whose 2026-08-17 run produced the measurement
//! table on `TRANSPOSE_RATIO_NUM` and exposed the all-`z` crash defect (see
//! `crash_at_dual_image_of_x0`).
//!
//! Run with:
//! ```text
//! AY_LP_REPLAY_DIR=<dir> cargo test --release -p ay-pb-core \
//!     replay_crossover -- --ignored --nocapture
//! ```
//! Knobs: `AY_REPLAY_REPS` (default 5) interleaved reps per arm,
//! `AY_REPLAY_ITERS` (default 300000) per-phase iteration cap. Output: one
//! `AYXOVER` line per model — shape, per-arm median wall, per-arm iteration
//! counts, and agreement of the two certified Lagrangian bounds.
//!
//! Model files: line 1 `n m`; line 2 the n costs; then m lines
//! `b k v a v a ...` (k sparse coefficient pairs), floats in Rust `{:?}`
//! round-trip form. To capture fresh REAL models, temporarily dump `(n, c,
//! rows)` at the top of `approx_dual_for_box_lp_with_limits` (that point sees
//! the post-equilibration data the transpose would solve) while running
//! `ay pb solve` on the instances of interest; the hook is deliberately not
//! kept in production.

use super::super::transpose;
use super::*;

fn lagrangian(n: usize, c: &[f64], rows: &[(Vec<(usize, f64)>, f64)], y: &[f64]) -> f64 {
    let mut aty = vec![0.0f64; n];
    let mut val = 0.0f64;
    for (r, (coeffs, b)) in rows.iter().enumerate() {
        let yr = y[r].max(0.0);
        val += b * yr;
        for &(v, a) in coeffs {
            aty[v] += a * yr;
        }
    }
    for v in 0..n {
        val += (c[v] - aty[v]).min(0.0);
    }
    val
}

struct ReplayModel {
    name: String,
    n: usize,
    c: Vec<f64>,
    rows: Vec<(Vec<(usize, f64)>, f64)>,
}

fn parse_model(path: &std::path::Path) -> Option<ReplayModel> {
    let text = std::fs::read_to_string(path).ok()?;
    let mut lines = text.lines();
    let mut header = lines.next()?.split_whitespace();
    let n: usize = header.next()?.parse().ok()?;
    let m: usize = header.next()?.parse().ok()?;
    let c: Vec<f64> = lines
        .next()?
        .split_whitespace()
        .map(|t| t.parse::<f64>())
        .collect::<Result<_, _>>()
        .ok()?;
    if c.len() != n {
        return None;
    }
    let mut rows = Vec::with_capacity(m);
    for line in lines {
        let mut it = line.split_whitespace();
        let b: f64 = it.next()?.parse().ok()?;
        let k: usize = it.next()?.parse().ok()?;
        let mut coeffs = Vec::with_capacity(k);
        for _ in 0..k {
            let v: usize = it.next()?.parse().ok()?;
            let a: f64 = it.next()?.parse().ok()?;
            coeffs.push((v, a));
        }
        rows.push((coeffs, b));
    }
    if rows.len() != m {
        return None;
    }
    Some(ReplayModel {
        name: path.file_name()?.to_string_lossy().into_owned(),
        n,
        c,
        rows,
    })
}

struct ArmResult {
    wall: std::time::Duration,
    iters: (usize, usize),
    converged: bool,
    bound: f64,
}

fn run_primal(model: &ReplayModel, limits: SimplexLimits) -> ArmResult {
    let rows: Vec<RowF64> = model
        .rows
        .iter()
        .map(|(coeffs, b)| RowF64 {
            coeffs: coeffs.clone(),
            b: *b,
        })
        .collect();
    let lp = LpF64 {
        n: model.n,
        c: model.c.clone(),
        offset: 0.0,
        rows,
        upper: None,
    };
    let m = lp.rows.len();
    let start = std::time::Instant::now();
    let mut s = Simplex::new(&lp, model.n, m, model.n + m);
    let stats = s.run_instrumented(&|| false, limits, None);
    let result = s.extract(&lp);
    let wall = start.elapsed();
    ArmResult {
        wall,
        iters: (stats.stats1.iters, stats.stats2.iters),
        converged: stats.converged(),
        bound: lagrangian(model.n, &model.c, &model.rows, &result.dual),
    }
}

fn run_transposed(model: &ReplayModel, limits: SimplexLimits) -> Option<ArmResult> {
    let rows: Vec<RowF64> = model
        .rows
        .iter()
        .map(|(coeffs, b)| RowF64 {
            coeffs: coeffs.clone(),
            b: *b,
        })
        .collect();
    let start = std::time::Instant::now();
    let (dual, _primal, stats) = transpose::solve_transposed_for_box_lp_instrumented(
        model.n,
        &model.c,
        &rows,
        limits,
        &|| false,
    )?;
    let wall = start.elapsed();
    Some(ArmResult {
        wall,
        iters: (stats.stats1.iters, stats.stats2.iters),
        converged: stats.converged(),
        bound: lagrangian(model.n, &model.c, &model.rows, &dual),
    })
}

fn median(mut xs: Vec<f64>) -> f64 {
    xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    xs[xs.len() / 2]
}

/// A measurement harness, not a regression: without `AY_LP_REPLAY_DIR`
/// pointing at model files (format in the module docs above) it no-ops
/// instantly, so it runs un-ignored like the repo's other env-guarded
/// harnesses (the gate forbids disabled tests).
#[test]
fn replay_crossover() {
    let Some(dir) = std::env::var_os("AY_LP_REPLAY_DIR") else {
        eprintln!("AY_LP_REPLAY_DIR not set; nothing to replay");
        return;
    };
    let reps: usize = std::env::var("AY_REPLAY_REPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(5);
    // Iteration-based limits, constructed fresh per model: a shared WALL
    // deadline is an absolute instant, so one slow solve would expire it for
    // every later model (measured: exactly that happened on the first draft of
    // this harness — every post-expiry run reported 1+1 iterations). Iteration
    // caps are also load-independent, which matters on a busy machine.
    let iters_cap: usize = std::env::var("AY_REPLAY_ITERS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(300_000);
    let budget = SimplexLimits::iterations(iters_cap);
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .expect("replay dir must be readable")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "txt"))
        .collect();
    paths.sort();
    for path in paths {
        let Some(model) = parse_model(&path) else {
            eprintln!("AYXOVER skip unparseable {}", path.display());
            continue;
        };
        let mut p_walls = Vec::new();
        let mut t_walls = Vec::new();
        let mut p_last = None;
        let mut t_last = None;
        for rep in 0..reps {
            // Interleave the arms and alternate their order so shared machine
            // load cancels in the pairing.
            if rep % 2 == 0 {
                p_last = Some(run_primal(&model, budget));
                t_last = run_transposed(&model, budget);
            } else {
                t_last = run_transposed(&model, budget);
                p_last = Some(run_primal(&model, budget));
            }
            if let Some(p) = &p_last {
                p_walls.push(p.wall.as_secs_f64() * 1e3);
            }
            if let Some(t) = &t_last {
                t_walls.push(t.wall.as_secs_f64() * 1e3);
            }
        }
        let p = p_last.expect("primal arm always runs");
        let Some(t) = t_last else {
            eprintln!(
                "AYXOVER {} n={} m={} transpose-declined",
                model.name,
                model.n,
                model.rows.len()
            );
            continue;
        };
        let pm = median(p_walls);
        let tm = median(t_walls);
        let agree = if p.converged && t.converged {
            ((p.bound - t.bound).abs() <= 1e-4 * (1.0 + p.bound.abs())).to_string()
        } else {
            "n/a".to_string()
        };
        eprintln!(
            "AYXOVER {} n={} m={} ratio={:.2} primal_ms={:.3} transpose_ms={:.3} speedup={:.3} \
             p_iters={}+{} t_iters={}+{} p_conv={} t_conv={} p_bound={:.4} t_bound={:.4} agree={}",
            model.name,
            model.n,
            model.rows.len(),
            model.rows.len() as f64 / model.n as f64,
            pm,
            tm,
            pm / tm,
            p.iters.0,
            p.iters.1,
            t.iters.0,
            t.iters.1,
            p.converged,
            t.converged,
            p.bound,
            t.bound,
            agree
        );
    }
}
