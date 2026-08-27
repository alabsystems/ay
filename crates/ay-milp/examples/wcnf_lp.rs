// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! REPRODUCTION SCAFFOLD (not shipped): build the exact 0/1-ILP that the MaxSAT
//! MILP race lane builds from a `.wcnf` (mirrors
//! `ay::cmd_maxsat::build_maxsat_milp_model`), then run the ROOT LP relaxation
//! cold in the float lane and (optionally) the exact-rational probe — the
//! metro / correlation-clustering LP-convergence pathology instrument.
//!
//! ```text
//! cargo run --release -p ay-milp --example wcnf_lp -- metro.wcnf 90 [exact] [--no-tall-cold-dual ...]
//! ```
//!
//! Trailing `--flag` arguments are `engine_cli` switches (the same table
//! `mps_solve` takes), so the TALL cold-dual A/B is
//! `wcnf_lp metro.wcnf 120` vs `wcnf_lp metro.wcnf 120 --no-tall-cold-dual`.
//!
//!   var x_v          -> binary col c_v
//!   hard (l1..lk)    -> row  Σ lit >= 1        (¬x contributes 1 - c_v)
//!   soft w unit (l)  -> objective on c_v directly (no relaxation var)
//!   soft w (l1..lk)  -> binary r; row Σ lit + r >= 1; objective += w·r

use ay_milp::{Col, Model, Sense};
use std::time::Instant;

fn main() {
    // WCNF_MODE=synth: skip the file, build a SMALL synthetic tall set-cover LP
    // (same ±1 covering shape as metro, but tractable for the exact solver) and
    // cross-check the float cold-dual optimum against the exact-rational optimum.
    if std::env::var("WCNF_MODE").as_deref() == Ok("synth") {
        synth_cross_check();
        return;
    }

    let all: Vec<String> = std::env::args().skip(1).collect();
    let (positional, flags): (Vec<String>, Vec<String>) =
        all.into_iter().partition(|a| !a.starts_with("--"));
    let mut args = positional.into_iter();
    let Some(path) = args.next() else {
        eprintln!("usage: wcnf_lp <file.wcnf> [seconds] [exact] [--engine-flags...]");
        std::process::exit(2);
    };
    let secs: f64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(90.0);
    let want_exact = args.next().as_deref() == Some("exact");
    // Engine switches (`--no-tall-cold-dual`, `--no-cold-dual`, ...) ride the
    // caller profile exactly as `mps_solve` carries them.
    // `applied_flags()` only. This harness has no flags of its own and takes
    // its time limit as POSITIONAL #2, so the `VALUE_FLAGS` table it used to
    // hand the parser accepted sixteen names it could not carry — `--time-limit`
    // among them, which would have renamed a 90-second default run without
    // shortening it.
    let flags = ay_milp::engine_cli::parse_applied(&flags, &[], &[]).unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(2);
    });
    let opts = ay_milp::engine_cli::apply(
        &flags,
        ay_milp::SolveOpts::new().with_time_limit(std::time::Duration::from_secs_f64(secs)),
    )
    .unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(2);
    });

    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("cannot read {path}: {e}");
        std::process::exit(2);
    });

    // --- Parse the new-format wcnf: `h <lits> 0` hard, `<w> <lits> 0` soft. ---
    let mut hard: Vec<Vec<i32>> = Vec::new();
    let mut soft: Vec<(u64, Vec<i32>)> = Vec::new();
    let mut num_vars = 0usize;
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') || line.starts_with('p') {
            continue;
        }
        let mut it = line.split_whitespace();
        let Some(first) = it.next() else { continue };
        let rest: Vec<i32> = it
            .map(|t| t.parse::<i32>().expect("literal"))
            .take_while(|&t| t != 0)
            .collect();
        for &l in &rest {
            num_vars = num_vars.max(l.unsigned_abs() as usize);
        }
        if first == "h" {
            hard.push(rest);
        } else {
            let w: u64 = first.parse().expect("weight");
            soft.push((w, rest));
        }
    }
    eprintln!(
        "parsed: {} vars, {} hard, {} soft",
        num_vars,
        hard.len(),
        soft.len()
    );

    // HARD_LIMIT=K: keep the first K hard clauses, then COMPACT the variable
    // indices to only those referenced (in the kept hards + all softs), so the
    // truncated LP stays self-contained and small enough for the exact-rational
    // solver to finish — a tractable-but-still-TALL slice of the real metro LP
    // for the float-vs-exact cross-check.
    if let Ok(k) = std::env::var("HARD_LIMIT") {
        let k: usize = k.parse().expect("HARD_LIMIT");
        hard.truncate(k);
        let mut remap: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();
        let mut relabel = |lit: i32| -> i32 {
            let v = lit.unsigned_abs();
            let next = remap.len() as u32 + 1;
            let nv = *remap.entry(v).or_insert(next);
            if lit < 0 {
                -(nv as i32)
            } else {
                nv as i32
            }
        };
        for cl in &mut hard {
            for l in cl.iter_mut() {
                *l = relabel(*l);
            }
        }
        for (_, cl) in &mut soft {
            for l in cl.iter_mut() {
                *l = relabel(*l);
            }
        }
        num_vars = remap.len();
        eprintln!(
            "truncated: {} vars, {} hard, {} soft",
            num_vars,
            hard.len(),
            soft.len()
        );
    }

    // --- Build the model exactly as the MILP race lane does. ---
    // WCNF_MODE=exlp builds the CONTINUOUS [0,1] relaxation so `LpSession`'s
    // exact-rational simplex can be cross-checked against the float lane.
    let mode = std::env::var("WCNF_MODE").unwrap_or_default();
    // exlp: exact LpSession. cbab: continuous BabSession (float LP + EXACT
    // optimality certificate — the fast float-vs-exact agreement check).
    let continuous = mode == "exlp" || mode == "cbab";
    let mut m = Model::new();
    let var_cols: Vec<Col> = (0..num_vars)
        .map(|_| {
            if continuous {
                m.add_col(0.0, 1.0)
            } else {
                m.add_binary_col()
            }
        })
        .collect();
    let clause_row = |lits: &[i32]| -> (Vec<(Col, f64)>, f64) {
        let mut coeffs = Vec::with_capacity(lits.len() + 1);
        let mut rhs = 1.0_f64;
        for &l in lits {
            let c = var_cols[(l.unsigned_abs() as usize) - 1];
            if l > 0 {
                coeffs.push((c, 1.0));
            } else {
                coeffs.push((c, -1.0));
                rhs -= 1.0;
            }
        }
        (coeffs, rhs)
    };
    for cl in &hard {
        if cl.is_empty() {
            eprintln!("empty hard clause -> trivially UNSAT");
            std::process::exit(1);
        }
        let (coeffs, rhs) = clause_row(cl);
        m.add_row(rhs, f64::INFINITY, &coeffs);
    }
    let mut obj_map: std::collections::HashMap<Col, f64> = std::collections::HashMap::new();
    let mut offset = 0.0_f64;
    for (w, cl) in &soft {
        let w = *w as f64;
        match cl.as_slice() {
            [] => offset += w,
            &[l] => {
                let c = var_cols[(l.unsigned_abs() as usize) - 1];
                if l > 0 {
                    *obj_map.entry(c).or_insert(0.0) -= w;
                    offset += w;
                } else {
                    *obj_map.entry(c).or_insert(0.0) += w;
                }
            }
            _ => {
                let r = if continuous {
                    m.add_col(0.0, 1.0)
                } else {
                    m.add_binary_col()
                };
                let (mut coeffs, rhs) = clause_row(cl);
                coeffs.push((r, 1.0));
                m.add_row(rhs, f64::INFINITY, &coeffs);
                *obj_map.entry(r).or_insert(0.0) += w;
            }
        }
    }
    let obj: Vec<(Col, f64)> = obj_map.into_iter().filter(|&(_, a)| a != 0.0).collect();
    m.set_objective(&obj, Sense::Minimize);
    if offset != 0.0 {
        m.set_objective_offset(offset);
    }
    eprintln!("model: {} rows, {} cols", m.num_rows(), m.num_cols());

    // --- Exact-rational LP relaxation cross-check (WCNF_MODE=exlp). ---
    if mode == "exlp" {
        use ay_milp::{LpSession, Outcome};
        use num_traits::ToPrimitive;
        let mut s = LpSession::new(&m, &opts).expect("continuous model");
        let t = Instant::now();
        let out = s.optimize_model_objective().expect("optimize");
        let dt = t.elapsed().as_secs_f64();
        match out {
            Outcome::Optimal { value, .. } => {
                eprintln!(
                    "[{dt:.1}s] EXACT-LP Optimal value={} (= {})",
                    value.to_f64().unwrap_or(f64::NAN),
                    value
                );
            }
            o => eprintln!("[{dt:.1}s] EXACT-LP {o:?}"),
        }
        return;
    }

    // --- Root float LP relaxation, cold. ---
    if mode != "bab" && mode != "cbab" {
        let t = Instant::now();
        let line = ay_milp::diag_float_lp_with(&m, secs, &opts);
        eprintln!("[{:.1}s] {line}", t.elapsed().as_secs_f64());
        if want_exact {
            let t = Instant::now();
            let line = ay_milp::diag_exact_probe(&m, secs);
            eprintln!("[{:.1}s] {line}", t.elapsed().as_secs_f64());
        }
        return;
    }

    // --- Branch-and-bound: WCNF_MODE=bab (binary, real MILP-race lane) or
    //     WCNF_MODE=cbab (continuous relaxation, exact-certified LP optimum). ---
    use ay_milp::{BabSession, Outcome};
    let mut s = BabSession::new(m, &opts).expect("session");
    let t = Instant::now();
    let out = s.check();
    let dt = t.elapsed().as_secs_f64();
    match out {
        Ok(Outcome::Optimal { value, .. }) => {
            use num_traits::ToPrimitive;
            eprintln!(
                "[{dt:.1}s] BAB Optimal value={}",
                value.to_f64().unwrap_or(f64::NAN)
            );
        }
        Ok(Outcome::Feasible { dual_bound, .. }) => {
            use num_traits::ToPrimitive;
            let db = dual_bound
                .as_ref()
                .and_then(|d| d.to_f64())
                .map(|f| format!("{f:.4}"))
                .unwrap_or_else(|| "none".to_string());
            eprintln!("[{dt:.1}s] BAB Feasible dual_bound={db}");
        }
        Ok(o) => eprintln!("[{dt:.1}s] BAB {o:?}"),
        Err(e) => eprintln!("[{dt:.1}s] BAB ERROR {e:?}"),
    }
}

/// Build a small synthetic TALL set-cover LP (m rows >> n cols, ±1 coverage
/// rows `Σ x >= 1`, varied costs) — metro's shape at a size the exact-rational
/// simplex can finish — and cross-check the FLOAT cold-dual optimum against the
/// EXACT `LpSession` optimum.
fn synth_cross_check() {
    use ay_milp::{LpSession, Outcome, SolveOpts};
    use num_traits::ToPrimitive;

    // m sits above `TALL_LU_ROWS` (1,000 — a const on main, no runtime
    // override) so this small LP trips `tall_cold_dual` (m >= tall_lu_rows &&
    // n < m) while staying tractable for the exact-rational simplex. The
    // cold-dual algorithm is size-agnostic — the code path exercised is
    // identical to metro's.
    let n: usize = 80;
    let m: usize = 1_200;
    let mut state: u64 = 0x1234_5678_9abc_def0;
    let mut rng = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };

    let mut model = Model::new();
    let cols: Vec<Col> = (0..n).map(|_| model.add_col(0.0, 1.0)).collect();
    for _ in 0..m {
        // Two distinct columns, `x_a + x_b >= 1`: a vertex-cover-style row whose
        // LP relaxation drives FRACTIONAL (1/2) optima — the discriminating case.
        let a = (rng() as usize) % n;
        let mut b = (rng() as usize) % n;
        while b == a {
            b = (rng() as usize) % n;
        }
        model.add_row(1.0, f64::INFINITY, &[(cols[a], 1.0), (cols[b], 1.0)]);
    }
    // Uniform unit costs: min Σ x over the cover LP — the classic fractional
    // vertex-cover relaxation.
    let obj: Vec<(Col, f64)> = (0..n).map(|j| (cols[j], 1.0)).collect();
    model.set_objective(&obj, Sense::Minimize);
    eprintln!("synth model: {m} rows, {n} cols (tall covering)");

    // EXACT optimum (Dutertre-de Moura exact-rational simplex).
    let opts = SolveOpts::new().with_time_limit(std::time::Duration::from_mins(1));
    let mut s = LpSession::new(&model, &opts).expect("continuous");
    let out = s.optimize_model_objective().expect("optimize");
    let exact = match out {
        Outcome::Optimal { value, .. } => value,
        o => {
            eprintln!("EXACT not optimal: {o:?}");
            std::process::exit(1);
        }
    };
    let exact_f = exact.to_f64().unwrap_or(f64::NAN);
    eprintln!("EXACT optimum = {exact}  ({exact_f})");

    // THE SCAFFOLD'S COLD WALK — *not* "the float lane", which is what this
    // line used to call it. `diag_float_lp` is one cold walk with no ladder and
    // nothing certified; the lane a solve runs is `diag_shipped_float_lp`
    // below. The distinction is load-bearing in BOTH directions here: a
    // scaffold `Stopped` would have been reported as the float lane
    // disagreeing with exact arithmetic (a false soundness alarm), and a
    // scaffold agreement was being read as evidence about a lane it never ran.
    let line = ay_milp::diag_float_lp(&model, 60.0);
    eprintln!("{line}");
    // Split from the RIGHT of the banner: the prefix deliberately contains no
    // `status=` / `obj(min-form)=` token, so these two parses are unaffected by
    // it, but say so here rather than leaving the coupling implicit.
    let status = line
        .split("status=")
        .nth(1)
        .and_then(|s| s.split_whitespace().next())
        .unwrap_or("?");
    let float_obj: f64 = line
        .split("obj(min-form)=")
        .nth(1)
        .and_then(|s| s.split_whitespace().next())
        .and_then(|s| s.parse().ok())
        .unwrap_or(f64::NAN);
    let agree = status == "Optimal" && (float_obj - exact_f).abs() <= 1e-6 * (1.0 + exact_f.abs());
    eprintln!(
        "CROSS-CHECK(scaffold cold walk): status={status} obj={float_obj} exact={exact_f} agree={agree}"
    );

    // THE SHIPPED LANE on the same model, so the reader can see the thing they
    // would actually quote. NOTE WHAT THIS IS NOT: it is PRINTED, not CHECKED.
    // `agree` and the `exit(1)` below are still computed from the scaffold walk
    // alone, so a disagreement between the shipped lane and exact arithmetic
    // would exit 0 and pass silently. Wiring it into the alarm needs its own
    // decision about what a `DECLINED` shipped line should mean, which is a
    // verdict change and not a labelling fix.
    let shipped = ay_milp::diag_shipped_float_lp(&model, 60.0, &opts);
    eprintln!("CROSS-CHECK(shipped lane): {shipped}");

    if !agree {
        std::process::exit(1);
    }
}
