// Copyright 2026 Andrew Yates
// Profiling harness: read the downstream optimization consumer's `.milp` hex dump format directly, lower it to an
// `ay_milp::Model` EXACTLY as ny-mip's `ay_lib::to_ay_model` does (feasibility
// solve, objective ignored, integer cols are ReLU binaries), and measure:
//   1. the ROOT LP relaxation (LpSession phase-1+2) -- the load-bearing "can the
//      LP engine even run" question (PFI cannot on the downstream optimization consumer's hard-six sizes),
//   2. the full MIP feasibility solve (BabSession::check).
//
// The LU / Forrest-Tomlin engine is env-gated by AY_MILP_LU=1 at simplex.rs:473,
// exercised by both sessions. Run: milp_profile <file.milp> <seconds> [lp|mip|both]

use std::time::{Duration, Instant};

use ay_milp::{BabSession, LpSession, Model, Outcome, Sense, SolveOpts};
use num_traits::ToPrimitive;

fn parse_hex_f64(t: &str) -> f64 {
    f64::from_bits(u64::from_str_radix(t, 16).expect("hex f64"))
}

struct ColSpec {
    lb: f64,
    ub: f64,
    obj: f64,
    integer: bool,
}
struct RowSpec {
    lb: f64,
    ub: f64,
    coeffs: Vec<(usize, f64)>, // (col index, weight)
}

/// Parse the `.milp` text into raw col/row specs (no Model yet), so an optional
/// scaling pass can see the whole matrix before it is built.
fn parse_specs(text: &str) -> (Vec<ColSpec>, Vec<RowSpec>) {
    let mut lines = text
        .lines()
        .map(|l| l.split('#').next().unwrap_or("").trim())
        .filter(|l| !l.is_empty());
    assert_eq!(lines.next(), Some("milp v1"), "missing milp v1 header");
    let ncols: usize = lines
        .next()
        .unwrap()
        .strip_prefix("cols ")
        .unwrap()
        .trim()
        .parse()
        .unwrap();
    let mut cols = Vec::with_capacity(ncols);
    for _ in 0..ncols {
        let mut f = lines
            .next()
            .expect("truncated cols")
            .split_ascii_whitespace();
        let lb = parse_hex_f64(f.next().unwrap());
        let ub = parse_hex_f64(f.next().unwrap());
        let obj = parse_hex_f64(f.next().unwrap());
        let integer = f.next().unwrap() == "1";
        cols.push(ColSpec {
            lb,
            ub,
            obj,
            integer,
        });
    }
    let nrows: usize = lines
        .next()
        .unwrap()
        .strip_prefix("rows ")
        .unwrap()
        .trim()
        .parse()
        .unwrap();
    let mut rows = Vec::with_capacity(nrows);
    for _ in 0..nrows {
        let mut f = lines
            .next()
            .expect("truncated rows")
            .split_ascii_whitespace();
        let lb = parse_hex_f64(f.next().unwrap());
        let ub = parse_hex_f64(f.next().unwrap());
        let k: usize = f.next().unwrap().parse().unwrap();
        let mut coeffs = Vec::with_capacity(k);
        for _ in 0..k {
            let idx: usize = f.next().unwrap().parse().unwrap();
            let w = parse_hex_f64(f.next().unwrap());
            coeffs.push((idx, w));
        }
        rows.push(RowSpec { lb, ub, coeffs });
    }
    (cols, rows)
}

/// EXACT power-of-2 geometric equilibration (the HiGHS/CPLEX-style preconditioner).
///
/// Returns (row_scale R_i, col_scale C_j), both powers of two so that
/// A'_ij = R_i·A_ij·C_j is computed with NO mantissa roundoff (pure exponent
/// shift) — the scaled LP is EXACTLY the mathematically-scaled one, so the
/// objective value and feasible set are preserved to the bit. Integer columns
/// keep C_j = 1 (scaling would move their {0,1} box). A few geometric-mean
/// sweeps drive each row's and column's coefficients toward magnitude ~1,
/// compressing a matrix that here spans 13 orders of magnitude.
fn pow2_geometric_scales(cols: &[ColSpec], rows: &[RowSpec]) -> (Vec<f64>, Vec<f64>) {
    let n = cols.len();
    let m = rows.len();
    let mut rscale = vec![1.0f64; m];
    let mut cscale = vec![1.0f64; n];
    let pow2 = |x: f64| -> f64 {
        if x <= 0.0 || !x.is_finite() {
            1.0
        } else {
            2f64.powi(x.log2().round() as i32)
        }
    };
    for _pass in 0..5 {
        // Columns (skip integer cols): C_j *= 1/sqrt(min·max of |A_ij·R_i·C_j|).
        let mut cmin = vec![f64::INFINITY; n];
        let mut cmax = vec![0.0f64; n];
        for (i, r) in rows.iter().enumerate() {
            for &(j, w) in &r.coeffs {
                if w == 0.0 || cols[j].integer {
                    continue;
                }
                let a = (w * rscale[i] * cscale[j]).abs();
                if a > 0.0 {
                    cmin[j] = cmin[j].min(a);
                    cmax[j] = cmax[j].max(a);
                }
            }
        }
        for j in 0..n {
            if cols[j].integer || cmax[j] == 0.0 {
                continue;
            }
            cscale[j] *= pow2(1.0 / (cmin[j] * cmax[j]).sqrt());
        }
        // Rows: R_i *= 1/sqrt(min·max of |A_ij·R_i·C_j|).
        for (i, r) in rows.iter().enumerate() {
            let (mut lo, mut hi) = (f64::INFINITY, 0.0f64);
            for &(j, w) in &r.coeffs {
                if w == 0.0 {
                    continue;
                }
                let a = (w * rscale[i] * cscale[j]).abs();
                if a > 0.0 {
                    lo = lo.min(a);
                    hi = hi.max(a);
                }
            }
            if hi > 0.0 {
                rscale[i] *= pow2(1.0 / (lo * hi).sqrt());
            }
        }
    }
    (rscale, cscale)
}

// The objective is returned as (col_index, Col, coeff): the index positions into
// `model_values`, the `Col` handle feeds `set_objective`. When `equilibrate` is
// set the model is built in the scaled frame (x_j = C_j·x'_j); the reported
// optimum VALUE is unchanged (column scaling preserves the objective), only the
// solution vector is in scaled coordinates.
fn build_model(
    text: &str,
    relax: bool,
) -> (Model, usize, usize, usize, Vec<(usize, ay_milp::Col, f64)>) {
    let (colspecs, rowspecs) = parse_specs(text);
    let ncols = colspecs.len();
    let equilibrate = std::env::var_os("MILP_EQUILIBRATE").is_some();
    let (rscale, cscale) = if equilibrate {
        pow2_geometric_scales(&colspecs, &rowspecs)
    } else {
        (vec![1.0; rowspecs.len()], vec![1.0; ncols])
    };
    if equilibrate {
        let cs: Vec<f64> = cscale.iter().filter(|&&c| c != 1.0).copied().collect();
        let rs_lo = rscale.iter().cloned().fold(f64::INFINITY, f64::min);
        let rs_hi = rscale.iter().cloned().fold(0.0f64, f64::max);
        eprintln!(
            "EQUILIBRATE: {} cols scaled (C range {:.2e}..{:.2e}), R range {:.2e}..{:.2e}",
            cs.len(),
            cs.iter().cloned().fold(f64::INFINITY, f64::min),
            cs.iter().cloned().fold(0.0, f64::max),
            rs_lo,
            rs_hi
        );
    }

    let mut model = Model::new();
    let mut bins = 0usize;
    let mut pinned = 0usize;
    let mut cols: Vec<ay_milp::Col> = Vec::with_capacity(ncols);
    let mut objective: Vec<(usize, ay_milp::Col, f64)> = Vec::new();
    for (i, c) in colspecs.iter().enumerate() {
        // x_j = C_j·x'_j, so the scaled box is [lb/C_j, ub/C_j] (C_j=1 for integer cols).
        let cj = cscale[i];
        let (lb, ub, obj, integer) = (c.lb, c.ub, c.obj, c.integer);
        let col = if integer && relax {
            bins += 1;
            if lb == ub {
                pinned += 1;
            }
            model.add_col(lb, ub)
        } else if integer {
            bins += 1;
            let cc = model.add_binary_col();
            let pinned_zero = lb == 0.0 && ub == 0.0;
            let pinned_one = lb == 1.0 && ub == 1.0;
            let full = lb == 0.0 && ub == 1.0;
            if pinned_zero || pinned_one {
                model.fix_col(cc, lb);
                pinned += 1;
            } else if !full {
                panic!("integer col {i} not a ReLU binary: [{lb},{ub}]");
            }
            cc
        } else {
            model.add_col(lb / cj, ub / cj)
        };
        if obj != 0.0 {
            // c'_j = c_j·C_j, so c'·x' = c·x (objective value preserved).
            objective.push((i, col, obj * cj));
        }
        cols.push(col);
    }

    for (i, r) in rowspecs.iter().enumerate() {
        let ri = rscale[i];
        let coeffs: Vec<(ay_milp::Col, f64)> = r
            .coeffs
            .iter()
            .map(|&(idx, w)| (cols[idx], w * ri * cscale[idx]))
            .collect();
        // Row i scaled by R_i: [R_i·lb, R_i·ub].
        model.add_row(r.lb * ri, r.ub * ri, &coeffs);
    }
    let (nc, nr) = (model.num_cols(), model.num_rows());
    eprintln!("model: {nc} cols ({bins} binary, {pinned} pinned), {nr} rows");
    (model, nc, nr, bins, objective)
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: milp_profile <file.milp> <seconds> [lp|mip|both]");
    let secs: f64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(60.0);
    let mode = args.next().unwrap_or_else(|| "both".to_string());

    let lu = std::env::var_os("AY_MILP_LU").is_some();
    eprintln!(
        "=== AY_MILP_LU={} timeout={secs}s mode={mode} ===",
        if lu { "1" } else { "unset" }
    );

    let text = std::fs::read_to_string(&path).expect("read .milp");
    let opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));

    if mode == "lp" || mode == "both" {
        // ROOT LP relaxation: integrality dropped so LpSession accepts it. Phase-1
        // feasibility + phase-2 on a trivial objective exercises the LP engine
        // (PFI vs LU) with no branch-and-bound around it.
        let t_parse = Instant::now();
        let (model, _nc, _nr, _bins, _obj) = build_model(&text, true);
        eprintln!(
            "LP  parse+build(relaxed): {:.3}s",
            t_parse.elapsed().as_secs_f64()
        );
        let col0 = model.col_at(0).expect("col 0");
        let t = Instant::now();
        let mut lp = match LpSession::new(&model, &opts) {
            Ok(s) => s,
            Err(e) => {
                println!("LP  SETUP_ERROR {e:?} {:.3}", t.elapsed().as_secs_f64());
                return;
            }
        };
        let setup = t.elapsed().as_secs_f64();
        eprintln!("LP  session setup: {setup:.3}s");
        let t2 = Instant::now();
        let out = lp.optimize(col0, Sense::Minimize);
        let dt = t2.elapsed().as_secs_f64();
        let tag = match &out {
            Ok(Outcome::Optimal { .. }) => "OPTIMAL".to_string(),
            Ok(Outcome::Feasible { .. }) => "FEASIBLE".to_string(),
            Ok(Outcome::Infeasible { .. }) => "INFEASIBLE".to_string(),
            Ok(Outcome::Unbounded) => "UNBOUNDED".to_string(),
            Ok(Outcome::Unknown { reason }) => format!("UNKNOWN({reason:?})"),
            Ok(other) => format!("OTHER({other:?})"),
            Err(e) => format!("ERROR({e:?})"),
        };
        println!(
            "LP  {tag} solve={dt:.3}s setup={setup:.3}s total={:.3}s",
            setup + dt
        );
    }

    if mode == "mip" || mode == "both" {
        let t_parse = Instant::now();
        let (model, _nc, _nr, _bins, _obj) = build_model(&text, false);
        eprintln!(
            "MIP parse+build(true): {:.3}s",
            t_parse.elapsed().as_secs_f64()
        );
        let t = Instant::now();
        let mut s = match BabSession::new(model.clone(), &opts) {
            Ok(s) => s,
            Err(e) => {
                println!("MIP SETUP_ERROR {e:?} {:.3}", t.elapsed().as_secs_f64());
                return;
            }
        };
        let setup = t.elapsed().as_secs_f64();
        eprintln!("MIP session setup: {setup:.3}s");
        let t2 = Instant::now();
        let out = s.check();
        let dt = t2.elapsed().as_secs_f64();
        // Caller-side stamp of the finalization-split instrument (see the
        // `AY_MILP_TRACE finalize:` lines in bab.rs): the gap between bab's
        // "outcome built" line and this one is the session-layer + drop cost.
        eprintln!("MIP check returned: {dt:.3}s");
        let tag = match &out {
            Ok(Outcome::Optimal { .. }) => "OPTIMAL".to_string(),
            // The session maps a COMPLETE `Optimal` on a no-objective model to
            // `Feasible { incumbent_only: false }` (feasibility was the question
            // asked — see `BabSession::check`). The flag is the whole verdict
            // class: `false` = the tree was EXHAUSTED and the claim is closed
            // (the feasibility-objective closure landing), `true` = a deadline
            // interrupt with open nodes (the historical w5 grind). Print it.
            Ok(Outcome::Feasible {
                incumbent_only,
                dual_bound,
                ..
            }) => {
                let db = dual_bound
                    .as_ref()
                    .map(|b| format!(" dual_bound={:.6}", b.to_f64().unwrap_or(f64::NAN)))
                    .unwrap_or_default();
                if *incumbent_only {
                    format!("FEASIBLE(sat) incumbent-only, tree OPEN{db}")
                } else {
                    format!("FEASIBLE(sat) COMPLETE (optimal claim closed){db}")
                }
            }
            Ok(Outcome::Infeasible { .. }) => "INFEASIBLE(unsat)".to_string(),
            Ok(Outcome::Unbounded) => "UNBOUNDED".to_string(),
            Ok(Outcome::Unknown { reason }) => format!("UNKNOWN({reason:?})"),
            Ok(other) => format!("OTHER({other:?})"),
            Err(e) => format!("ERROR({e:?})"),
        };
        println!(
            "MIP {tag} solve={dt:.3}s setup={setup:.3}s total={:.3}s",
            setup + dt
        );
    }

    if mode == "dumproot" {
        // MEASUREMENT: cold root LP -> dump the optimal basis (AY_BASIS_FILE).
        let (model, _nc, _nr, _bins, _obj) = build_model(&text, false);
        let path =
            std::env::var("AY_BASIS_FILE").unwrap_or_else(|_| "/tmp/ay_root_basis.txt".into());
        println!("{}", ay_milp::diag_dump_root_basis(&model, secs, &path));
        return;
    }

    if mode == "pinprobe" {
        // MEASUREMENT: reload a dumped basis (AY_BASIS_FILE) and pin-probe
        // column AY_PIN_COL to 0 and 1 — the dive's probe shape, in minutes.
        let (model, _nc, _nr, _bins, _obj) = build_model(&text, false);
        let path =
            std::env::var("AY_BASIS_FILE").unwrap_or_else(|_| "/tmp/ay_root_basis.txt".into());
        let col: usize = std::env::var("AY_PIN_COL")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(0);
        println!("{}", ay_milp::diag_pin_probe(&model, secs, &path, col));
        return;
    }

    if mode == "presolve" {
        // MEASUREMENT: root presolve alone (tighten_bounds -> tighten_coefficients)
        // with `secs` as its whole deadline. AY_MILP_TRACE=1 for per-round lines.
        let (model, _nc, _nr, _bins, _obj) = build_model(&text, false);
        println!("{}", ay_milp::diag_presolve(&model, secs));
        return;
    }

    if mode == "flp" {
        // MEASUREMENT: one cold float-lane LP solve with iteration economics.
        let (model, _nc, _nr, _bins, _obj) = build_model(&text, false);
        println!("{}", ay_milp::diag_float_lp(&model, secs));
        return;
    }

    if mode == "refine" {
        // MEASUREMENT: iterative refinement of the pinned float basis toward B*.
        // See `diag_refine_probe`.
        let (model, _nc, _nr, _bins, _obj) = build_model(&text, false);
        let report = ay_milp::diag_refine_probe(&model, secs, 40);
        println!("{report}");
        return;
    }

    if mode == "exact" {
        // MEASUREMENT: time one exact_point on the round(relax)-pinned basis, with
        // AY_MILP_SOLVE_DBG phase traces. See `diag_exact_probe`.
        let (model, _nc, _nr, _bins, _obj) = build_model(&text, false);
        let report = ay_milp::diag_exact_probe(&model, secs);
        println!("{report}");
        return;
    }

    if mode == "opt" {
        // The OPTIMIZE formulation — the apples-to-apples comparison with HiGHS,
        // which minimises the .milp's real objective column (col 6276, obj=1 on
        // the w2 window) to -4.212. the downstream optimization consumer's `optimize_col` path does exactly this:
        // build the model, `set_objective` on the objective column(s), `check()`.
        // Unlike the feasibility path (objective ignored → no bound pruning →
        // enumeration-hard), the objective gives the tree a dual bound to prune on.
        let t_parse = Instant::now();
        let (mut model, _nc, _nr, _bins, objective) = build_model(&text, false);
        eprintln!(
            "OPT parse+build(true): {:.3}s",
            t_parse.elapsed().as_secs_f64()
        );
        if objective.is_empty() {
            println!("OPT NO_OBJECTIVE (all-zero objective column — feasibility dump)");
            return;
        }
        eprintln!(
            "OPT objective: {} nonzero col(s), minimizing",
            objective.len()
        );
        let obj_terms: Vec<(ay_milp::Col, f64)> =
            objective.iter().map(|(_, c, w)| (*c, *w)).collect();
        model.set_objective(&obj_terms, Sense::Minimize);
        let t = Instant::now();
        let mut s = match BabSession::new(model.clone(), &opts) {
            Ok(s) => s,
            Err(e) => {
                println!("OPT SETUP_ERROR {e:?} {:.3}", t.elapsed().as_secs_f64());
                return;
            }
        };
        let setup = t.elapsed().as_secs_f64();
        eprintln!("OPT session setup: {setup:.3}s");
        let t2 = Instant::now();
        let out = s.check();
        let dt = t2.elapsed().as_secs_f64();
        let tag = match &out {
            Ok(Outcome::Optimal { value, .. }) => {
                format!("OPTIMAL value={:.6}", value.to_f64().unwrap_or(f64::NAN))
            }
            Ok(Outcome::Feasible {
                model_values,
                incumbent_only,
                dual_bound,
            }) => {
                // The incumbent's objective value = Σ obj_j · x_j.
                let mut v = 0.0f64;
                for (idx, _c, w) in &objective {
                    v += w * model_values[*idx].to_f64().unwrap_or(f64::NAN);
                }
                let db = dual_bound
                    .as_ref()
                    .map(|b| format!("{:.6}", b.to_f64().unwrap_or(f64::NAN)))
                    .unwrap_or_else(|| "none".to_string());
                format!("FEASIBLE incumbent={v:.6} dual_bound={db} incumbent_only={incumbent_only}")
            }
            Ok(Outcome::Infeasible { .. }) => "INFEASIBLE".to_string(),
            Ok(Outcome::Unbounded) => "UNBOUNDED".to_string(),
            Ok(Outcome::Bound {
                dual_bound,
                rigorous,
            }) => format!(
                "BOUND dual_bound={:.6} rigorous={rigorous}",
                dual_bound.to_f64().unwrap_or(f64::NAN)
            ),
            Ok(Outcome::Unknown { reason }) => format!("UNKNOWN({reason:?})"),
            Ok(other) => format!("OTHER({other:?})"),
            Err(e) => format!("ERROR({e:?})"),
        };
        println!(
            "OPT {tag} solve={dt:.3}s setup={setup:.3}s total={:.3}s",
            setup + dt
        );
    }

    if mode == "obbt" {
        // DECOMPOSITION box-tightening: rigorous OBBT (fixpoint of NS-safe
        // min+max, outward-rounded) on the pre-activation columns named in
        // AY_OBBT_COLS. A pre-activation whose box tightens off 0 turns its
        // ReLU stable -> its binary is removable. Sound by construction: every
        // bound is a rigorous dual bound weakened outward, so a box can only
        // over-approximate. AY_OBBT_OUT (optional) writes `col lb ub` per
        // tightened column for re-emission.
        use ay_milp::ObbtOpts;
        let t_parse = Instant::now();
        let (model, _nc, _nr, _bins, _obj) = build_model(&text, true);
        eprintln!(
            "OBBT parse+build(relaxed): {:.3}s",
            t_parse.elapsed().as_secs_f64()
        );
        let cols_path = std::env::var("AY_OBBT_COLS")
            .expect("obbt mode needs AY_OBBT_COLS=<file of column indices>");
        let idxs: Vec<usize> = std::fs::read_to_string(&cols_path)
            .expect("read AY_OBBT_COLS")
            .lines()
            .filter_map(|l| l.trim().parse().ok())
            .collect();
        let cols: Vec<ay_milp::Col> = idxs
            .iter()
            .map(|&i| model.col_at(i).expect("obbt col in range"))
            .collect();
        // Straddle-at-entry: the cols that carry a binary today.
        let before: Vec<(f64, f64)> = cols.iter().map(|&c| model.col_bounds(c)).collect();
        let n_straddle0 = before.iter().filter(|(l, u)| *l < 0.0 && *u > 0.0).count();
        eprintln!(
            "OBBT targets: {} cols, {} straddling 0 at entry",
            cols.len(),
            n_straddle0
        );
        let rounds: usize = std::env::var("AY_OBBT_ROUNDS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(2);
        let mut lp = match LpSession::new(&model, &opts) {
            Ok(s) => s,
            Err(e) => {
                println!("OBBT SETUP_ERROR {e:?}");
                return;
            }
        };
        let t2 = Instant::now();
        let report = lp.obbt(
            &cols,
            &ObbtOpts {
                max_rounds: rounds,
                tol: 1e-9,
            },
        );
        let dt = t2.elapsed().as_secs_f64();
        match report {
            Ok(rep) if rep.infeasible => {
                // A rigorous solve proved the sub-model INFEASIBLE — that is a
                // sound verdict on this sub-problem (the layer/prefix has no
                // feasible point over its box).
                println!(
                    "OBBT INFEASIBLE (sub-model empty) rounds={} solve={:.1}s",
                    rep.rounds, dt
                );
            }
            Ok(rep) => {
                let mut freed = 0usize; // straddled at entry, no longer straddles
                let mut narrowed = 0usize;
                let out = std::env::var("AY_OBBT_OUT").ok();
                let mut lines = String::new();
                for (k, _c) in cols.iter().enumerate() {
                    let (l0, u0) = before[k];
                    let (l1, u1) = rep.bounds[k];
                    if l1 > l0 + 1e-9 || u1 < u0 - 1e-9 {
                        narrowed += 1;
                    }
                    if l0 < 0.0 && u0 > 0.0 && !(l1 < 0.0 && u1 > 0.0) {
                        freed += 1;
                    }
                    if out.is_some() {
                        lines.push_str(&format!("{} {} {}\n", idxs[k], l1, u1));
                    }
                }
                if let Some(p) = out {
                    std::fs::write(&p, lines).expect("write AY_OBBT_OUT");
                }
                println!(
                    "OBBT rounds={} cols_tightened={} cols_narrowed={} BINARIES_FREED={}/{} solve={:.1}s",
                    rep.rounds, rep.tightened, narrowed, freed, n_straddle0, dt
                );
            }
            Err(e) => println!("OBBT ERROR {e:?} solve={dt:.1}s"),
        }
    }
}
