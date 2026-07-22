// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Post-solve MILP optimality upgrade — the ay-milp engine lane.
//!
//! When the portfolio ends `SATISFIABLE` on a LINEAR optimization instance, the
//! remaining question is a *dual bound*: is the incumbent optimal? The ay-milp
//! branch-and-bound engine (exact-rational node arithmetic, measured 2026-07-16 as
//! the fastest prover in a 6-solver field — incl. Gurobi — on its dense-binary
//! ladder and 9/11 on diverse MIPLIB) is AY's native engine for exactly that
//! question. This lane hands it the instance and adopts its verdict fail-closed.
//!
//! # Soundness (the entire point)
//!
//! An adopted `OPTIMUM` rests on three independent checks, all here:
//!
//! 1. **Exact translation.** The 0/1 MILP is built from the ORIGINAL constraints
//!    with every coefficient/rhs gated to be exactly representable in `f64`
//!    (`|v| <= 2^53`, folding `~x = 1 - x` into the rhs in exact `i128` first).
//!    On any non-linear term, oversized coefficient, or unsupported relation the
//!    lane DECLINES — the translated model is the instance or nothing.
//! 2. **Engine verdict.** Only `Outcome::Optimal` is upgraded. `Feasible`/`Bound`/
//!    `Unknown` leave the portfolio's answer untouched (the engine's incumbent is
//!    still surfaced through `on_improve` if it re-verifies and improves).
//! 3. **Independent re-verification.** The claimed optimal point is rounded to a
//!    0/1 assignment and re-checked against the ORIGINAL `i128` constraints via
//!    [`crate::eval::verify_all_constraints`], and its exact objective value via
//!    `eval_objective` must equal BOTH the engine's claimed value AND be `<=` the
//!    portfolio incumbent's value. Any mismatch declines. A wrong engine claim can
//!    therefore never surface as a wrong `OPTIMUM` — at worst the lane is a no-op.

use crate::eval::verify_all_constraints;
use crate::solver::eval_objective;
use crate::types::{PbInstance, PbObjective, PbRel, PbTerm};
use ay_milp::{BabSession, Col, Model, Outcome, Sense, SolveOpts};
use num_traits::ToPrimitive;
use std::time::Duration;

/// Largest integer magnitude exactly representable in `f64`.
const MAX_EXACT_F64: i128 = 1 << 53;

/// Size gates: keep the lane on instances where the engine's dense-LP B&B is
/// MEASURED competent. The 2026-07-16 A/B pinned the boundary: the wins (lp4l
/// 85 rows / ~4k nnz, `10:10` 421 rows) are low-row/low-nnz; the losses are huge
/// (bnn ~500k nnz RSS-memouts even with the engine budget; 2club's 17k rows burn
/// the pre-slice for nothing). Rows/nnz caps exclude exactly the measured losers
/// while keeping every measured winner (incl. single-row knapsacks).
const MILP_MAX_VARS: u32 = 4096;
const MILP_MAX_ROWS: usize = 2_000;
const MILP_MAX_NNZ: usize = 60_000;

/// Linear-term view: `(var0, coeff_on_x, rhs_delta)`. A negated literal `~x`
/// contributes `c*(1-x)`, i.e. `-c` on `x` and `-c` folded into the rhs side
/// (LHS constant `+c` == rhs `-c`). `None` on a non-linear (product) term.
fn lin(term: &PbTerm) -> Option<(usize, i128, i128)> {
    let [lit] = term.lits.as_slice() else {
        return None;
    };
    let v = (lit.var as usize).checked_sub(1)?;
    if lit.negated {
        Some((v, term.coeff.checked_neg()?, term.coeff))
    } else {
        Some((v, term.coeff, 0))
    }
}

fn exact_f64(v: i128) -> Option<f64> {
    if v.abs() > MAX_EXACT_F64 {
        return None;
    }
    Some(v as f64)
}

/// Builds the exact 0/1 MILP or declines. Returns the model; column `j`
/// corresponds to PB variable `j + 1`.
fn build_model(instance: &PbInstance, objective: &PbObjective) -> Option<Model> {
    let n = instance.num_vars as usize;
    let mut model = Model::new();
    let cols: Vec<Col> = (0..n).map(|_| model.add_binary_col()).collect();

    for c in &instance.constraints {
        let mut coeffs: std::collections::HashMap<usize, i128> = std::collections::HashMap::new();
        let mut rhs = c.rhs;
        for t in &c.terms {
            let (v, cx, off) = lin(t)?;
            if v >= n {
                return None;
            }
            *coeffs.entry(v).or_insert(0) = coeffs.get(&v).copied().unwrap_or(0).checked_add(cx)?;
            rhs = rhs.checked_sub(off)?;
        }
        let row: Vec<(Col, f64)> = coeffs
            .iter()
            .map(|(&v, &a)| Some((cols[v], exact_f64(a)?)))
            .collect::<Option<_>>()?;
        let rhs_f = exact_f64(rhs)?;
        match c.rel {
            PbRel::Ge => model.add_row(rhs_f, f64::INFINITY, &row),
            PbRel::Eq => model.add_row(rhs_f, rhs_f, &row),
        };
    }

    let mut ocoeffs: std::collections::HashMap<usize, i128> = std::collections::HashMap::new();
    let mut offset = 0i128;
    for t in &objective.terms {
        let (v, cx, off) = lin(t)?;
        if v >= n {
            return None;
        }
        *ocoeffs.entry(v).or_insert(0) = ocoeffs.get(&v).copied().unwrap_or(0).checked_add(cx)?;
        offset = offset.checked_add(off)?;
    }
    let orow: Vec<(Col, f64)> = ocoeffs
        .iter()
        .map(|(&v, &a)| Some((cols[v], exact_f64(a)?)))
        .collect::<Option<_>>()?;
    model.set_objective(&orow, Sense::Minimize);
    model.set_objective_offset(exact_f64(offset)?);
    Some(model)
}

/// Eligibility pre-check (cheap): linear single-literal terms everywhere, size
/// gates, every coefficient/rhs exactly `f64`-representable.
pub(crate) fn milp_lane_eligible(instance: &PbInstance, objective: &PbObjective) -> bool {
    if instance.num_vars == 0 || instance.num_vars > MILP_MAX_VARS {
        return false;
    }
    if instance.constraints.len() > MILP_MAX_ROWS {
        return false;
    }
    let nnz: usize = instance.constraints.iter().map(|c| c.terms.len()).sum();
    if nnz > MILP_MAX_NNZ {
        return false;
    }
    let term_ok = |t: &PbTerm| t.lits.len() == 1 && t.coeff.abs() <= MAX_EXACT_F64;
    if !objective.terms.iter().all(term_ok) {
        return false;
    }
    instance
        .constraints
        .iter()
        .all(|c| c.rhs.abs() <= MAX_EXACT_F64 && c.terms.iter().all(term_ok))
}

/// Runs the ay-milp engine on `instance` for up to `budget`, seeded with the
/// portfolio incumbent. Returns a RE-VERIFIED optimal assignment + value iff the
/// engine proves optimality and every independent check passes; `None` otherwise
/// (including on any engine error — fail-closed).
pub(crate) fn try_milp_optimum_upgrade(
    instance: &PbInstance,
    objective: &PbObjective,
    incumbent: Option<(&[bool], i128)>,
    budget: Duration,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<(Vec<bool>, i128)> {
    let n = instance.num_vars as usize;
    let incumbent_value = match incumbent {
        Some((a, v)) => {
            if a.len() != n {
                return None;
            }
            v
        }
        None => i128::MAX,
    };
    let model = build_model(instance, objective)?;
    // Bound the engine's memory so a dense instance can never push the PROCESS
    // over the harness envelope (measured: an unbounded run on a 1289-var dense
    // BNN instance tripped the external 6000 MiB watchdog). 1.5 GiB is far above
    // anything the winning instances need and safely below competition limits.
    const ENGINE_MEMORY_BUDGET: usize = 1_536 * 1024 * 1024;
    let opts = SolveOpts::new()
        .with_time_limit(budget)
        .with_memory_budget(Some(ENGINE_MEMORY_BUDGET));
    let mut session = BabSession::new(model.clone(), &opts).ok()?;
    // Seed the engine with the portfolio incumbent when one exists (a valid
    // feasible point of the exact translation); the lane stays authoritative via
    // re-verification below regardless.
    if let Some((a, _)) = incumbent {
        let seed: Vec<f64> = a.iter().map(|&b| if b { 1.0 } else { 0.0 }).collect();
        session.seed_incumbent(&seed);
    }

    let outcome = session.check().ok()?;
    let extract = |vals: &[num_rational::BigRational]| -> Vec<bool> {
        (0..n)
            .map(|i| vals.get(i).and_then(|r| r.to_f64()).unwrap_or(0.0) > 0.5)
            .collect()
    };
    match outcome {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            // Exact integer claimed value (decline on a non-integer optimum —
            // cannot happen for an integral objective, so treat as engine error).
            if !value.is_integer() {
                return None;
            }
            let claimed = value.to_integer().to_i128()?;
            let assignment = extract(&model_values);
            if !verify_all_constraints(&instance.constraints, &assignment) {
                return None;
            }
            let actual = eval_objective(objective, &assignment);
            if actual != claimed || (incumbent_value != i128::MAX && actual > incumbent_value) {
                return None;
            }
            on_improve(actual, &assignment);
            Some((assignment, actual))
        }
        Outcome::Feasible { model_values, .. } => {
            // No optimality claim: surface a strictly-better re-verified incumbent
            // through the anytime channel, but never upgrade the status.
            let assignment = extract(&model_values);
            if verify_all_constraints(&instance.constraints, &assignment) {
                let val = eval_objective(objective, &assignment);
                if val < incumbent_value {
                    on_improve(val, &assignment);
                }
            }
            None
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbConstraint, PbLit};

    fn term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        }
    }
    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    /// LP-gap toy: min 2x1+2x2 s.t. 2x1+2x2 >= 3 — LP 3, integer optimum 4. The
    /// engine must prove 4 and the lane must adopt it after re-verification.
    #[test]
    fn milp_lane_proves_lp_gap_toy() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(2, 1), term(2, 2)], 3)],
            objective: Some(PbObjective {
                terms: vec![term(2, 1), term(2, 2)],
            }),
        };
        let objective = instance.objective.clone().unwrap();
        assert!(milp_lane_eligible(&instance, &objective));
        let mut best = None;
        let got = try_milp_optimum_upgrade(
            &instance,
            &objective,
            Some((&[true, true][..], 4)),
            Duration::from_secs(10),
            &mut |v, a| best = Some((v, a.to_vec())),
        );
        let (assignment, value) = got.expect("engine must prove the LP-gap toy");
        assert_eq!(value, 4);
        assert!(verify_all_constraints(&instance.constraints, &assignment));
    }

    /// Oversized coefficients (not exactly f64-representable) must decline.
    #[test]
    fn milp_lane_declines_inexact_coefficients() {
        let big = (1i128 << 53) + 1;
        let instance = PbInstance {
            num_vars: 1,
            num_constraints: 1,
            constraints: vec![ge(vec![term(big, 1)], 1)],
            objective: Some(PbObjective {
                terms: vec![term(1, 1)],
            }),
        };
        let objective = instance.objective.clone().unwrap();
        assert!(!milp_lane_eligible(&instance, &objective));
    }
}

#[cfg(test)]
mod lane_probe {
    use super::*;

    /// Manual lane probe: MILP_LANE_FILE=<opb> runs the lane on the real instance
    /// with the engine's own first answer as the seed. PROBE_SECS overrides the
    /// per-phase budget (default 30). MILP_LANE_SEED_FILE=<txt of space-separated
    /// 0/1 per var> skips the unseeded phase and seeds an EXTERNAL verified
    /// incumbent instead — the warm-restart experiment: the whole budget goes to
    /// the lane with the best-known point pruning from t=0. Prints the outcome,
    /// including the rigorous dual bound on interrupted runs — the number to
    /// watch on the hard tail.
    #[test]
    #[ignore = "manual; set MILP_LANE_FILE"]
    fn milp_lane_file_probe() {
        let path = std::env::var("MILP_LANE_FILE").expect("set MILP_LANE_FILE");
        let secs: u64 = std::env::var("PROBE_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(30);
        let raw = std::fs::read_to_string(&path).expect("read");
        let inst = crate::parse_opb(&raw).expect("parse");
        let obj = inst.objective.clone().expect("objective");
        let seed: Vec<bool> = if let Ok(sf) = std::env::var("MILP_LANE_SEED_FILE") {
            let toks = std::fs::read_to_string(&sf).expect("read seed");
            let s: Vec<bool> = toks.split_whitespace().map(|t| t == "1").collect();
            assert_eq!(s.len(), inst.num_vars as usize, "seed length");
            assert!(
                crate::eval::verify_all_constraints(&inst.constraints, &s),
                "external seed does not satisfy the instance"
            );
            eprintln!("external seed verified");
            s
        } else {
            // Unseeded engine run to obtain a feasible point + value for the seed.
            let model = build_model(&inst, &obj).expect("model");
            let opts = SolveOpts::new().with_time_limit(Duration::from_secs(secs));
            let mut s = BabSession::new(model.clone(), &opts).expect("session");
            let out = s.check().expect("check");
            let mvals = match &out {
                Outcome::Optimal {
                    model_values,
                    value,
                    ..
                } => {
                    eprintln!("unseeded: Optimal value={value}");
                    model_values.clone()
                }
                Outcome::Feasible {
                    model_values,
                    dual_bound,
                    ..
                } => {
                    eprintln!("unseeded: Feasible dual_bound={dual_bound:?}");
                    model_values.clone()
                }
                other => panic!("unseeded run gave {other:?}"),
            };
            (0..inst.num_vars as usize)
                .map(|i| mvals.get(i).and_then(|r| r.to_f64()).unwrap_or(0.0) > 0.5)
                .collect()
        };
        let seed_val = crate::solver::eval_objective(&obj, &seed);
        eprintln!("seed value = {seed_val}");
        let mut streamed = vec![];
        let got = try_milp_optimum_upgrade(
            &inst,
            &obj,
            Some((&seed[..], seed_val)),
            Duration::from_secs(secs),
            &mut |v, _| streamed.push(v),
        );
        eprintln!(
            "LANE RESULT: {:?} streamed={streamed:?}",
            got.map(|(_, v)| v)
        );
    }
}
