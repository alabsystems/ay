// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TEST-ONLY measurement scaffolding for the exact rim's TABLEAU
//! REPRESENTATION. Not compiled into any shipped binary (`#[cfg(test)]`), so
//! it can be as expensive as it likes at the sites it is allowed to touch.
//!
//! What it reports, per solve, all load-invariant except the walls:
//!
//! * `pivots` — algebraic pivots (`ExactLp::pivot`), the currency an A/B of
//!   two ARITHMETICS must hold fixed: the pivot RULE is untouched by any
//!   representation change, so a differing pivot count is a bug, not a result.
//! * `inline_i64` — the share of tableau entries a pivot WROTE that landed on
//!   `Rational::Small`, i.e. did not leave the inline `i64` path. This is the
//!   switch's signal, measured exactly where the policy would measure it.
//! * `lambda` — the per-row integralising scale census: how many rows of the
//!   model are not integral, and how wide the scale that would fix them is.
//!
//! Driven by `cargo test -p ay-milp --release exact::probe::rim -- --nocapture`.
//! With no environment it exercises a tiny built-in model; `RIM_INST` can name
//! an MPS file and `RIM_SECS` can set its budget for a corpus measurement.

use std::time::Instant;

use ay_lra::rational::Rational;
use num_bigint::BigInt;
use num_integer::Integer as _;
use num_traits::{One as _, Zero as _};

use super::{Budget, ExactLp, LpFeasibility, LpOptimum};
use crate::model::{Col, Model, Row, Sense};

thread_local! {
    static PIVOTS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static WRITTEN: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static WRITTEN_SMALL: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Window trace: stride (0 = off), and the window's own two counters.
    static TRACE: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static WIN: std::cell::Cell<(u64, u64)> = const { std::cell::Cell::new((0, 0)) };
}

pub(super) fn reset() {
    PIVOTS.with(|p| p.set(0));
    WRITTEN.with(|p| p.set(0));
    WRITTEN_SMALL.with(|p| p.set(0));
    WIN.with(|p| p.set((0, 0)));
    SWITCH_AT.with(|p| p.set(0));
    FORCE.with(|p| {
        p.set(
            std::env::var("RIM_FORCE")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(0),
        )
    });
    TRACE.with(|p| {
        p.set(
            std::env::var("RIM_TRACE")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(0),
        )
    });
}

pub(super) fn pivots() -> u64 {
    PIVOTS.with(std::cell::Cell::get)
}

fn written() -> (u64, u64) {
    (
        WRITTEN.with(std::cell::Cell::get),
        WRITTEN_SMALL.with(std::cell::Cell::get),
    )
}

thread_local! {
    /// A/B override for the policy: 0 auto (what ships), 1 never switch,
    /// 2 switch at the first pivot that can. Test-only, so the shipped policy
    /// has no way to be overridden at all.
    static FORCE: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
    /// Pivot at which the conversion fired (0 = never).
    static SWITCH_AT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

#[inline]
pub(super) fn force() -> u8 {
    FORCE.with(std::cell::Cell::get)
}

/// Pin the A/B override for the current thread (unit tests drive the arms
/// directly rather than through the environment).
pub(super) fn set_force(v: u8) {
    FORCE.with(|p| p.set(v));
}

/// The policy's three constants, overridable in a test build only:
/// `RIM_PARAMS=<window>,<inline percent>,<sustain>`.
pub(super) fn params() -> (u64, u64, u32) {
    let default = (
        super::SWITCH_WINDOW,
        super::SWITCH_INLINE_PERCENT,
        super::SWITCH_SUSTAIN,
    );
    let Ok(spec) = std::env::var("RIM_PARAMS") else {
        return default;
    };
    let parts: Vec<&str> = spec.split(',').collect();
    if parts.len() != 3 {
        return default;
    }
    match (parts[0].parse(), parts[1].parse(), parts[2].parse()) {
        (Ok(w), Ok(p), Ok(s)) => (w, p, s),
        _ => default,
    }
}

/// The tableau converted, at the pivot in progress.
pub(super) fn switched() {
    if SWITCH_AT.with(std::cell::Cell::get) == 0 {
        SWITCH_AT.with(|p| p.set(pivots().max(1)));
    }
}

/// One pivot happened.
#[inline]
pub(super) fn tick() {
    let n = PIVOTS.with(|p| {
        let v = p.get() + 1;
        p.set(v);
        v
    });
    let stride = TRACE.with(std::cell::Cell::get);
    if stride > 0 && n % stride == 0 {
        let (w, s) = WIN.with(|p| p.replace((0, 0)));
        let share = if w == 0 {
            100.0
        } else {
            100.0 * s as f64 / w as f64
        };
        eprintln!("RIMWIN pivot={n} window_entries={w} window_inline_i64={share:.3}%");
    }
}

/// A pivot rewrote `terms` — census the entries it wrote.
#[inline]
pub(super) fn census(terms: &[(u32, Rational)]) {
    let small = terms.iter().filter(|(_, c)| c.is_small()).count() as u64;
    WRITTEN.with(|p| p.set(p.get() + terms.len() as u64));
    WRITTEN_SMALL.with(|p| p.set(p.get() + small));
    if TRACE.with(std::cell::Cell::get) > 0 {
        WIN.with(|p| {
            let (w, s) = p.get();
            p.set((w + terms.len() as u64, s + small));
        });
    }
}

fn load(path: &str) -> Model {
    let text = std::fs::read_to_string(path).expect("instance");
    crate::read_mps(&text).expect("parse").model
}

fn objective(model: &Model) -> Vec<(u32, Rational)> {
    let mut obj: Vec<(u32, Rational)> = Vec::new();
    for j in 0..model.num_cols() {
        let a = model.obj_coeff(Col(j as u32));
        if a != 0.0 {
            let e = model.obj_coeff_exact_at(j as u32, a);
            if !e.is_zero() {
                obj.push((j as u32, Rational::from_big(e)));
            }
        }
    }
    if model.sense() == Sense::Maximize {
        for (_, c) in &mut obj {
            *c = -c.clone();
        }
    }
    obj
}

/// The row-integralisation census: `λ_r = lcm(denominators of row r)`.
/// A model whose every `λ_r` is 1 is one whose tableau matrix is already the
/// integer matrix the fraction-free form needs.
fn lambda_census(model: &Model) -> (usize, usize, u64, u64) {
    let mut nonunit = 0usize;
    let mut max_bits = 0u64;
    let mut prod_bits = 0u64;
    for r in 0..model.num_rows() {
        let (coeffs, _, _) = model.row(Row(r as u32));
        let mut lam = BigInt::one();
        for &(c, a) in coeffs {
            lam = lam.lcm(model.row_coeff_exact(r, c, a).denom());
        }
        if !lam.is_one() {
            nonunit += 1;
            max_bits = max_bits.max(lam.bits());
            prod_bits += lam.bits();
        }
    }
    (model.num_rows(), nonunit, max_bits, prod_bits)
}

/// One instance, the rim driven directly (no float lane in the picture).
#[test]
fn rim() {
    let (name, model) = match std::env::var("RIM_INST") {
        Ok(path) => {
            let name = path.rsplit('/').next().unwrap_or(&path).to_string();
            (name, load(&path))
        }
        Err(_) => {
            let mut model = Model::new();
            let x = model.add_col(0.0, 1.0);
            let y = model.add_col(0.0, 1.0);
            model.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
            model.set_objective(&[(x, 1.0), (y, 1.0)], Sense::Minimize);
            ("built-in-smoke".to_string(), model)
        }
    };
    let secs: u64 = std::env::var("RIM_SECS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(120);
    let (rows, nonunit, lam_max, lam_prod) = lambda_census(&model);
    eprintln!(
        "RIMLAMBDA inst={name} rows={rows} cols={} nonintegral_rows={nonunit} \
         max_lambda_bits={lam_max} sum_lambda_bits={lam_prod}",
        model.num_cols()
    );
    let obj = objective(&model);
    // `RIM_ITERS` caps the iteration budget so an instance that FINISHES in
    // neither representation still yields a like-for-like comparison: both arms
    // run the same pivot sequence to the same cut-off, and only the wall
    // differs.
    let iters: u64 = std::env::var("RIM_ITERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| Budget::default_iters(model.num_cols() + model.num_rows()));
    let budget = Budget {
        deadline: Some(Instant::now() + std::time::Duration::from_secs(secs)),
        max_iters: iters,
    };
    reset();
    let t_build = Instant::now();
    let mut lp = ExactLp::new(&model);
    let build = t_build.elapsed();
    let t_p1 = Instant::now();
    let feas = lp.make_feasible(&budget);
    let p1 = t_p1.elapsed();
    let p1_pivots = pivots();
    let feas_label = match &feas {
        LpFeasibility::Feasible => "Feasible",
        LpFeasibility::Infeasible(_) => "Infeasible",
        LpFeasibility::Unknown(_) => "Unknown",
    };
    let t = Instant::now();
    let out = lp.minimize(&obj, &budget);
    let dt = t.elapsed();
    let piv = pivots();
    let (w, ws) = written();
    let share = if w == 0 {
        100.0
    } else {
        100.0 * ws as f64 / w as f64
    };
    let form = lp.form_label();
    let switch_at = SWITCH_AT.with(std::cell::Cell::get);
    match out {
        LpOptimum::Optimal { value, multipliers } => {
            eprintln!(
                "RIMRESULT inst={name} status=OPTIMAL form={form} switch_at={switch_at} phase1={feas_label} \
                 p1_pivots={p1_pivots} pivots={piv} entries_written={w} inline_i64={share:.2}% \
                 build={:.3}s p1={:.3}s solve={:.3}s mult={} value={value}",
                build.as_secs_f64(),
                p1.as_secs_f64(),
                dt.as_secs_f64(),
                multipliers.len(),
            );
        }
        other => eprintln!(
            "RIMRESULT inst={name} status=NONOPTIMAL form={form} switch_at={switch_at} phase1={feas_label} \
             p1_pivots={p1_pivots} pivots={piv} entries_written={w} inline_i64={share:.2}% \
             build={:.3}s p1={:.3}s solve={:.3}s detail={other:?}",
            build.as_secs_f64(),
            p1.as_secs_f64(),
            dt.as_secs_f64(),
        ),
    }
}
