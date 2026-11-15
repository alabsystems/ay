//! Blocking-clause AllSAT scaling probe (TY consumer shape, 2026-10-05).
//!
//! Reproduces the reference implementation's `tla-ay` `NestedPowersetEncoder::enumerate_all` constrained
//! path: `n` Boolean variables, a QF_LIA cardinality bound
//! `sum(ite(b_i, 1, 0)) >= k`, and one full blocking clause asserted after
//! each model, re-solved incrementally on one `Solver`.
//!
//! usage: allsat_blocking_scaling <n> <k> [checkpoint-every] [lia|bool]
//! `bool` encodes the same at-least-k family propositionally (one clause per
//! (n-k+1)-subset) so the LIA route is not taken.
//! Prints the cumulative wall time and per-window mean at each checkpoint.
use std::io::{self, Write};
use std::time::Instant;

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

fn main() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let n: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(10);
    let k: i64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(4);
    let every: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(50);
    let mode = args.next().unwrap_or_else(|| "lia".to_string());

    let logic = if mode == "bool" {
        Logic::QfUf
    } else {
        Logic::QfLia
    };
    let mut solver = Solver::try_new(logic).map_err(|e| e.to_string())?;
    let vars: Vec<_> = (0..n)
        .map(|i| solver.declare_const(&format!("__npow_base_{i}"), Sort::Bool))
        .collect();
    if mode == "bool" {
        // at least k true  <=>  every (n-k+1)-subset contains a true variable
        let width = n + 1 - k as usize;
        for mask in 0u32..(1u32 << n) {
            if mask.count_ones() as usize != width {
                continue;
            }
            let lits: Vec<_> = (0..n)
                .filter(|i| mask & (1 << i) != 0)
                .map(|i| vars[i])
                .collect();
            let clause = solver.try_or_many(&lits).map_err(|e| e.to_string())?;
            solver.try_assert_term(clause).map_err(|e| e.to_string())?;
        }
    } else {
        let zero = solver.int_const(0);
        let one = solver.int_const(1);
        let mut sum = zero;
        for &v in &vars {
            let c = solver.try_ite(v, one, zero).map_err(|e| e.to_string())?;
            sum = solver.try_add(sum, c).map_err(|e| e.to_string())?;
        }
        let kt = solver.int_const(k);
        let ge = solver.try_ge(sum, kt).map_err(|e| e.to_string())?;
        solver.try_assert_term(ge).map_err(|e| e.to_string())?;
    }

    let stdout = io::stdout();
    let mut out = stdout.lock();
    let start = Instant::now();
    let mut window = Instant::now();
    let mut count = 0usize;
    loop {
        let r = solver.try_check_sat().map_err(|e| e.to_string())?;
        match r.into_inner() {
            SolveResult::Sat => {
                let model = solver
                    .try_get_model_for_consumer()
                    .map_err(|e| e.to_string())?
                    .into_inner();
                let mut block = None;
                for (i, &v) in vars.iter().enumerate() {
                    let val = model.bool_val(&format!("__npow_base_{i}")).unwrap_or(false);
                    let lit = if val {
                        solver.try_not(v).map_err(|e| e.to_string())?
                    } else {
                        v
                    };
                    block = Some(match block {
                        None => lit,
                        Some(b) => solver.try_or(b, lit).map_err(|e| e.to_string())?,
                    });
                }
                if let Some(b) = block {
                    solver.try_assert_term(b).map_err(|e| e.to_string())?;
                }
                count += 1;
                if count.is_multiple_of(every) {
                    let s = solver.statistics();
                    writeln!(
                        out,
                        "solutions={count:>6} total_ms={:>9.1} window_mean_ms={:>8.3} conflicts={} decisions={} propagations={}",
                        start.elapsed().as_secs_f64() * 1e3,
                        window.elapsed().as_secs_f64() * 1e3 / every as f64,
                        s.conflicts,
                        s.decisions,
                        s.propagations
                    )
                    .map_err(|e| e.to_string())?;
                    window = Instant::now();
                }
            }
            SolveResult::Unsat(_) => break,
            other => return Err(format!("unexpected result {other:?}")),
        }
    }
    writeln!(
        out,
        "DONE mode={mode} n={n} k={k} solutions={count} total_ms={:.1}",
        start.elapsed().as_secs_f64() * 1e3
    )
    .map_err(|e| e.to_string())?;
    Ok(())
}
