// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Measure the native branch-and-bound (P2) against the ay-dpll `smt` lane it
//! replaces, and emit the same MILP for HiGHS so a third party settles the
//! answer.
//!
//! ```text
//! cargo run --release -p ay-milp --features smt --example milp_speed -- 30 20
//! AY_MILP_SMT=1 cargo run --release -p ay-milp --features smt --example milp_speed -- 30 20
//! ```

use std::fmt::Write as _;
use std::time::Instant;

use ay_milp::{BabSession, Col, Model, Outcome, Row, Sense, SolveOpts};

struct Rng(u64);
impl Rng {
    fn next_u32(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (self.0 >> 33) as u32
    }
    fn coeff(&mut self) -> f64 {
        f64::from(self.next_u32() % 9) - 4.0
    }
}

/// A 0/1 knapsack-ish MILP: `n` binary columns, `m` covering rows. Always
/// feasible (all-zero satisfies every `<=` row) and bounded (the box is `{0,1}`).
fn build(n: usize, m: usize, seed: u64) -> (Model, Vec<Col>, Vec<Row>) {
    let mut rng = Rng(seed);
    let mut model = Model::new();
    let cols: Vec<_> = (0..n).map(|_| model.add_binary_col()).collect();
    let mut rows = Vec::new();
    for _ in 0..m {
        let terms: Vec<_> = cols
            .iter()
            .filter_map(|&c| {
                let a = rng.coeff();
                (a != 0.0).then_some((c, a))
            })
            .collect();
        if terms.is_empty() {
            continue;
        }
        let b = f64::from(rng.next_u32() % 12) + 3.0;
        rows.push(model.add_row(f64::NEG_INFINITY, b, &terms));
    }
    let obj: Vec<_> = cols
        .iter()
        .map(|&c| (c, f64::from(rng.next_u32() % 10) + 1.0))
        .collect();
    model.set_objective(&obj, Sense::Maximize);
    (model, cols, rows)
}

fn to_lp_format(model: &Model, cols: &[Col], rows: &[Row]) -> String {
    let mut s = String::from("Maximize\n obj:");
    for (j, &c) in cols.iter().enumerate() {
        let a = model.obj_coeff(c);
        if a != 0.0 {
            let _ = write!(s, " {a:+} x{j}");
        }
    }
    s.push_str("\nSubject To\n");
    for (i, &r) in rows.iter().enumerate() {
        let (coeffs, _, ub) = model.row(r);
        let _ = write!(s, " c{i}:");
        for &(c, a) in coeffs {
            let _ = write!(s, " {a:+} x{c}");
        }
        let _ = writeln!(s, " <= {ub}");
    }
    s.push_str("Binaries\n");
    for j in 0..cols.len() {
        let _ = write!(s, " x{j}");
    }
    s.push_str("\nEnd\n");
    s
}

/// Serialize this generator's deliberately integral model as deterministic
/// free-form MPS.  The closure harness feeds these exact bytes to both AY and
/// Gurobi; neither solver gets an in-memory construction or a different parser
/// lane.  This generator only creates integer coefficients and one-sided rows,
/// so refusing any future shape drift is safer than rounding it silently.
fn to_mps_format(model: &Model, cols: &[Col], rows: &[Row]) -> String {
    fn integer(value: f64) -> i64 {
        assert!(value.is_finite(), "dense-ladder MPS value must be finite");
        assert_eq!(
            value.fract(),
            0.0,
            "dense-ladder MPS value must be integral"
        );
        assert!(
            value >= i64::MIN as f64 && value <= i64::MAX as f64,
            "dense-ladder MPS value must fit i64"
        );
        value as i64
    }

    let mut s = String::from("NAME DENSE_LADDER\nOBJSENSE\n MAX\nROWS\n N obj\n");
    for i in 0..rows.len() {
        let _ = writeln!(s, " L c{i}");
    }
    s.push_str("COLUMNS\n");
    for (j, &col) in cols.iter().enumerate() {
        let objective = model.obj_coeff(col);
        if objective != 0.0 {
            let _ = writeln!(s, " x{j} obj {}", integer(objective));
        }
        for (i, &row) in rows.iter().enumerate() {
            let (terms, lower, upper) = model.row(row);
            assert!(
                lower == f64::NEG_INFINITY && upper.is_finite(),
                "dense-ladder MPS rows must be upper-bounded only"
            );
            if let Some((_, coefficient)) = terms
                .iter()
                .find(|(term_col, _)| *term_col as usize == col.index())
            {
                let _ = writeln!(s, " x{j} c{i} {}", integer(*coefficient));
            }
        }
    }
    s.push_str("RHS\n");
    for (i, &row) in rows.iter().enumerate() {
        let (_, _, upper) = model.row(row);
        let _ = writeln!(s, " rhs c{i} {}", integer(upper));
    }
    s.push_str("BOUNDS\n");
    for j in 0..cols.len() {
        let _ = writeln!(s, " BV bounds x{j}");
    }
    s.push_str("ENDATA\n");
    s
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(30);
    let m: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(20);
    let seed: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(2_026);

    let (model, cols, rows) = build(n, m, seed);
    let lane = if std::env::var_os("AY_MILP_SMT").is_some() {
        "ay-dpll smt lane"
    } else {
        "native branch-and-bound"
    };
    eprintln!("MILP: {n} binaries x {m} rows   lane: {lane}");

    let mut dumped = false;
    if let Ok(path) = std::env::var("LP_DUMP") {
        std::fs::write(&path, to_lp_format(&model, &cols, &rows)).expect("write LP");
        eprintln!("wrote {path}");
        dumped = true;
    }
    if let Ok(path) = std::env::var("MPS_DUMP") {
        std::fs::write(&path, to_mps_format(&model, &cols, &rows)).expect("write MPS");
        eprintln!("wrote {path}");
        dumped = true;
    }
    if std::env::var_os("DUMP_ONLY").is_some() {
        assert!(
            dumped,
            "DUMP_ONLY requires LP_DUMP=<path> or MPS_DUMP=<path>"
        );
        return;
    }

    // A time limit, so an unfinished solve reports its incumbent rather than grinding on
    // — which is what makes a like-for-like comparison against another solver's
    // time-limited run possible at all.
    let mut opts = SolveOpts::new();
    if let Ok(secs) = std::env::var("TIME_LIMIT") {
        if let Ok(secs) = secs.parse::<f64>() {
            opts = opts.with_time_limit(std::time::Duration::from_secs_f64(secs));
        }
    }
    // Match the typed production contract used by `ay-milp solve --threads`.
    // This example is the canonical dense-binary ladder generator, so silently
    // ignoring the requested worker count here would make its 8T comparison a
    // mislabeled 1T run.  Determinism remains the default at one thread; an
    // explicit multi-worker request opts out exactly as the real CLI does.
    if let Ok(raw) = std::env::var("AY_MILP_THREADS") {
        let threads = raw
            .parse::<u32>()
            .expect("AY_MILP_THREADS must be a positive integer");
        assert!(threads > 0, "AY_MILP_THREADS must be positive");
        if threads > 1 {
            opts = opts.with_threads(threads).with_determinism(false);
        }
    }
    eprintln!(
        "worker budget: {}   deterministic: {}",
        opts.threads, opts.determinism
    );
    let mut s = BabSession::new(model, &opts).expect("model");
    let t0 = Instant::now();
    let out = s.check().expect("solve");
    let dt = t0.elapsed();

    match out {
        Outcome::Optimal { value, .. } => {
            println!("optimum = {value}");
            println!("time    = {:.3}s", dt.as_secs_f64());
        }
        Outcome::Feasible {
            model_values,
            dual_bound,
            ..
        } => {
            // Not proven optimal — report the incumbent's VALUE so it can be compared
            // against another solver's primal bound on the same instance.
            let mut v = num_rational::BigRational::from_integer(0.into());
            for (j, &c) in cols.iter().enumerate() {
                let a = s.model().obj_coeff(c);
                if a != 0.0 {
                    let a = num_rational::BigRational::from_float(a).unwrap();
                    v += a * &model_values[j];
                }
            }
            println!("incumbent (NOT proven optimal) = {v}");
            if let Some(db) = dual_bound {
                println!("dual bound (rigorous) = {db}");
            }
            if std::env::var_os("AY_MILP_PRINT_POINT").is_some() {
                let s: String = model_values
                    .iter()
                    .map(|v| {
                        if v.is_integer() && *v == num_rational::BigRational::from_integer(1.into())
                        {
                            '1'
                        } else {
                            '0'
                        }
                    })
                    .collect();
                println!("point   = {s}");
            }
            println!("time    = {:.3}s", dt.as_secs_f64());
        }
        other => {
            println!("NO OPTIMUM: {other:?}");
            println!("time    = {:.3}s", dt.as_secs_f64());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{build, to_mps_format};

    #[test]
    fn deterministic_mps_round_trips_the_generated_model_exactly() {
        let (model, cols, rows) = build(12, 9, 7);
        let text = to_mps_format(&model, &cols, &rows);
        assert_eq!(text, to_mps_format(&model, &cols, &rows));

        let parsed = ay_milp::read_mps(&text).expect("generated MPS must parse");
        assert_eq!(parsed.name, "DENSE_LADDER");
        assert_eq!(parsed.model.sense(), model.sense());
        assert_eq!(parsed.model.num_cols(), model.num_cols());
        assert_eq!(parsed.model.num_rows(), model.num_rows());
        assert_eq!(parsed.col_names.len(), cols.len());
        assert_eq!(parsed.row_names.len(), rows.len());

        for (index, &source_col) in cols.iter().enumerate() {
            let parsed_col = parsed.model.col_at(index).expect("parsed column");
            assert_eq!(parsed.col_names[index], format!("x{index}"));
            assert_eq!(parsed.model.col_kind(parsed_col), ay_milp::ColKind::Binary);
            assert_eq!(
                parsed.model.col_bounds(parsed_col),
                model.col_bounds(source_col)
            );
            assert_eq!(
                parsed.model.obj_coeff(parsed_col),
                model.obj_coeff(source_col)
            );
        }
        for (index, &source_row) in rows.iter().enumerate() {
            let parsed_row = parsed.model.row_at(index).expect("parsed row");
            assert_eq!(parsed.row_names[index], format!("c{index}"));
            assert_eq!(parsed.model.row(parsed_row), model.row(source_row));
        }
    }
}
