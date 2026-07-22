// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Acceptance demo for the incremental lazy-constraint session API
//! (#lra-lazy-session): a cutting-plane driver (geometry_consumer-solve's loop) creates a
//! session, asserts base constraints, checks, then lazily adds violated point
//! constraints and re-checks WITHOUT a full restart.
//!
//! The demo solves a fixed-band 10-point flatness query: does a plane
//! `z = a*x + b*y + c` fit all points within a band of width 9/100? The base
//! session holds 7 coplanar points (sat); three off-plane points are added
//! one at a time — each first shown VIOLATED by the current model via
//! `(get-value ...)`, exactly like a real lazy-constraint driver — with a
//! re-check after each. The final point makes the system unsat (the true
//! min-zone width of all 10 points is 1/10 > 9/100).
//!
//! Warm-restart verification (the cold-restart regression canary) runs on the
//! persistent push/pop LRA pipeline: the persistent SAT solver must survive
//! every re-check, base assertions must keep their original SAT encodings
//! (a cold restart would rebuild the map), and the clause count must never
//! shrink (learned clauses are retained across check-sats).

use crate::Executor;
use ay_frontend::parse;
use ay_frontend::sexp::{parse_sexp, SExpr};
use num_bigint::BigInt;
use num_rational::BigRational;

/// Band half-question width: 9/100, strictly between the 2-point stage
/// optimum (1/12) and the full 10-point min-zone width (1/10).
const BAND: (i64, i64) = (9, 100);

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

/// Evaluate an SMT-LIB value s-expression (as printed by `(get-value ...)`)
/// to an exact rational: numerals, decimals, `(- v)`, and `(/ p q)`.
fn eval_value_sexp(sexp: &SExpr) -> BigRational {
    match sexp {
        SExpr::Numeral(n) => BigRational::from(n.parse::<BigInt>().expect("numeral")),
        // `(/ -1 20)`: the sign makes `-1` lex as a symbol, not a numeral.
        SExpr::Symbol(s) if s.parse::<BigInt>().is_ok() => {
            BigRational::from(s.parse::<BigInt>().expect("signed numeral"))
        }
        SExpr::Decimal(d) => {
            let (int_part, frac_part) = d.split_once('.').expect("decimal");
            let scale = BigInt::from(10).pow(frac_part.len() as u32);
            let num = format!("{int_part}{frac_part}")
                .parse::<BigInt>()
                .expect("decimal digits");
            BigRational::new(num, scale)
        }
        SExpr::List(items) => match items[0].as_symbol() {
            Some("-") if items.len() == 2 => -eval_value_sexp(&items[1]),
            Some("/") if items.len() == 3 => {
                eval_value_sexp(&items[1]) / eval_value_sexp(&items[2])
            }
            other => panic!("unexpected value operator {other:?} in {sexp:?}"),
        },
        other => panic!("unexpected value s-expression {other:?}"),
    }
}

/// Parse a `(get-value ...)` response and return the value of each pair, in
/// query order.
fn parse_get_value(output: &str) -> Vec<BigRational> {
    let sexp = parse_sexp(output).expect("get-value output should parse");
    sexp.as_list()
        .expect("get-value output is a list")
        .iter()
        .map(|pair| {
            let pair = pair.as_list().expect("get-value pair");
            eval_value_sexp(&pair[1])
        })
        .collect()
}

/// The residual of point `(x, y, z)` against the candidate plane, as an
/// SMT-LIB term over `a b c`.
fn residual(x: i64, y: i64, z: &str) -> String {
    format!("(- {z} (+ (* {x} a) (* {y} b) c))")
}

/// The two band constraints for one point: `lo <= residual <= lo + 9/100`.
fn point_asserts(x: i64, y: i64, z: &str) -> String {
    let r = residual(x, y, z);
    format!(
        "(assert (>= {r} lo))\n(assert (<= {r} (+ lo (/ {} {}))))\n",
        BAND.0, BAND.1
    )
}

/// Base session: 7 coplanar points (z = 0) spanning the 5x2 grid.
fn base_script() -> String {
    let mut s = String::from(
        "(set-logic QF_LRA)\n\
         (declare-const a Real)\n\
         (declare-const b Real)\n\
         (declare-const c Real)\n\
         (declare-const lo Real)\n\
         (push 1)\n",
    );
    for (x, y) in [(0, 0), (0, 1), (4, 0), (4, 1), (1, 1), (2, 1), (3, 1)] {
        s.push_str(&point_asserts(x, y, "0"));
    }
    s.push_str("(check-sat)\n");
    s
}

/// The three lazily-added off-plane points, in driver order. Each is violated
/// by the model of the preceding check-sat (asserted below via `(get-value)`),
/// and only the third makes the session unsat.
fn lazy_points() -> [(i64, i64, &'static str); 3] {
    [
        (2, 0, "(- (/ 1 20))"),
        (3, 0, "(/ 1 20)"),
        (1, 0, "(/ 1 20)"),
    ]
}

#[test]
fn lazy_constraint_session_adds_violated_points_across_checksats() {
    let mut exec = Executor::new();
    // Pin the persistent push/pop LRA pipeline (the warm-restart lane) so the
    // white-box observables below are meaningful. The default #lra-ind eager
    // routing re-solves each check-sat standalone by design; a driver that
    // wants cross-check-sat state reuse gets it via this pipeline (also the
    // default whenever proofs are enabled).
    exec.lra_incremental_eager_override = Some(false);

    // --- Base session: 7 coplanar points, feasible. ---
    let mut outputs = Vec::new();
    for cmd in &parse(&base_script()).expect("base script parses") {
        if let Some(out) = exec.execute(cmd).expect("base command executes") {
            outputs.push(out);
        }
    }
    assert_eq!(outputs, vec!["sat"]);

    // Warm-restart canary, part 1: the persistent SAT solver exists and the
    // base assertions are encoded in it.
    let (base_clauses, base_encodings) = {
        let state = exec
            .incr_theory_state
            .as_ref()
            .expect("incremental theory state after first check-sat");
        let sat = state
            .persistent_sat
            .as_ref()
            .expect("persistent SAT solver must be materialized");
        let encodings: Vec<(ay_core::TermId, i32)> = {
            let mut e: Vec<_> = state
                .encoded_assertions
                .iter()
                .map(|(t, l)| (*t, *l))
                .collect();
            e.sort_unstable();
            e
        };
        assert!(
            !encodings.is_empty(),
            "base assertions must be encoded into the persistent solver"
        );
        (sat.num_clauses(), encodings)
    };

    // --- Lazy loop: 3 violated point constraints across 3 re-checks. ---
    let expected_verdicts = ["sat", "sat", "unsat"];
    let mut prev_clauses = base_clauses;
    for (round, (x, y, z)) in lazy_points().into_iter().enumerate() {
        // Driver step 1: the candidate constraint is VIOLATED by the current
        // model — the residual falls outside the band [lo, lo + 9/100].
        let query = format!("(get-value ({} lo))", residual(x, y, z));
        let cmds = parse(&query).expect("get-value parses");
        let out = exec.execute(&cmds[0]).expect("get-value executes").unwrap();
        let values = parse_get_value(&out);
        let (resid, lo) = (&values[0], &values[1]);
        let band = rat(BAND.0, BAND.1);
        assert!(
            resid < lo || resid > &(lo + &band),
            "round {round}: candidate point ({x},{y}) must be violated by the \
             current model: residual={resid}, band=[{lo}, {}]",
            lo + &band
        );

        // Driver step 2: add the violated constraints, re-check.
        let cmds =
            parse(&format!("{}(check-sat)\n", point_asserts(x, y, z))).expect("asserts parse");
        let mut verdict = None;
        for cmd in &cmds {
            if let Some(out) = exec.execute(cmd).expect("lazy round executes") {
                verdict = Some(out);
            }
        }
        assert_eq!(
            verdict.as_deref(),
            Some(expected_verdicts[round]),
            "round {round}"
        );

        // Warm-restart canary, part 2: still the SAME persistent solver —
        // base assertions keep their original encodings and the clause count
        // never shrinks. A cold restart (fresh solver per check-sat) would
        // reset both.
        let state = exec
            .incr_theory_state
            .as_ref()
            .expect("incremental theory state must survive re-checks");
        let sat = state
            .persistent_sat
            .as_ref()
            .expect("persistent SAT solver must survive re-checks");
        assert!(
            sat.num_clauses() >= prev_clauses,
            "round {round}: clause count must not shrink across warm re-checks \
             ({} < {prev_clauses})",
            sat.num_clauses()
        );
        prev_clauses = sat.num_clauses();
        for (term, lit) in &base_encodings {
            assert_eq!(
                state.encoded_assertions.get(term),
                Some(lit),
                "round {round}: base assertion encoding must be stable across \
                 warm re-checks (cold-restart regression)"
            );
        }
        assert!(
            state.encoded_assertions.len() > base_encodings.len(),
            "round {round}: lazily added constraints must be incrementally encoded"
        );
    }

    // The final unsat certifies the lower-bound side of the bracket: no plane
    // fits all 10 points within 9/100 — consistent with the certified
    // min-zone optimum 1/10 from the optimization demo
    // (`lra_opt_certificates.rs`).
}
