// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the R1 wrong-optimum chain found by the downstream optimization consumer's P0 MIP
//! backend (the development design notes, "Track R"):
//!
//! 1. `check-sat-assuming` on QF_LRA answered `unknown` for a trivially-SAT
//!    query whenever the assumption was TIGHT through an equality row
//!    (several variables forced to one value): LRA's final check emitted
//!    `NeedModelEqualities` (assume_eqs / fixed-term, #6617/#8901), which the
//!    bare assumption loop mapped to Unknown. Fixed by the QfNia-style
//!    scoped-assumption retry in `check_sat_assuming.rs`.
//! 2. That Unknown silently disabled the OMT simplex confirm-solve, so
//!    `(maximize c)` over an equality-defined variable fell into the
//!    iterative epsilon-crawl and — after exhausting its round budget —
//!    reported the crawl position (-1/2^128) as the optimum of a problem
//!    whose true maximum is 1. The round-budget exit now fails closed
//!    (`unknown`), and with (1) fixed the simplex optimum is confirmed.
//!
//! Methodology: every positive case has a refuted negative twin — a green
//! without its refuted twin is vacuous.

use crate::Executor;
use ay_frontend::parse;

/// The minimal repro shape: x, y in [0,1], x + y - z = 1. The maximum of z
/// is 1 (at x = y = 1, a degenerate vertex where three values coincide).
const BASE: &str = "(set-logic QF_LRA)\n\
     (declare-const x Real)\n\
     (declare-const y Real)\n\
     (declare-const z Real)\n\
     (assert (>= x 0.0))(assert (<= x 1.0))\n\
     (assert (>= y 0.0))(assert (<= y 1.0))\n\
     (assert (= (+ (* 1.0 x) (* 1.0 y) (* -1.0 z)) 1.0))\n";

fn run(script: &str) -> Vec<String> {
    let commands = parse(script).expect("script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script should execute")
}

/// Tight assumption through the equality row: satisfiable at the single
/// point x = y = z = 1. Previously answered `unknown` (NeedModelEqualities
/// degrade in the bare assumption loop).
#[test]
fn check_sat_assuming_tight_equality_through_row_is_sat() {
    let script = format!("{BASE}(check-sat-assuming ((>= z 1.0)))\n(get-value (x y z))\n");
    let outputs = run(&script);
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "tight-through-equality assumption must be sat, got: {outputs:?}"
    );
    assert_eq!(
        outputs.get(1).map(String::as_str),
        Some("((x 1.0) (y 1.0) (z 1.0))"),
        "the single feasible point is x = y = z = 1"
    );
}

/// Refuted twin: past the vertex the assumption is infeasible — the retry
/// lane must still prove UNSAT, never fail open to sat/unknown.
#[test]
fn check_sat_assuming_past_vertex_is_unsat() {
    let script = format!("{BASE}(check-sat-assuming ((>= z 1.5)))\n");
    let outputs = run(&script);
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "z >= 3/2 exceeds max(z) = 1, got: {outputs:?}"
    );
}

/// The ny P0 wrong-optimum repro: maximize an equality-defined variable.
/// Previously reported -1/2^128 (epsilon-crawl exit) instead of 1.
#[test]
fn maximize_equality_defined_var_reports_exact_optimum() {
    let script = format!("{BASE}(maximize z)\n(check-sat)\n(get-value (z))\n");
    let outputs = run(&script);
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert_eq!(
        outputs.get(1).map(String::as_str),
        Some("((z 1.0))"),
        "max of z = x + y - 1 with x, y in [0,1] is exactly 1"
    );
}

/// Twin in the healthy direction (was already exact): minimize.
#[test]
fn minimize_equality_defined_var_reports_exact_optimum() {
    let script = format!("{BASE}(minimize z)\n(check-sat)\n(get-value (z))\n");
    let outputs = run(&script);
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert_eq!(
        outputs.get(1).map(String::as_str),
        Some("((z (- 1.0)))"),
        "min of z = x + y - 1 with x, y in [0,1] is exactly -1"
    );
}

/// The full 5-variable ny P0 shape, with passthrough equality rows
/// (c2 = c0, c3 = c1) that make the optimum vertex DEGENERATE: with the
/// ratio test in place, arbitrary entering/leaving order cycled zero-length
/// pivots to the iteration cap (then failed closed to unknown). Bland's
/// rule terminates it at the exact optimum.
#[test]
fn maximize_degenerate_passthrough_rows_terminates_at_optimum() {
    let script = "(set-logic QF_LRA)\n\
         (declare-const c0 Real)(assert (>= c0 0.0))(assert (<= c0 1.0))\n\
         (declare-const c1 Real)(assert (>= c1 0.0))(assert (<= c1 1.0))\n\
         (declare-const c2 Real)(declare-const c3 Real)(declare-const c4 Real)\n\
         (assert (= (+ (* 1.0 c0) (* -1.0 c2)) 0.0))\n\
         (assert (= (+ (* 1.0 c1) (* -1.0 c3)) 0.0))\n\
         (assert (= (+ (* 1.0 c0) (* 1.0 c1) (* -1.0 c4)) 1.0))\n\
         (maximize c4)\n(check-sat)\n(get-value (c4))\n";
    let outputs = run(script);
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert_eq!(
        outputs.get(1).map(String::as_str),
        Some("((c4 1.0))"),
        "degenerate 5-var maximize must terminate at the exact optimum 1"
    );
}

/// Negative control against bound-echoing: with an explicit cap BELOW the
/// structural maximum, the reported optimum must be the cap, not the
/// structural bound — a maximizer that merely reports a derived upper bound
/// (rather than optimizing) fails here.
#[test]
fn maximize_with_interior_cap_reports_cap() {
    let script = format!("{BASE}(assert (<= z 0.5))\n(maximize z)\n(check-sat)\n(get-value (z))\n");
    let outputs = run(&script);
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert_eq!(
        outputs.get(1).map(String::as_str),
        Some("((z (/ 1.0 2.0)))"),
        "capped maximum must be exactly 1/2"
    );
}
