// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CLI integration tests for proof-producing LRA optimization
//! (#lra-opt-cert) and the incremental lazy-constraint session protocol
//! (#lra-lazy-session).
//!
//! Drives the `ay` binary over stdin (`-in`), the exact surface a
//! cutting-plane driver like geometry_consumer-solve uses:
//!
//! * `(minimize <term>)` + `(check-sat)` + `(get-objectives)` +
//!   `(get-objective-certificates)` — the optimum arrives WITH a dual
//!   (Farkas) certificate whose entailed bound matches it (format spec:
//!   the development design notes).
//! * `(assert ...)` / `(check-sat)` sequences without restarting the process —
//!   base constraints, then lazily added violated constraints, re-checked in
//!   one session.

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

/// Run the `ay` binary in SMT-LIB stdin mode and return stdout.
fn run_ay_stdin(script: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let mut child = Command::new(ay_path)
        .arg("--z3-mode")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(script.as_bytes())
        .expect("write stdin");
    let output = child.wait_with_output().expect("wait ay");
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// The 10-point checkerboard flatness system from the acceptance demo
/// (`ay-dpll/src/executor_tests/lra_opt_certificates.rs`): min-zone band
/// width is exactly 1/10.
fn flatness_minimize_script() -> String {
    let mut s = String::from(
        "(set-logic QF_LRA)\n\
         (declare-const a Real)\n\
         (declare-const b Real)\n\
         (declare-const c Real)\n\
         (declare-const lo Real)\n\
         (declare-const w Real)\n",
    );
    for x in 0..5 {
        for y in 0..2 {
            let z = if (x + y) % 2 == 0 { "0" } else { "(/ 1 10)" };
            let resid = format!("(- {z} (+ (* {x} a) (* {y} b) c))");
            s.push_str(&format!("(assert (>= {resid} lo))\n"));
            s.push_str(&format!("(assert (<= {resid} (+ lo w)))\n"));
        }
    }
    s.push_str("(minimize w)\n(check-sat)\n(get-objectives)\n(get-objective-certificates)\n");
    s
}

#[test]
#[timeout(60_000)]
fn minimize_flatness_band_reports_optimum_with_dual_certificate() {
    let out = run_ay_stdin(&flatness_minimize_script());

    assert!(out.contains("sat"), "expected sat: {out}");
    assert!(
        out.contains("(w (/ 1.0 10.0))"),
        "optimum must be 1/10: {out}"
    );
    // The certificate's entailed bound must MATCH the reported optimum.
    assert!(out.contains("(objective-certificates"), "{out}");
    assert!(out.contains("(sense minimize)"), "{out}");
    assert!(out.contains("(bound (/ 1.0 10.0))"), "{out}");
    assert!(out.contains("(entails (>= w (/ 1.0 10.0)))"), "{out}");
    assert!(out.contains("(farkas"), "{out}");
    // Dual multipliers are printed as positive rationals; the checkerboard
    // optimum is blocked by four binding point constraints at coefficient 1/2.
    assert!(
        out.matches("(/ 1 2) (<=").count() >= 2,
        "expected the binding point constraints with multiplier 1/2: {out}"
    );
}

#[test]
#[timeout(60_000)]
fn maximize_direction_certificate_entails_upper_bound() {
    let out = run_ay_stdin(
        "(set-logic QF_LRA)\n\
         (declare-const x Real)\n\
         (assert (<= (* 2 x) 10))\n\
         (assert (>= x 0))\n\
         (maximize x)\n\
         (check-sat)\n\
         (get-objective-certificates)\n",
    );
    assert!(out.contains("(sense maximize)"), "{out}");
    assert!(out.contains("(entails (<= x 5.0))"), "{out}");
    assert!(
        out.contains("(/ 1 2)"),
        "scaled multiplier 1/2 expected: {out}"
    );
}

#[test]
#[timeout(60_000)]
fn certificate_unavailable_is_an_explicit_error() {
    // Equality-justified bounds fail closed: the optimum is still reported,
    // but no unverifiable certificate is ever printed.
    let out = run_ay_stdin(
        "(set-logic QF_LRA)\n\
         (declare-const x Real)\n\
         (assert (= x 5))\n\
         (minimize x)\n\
         (check-sat)\n\
         (get-objectives)\n\
         (get-objective-certificates)\n",
    );
    // Sort-aware objective output (#real-fmt): x is Real, so the optimum
    // prints as a Real literal. (z3 5.0.0 itself prints a bare `5` for an
    // integer-valued Real objective in `(get-objectives)` — AY deliberately
    // keeps the value a valid Real literal instead.)
    assert!(out.contains("(x 5.0)"), "{out}");
    assert!(
        out.contains("(error \"no objective certificates available\")"),
        "fail-closed error expected: {out}"
    );
}

/// The incremental lazy-constraint session, end to end over one `-in`
/// process: 7-point base is sat at band 9/100; three violated points are
/// added across three re-checks; only the third flips the verdict to unsat
/// (the full 10-point min-zone width is 1/10 > 9/100).
#[test]
#[timeout(60_000)]
fn incremental_session_lazy_points_flip_verdict_on_third_recheck() {
    let mut script = String::from(
        "(set-logic QF_LRA)\n\
         (declare-const a Real)\n\
         (declare-const b Real)\n\
         (declare-const c Real)\n\
         (declare-const lo Real)\n",
    );
    let point = |x: i64, y: i64, z: &str| {
        let r = format!("(- {z} (+ (* {x} a) (* {y} b) c))");
        format!("(assert (>= {r} lo))\n(assert (<= {r} (+ lo (/ 9 100))))\n")
    };
    for (x, y) in [(0, 0), (0, 1), (4, 0), (4, 1), (1, 1), (2, 1), (3, 1)] {
        script.push_str(&point(x, y, "0"));
    }
    script.push_str("(check-sat)\n");
    for (x, y, z) in [
        (2, 0, "(- (/ 1 20))"),
        (3, 0, "(/ 1 20)"),
        (1, 0, "(/ 1 20)"),
    ] {
        script.push_str(&point(x, y, z));
        script.push_str("(check-sat)\n");
    }

    let out = run_ay_stdin(&script);
    let verdicts: Vec<&str> = out
        .lines()
        .filter(|l| *l == "sat" || *l == "unsat")
        .collect();
    assert_eq!(
        verdicts,
        vec!["sat", "sat", "sat", "unsat"],
        "lazy session verdict sequence: {out}"
    );
}

/// push/pop scoping in the same stdin session: retracting the lazily added
/// points restores feasibility (no state leaks across pop).
#[test]
#[timeout(60_000)]
fn incremental_session_push_pop_retracts_lazy_points() {
    let out = run_ay_stdin(
        "(set-logic QF_LRA)\n\
         (declare-const x Real)\n\
         (assert (>= x 0))\n\
         (check-sat)\n\
         (push 1)\n\
         (assert (<= x (- 1)))\n\
         (check-sat)\n\
         (pop 1)\n\
         (check-sat)\n",
    );
    let verdicts: Vec<&str> = out
        .lines()
        .filter(|l| *l == "sat" || *l == "unsat")
        .collect();
    assert_eq!(verdicts, vec!["sat", "unsat", "sat"], "{out}");
}
