// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Acceptance demo for proof-producing LRA optimization (#lra-opt-cert):
//! minimize the band width of a 10-point min-zone flatness system and check
//! the dual (Farkas) optimality certificate end to end.
//!
//! The system is the QF_LRA encoding geometry_consumer's cutting-plane driver emits: points
//! `(x_i, y_i, z_i)`, a candidate plane `z = a*x + b*y + c`, a band
//! `[lo, lo + w]` that every residual `z_i - (a*x_i + b*y_i + c)` must fall
//! into, and the objective `(minimize w)`. The reported optimum is the ISO
//! 1101 min-zone flatness of the point set; the certificate proves the lower
//! bound `w >= optimum` from the asserted point constraints alone.

use crate::Executor;
use ay_frontend::parse;
use num_bigint::BigInt;
use num_rational::BigRational;

/// 10 points on a 5x2 unit grid with checkerboard heights 0 / (1/10).
/// The min-zone band width is exactly 1/10 (cross-checked against z3).
fn checkerboard_flatness_script() -> String {
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
fn flatness_min_zone_certificate_end_to_end() {
    let commands = parse(&checkerboard_flatness_script()).expect("script should parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script should execute");

    // Upper bound: a feasible plane achieves w = 1/10.
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert!(
        outputs[1].contains("(w (/ 1.0 10.0))"),
        "optimum must be 1/10, got: {}",
        outputs[1]
    );

    // The rendered certificate states the entailed lower bound `w >= 1/10`.
    let cert_out = &outputs[2];
    assert!(
        cert_out.starts_with("(objective-certificates"),
        "unexpected certificate output: {cert_out}"
    );
    assert!(cert_out.contains("(sense minimize)"), "{cert_out}");
    assert!(cert_out.contains("(bound (/ 1.0 10.0))"), "{cert_out}");
    assert!(
        cert_out.contains("(entails (>= w (/ 1.0 10.0)))"),
        "{cert_out}"
    );
    assert!(cert_out.contains("(farkas"), "{cert_out}");

    // Structured check: the stored certificate must pass the independent
    // verifier (multiplier combination == `w - 1/10` as a polynomial identity
    // over the asserted atoms), and its entailed bound must equal the
    // reported optimum, closing the two-sided bracket:
    //   model value (upper bound) == certificate bound (lower bound).
    let objectives = exec.ctx.objectives().to_vec();
    assert_eq!(objectives.len(), 1);
    let obj_term = objectives[0].term;
    let cert = exec
        .objective_certificates
        .get(&0)
        .expect("flatness minimize must produce a dual certificate")
        .clone();
    let expected = BigRational::new(BigInt::from(1), BigInt::from(10));
    assert_eq!(
        cert.bound, expected,
        "certificate bound must be the optimum"
    );
    assert!(!cert.strict);
    assert!(
        cert.verify(&exec.ctx.terms, obj_term),
        "independent certificate check must pass: {cert:?}"
    );
    // Every multiplier is over an asserted point constraint with a positive
    // coefficient (dual feasibility).
    assert!(!cert.atoms.is_empty());
    for entry in &cert.atoms {
        assert!(
            entry.coeff > BigRational::from(BigInt::from(0)),
            "dual multipliers must be positive: {entry:?}"
        );
        assert!(
            exec.ctx.assertions.contains(&entry.atom)
                || exec
                    .ctx
                    .assertions
                    .iter()
                    .any(|a| matches!(exec.ctx.terms.get(*a),
                        ay_core::term::TermData::Not(inner) if *inner == entry.atom)),
            "certificate atoms must be asserted constraints"
        );
    }
}

/// A tampered certificate (better-than-entailed bound) must be rejected by
/// the independent checker even at the executor level.
#[test]
fn flatness_certificate_rejects_tampered_bound() {
    let commands = parse(&checkerboard_flatness_script()).expect("script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script should execute");

    let obj_term = exec.ctx.objectives()[0].term;
    let mut cert = exec
        .objective_certificates
        .get(&0)
        .expect("certificate")
        .clone();
    assert!(cert.verify(&exec.ctx.terms, obj_term));
    cert.bound = BigRational::new(BigInt::from(11), BigInt::from(100));
    assert!(
        !cert.verify(&exec.ctx.terms, obj_term),
        "claiming w >= 11/100 must fail the independent check"
    );
}

/// A fresh optimizing check-sat replaces stale certificates: after the
/// problem is tightened, the certificate must match the NEW optimum.
#[test]
fn certificate_refreshes_across_incremental_recheck() {
    let script = "(set-logic QF_LRA)\n\
                  (declare-const x Real)\n\
                  (assert (>= x 2))\n\
                  (minimize x)\n\
                  (check-sat)\n\
                  (get-objective-certificates)\n\
                  (assert (>= x 7))\n\
                  (check-sat)\n\
                  (get-objective-certificates)\n";
    let commands = parse(script).expect("script should parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script should execute");

    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("(entails (>= x 2.0))"),
        "{}",
        outputs[1]
    );
    assert_eq!(outputs[2], "sat");
    assert!(
        outputs[3].contains("(entails (>= x 7.0))"),
        "{}",
        outputs[3]
    );
}

/// Certificates are per objective declaration, not per term. In box mode the
/// same Real term can have an independently certified maximum and minimum; a
/// term-keyed map overwrites the first certificate and renders the second twice.
#[test]
fn duplicate_term_box_objectives_keep_distinct_certificates() {
    let script = "(set-logic QF_LRA)\n\
                  (set-option :opt.priority box)\n\
                  (declare-const x Real)\n\
                  (assert (>= x 0))\n\
                  (assert (<= x 10))\n\
                  (maximize x)\n\
                  (minimize x)\n\
                  (check-sat)\n\
                  (get-objectives)\n\
                  (get-objective-certificates)\n";
    let commands = parse(script).expect("script should parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script should execute");

    assert_eq!(outputs[0], "sat");
    assert_eq!(outputs[1], "(objectives\n (x 10.0)\n (x 0.0)\n)\n");
    let rendered = &outputs[2];
    assert_eq!(
        rendered.matches("(sense maximize)").count(),
        1,
        "{rendered}"
    );
    assert_eq!(
        rendered.matches("(sense minimize)").count(),
        1,
        "{rendered}"
    );
    assert!(rendered.contains("(entails (<= x 10.0))"), "{rendered}");
    assert!(rendered.contains("(entails (>= x 0.0))"), "{rendered}");

    let objectives = exec.ctx.objectives();
    assert_eq!(objectives.len(), 2);
    let maximize = exec
        .objective_certificates
        .get(&0)
        .expect("maximize certificate");
    let minimize = exec
        .objective_certificates
        .get(&1)
        .expect("minimize certificate");
    assert_eq!(maximize.sense, ay_lra::OptimizationSense::Maximize);
    assert_eq!(minimize.sense, ay_lra::OptimizationSense::Minimize);
    assert!(maximize.verify(&exec.ctx.terms, objectives[0].term));
    assert!(minimize.verify(&exec.ctx.terms, objectives[1].term));
}

/// geometry_consumer MD-7 shape: 0/1 indicators with implication constraints, minimize a sum.
/// `(minimize <Int term>)` previously optimized correctly but the certificate
/// path errored `"no objective certificates available"`. The LP relaxation of
/// this covering polytope is integral (implication + covering constraints are
/// totally unimodular), so the integer optimum equals the LP dual bound and the
/// dual (Farkas) certificate proves the integer optimum exactly — it must now be
/// emitted, and pass the SAME independent verifier as the Real path.
#[test]
fn md7_int_indicator_minimize_certificate_end_to_end() {
    let script = "(set-logic QF_LIA)\n\
                  (declare-const a Int)\n\
                  (declare-const b Int)\n\
                  (declare-const c Int)\n\
                  (assert (<= 0 a)) (assert (<= a 1))\n\
                  (assert (<= 0 b)) (assert (<= b 1))\n\
                  (assert (<= 0 c)) (assert (<= c 1))\n\
                  (assert (>= b a))\n\
                  (assert (>= c a))\n\
                  (assert (>= (+ b c) 1))\n\
                  (minimize (+ a b c))\n\
                  (check-sat)\n\
                  (get-objectives)\n\
                  (get-objective-certificates)\n";
    let commands = parse(script).expect("script should parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script should execute");

    // Upper bound: the integer model achieves sum = 1 (a=0, b=1, c=0).
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert!(
        outputs[1].contains("((+ a b c) 1)"),
        "integer optimum must be 1, got: {}",
        outputs[1]
    );

    // The rendered certificate states the entailed lower bound `sum >= 1`.
    let cert_out = &outputs[2];
    assert!(
        cert_out.starts_with("(objective-certificates"),
        "MD-7 minimize must produce a certificate, got: {cert_out}"
    );
    assert!(cert_out.contains("(sense minimize)"), "{cert_out}");
    assert!(cert_out.contains("(bound 1)"), "{cert_out}");
    assert!(
        cert_out.contains("(entails (>= (+ a b c) 1))"),
        "{cert_out}"
    );
    assert!(cert_out.contains("(farkas"), "{cert_out}");

    // Structured check: the stored certificate passes the independent verifier
    // (multiplier combination == `sum - 1` as a polynomial identity over the
    // asserted atoms) and its bound equals the integer optimum, closing the
    // two-sided bracket: integer model value (upper) == certificate bound
    // (lower). This is the LP dual, valid because the relaxation is tight.
    let objectives = exec.ctx.objectives().to_vec();
    assert_eq!(objectives.len(), 1);
    let obj_term = objectives[0].term;
    let cert = exec
        .objective_certificates
        .get(&0)
        .expect("MD-7 integer minimize must produce a dual certificate")
        .clone();
    assert_eq!(
        cert.bound,
        BigRational::from(BigInt::from(1)),
        "certificate bound must be the integer optimum"
    );
    assert!(!cert.strict);
    assert!(
        cert.verify(&exec.ctx.terms, obj_term),
        "independent certificate check must pass: {cert:?}"
    );
    assert!(!cert.atoms.is_empty());
    for entry in &cert.atoms {
        assert!(
            entry.coeff > BigRational::from(BigInt::from(0)),
            "dual multipliers must be positive: {entry:?}"
        );
    }
}

/// Integrality gap: the LP relaxation minimum (`x >= 1/2`) is STRICTLY below the
/// integer optimum (`x = 1`). The LP dual proves only `x >= 1/2`, which does not
/// entail the integer bound `x >= 1`, so no certificate may be fabricated — the
/// honest `"no objective certificates available"` error must stand.
#[test]
fn int_integrality_gap_keeps_honest_error() {
    let script = "(set-logic QF_LIA)\n\
                  (declare-const x Int)\n\
                  (assert (>= x 0))\n\
                  (assert (>= (* 2 x) 1))\n\
                  (minimize x)\n\
                  (check-sat)\n\
                  (get-objectives)\n\
                  (get-objective-certificates)\n";
    let commands = parse(script).expect("script should parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script should execute");

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert!(
        outputs[1].contains("(x 1)"),
        "integer optimum must be 1, got: {}",
        outputs[1]
    );
    assert_eq!(
        outputs[2], "(error \"no objective certificates available\")",
        "an integrality gap must not fabricate a certificate: {}",
        outputs[2]
    );
    assert!(
        exec.objective_certificates.get(&0).is_none(),
        "no certificate may be stored across an integrality gap"
    );
}
