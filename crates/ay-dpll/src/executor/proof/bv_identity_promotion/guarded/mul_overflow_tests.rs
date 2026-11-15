// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::ProofStep;

/// external-codegen's checked `2m`-bit multiplication overflow row over `m`-bit limbs,
/// spelled as its corpus spells it; `swap` compares the quotient against the
/// multiplier with its limbs swapped.
fn row(m: u32, swap: bool) -> String {
    let top = 2 * m - 1;
    let z = |k: &str| format!("((_ zero_extend {m}) {k})");
    let p = |x: &str, y: &str| format!("(bvmul {} {})", z(x), z(y));
    let t = z(&format!("((_ extract {top} {m}) {})", p("a_lo", "b_lo")));
    let mid = format!(
        "(bvadd (bvadd {t} {}) {})",
        p("a_hi", "b_lo"),
        p("a_lo", "b_hi")
    );
    let mid0 = format!("(bvadd {t} {})", p("a_lo", "b_hi"));
    let zero = format!("(concat (_ bv0 {m}) (_ bv0 {m}))");
    let carry = format!(
        "(bvshl ((_ zero_extend {top}) (ite (bvult {mid} {mid0}) (_ bv1 1) (_ bv0 1))) {})",
        z(&format!("(_ bv{m} {m})"))
    );
    let high = format!(
        "(bvadd (bvadd {} {}) {carry})",
        z(&format!("((_ extract {top} {m}) {mid})")),
        p("a_hi", "b_hi")
    );
    let (a, b) = ("(concat a_hi a_lo)", "(concat b_hi b_lo)");
    let quotient_b = if swap { "(concat b_lo b_hi)" } else { b };
    let divisor = format!("(ite (= {a} {zero}) (concat (_ bv0 {m}) (_ bv1 {m})) {a})");
    format!(
        "(set-logic QF_BV)\n\
         (declare-const a_lo (_ BitVec {m}))\n(declare-const a_hi (_ BitVec {m}))\n\
         (declare-const b_lo (_ BitVec {m}))\n(declare-const b_hi (_ BitVec {m}))\n\
         (assert (not (= (ite (not (= {high} {zero})) (_ bv1 1) (_ bv0 1)) \
         (ite (and (not (= {a} {zero})) (not (= (bvudiv (bvmul {a} {b}) {divisor}) {quotient_b}))) \
         (_ bv1 1) (_ bv0 1)))))\n"
    )
}

fn solve(source: &str) -> (Executor, Vec<String>) {
    let mut executor = Executor::new();
    let script = format!("(set-option :produce-proofs true){source}(check-sat)(get-proof)");
    let outputs = executor
        .execute_all(&ay_frontend::parse(&script).unwrap())
        .unwrap();
    (executor, outputs)
}

#[test]
fn the_checked_multiplication_overflow_row_is_refuted_by_its_certificate() {
    let (executor, outputs) = solve(&row(4, false));
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    let proof = executor.last_proof().expect("proof");
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvMulOverflowDivision,
            ..
        }
    )));
    executor.check_proof_strict_with_datatypes(proof).unwrap();
    let text = outputs.last().unwrap();
    assert!(text.contains(":rule bitblast_udiv"), "{text}");
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
}

/// Negative control: against the swapped multiplier the identity is false,
/// the route declines, and the query is satisfiable.
#[test]
fn a_swapped_multiplier_is_not_the_identity() {
    let (_, outputs) = solve(&row(4, true));
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
}

/// external-codegen's checked signed `2m`-bit multiplication overflow row over
/// `m`-bit limbs, with `bvsdiv` expanded by its SMT-LIB definition, spelled
/// as its corpus spells it; `wide_limit` compares the magnitudes' product
/// against `MAX` whatever the signs.
fn signed_row(m: u32, wide_limit: bool) -> String {
    let top = 2 * m - 1;
    let (a, b) = ("(concat a_hi a_lo)", "(concat b_hi b_lo)");
    let zero = format!("(concat (_ bv0 {m}) (_ bv0 {m}))");
    let sign = |w: &str| format!("(= ((_ extract {top} {top}) {w}) (_ bv1 1))");
    let (sa, sb) = (sign(a), sign(b));
    let xa = format!("(ite {sa} (bvneg {a}) {a})");
    let xb = format!("(ite {sb} (bvneg {b}) {b})");
    let z = |k: &str| format!("((_ zero_extend {m}) {k})");
    let limb = |w: &str, hi: bool| {
        if hi {
            format!("((_ extract {top} {m}) {w})")
        } else {
            format!("((_ extract {} 0) {w})", m - 1)
        }
    };
    let (x_lo, x_hi, y_lo, y_hi) = (
        z(&limb(&xa, false)),
        z(&limb(&xa, true)),
        z(&limb(&xb, false)),
        z(&limb(&xb, true)),
    );
    let pll = format!("(bvmul {x_lo} {y_lo})");
    let xt = z(&format!("((_ extract {top} {m}) {pll})"));
    let (s1, s2) = (
        format!("(bvmul {x_hi} {y_lo})"),
        format!("(bvmul {y_hi} {x_lo})"),
    );
    let mid = format!("(bvadd (bvadd {xt} {s1}) {s2})");
    let mid0 = format!("(bvadd {xt} {s2})");
    let carry = format!(
        "(bvshl ((_ zero_extend {top}) (ite (bvult {mid} {mid0}) (_ bv1 1) (_ bv0 1))) {})",
        z(&format!("(_ bv{m} {m})"))
    );
    let high = format!(
        "(bvadd (bvadd {} (bvmul {x_hi} {y_hi})) {carry})",
        z(&format!("((_ extract {top} {m}) {mid})"))
    );
    let half = 1_u128 << (m - 1);
    let full = (1_u128 << m) - 1;
    let minw = format!("(concat (_ bv{half} {m}) (_ bv0 {m}))");
    let maxw = format!("(concat (_ bv{} {m}) (_ bv{full} {m}))", half - 1);
    let neg1 = format!("(concat (_ bv{full} {m}) (_ bv{full} {m}))");
    let one = format!("(concat (_ bv0 {m}) (_ bv1 {m}))");
    let lim = if wide_limit {
        maxw.clone()
    } else {
        format!("(ite (not (= {sa} {sb})) {minw} {maxw})")
    };
    let l = format!(
        "(ite (or (not (= {high} {zero})) (bvult {lim} (bvmul {xa} {xb}))) (_ bv1 1) (_ bv0 1))"
    );
    let spec = format!("(and (= {a} {minw}) (= {b} {neg1}))");
    let d = format!("(ite (or (= {b} {zero}) {spec}) {one} {b})");
    let p = format!("(bvmul {a} {b})");
    let bit = |w: &str, v: u32| format!("(= ((_ extract {top} {top}) {w}) (_ bv{v} 1))");
    let sd = format!(
        "(ite (and {} {}) (bvudiv {p} {d}) (ite (and {} {}) (bvneg (bvudiv (bvneg {p}) {d})) \
         (ite (and {} {}) (bvneg (bvudiv {p} (bvneg {d}))) (bvudiv (bvneg {p}) (bvneg {d})))))",
        bit(&p, 0),
        bit(&d, 0),
        bit(&p, 1),
        bit(&d, 0),
        bit(&p, 0),
        bit(&d, 1)
    );
    let r = format!(
        "(ite (or (and (not (= {b} {zero})) (not (= {sd} {a}))) {spec}) (_ bv1 1) (_ bv0 1))"
    );
    format!(
        "(set-logic QF_BV)\n\
         (declare-const a_lo (_ BitVec {m}))\n(declare-const a_hi (_ BitVec {m}))\n\
         (declare-const b_lo (_ BitVec {m}))\n(declare-const b_hi (_ BitVec {m}))\n\
         (assert (not (= {l} {r})))\n"
    )
}

#[test]
fn the_checked_signed_multiplication_overflow_row_is_refuted_by_its_certificate() {
    let (executor, outputs) = solve(&signed_row(4, false));
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    let proof = executor.last_proof().expect("proof");
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvMulOverflowDivision,
            ..
        }
    )));
    executor.check_proof_strict_with_datatypes(proof).unwrap();
    let text = outputs.last().unwrap();
    assert!(text.contains(":rule bitblast_udiv"), "{text}");
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
}

/// Negative control: a limit that ignores the signs misses `MIN`'s product
/// with a positive operand, the route declines, and the query is satisfiable.
#[test]
fn a_sign_blind_limit_is_not_the_signed_identity() {
    let (_, outputs) = solve(&signed_row(4, true));
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
}
