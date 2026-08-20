// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use super::eval::{eval, EvalResult};
use super::selfcheck::equivalence_self_check;
use super::*;
use ay_core::{Sort, TermStore};
use num_bigint::BigInt;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn int_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Int)
}

fn ci(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

/// Independently decide `∃x.φ[σ]` over `x ∈ [-bound, bound]` by direct
/// evaluation, used by tests to cross-check the eliminated formula `O`.
fn exists_brute(
    terms: &TermStore,
    literals: &[TermId],
    var: TermId,
    assign: &HashMap<TermId, BigInt>,
    bound: i64,
) -> bool {
    let mut a = assign.clone();
    for x in -bound..=bound {
        a.insert(var, BigInt::from(x));
        let mut ok = true;
        for &lit in literals {
            match eval(terms, lit, &a) {
                EvalResult::Bool(true) => {}
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if ok {
            return true;
        }
    }
    false
}

fn eval_bool(terms: &TermStore, t: TermId, assign: &HashMap<TermId, BigInt>) -> bool {
    match eval(terms, t, assign) {
        EvalResult::Bool(b) => b,
        other => panic!("expected bool, got {other:?}"),
    }
}

/// Exhaustively compare O against the brute-force `∃x.φ` over a grid of the
/// given free variables. Panics on any mismatch.
fn compare_grid(
    terms: &TermStore,
    literals: &[TermId],
    var: TermId,
    result: TermId,
    free: &[TermId],
    grid: i64,
    brute_bound: i64,
) {
    // Enumerate all assignments in [-grid, grid]^|free|.
    let n = free.len();
    let span = (2 * grid + 1) as usize;
    let total = span.pow(n as u32);
    for idx in 0..total {
        let mut assign = HashMap::new();
        let mut rem = idx;
        for &fv in free {
            let digit = (rem % span) as i64 - grid;
            rem /= span;
            assign.insert(fv, BigInt::from(digit));
        }
        let o = eval_bool(terms, result, &assign);
        let ex = exists_brute(terms, literals, var, &assign, brute_bound);
        assert_eq!(o, ex, "mismatch at assign={assign:?}: O={o} exists={ex}");
    }
}

// ---------------------------------------------------------------------------
// In-fragment correctness
// ---------------------------------------------------------------------------

#[test]
fn elim_single_lower_bound() {
    // ∃x. x > y   ≡   true (always satisfiable).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let body = terms.mk_gt(x, y);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => {
            compare_grid(&terms, &[body], x, o, &[y], 4, 40);
        }
        QeResult::NotSupported => panic!("should eliminate ∃x. x > y"),
    }
}

#[test]
fn elim_range_unsat_when_empty() {
    // ∃x. (x > y) ∧ (x < y)  ≡  false (no integer strictly between y and y).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let l1 = terms.mk_gt(x, y);
    let l2 = terms.mk_lt(x, y);
    let body = terms.mk_and(vec![l1, l2]);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => {
            compare_grid(&terms, &[l1, l2], x, o, &[y], 4, 40);
        }
        QeResult::NotSupported => panic!("should eliminate range conjunction"),
    }
}

#[test]
fn elim_range_with_gap() {
    // ∃x. (x > y) ∧ (x < y + 3)  ≡  true (x = y+1 works).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let three = ci(&mut terms, 3);
    let yp3 = terms.mk_add(vec![y, three]);
    let l1 = terms.mk_gt(x, y);
    let l2 = terms.mk_lt(x, yp3);
    let body = terms.mk_and(vec![l1, l2]);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[l1, l2], x, o, &[y], 4, 40),
        QeResult::NotSupported => panic!("should eliminate"),
    }
}

#[test]
fn elim_with_coefficient() {
    // ∃x. 2*x = y   ≡   2 | y  (y even).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let two = ci(&mut terms, 2);
    let two_x = terms.mk_mul(vec![two, x]);
    let body = terms.mk_eq(two_x, y);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[body], x, o, &[y], 6, 40),
        QeResult::NotSupported => panic!("should eliminate 2x = y"),
    }
}

#[test]
fn elim_coefficient_inequalities() {
    // ∃x. (3*x >= y) ∧ (3*x <= y + 2)
    // Satisfiable iff some multiple of 3 lies in [y, y+2].
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let three = ci(&mut terms, 3);
    let two = ci(&mut terms, 2);
    let three_x = terms.mk_mul(vec![three, x]);
    let yp2 = terms.mk_add(vec![y, two]);
    let l1 = terms.mk_ge(three_x, y);
    let l2 = terms.mk_le(three_x, yp2);
    let body = terms.mk_and(vec![l1, l2]);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[l1, l2], x, o, &[y], 6, 60),
        QeResult::NotSupported => panic!("should eliminate"),
    }
}

#[test]
fn elim_divisibility_literal() {
    // ∃x. (x = y) ∧ (4 | x)  ≡  4 | y.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let four = ci(&mut terms, 4);
    let zero = ci(&mut terms, 0);
    let xmod4 = terms.mk_mod(x, four);
    let div = terms.mk_eq(xmod4, zero);
    let eqxy = terms.mk_eq(x, y);
    let body = terms.mk_and(vec![eqxy, div]);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[eqxy, div], x, o, &[y], 8, 40),
        QeResult::NotSupported => panic!("should eliminate divisibility"),
    }
}

#[test]
fn elim_disequality() {
    // ∃x. (x >= y) ∧ (x != y)  ≡  true (x = y+1).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let ge = terms.mk_ge(x, y);
    let eq = terms.mk_eq(x, y);
    let ne = terms.mk_not(eq);
    let body = terms.mk_and(vec![ge, ne]);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[ge, ne], x, o, &[y], 4, 40),
        QeResult::NotSupported => panic!("should eliminate disequality"),
    }
}

#[test]
fn elim_two_free_vars() {
    // ∃x. (x > y) ∧ (x > z) ∧ (x < y + z + 5)
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let z = int_var(&mut terms, "z");
    let five = ci(&mut terms, 5);
    let yz5 = terms.mk_add(vec![y, z, five]);
    let l1 = terms.mk_gt(x, y);
    let l2 = terms.mk_gt(x, z);
    let l3 = terms.mk_lt(x, yz5);
    let body = terms.mk_and(vec![l1, l2, l3]);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[l1, l2, l3], x, o, &[y, z], 3, 60),
        QeResult::NotSupported => panic!("should eliminate"),
    }
}

#[test]
fn elim_no_x_in_body() {
    // ∃x. (y > 0)  ≡  (y > 0)  (x does not occur).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let zero = ci(&mut terms, 0);
    let body = terms.mk_gt(y, zero);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[body], x, o, &[y], 4, 40),
        QeResult::NotSupported => panic!("should eliminate even when x absent"),
    }
}

#[test]
fn elim_negated_coeff_combo() {
    // ∃x. (2*x <= y) ∧ (3*x >= z)   (coefficients differing in sign/magnitude)
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let z = int_var(&mut terms, "z");
    let two = ci(&mut terms, 2);
    let three = ci(&mut terms, 3);
    let two_x = terms.mk_mul(vec![two, x]);
    let three_x = terms.mk_mul(vec![three, x]);
    let l1 = terms.mk_le(two_x, y);
    let l2 = terms.mk_ge(three_x, z);
    let body = terms.mk_and(vec![l1, l2]);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[l1, l2], x, o, &[y, z], 3, 80),
        QeResult::NotSupported => panic!("should eliminate"),
    }
}

#[test]
fn elim_exact_equality_with_offset() {
    // ∃x. x + 1 = 2*y  ≡  true (x = 2y - 1 always exists).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let one = ci(&mut terms, 1);
    let two = ci(&mut terms, 2);
    let xp1 = terms.mk_add(vec![x, one]);
    let twoy = terms.mk_mul(vec![two, y]);
    let body = terms.mk_eq(xp1, twoy);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[body], x, o, &[y], 5, 40),
        QeResult::NotSupported => panic!("should eliminate"),
    }
}

// ---------------------------------------------------------------------------
// Out-of-fragment REFUSALS
// ---------------------------------------------------------------------------

#[test]
fn refuse_nonlinear_xx() {
    // ∃x. x*x = y  — non-linear ⇒ refuse.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let xx = terms.mk_mul(vec![x, x]);
    let body = terms.mk_eq(xx, y);
    assert_eq!(
        eliminate_exists(&mut terms, body, x),
        QeResult::NotSupported
    );
}

#[test]
fn refuse_nonlinear_xy() {
    // ∃x. x*y = z  — product of two variables ⇒ refuse.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let z = int_var(&mut terms, "z");
    let xy = terms.mk_mul(vec![x, y]);
    let body = terms.mk_eq(xy, z);
    assert_eq!(
        eliminate_exists(&mut terms, body, x),
        QeResult::NotSupported
    );
}

#[test]
fn refuse_disjunction() {
    // ∃x. (x > y) ∨ (x < z)  — disjunction not in fragment ⇒ refuse.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let z = int_var(&mut terms, "z");
    let l1 = terms.mk_gt(x, y);
    let l2 = terms.mk_lt(x, z);
    let body = terms.mk_or(vec![l1, l2]);
    assert_eq!(
        eliminate_exists(&mut terms, body, x),
        QeResult::NotSupported
    );
}

#[test]
fn refuse_real_var() {
    // ∃x:Real. x > y  — real sort ⇒ refuse.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let body = terms.mk_gt(x, y);
    assert_eq!(
        eliminate_exists(&mut terms, body, x),
        QeResult::NotSupported
    );
}

#[test]
fn refuse_nested_quantifier() {
    // ∃x. ∀y. (x > y)  — nested quantifier ⇒ refuse.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let inner = terms.mk_gt(x, y);
    let forall = terms.mk_forall(vec![("y".to_string(), Sort::Int)], inner);
    assert_eq!(
        eliminate_exists(&mut terms, forall, x),
        QeResult::NotSupported
    );
}

#[test]
fn refuse_mod_of_x_nonconst_divisor() {
    // ∃x. (mod x y) = 0  — divisor is a variable, not a positive literal ⇒
    // refuse (out of the `d | t` fragment).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let zero = ci(&mut terms, 0);
    let m = terms.mk_mod(x, y);
    let body = terms.mk_eq(m, zero);
    assert_eq!(
        eliminate_exists(&mut terms, body, x),
        QeResult::NotSupported
    );
}

#[test]
fn elim_negated_divisibility() {
    // ∃x. (x = y) ∧ ¬(2 | x)  ≡  ¬(2 | y).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let two = ci(&mut terms, 2);
    let zero = ci(&mut terms, 0);
    let xmod2 = terms.mk_mod(x, two);
    let div = terms.mk_eq(xmod2, zero);
    let ndiv = terms.mk_not(div);
    let eqxy = terms.mk_eq(x, y);
    let body = terms.mk_and(vec![eqxy, ndiv]);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[eqxy, ndiv], x, o, &[y], 8, 40),
        QeResult::NotSupported => panic!("should eliminate negated divisibility"),
    }
}

#[test]
fn elim_ndiv_pair_covers_all_residues() {
    // ∃x. ¬(2 | x) ∧ ¬(2 | x+1)  ≡  false (every x hits one of the two
    // residues) — the p2 duality core: ∀x.(2|x ∨ 2|x+1) negates to this.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let one = ci(&mut terms, 1);
    let two = ci(&mut terms, 2);
    let zero = ci(&mut terms, 0);
    let xmod2 = terms.mk_mod(x, two);
    let d1 = terms.mk_eq(xmod2, zero);
    let n1 = terms.mk_not(d1);
    let xp1 = terms.mk_add(vec![x, one]);
    let xp1mod2 = terms.mk_mod(xp1, two);
    let d2 = terms.mk_eq(xp1mod2, zero);
    let n2 = terms.mk_not(d2);
    let body = terms.mk_and(vec![n1, n2]);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => {
            let assign: HashMap<TermId, BigInt> = HashMap::new();
            assert!(
                !eval_bool(&terms, o, &assign),
                "∃x. ¬(2|x) ∧ ¬(2|x+1) must be false"
            );
        }
        QeResult::NotSupported => panic!("should eliminate the NDiv pair"),
    }
}

#[test]
fn elim_ndiv_with_div_mixed_periods() {
    // ∃x. (2 | x) ∧ ¬(4 | x) ∧ (x = y)  ≡  y ≡ 2 (mod 4). δ must be
    // lcm(2, 4) = 4 — an NDiv divisor omitted from δ would fail this grid.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let two = ci(&mut terms, 2);
    let four = ci(&mut terms, 4);
    let zero = ci(&mut terms, 0);
    let xmod2 = terms.mk_mod(x, two);
    let d2 = terms.mk_eq(xmod2, zero);
    let xmod4 = terms.mk_mod(x, four);
    let d4 = terms.mk_eq(xmod4, zero);
    let nd4 = terms.mk_not(d4);
    let eqxy = terms.mk_eq(x, y);
    let body = terms.mk_and(vec![d2, nd4, eqxy]);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[d2, nd4, eqxy], x, o, &[y], 10, 60),
        QeResult::NotSupported => panic!("should eliminate mixed Div/NDiv"),
    }
}

#[test]
fn elim_ndiv_scaled_coefficient() {
    // ∃x. ¬(3 | 2·x + 1) ∧ (x = y)  — NDiv normalization must scale the
    // divisor with the unit-coefficient factor (¬(3 | 2x+1) ⟺ ¬(6 | 4x+2)
    // after ·2 with x' = 2x).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let one = ci(&mut terms, 1);
    let two = ci(&mut terms, 2);
    let three = ci(&mut terms, 3);
    let zero = ci(&mut terms, 0);
    let twox = terms.mk_mul(vec![two, x]);
    let t = terms.mk_add(vec![twox, one]);
    let tmod3 = terms.mk_mod(t, three);
    let d = terms.mk_eq(tmod3, zero);
    let nd = terms.mk_not(d);
    let eqxy = terms.mk_eq(x, y);
    let body = terms.mk_and(vec![nd, eqxy]);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[nd, eqxy], x, o, &[y], 9, 60),
        QeResult::NotSupported => panic!("should eliminate scaled NDiv"),
    }
}

#[test]
fn elim_ndiv_large_divisor_97() {
    // ∃x. ¬(97 | x + 1)  ≡  true — the large-divisor adversarial case: a
    // δ or window miss would surface here as a refusal or a wrong constant.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let one = ci(&mut terms, 1);
    let ninety_seven = ci(&mut terms, 97);
    let zero = ci(&mut terms, 0);
    let xp1 = terms.mk_add(vec![x, one]);
    let m = terms.mk_mod(xp1, ninety_seven);
    let d = terms.mk_eq(m, zero);
    let body = terms.mk_not(d);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => {
            let assign: HashMap<TermId, BigInt> = HashMap::new();
            assert!(
                eval_bool(&terms, o, &assign),
                "∃x. ¬(97 | x+1) must be true"
            );
        }
        QeResult::NotSupported => panic!("should eliminate large-divisor NDiv"),
    }
}

#[test]
fn selfcheck_refuses_over_cap_divisor_period() {
    // ∃x. ¬(63 | x) ∧ ¬(130 | x): δ = lcm(63, 130) = 8190 exceeds
    // DIVISOR_PERIOD_CAP while the output constant-folds (no output
    // constants), so the hardened self-check must refuse (fail-closed)
    // rather than run an incomplete bounded search.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let zero = ci(&mut terms, 0);
    let d63 = ci(&mut terms, 63);
    let d130 = ci(&mut terms, 130);
    let m1 = terms.mk_mod(x, d63);
    let e1 = terms.mk_eq(m1, zero);
    let n1 = terms.mk_not(e1);
    let m2 = terms.mk_mod(x, d130);
    let e2 = terms.mk_eq(m2, zero);
    let n2 = terms.mk_not(e2);
    let body = terms.mk_and(vec![n1, n2]);
    assert_eq!(
        eliminate_exists(&mut terms, body, x),
        QeResult::NotSupported
    );
}

#[test]
fn elim_ndiv_coprime_triple_within_cap() {
    // ∃x. ¬(3 | x) ∧ ¬(5 | x) ∧ ¬(7 | x)  ≡  true (x = 1). δ = 105 exceeds
    // Σ|consts| but is under the cap, so the window folds the period in and
    // the check completes.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let zero = ci(&mut terms, 0);
    let mut lits: Vec<TermId> = Vec::new();
    for d in [3i64, 5, 7] {
        let dc = ci(&mut terms, d);
        let m = terms.mk_mod(x, dc);
        let e = terms.mk_eq(m, zero);
        let n = terms.mk_not(e);
        lits.push(n);
    }
    let body = terms.mk_and(lits.clone());
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => {
            let assign: HashMap<TermId, BigInt> = HashMap::new();
            assert!(
                eval_bool(&terms, o, &assign),
                "∃x. ¬(3|x) ∧ ¬(5|x) ∧ ¬(7|x) must be true"
            );
        }
        QeResult::NotSupported => panic!("coprime NDiv triple within cap should eliminate"),
    }
}

#[test]
fn refuse_eliminating_non_var() {
    // Eliminating a non-variable term ⇒ refuse.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let xy = terms.mk_add(vec![x, y]);
    let zero = ci(&mut terms, 0);
    let body = terms.mk_gt(x, zero);
    assert_eq!(
        eliminate_exists(&mut terms, body, xy),
        QeResult::NotSupported
    );
}

#[test]
fn refuse_ite_structure() {
    // ∃x. (ite (x > 0) (x = y) (x = z))  — ite formula structure ⇒ refuse.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let z = int_var(&mut terms, "z");
    let zero = ci(&mut terms, 0);
    let cond = terms.mk_gt(x, zero);
    let t = terms.mk_eq(x, y);
    let e = terms.mk_eq(x, z);
    let body = terms.mk_ite(cond, t, e);
    assert_eq!(
        eliminate_exists(&mut terms, body, x),
        QeResult::NotSupported
    );
}

// ---------------------------------------------------------------------------
// Randomized in-fragment fuzz: build random conjunctions, eliminate, and
// confirm the result agrees with brute force on a grid. The internal
// self-check is active throughout (any false elimination would have already
// been refused), but we re-verify here independently.
// ---------------------------------------------------------------------------

#[test]
fn fuzz_random_conjunctions() {
    let mut seed: u64 = 0xA1B2_C3D4_E5F6_0718;
    let mut next = || {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        seed >> 33
    };

    let mut eliminated = 0;
    let cases = 60;
    for _ in 0..cases {
        let mut terms = TermStore::new();
        let x = int_var(&mut terms, "x");
        let y = int_var(&mut terms, "y");
        let z = int_var(&mut terms, "z");
        let vars = [x, y, z];

        let nlits = 1 + (next() % 3) as usize;
        let mut literals = Vec::new();
        for _ in 0..nlits {
            // Build a random linear term over x,y,z with small coeffs.
            let mut summands = Vec::new();
            for &v in &vars {
                let c = (next() % 5) as i64 - 2; // -2..2
                if c != 0 {
                    let cc = ci(&mut terms, c);
                    summands.push(terms.mk_mul(vec![cc, v]));
                }
            }
            let k = (next() % 7) as i64 - 3;
            summands.push(ci(&mut terms, k));
            let lhs = if summands.len() == 1 {
                summands[0]
            } else {
                terms.mk_add(summands)
            };
            let zero = ci(&mut terms, 0);
            let kind = next() % 5;
            let lit = match kind {
                0 => terms.mk_le(lhs, zero),
                1 => terms.mk_lt(lhs, zero),
                2 => terms.mk_eq(lhs, zero),
                3 => {
                    let eq = terms.mk_eq(lhs, zero);
                    terms.mk_not(eq)
                }
                _ => {
                    let d = 2 + (next() % 3) as i64; // 2..4
                    let dd = ci(&mut terms, d);
                    let m = terms.mk_mod(lhs, dd);
                    terms.mk_eq(m, zero)
                }
            };
            literals.push(lit);
        }
        let body = if literals.len() == 1 {
            literals[0]
        } else {
            terms.mk_and(literals.clone())
        };

        if let QeResult::Eliminated(o) = eliminate_exists(&mut terms, body, x) {
            eliminated += 1;
            // Independent grid comparison over y, z.
            compare_grid(&terms, &literals, x, o, &[y, z], 3, 80);
        }
    }
    // Sanity: the procedure should succeed on a healthy fraction of random
    // in-fragment cases (not silently refuse everything).
    assert!(
        eliminated >= cases / 2,
        "expected many successful eliminations, got {eliminated}/{cases}"
    );
}

// ---------------------------------------------------------------------------
// Adversarial: prove the soundness gate REJECTS wrong eliminations (both
// directions). If these ever passed, the gate would be useless.
// ---------------------------------------------------------------------------

#[test]
fn selfcheck_rejects_too_strong_result() {
    // φ = (x > y). ∃x.φ ≡ true. A WRONG, too-strong candidate `O = false`
    // must be rejected by the self-check (it claims unsat where sat holds:
    // violates `∃x.φ ⇒ O`).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let body = terms.mk_gt(x, y);
    let wrong = terms.mk_bool(false);
    assert!(
        !equivalence_self_check(&terms, &[body], x, wrong),
        "self-check must reject O=false for the satisfiable ∃x. x>y"
    );
}

#[test]
fn selfcheck_rejects_too_weak_result() {
    // φ = (x > y) ∧ (x < y). ∃x.φ ≡ false. A WRONG, too-weak candidate
    // `O = true` must be rejected (claims sat where unsat holds: violates
    // `O ⇒ ∃x.φ`).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let l1 = terms.mk_gt(x, y);
    let l2 = terms.mk_lt(x, y);
    let wrong = terms.mk_bool(true);
    assert!(
        !equivalence_self_check(&terms, &[l1, l2], x, wrong),
        "self-check must reject O=true for the unsatisfiable ∃x. x>y ∧ x<y"
    );
}

#[test]
fn selfcheck_rejects_off_by_one_result() {
    // φ = (2*x = y). ∃x.φ ≡ (2 | y). A subtly WRONG candidate
    // `O = (3 | y)` (right shape, wrong divisor) must be rejected.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let two = ci(&mut terms, 2);
    let three = ci(&mut terms, 3);
    let zero = ci(&mut terms, 0);
    let two_x = terms.mk_mul(vec![two, x]);
    let body = terms.mk_eq(two_x, y);
    let ymod3 = terms.mk_mod(y, three);
    let wrong = terms.mk_eq(ymod3, zero); // (3 | y) — wrong
    assert!(
        !equivalence_self_check(&terms, &[body], x, wrong),
        "self-check must reject the off-by-divisor O=(3|y) for ∃x. 2x=y"
    );
}

// ---------------------------------------------------------------------------
// Termination (#clusterD divergence): huge-constant search windows must
// REFUSE fail-closed, never run the exhaustive self-check to completion.
// ---------------------------------------------------------------------------

#[test]
fn type_range_guard_refuses_fast_instead_of_diverging() {
    // The deductive-checks exists-witness shape (machine-integer type-range guards):
    // ∃x. (x ≥ −2³¹ ∧ x < 2³¹ ∧ x = 42). Cooper's elimination itself is
    // cheap, but the equivalence self-check's exhaustive x-search window
    // scales with Σ|consts| ≈ 2³², i.e. ~10¹⁰ candidate values × ~200
    // battery assignments — effectively nonterminating. SEARCH_WINDOW_CAP
    // makes the check refuse (fail-closed → NotSupported) promptly instead;
    // the caller keeps the quantifier for the downstream quantifier loop.
    // The REAL assertion is termination: pre-fix, this test hangs.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let lo = ci(&mut terms, -2_147_483_648);
    let hi = ci(&mut terms, 2_147_483_648);
    let c42 = ci(&mut terms, 42);
    let ge = terms.mk_ge(x, lo);
    let lt = terms.mk_lt(x, hi);
    let eq = terms.mk_eq(x, c42);
    let body = terms.mk_and(vec![ge, lt, eq]);
    assert_eq!(
        eliminate_exists(&mut terms, body, x),
        QeResult::NotSupported,
        "over-cap self-check window must refuse fail-closed, not adopt unverified output"
    );
}

#[test]
fn small_range_witness_still_eliminates_under_cap() {
    // Companion to the cap test: a small-constant witness shape
    // (∃w. w ≥ 0 ∧ w < 10 ∧ w = 4 ≡ true) stays comfortably inside
    // SEARCH_WINDOW_CAP and must still be verified and adopted — the cap
    // only converts would-be divergence into refusal.
    let mut terms = TermStore::new();
    let w = int_var(&mut terms, "w");
    let zero = ci(&mut terms, 0);
    let ten = ci(&mut terms, 10);
    let four = ci(&mut terms, 4);
    let ge = terms.mk_ge(w, zero);
    let lt = terms.mk_lt(w, ten);
    let eq = terms.mk_eq(w, four);
    let body = terms.mk_and(vec![ge, lt, eq]);
    match eliminate_exists(&mut terms, body, w) {
        QeResult::Eliminated(qf) => {
            assert!(
                matches!(terms.get(qf), TermData::Const(Constant::Bool(true))),
                "∃w. 0≤w<10 ∧ w=4 must eliminate to true, got {:?}",
                terms.get(qf)
            );
        }
        QeResult::NotSupported => panic!("small-window elimination must not be refused by the cap"),
    }
}

// ---------------------------------------------------------------------------
// z3py / z3 cross-check.
//
// For a suite of in-fragment φ, run AY's `eliminate_exists`, then ask z3 (via
// the `z3` CLI, which ships with z3py 4.15.4) to *prove the equivalence*
// `O ⟺ ∃x.φ` by checking both `(∃x.φ) ∧ ¬O` and `¬(∃x.φ) ∧ O` are UNSAT.
// This is a genuine equivalence check against z3, not sampling.
//
// The test is gated on z3 being on PATH; if absent it prints a notice and
// passes (so CI without z3 still works). The fragment shapes Cooper produces
// are exactly covered by the small serializer below, so the round-trip is
// faithful.
// ---------------------------------------------------------------------------

/// Render a fragment term to SMT-LIB. Covers exactly the operators AY's Cooper
/// procedure can emit; panics on anything else (which would indicate the
/// procedure left the fragment — a bug we want surfaced).
fn to_smt(terms: &TermStore, t: TermId) -> String {
    use ay_core::term::{Constant, Symbol, TermData};
    match terms.get(t) {
        TermData::Const(Constant::Int(n)) => {
            if *n < BigInt::from(0) {
                format!("(- {})", -n.clone())
            } else {
                n.to_string()
            }
        }
        TermData::Const(Constant::Bool(b)) => b.to_string(),
        TermData::Var(name, _) => name.clone(),
        TermData::Not(inner) => format!("(not {})", to_smt(terms, *inner)),
        TermData::Ite(c, a, b) => format!(
            "(ite {} {} {})",
            to_smt(terms, *c),
            to_smt(terms, *a),
            to_smt(terms, *b)
        ),
        TermData::App(Symbol::Named(name), args) => {
            let parts: Vec<String> = args.iter().map(|&a| to_smt(terms, a)).collect();
            format!("({} {})", name, parts.join(" "))
        }
        other => panic!("to_smt: unsupported term shape {other:?}"),
    }
}

/// Collect the free variable names in a term (for declarations).
fn free_var_names(terms: &TermStore, t: TermId, out: &mut Vec<String>) {
    use ay_core::term::{Symbol, TermData};
    match terms.get(t) {
        TermData::Var(name, _) if !out.contains(name) => out.push(name.clone()),
        TermData::Var(_, _) => {}
        TermData::Not(inner) => free_var_names(terms, *inner, out),
        TermData::Ite(c, a, b) => {
            free_var_names(terms, *c, out);
            free_var_names(terms, *a, out);
            free_var_names(terms, *b, out);
        }
        TermData::App(Symbol::Named(_), args) => {
            for &a in args {
                free_var_names(terms, a, out);
            }
        }
        _ => {}
    }
}

/// Returns Some(true) if z3 proves `O ⟺ ∃x.φ`, Some(false) if z3 finds a
/// discrepancy, None if z3 is unavailable.
fn z3_equiv_check(terms: &TermStore, var_name: &str, body: TermId, result: TermId) -> Option<bool> {
    use std::io::Write;
    use std::process::{Command, Stdio};

    // z3 availability probe.
    if Command::new("z3").arg("--version").output().is_err() {
        return None;
    }

    // Free vars = all vars in body/result except the eliminated one.
    let mut names = Vec::new();
    free_var_names(terms, body, &mut names);
    free_var_names(terms, result, &mut names);
    names.retain(|n| n != var_name);

    use std::fmt::Write as _;
    let mut decls = String::new();
    for n in &names {
        let _ = writeln!(decls, "(declare-const {n} Int)");
    }

    let phi = to_smt(terms, body);
    let o = to_smt(terms, result);
    let exists_phi = format!("(exists (({var_name} Int)) {phi})");

    // Direction 1: (∃x.φ) ∧ ¬O must be UNSAT  (proves ∃x.φ ⇒ O).
    // Direction 2: O ∧ ¬(∃x.φ) must be UNSAT  (proves O ⇒ ∃x.φ).
    let run = |assertion: &str| -> Option<String> {
        let script = format!("(set-logic LIA)\n{decls}(assert {assertion})\n(check-sat)\n");
        let mut child = Command::new("z3")
            .args(["-in", "-smt2"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .ok()?;
        child.stdin.as_mut()?.write_all(script.as_bytes()).ok()?;
        let out = child.wait_with_output().ok()?;
        Some(String::from_utf8_lossy(&out.stdout).trim().to_string())
    };

    let dir1 = run(&format!("(and {exists_phi} (not {o}))"))?;
    let dir2 = run(&format!("(and {o} (not {exists_phi}))"))?;

    Some(dir1 == "unsat" && dir2 == "unsat")
}

#[test]
fn z3_cross_check_suite() {
    // Build a deterministic suite of in-fragment formulas, eliminate, and ask
    // z3 to prove equivalence of O and ∃x.φ.
    let mut z3_available = true;
    let mut checked = 0;
    let mut passed = 0;

    // Each case: a closure building (body, eliminated_var) given a fresh store.
    type Case = fn(&mut TermStore) -> (TermId, TermId);
    let cases: Vec<Case> = vec![
        |t| {
            // ∃x. x > y
            let x = t.mk_var("x", Sort::Int);
            let y = t.mk_var("y", Sort::Int);
            let b = t.mk_gt(x, y);
            (b, x)
        },
        |t| {
            // ∃x. (x > y) ∧ (x < y)
            let x = t.mk_var("x", Sort::Int);
            let y = t.mk_var("y", Sort::Int);
            let l1 = t.mk_gt(x, y);
            let l2 = t.mk_lt(x, y);
            let b = t.mk_and(vec![l1, l2]);
            (b, x)
        },
        |t| {
            // ∃x. 2*x = y
            let x = t.mk_var("x", Sort::Int);
            let y = t.mk_var("y", Sort::Int);
            let two = t.mk_int(BigInt::from(2));
            let tx = t.mk_mul(vec![two, x]);
            let b = t.mk_eq(tx, y);
            (b, x)
        },
        |t| {
            // ∃x. (3*x >= y) ∧ (3*x <= y + 2)
            let x = t.mk_var("x", Sort::Int);
            let y = t.mk_var("y", Sort::Int);
            let three = t.mk_int(BigInt::from(3));
            let two = t.mk_int(BigInt::from(2));
            let tx = t.mk_mul(vec![three, x]);
            let yp2 = t.mk_add(vec![y, two]);
            let l1 = t.mk_ge(tx, y);
            let l2 = t.mk_le(tx, yp2);
            let b = t.mk_and(vec![l1, l2]);
            (b, x)
        },
        |t| {
            // ∃x. (x = y) ∧ (4 | x)
            let x = t.mk_var("x", Sort::Int);
            let y = t.mk_var("y", Sort::Int);
            let four = t.mk_int(BigInt::from(4));
            let zero = t.mk_int(BigInt::from(0));
            let xm4 = t.mk_mod(x, four);
            let div = t.mk_eq(xm4, zero);
            let eq = t.mk_eq(x, y);
            let b = t.mk_and(vec![eq, div]);
            (b, x)
        },
        |t| {
            // ∃x. (x >= y) ∧ (x != y)
            let x = t.mk_var("x", Sort::Int);
            let y = t.mk_var("y", Sort::Int);
            let ge = t.mk_ge(x, y);
            let eq = t.mk_eq(x, y);
            let ne = t.mk_not(eq);
            let b = t.mk_and(vec![ge, ne]);
            (b, x)
        },
        |t| {
            // ∃x. (x > y) ∧ (x > z) ∧ (x < y + z + 5)
            let x = t.mk_var("x", Sort::Int);
            let y = t.mk_var("y", Sort::Int);
            let z = t.mk_var("z", Sort::Int);
            let five = t.mk_int(BigInt::from(5));
            let s = t.mk_add(vec![y, z, five]);
            let l1 = t.mk_gt(x, y);
            let l2 = t.mk_gt(x, z);
            let l3 = t.mk_lt(x, s);
            let b = t.mk_and(vec![l1, l2, l3]);
            (b, x)
        },
        |t| {
            // ∃x. (2*x <= y) ∧ (3*x >= z)
            let x = t.mk_var("x", Sort::Int);
            let y = t.mk_var("y", Sort::Int);
            let z = t.mk_var("z", Sort::Int);
            let two = t.mk_int(BigInt::from(2));
            let three = t.mk_int(BigInt::from(3));
            let tx = t.mk_mul(vec![two, x]);
            let thx = t.mk_mul(vec![three, x]);
            let l1 = t.mk_le(tx, y);
            let l2 = t.mk_ge(thx, z);
            let b = t.mk_and(vec![l1, l2]);
            (b, x)
        },
        |t| {
            // ∃x. (x = y) ∧ ¬(2 | x)
            let x = t.mk_var("x", Sort::Int);
            let y = t.mk_var("y", Sort::Int);
            let two = t.mk_int(BigInt::from(2));
            let zero = t.mk_int(BigInt::from(0));
            let m = t.mk_mod(x, two);
            let e = t.mk_eq(m, zero);
            let nd = t.mk_not(e);
            let eq = t.mk_eq(x, y);
            let b = t.mk_and(vec![eq, nd]);
            (b, x)
        },
        |t| {
            // ∃x. (x > y) ∧ (x < y + 4) ∧ ¬(3 | x)
            let x = t.mk_var("x", Sort::Int);
            let y = t.mk_var("y", Sort::Int);
            let three = t.mk_int(BigInt::from(3));
            let four = t.mk_int(BigInt::from(4));
            let zero = t.mk_int(BigInt::from(0));
            let m = t.mk_mod(x, three);
            let e = t.mk_eq(m, zero);
            let nd = t.mk_not(e);
            let g = t.mk_gt(x, y);
            let s = t.mk_add(vec![y, four]);
            let l = t.mk_lt(x, s);
            let b = t.mk_and(vec![g, l, nd]);
            (b, x)
        },
    ];

    for case in cases {
        let mut terms = TermStore::new();
        let (body, x) = case(&mut terms);
        let QeResult::Eliminated(o) = eliminate_exists(&mut terms, body, x) else {
            panic!("z3_cross_check_suite: expected elimination for a fragment case");
        };
        match z3_equiv_check(&terms, "x", body, o) {
            Some(true) => {
                checked += 1;
                passed += 1;
            }
            Some(false) => {
                panic!(
                    "z3 cross-check FAILED: O = {} is not equivalent to ∃x.φ where φ = {}",
                    to_smt(&terms, o),
                    to_smt(&terms, body)
                );
            }
            None => {
                z3_available = false;
                break;
            }
        }
    }

    if !z3_available {
        eprintln!(
            "z3_cross_check_suite: z3 binary not found on PATH — SKIPPING z3 cross-check \
             (in-fragment correctness still covered by the internal self-check + brute-force grid tests)."
        );
        return;
    }
    eprintln!("z3_cross_check_suite: z3 proved equivalence on {passed}/{checked} cases.");
    assert_eq!(passed, checked, "all z3 cross-checks must pass");
    assert!(checked >= 8, "expected the full suite to run under z3");
}

#[test]
fn selfcheck_accepts_correct_result() {
    // Positive control: the genuine elimination of ∃x. 2*x = y, which is
    // (2 | y), must PASS the self-check.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let two = ci(&mut terms, 2);
    let zero = ci(&mut terms, 0);
    let two_x = terms.mk_mul(vec![two, x]);
    let body = terms.mk_eq(two_x, y);
    let ymod2 = terms.mk_mod(y, two);
    let correct = terms.mk_eq(ymod2, zero); // (2 | y) — correct
    assert!(
        equivalence_self_check(&terms, &[body], x, correct),
        "self-check must accept the correct O=(2|y) for ∃x. 2x=y"
    );
}

// ---------------------------------------------------------------------------
// Period / instance ceiling (#cooper-period-blowup)
// ---------------------------------------------------------------------------

/// A large COEFFICIENT — not a written `mod` atom — drives Cooper's period.
/// `∃v. (1048576·v = x ∧ y ≤ v)` sets m = δ = 2^20, and the two instance
/// sweeps used to materialise ~2^20 interned terms with no ceiling: 3.07 GB
/// peak and 8.5 s at the CLI for 142 bytes of SMT, after which the bounded
/// differential self-check discards the result anyway.
///
/// The ceiling must refuse BEFORE allocating. Note which assertion does the
/// work: `NotSupported` alone does NOT discriminate — with the cap disabled
/// the self-check refuses this elimination too, so that assertion passes
/// either way. The INTERNED-TERM assertion is the mutation-discriminating
/// one, and unlike a wall-clock bound it measures the mechanism the cap
/// exists to bound and does not depend on host speed.
#[test]
fn large_coefficient_period_refuses_without_allocating() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let v = int_var(&mut terms, "v");
    let big = ci(&mut terms, 1_048_576);
    let bigv = terms.mk_mul(vec![big, v]);
    let l1 = terms.mk_eq(bigv, x);
    let l2 = terms.mk_le(y, v);
    let body = terms.mk_and(vec![l1, l2]);

    let before = terms.len();
    let t0 = std::time::Instant::now();
    let result = eliminate_exists(&mut terms, body, v);
    let elapsed = t0.elapsed();
    let interned = terms.len() - before;

    assert!(
        matches!(result, QeResult::NotSupported),
        "an over-ceiling period must fail closed, not ship an elimination"
    );

    // MUTATION GUARD, measured — not assumed. `COOPER_INSTANCE_CAP` bounds
    // `(1 + |B|) * δ`; δ = 2^20 and |B| = 1 here, so an uncapped run interns
    // the instance terms plus all their subterms. Measured on this host:
    //   cap = 16_384 (shipped)    →          0 new terms (refused first)
    //   cap = i64::MAX (disabled) → 13_631_491 new terms
    // The 4096 threshold is 3329x under the uncapped count, and the capped
    // run interns nothing at all, so it is a near-miss in neither direction
    // and does not depend on how fast the host is. Verified by mutation: with
    // the cap at `i64::MAX` this is the assertion that fires.
    assert!(
        interned < 4096,
        "refusal must happen before the instance sweeps allocate; \
         interned {interned} new terms"
    );

    // Wall-clock backstop, secondary to the count above. Measured uncapped:
    // 9.1 s in this test and 8.5 s at the CLI — 4.5x and 4.3x over this
    // bound. NOT "an order of magnitude", which an earlier revision of this
    // comment claimed off a 23.8 s figure this host does not reproduce.
    // Kept because it is what a reader reaches for, but the interned-term
    // assertion above is the one to trust.
    assert!(
        elapsed < std::time::Duration::from_secs(2),
        "refusal must happen before the instance sweeps allocate; took {elapsed:?}"
    );
}

/// The ceiling must not narrow the ordinary small-period fragment: a genuine
/// scaled elimination still succeeds and still agrees with brute force.
#[test]
fn small_period_still_eliminates_under_ceiling() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let six = ci(&mut terms, 6);
    let six_x = terms.mk_mul(vec![six, x]);
    let body = terms.mk_eq(six_x, y);
    match eliminate_exists(&mut terms, body, x) {
        QeResult::Eliminated(o) => compare_grid(&terms, &[body], x, o, &[y], 8, 40),
        QeResult::NotSupported => panic!("δ = 6 is far under the ceiling and must eliminate"),
    }
}
