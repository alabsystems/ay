// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #w11-ite-sum P0 wrong-UNSAT regression: `select` over a `store` at an
//! ite-sum index, plus a read disequality, a pinned read value, and a range
//! constraint EXCLUDING the stored value, was answered `unsat` on
//! satisfiable formulas (z3: `sat`) — a false theorem.
//!
//! Root cause: the Nelson-Oppen completeness pass
//! `check_int_equality_value_mismatches` treated a VALUE COINCIDENCE of the
//! two ite-sum index terms as a justified cross-theory conflict. The
//! arithmetic evaluator resolves `(ite b 1 0)` (condition a bare Bool var it
//! cannot decide) by falling back to the ITE term's bare LIA model value
//! with EMPTY reasons — a free simplex choice — but
//! `has_unjustified_int_leaf`'s `Ite` arm checked only the two constant
//! branches and classified the value as justified. The resulting 1-literal
//! conflict `{(= i1 i2) = false}` forced the indices equal UNCONDITIONALLY,
//! pruning the genuine model (`b2 = true` makes `i2 = i1 + 8`) on every
//! branch.
//!
//! The fix has three parts (see the w11 commit): the justification mirror
//! now follows the evaluator's ITE dispatch exactly; the model-side
//! reconcile pass pins don't-care ITE-condition Bools; and the AUFLIA
//! preprocessor injects definitional ITE-domain guard clauses + ROW
//! re-links for select-over-store reads surviving preprocessing.

/// The minimized wrong-unsat core (was `unsat`, must be `sat`): the bound
/// `>= 0` excludes the stored value `-2`, the disequality needs `b2 = true`
/// (indices then differ by 8), and the indices can never hit the store key
/// 36 (range [5, 14]).
#[test]
fn store_itesum_range_excludes_stored_value_sat() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const b1 Bool)
(declare-const b2 Bool)
(assert (not (= (select (store A 36 -2) (+ (ite b1 1 0) 5))
                (select (store A 36 -2) (+ (ite b1 1 0) (ite b2 8 0) 5)))))
(assert (>= (select (store A 36 -2) (+ (ite b1 1 0) 5)) 0))
(check-sat)
"#,
    );
    assert_eq!(
        outputs.first().map(|s| s.trim()),
        Some("sat"),
        "w11 minimized core is SAT (z3 agrees; b2=true separates the \
         indices); `unsat` is the false-theorem regression, `unknown` means \
         the model-repair half regressed — got: {outputs:?}"
    );
}

/// Full-repro shape with pinned read variable and constant-multiplied ITE
/// products (the w1b_fuzz_7_27 family). Was wrong-UNSAT; must be `sat`.
#[test]
fn store_itesum_product_coefficients_pinned_read_sat() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const x Int)
(declare-const b0 Bool)
(declare-const b1 Bool)
(declare-const b2 Bool)
(declare-const b3 Bool)
(declare-const b4 Bool)
(assert (not (= (select (store A 39 -4) (+ (* (ite b0 1 0) 2) (ite b1 1 0) (ite b2 1 0) (* (ite b3 1 0) 4) (* (ite b4 1 0) 4) 0))
                (select (store A 39 -4) (+ (* (ite b0 1 0) 2) (* (ite b1 1 0) 4) (ite b2 1 0) (* (ite b3 1 0) 4) (* (ite b4 1 0) 4) 0)))))
(assert (= (select (store A 39 -4) (+ (* (ite b0 1 0) 2) (ite b1 1 0) (ite b2 1 0) (* (ite b3 1 0) 4) (* (ite b4 1 0) 4) 0)) x))
(assert (>= x 0))
(assert (or (and (not b0) (not b1) (not b2) (not b3) (not b4)) b0))
(check-sat)
"#,
    );
    assert_eq!(
        outputs.first().map(|s| s.trim()),
        Some("sat"),
        "product-coefficient repro is SAT (z3 agrees) — got: {outputs:?}"
    );
}

/// Store key itself an ite-sum (the w1b_fuzz_1_229 family). Was
/// wrong-UNSAT; must be `sat`.
#[test]
fn store_itesum_symbolic_store_key_sat() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const x Int)
(declare-const b0 Bool)
(declare-const b1 Bool)
(assert (not (= (select (store A (+ (ite b0 1 0) (* (ite b1 1 0) 2) 8) -5) (+ (ite b0 1 0) (* (ite b1 1 0) 4) 5))
                (select (store A (+ (ite b0 1 0) (* (ite b1 1 0) 2) 8) -5) (+ (ite b0 1 0) (* (ite b1 1 0) 2) 5)))))
(assert (= (select (store A (+ (ite b0 1 0) (* (ite b1 1 0) 2) 8) -5) (+ (ite b0 1 0) (* (ite b1 1 0) 4) 5)) x))
(assert (>= x -2))
(assert (or (and (not b0) (not b1)) b0))
(check-sat)
"#,
    );
    assert_eq!(
        outputs.first().map(|s| s.trim()),
        Some("sat"),
        "symbolic-store-key repro is SAT (z3 agrees) — got: {outputs:?}"
    );
}

/// Genuine-unsat control: the SAME shape but with two contradictory pinned
/// reads of the IDENTICAL select term. Must stay `unsat` — guards against
/// the ITE-guard/ROW-re-link/pin machinery manufacturing a witness.
#[test]
fn store_itesum_contradictory_pinned_reads_stays_unsat() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const b1 Bool)
(declare-const b2 Bool)
(assert (= (select (store A 36 -2) (+ (ite b1 1 0) (ite b2 8 0) 5)) 1))
(assert (= (select (store A 36 -2) (+ (ite b1 1 0) (ite b2 8 0) 5)) 2))
(check-sat)
"#,
    );
    assert_eq!(
        outputs.first().map(|s| s.trim()),
        Some("unsat"),
        "contradictory pinned reads at one index are UNSAT and must stay \
         so — got: {outputs:?}"
    );
}

/// Genuine-unsat control at the ROOT-CAUSE boundary: the disequality holds
/// but BOTH branch valuations of the indices coincide (`i2 = i1` for every
/// Bool assignment because the extra summand is `(ite b2 0 0)`-free — here
/// literally the same index), so congruence forces the reads equal.
#[test]
fn store_itesum_identical_indices_diseq_stays_unsat() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const b1 Bool)
(declare-const b2 Bool)
(assert (not (= (select (store A 36 -2) (+ (ite b1 1 0) (* (ite b2 1 0) 2) 5))
                (select (store A 36 -2) (+ (* (ite b2 1 0) 2) (ite b1 1 0) 5)))))
(assert (>= (select (store A 36 -2) (+ (ite b1 1 0) (* (ite b2 1 0) 2) 5)) 0))
(check-sat)
"#,
    );
    assert_eq!(
        outputs.first().map(|s| s.trim()),
        Some("unsat"),
        "reordered-sum identical indices force equal reads; the disequality \
         is UNSAT and must stay so — got: {outputs:?}"
    );
}

/// Boundary: the range bound EQUALS the stored value (does not exclude it).
/// Genuinely SAT and previously already answered `sat` — must not degrade.
#[test]
fn store_itesum_bound_admits_stored_value_stays_sat() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const b1 Bool)
(declare-const b2 Bool)
(assert (not (= (select (store A 36 7) (+ (ite b1 1 0) 5))
                (select (store A 36 7) (+ (ite b1 1 0) (ite b2 8 0) 5)))))
(assert (>= (select (store A 36 7) (+ (ite b1 1 0) 5)) 7))
(check-sat)
"#,
    );
    assert_eq!(
        outputs.first().map(|s| s.trim()),
        Some("sat"),
        "bound-admits-stored-value variant is SAT and must not degrade — \
         got: {outputs:?}"
    );
}
