// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Nelson-Oppen disequality propagation verification tests (#8455, epic #8447).
//!
//! These tests verify that disequalities propagate correctly between theories
//! in the Nelson-Oppen theory combination framework. The core mechanism:
//!
//! 1. **Assert-time forwarding:** When `assert_literal` sees a negated UF equality
//!    like `(not (= (f x) (g y)))`, it forwards to arithmetic via
//!    `assert_shared_disequality`.
//!
//! 2. **N-O fixpoint propagation:** During the Nelson-Oppen fixpoint loop,
//!    `collect_implied_disequalities` on EUF collects disequalities implied by
//!    congruence closure (e.g., `a != b` and `c` in class of `a`, `d` in class
//!    of `b` implies `c != d`) and forwards them to arithmetic.
//!
//! 3. **Arithmetic checking:** LRA/LIA's `check_shared_disequalities` evaluates
//!    the disequality constraint and generates a split (or conflict) when the
//!    arithmetic model violates it.
//!
//! Reference: Z3's `propagate_th_diseqs` (smt_context.cpp:1678-1690) and
//! `arith_eq_adapter::new_diseq_eh` (arith_eq_adapter.cpp:240-243).

use ntest::timeout;

// ============================================================================
// QF_UFLIA: EUF → LIA disequality propagation
// ============================================================================

/// EUF proves f(a) != f(b) via a != b, LIA must respect this.
/// Without disequality propagation, LIA might assign f(a) = f(b) = 0,
/// causing incompleteness or extra splitting rounds.
#[test]
#[timeout(10_000)]
fn test_uflia_euf_diseq_to_lia_sat_8455() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (distinct a b))
(assert (= a 1))
(assert (= b 2))
(assert (>= (f a) 0))
(assert (<= (f a) 10))
(assert (>= (f b) 0))
(assert (<= (f b) 10))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Should be SAT: f(1) and f(2) are independent"
    );
}

/// When EUF knows a != b and LIA forces f(a) = f(b), the disequality
/// propagation must NOT cause UNSAT (f is not injective — a != b does
/// not imply f(a) != f(b)).
#[test]
#[timeout(10_000)]
fn test_uflia_diseq_noninjective_sat_8455() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (distinct a b))
(assert (= (f a) (f b)))
(assert (= a 1))
(assert (= b 2))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "SAT: f is not injective, so f(1) = f(2) is legal even with 1 != 2"
    );
}

/// Direct N-O disequality: not(= (f x) 5) forces LIA to respect f(x) != 5.
/// Combined with (>= (f x) 5) and (<= (f x) 5), this should be UNSAT.
#[test]
#[timeout(10_000)]
fn test_uflia_diseq_squeeze_unsat_8455() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (>= (f x) 5))
(assert (<= (f x) 5))
(assert (not (= (f x) 5)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "UNSAT: f(x) >= 5 and f(x) <= 5 forces f(x) = 5, contradicting f(x) != 5"
    );
}

/// Multi-hop disequality propagation through EUF congruence classes.
/// a = c, b = d, a != b. EUF must derive c != d and propagate to LIA.
/// Combined with f(c) constraints, check correctness.
#[test]
#[timeout(10_000)]
fn test_uflia_transitive_diseq_8455() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(assert (= a c))
(assert (= b d))
(assert (distinct a b))
(assert (= (f c) 10))
(assert (= (f d) 10))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "SAT: a!=b and a=c, b=d implies c!=d, but f(c)=f(d) is fine (f not injective)"
    );
}

/// Transitive diseq + congruence = UNSAT.
/// a = c, b = d, a != b, c = d → contradiction.
#[test]
#[timeout(10_000)]
fn test_uflia_transitive_diseq_unsat_8455() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(assert (= a c))
(assert (= b d))
(assert (distinct a b))
(assert (= c d))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "UNSAT: a=c, b=d, a!=b, c=d is contradictory"
    );
}

// ============================================================================
// QF_UFLRA: EUF → LRA disequality propagation
// ============================================================================

/// Real-valued disequality propagation: f(a) != 3.0 with bounds forcing f(a) = 3.0.
#[test]
#[timeout(10_000)]
fn test_uflra_diseq_squeeze_unsat_8455() {
    let smt = r#"
(set-logic QF_UFLRA)
(declare-fun g (Real) Real)
(declare-const x Real)
(assert (>= (g x) 3.0))
(assert (<= (g x) 3.0))
(assert (not (= (g x) 3.0)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "UNSAT: g(x) >= 3 and g(x) <= 3 forces g(x) = 3, contradicting g(x) != 3"
    );
}

/// Real-valued SAT case with disequality.
#[test]
#[timeout(10_000)]
fn test_uflra_diseq_sat_8455() {
    let smt = r#"
(set-logic QF_UFLRA)
(declare-fun g (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (= x 1.0))
(assert (= y 2.0))
(assert (not (= (g x) (g y))))
(assert (>= (g x) 0.0))
(assert (<= (g x) 100.0))
(assert (>= (g y) 0.0))
(assert (<= (g y) 100.0))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "SAT: g(1.0) != g(2.0) with loose bounds is satisfiable"
    );
}

/// Two functions, chain of disequalities through real arithmetic.
#[test]
#[timeout(10_000)]
fn test_uflra_chain_diseq_unsat_8455() {
    let smt = r#"
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun g (Real) Real)
(declare-const a Real)
(declare-const b Real)
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "UNSAT: a=b implies f(a)=f(b) by congruence, contradicting f(a) != f(b)"
    );
}

// ============================================================================
// QF_AUFLIA: Arrays + UF + LIA with disequality propagation
// ============================================================================

/// Array select with disequality: select(A, i) != select(A, j) when i != j is SAT.
#[test]
#[timeout(10_000)]
fn test_auflia_select_diseq_sat_8455() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (= i 0))
(assert (= j 1))
(assert (not (= (select A i) (select A j))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "SAT: A[0] != A[1] is satisfiable");
}

/// Array select with disequality: i = j forces select(A,i) = select(A,j).
#[test]
#[timeout(10_000)]
fn test_auflia_select_diseq_congruence_unsat_8455() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (= i j))
(assert (not (= (select A i) (select A j))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "UNSAT: i=j implies select(A,i) = select(A,j), contradicting the disequality"
    );
}

/// Mixed array + UF + arithmetic with disequality chain.
#[test]
#[timeout(10_000)]
fn test_auflia_mixed_diseq_chain_8455() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-fun f (Int) Int)
(declare-const A (Array Int Int))
(declare-const x Int)
(declare-const y Int)
(assert (= x 0))
(assert (= y 1))
(assert (= (select A x) (f x)))
(assert (= (select A y) (f y)))
(assert (not (= (f x) (f y))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "SAT: x!=y, A[x]=f(x), A[y]=f(y), f(x)!=f(y) is satisfiable"
    );
}

// ============================================================================
// Disequality propagation in the N-O fixpoint loop
// ============================================================================

/// This test exercises the N-O fixpoint loop's disequality propagation path.
/// EUF discovers a != b from distinct(a,b). During the fixpoint, EUF
/// propagates this as a disequality to LIA. LIA must generate a split
/// if its model has f(a) = f(b).
#[test]
#[timeout(10_000)]
fn test_no_fixpoint_diseq_propagation_8455() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (distinct a b))
(assert (= c (+ (f a) (f b))))
(assert (>= c 0))
(assert (<= c 100))
(assert (= a 5))
(assert (= b 10))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "SAT: distinct(5,10) with arithmetic on f(5)+f(10) is satisfiable"
    );
}

/// Multiple distinct pairs with UF: exercises batch disequality propagation.
#[test]
#[timeout(10_000)]
fn test_no_batch_diseq_propagation_8455() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (distinct a b c))
(assert (= a 1))
(assert (= b 2))
(assert (= c 3))
(assert (>= (f a) 0))
(assert (>= (f b) 0))
(assert (>= (f c) 0))
(assert (<= (f a) 100))
(assert (<= (f b) 100))
(assert (<= (f c) 100))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "SAT: multiple distinct integers with bounded UF application"
    );
}

/// Incremental disequality propagation: push/pop with changing disequalities.
#[test]
#[timeout(10_000)]
fn test_incremental_diseq_propagation_8455() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x 1))
(assert (= y 2))
(push 1)
(assert (= (f x) (f y)))
(check-sat)
(pop 1)
(push 1)
(assert (not (= (f x) (f y))))
(check-sat)
(pop 1)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat", "sat"],
        "Both cases are SAT: f(1)=f(2) and f(1)!=f(2) are both satisfiable"
    );
}

// ============================================================================
// Edge cases and soundness guards
// ============================================================================

/// Trivial disequality: constant != constant. No theory interaction needed.
#[test]
#[timeout(10_000)]
fn test_trivial_constant_diseq_sat_8455() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(assert (not (= 1 2)))
(assert (= (f 1) 42))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "SAT: 1 != 2 is trivially true");
}

/// Trivial disequality: constant = constant with distinct. UNSAT.
#[test]
#[timeout(10_000)]
fn test_trivial_constant_diseq_unsat_8455() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 5))
(assert (not (= x 5)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "UNSAT: x=5 and x!=5 is contradictory"
    );
}

/// Disequality with ITE: a complex N-O interaction.
#[test]
#[timeout(10_000)]
fn test_diseq_with_ite_8455() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const b Bool)
(assert (= x (ite b 1 2)))
(assert (= y (ite b 2 1)))
(assert (not (= (f x) (f y))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    // Whether b is true or false, x != y, so f(x) != f(y) is satisfiable.
    assert_eq!(
        outputs,
        vec!["sat"],
        "SAT: ITE forces x != y regardless of b, and f(x) != f(y) is fine"
    );
}
