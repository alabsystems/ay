// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #6869: QF_UF false-SAT from dropped Bool-alias equality in EUF.
//!
//! When a Bool-Bool equality aliases a theory-valued term (e.g., `(= b_alias (= x y))`),
//! the equality must reach EUF as a theory atom so congruence closure can propagate
//! through the alias chain. Without this, EUF misses contradictions involving
//! `h((= x y))` vs `h((pred z))` when `(= x y)` and `(pred z)` are connected
//! only through Bool alias equalities.

/// Seeded minimized regression from the cache_coherence_three_ab_reg_max benchmark.
///
/// The formula is UNSAT because the alias chain forces `(= x y) = (pred z)`:
///   b_alias = (= x y)           -- assertion 1
///   b_alias = b_mid              -- assertion 2
///   b_mid   = (pred z)           -- assertion 3 (seed: non-nullary UF on one side)
/// Therefore `(= x y)` and `(pred z)` must be equal, so `h((= x y))` and
/// `h((pred z))` must be equal by congruence — contradicting assertion 4.
#[test]
fn test_seeded_bool_alias_chain_unsat_6869() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const x U)
(declare-const y U)
(declare-const z U)
(declare-const b_alias Bool)
(declare-const b_mid Bool)
(declare-fun pred (U) Bool)
(declare-fun h (Bool) U)
(assert (= b_alias (= x y)))
(assert (= b_alias b_mid))
(assert (= b_mid (pred z)))
(assert (distinct (h (= x y)) (h (pred z))))
(check-sat)
"#;

    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// Variant without the intermediate b_mid: direct alias.
/// This tests the simpler case where a single Bool variable bridges
/// a raw equality and a UF application.
#[test]
fn test_direct_bool_alias_unsat_6869() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const x U)
(declare-const y U)
(declare-const z U)
(declare-const b Bool)
(declare-fun f (U) Bool)
(declare-fun g (Bool) U)
(assert (= b (= x y)))
(assert (= b (f z)))
(assert (distinct (g (= x y)) (g (f z))))
(check-sat)
"#;

    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// Longer alias chain: 3 hops to reach the UF application.
#[test]
fn test_long_bool_alias_chain_unsat_6869() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b_var U)
(declare-const c U)
(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)
(declare-fun f (U) Bool)
(declare-fun h (Bool) U)
(assert (= p1 (= a b_var)))
(assert (= p1 p2))
(assert (= p2 p3))
(assert (= p3 (f c)))
(assert (distinct (h (= a b_var)) (h (f c))))
(check-sat)
"#;

    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}
