// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for issue #8675: false SAFE on array store/select systems.
//!
//! PDR was incorrectly promoting array equalities like `(= arr (store const(0) 0 64))`
//! from init constraints to frame[1] as inductive invariants. These equalities pin
//! the entire array to its initial value, which is NOT inductive when transitions
//! modify the array via store operations. The SMT self-inductiveness check could
//! return false UNSAT for complex array formulas, allowing non-inductive array
//! equalities to slip through and produce false SAFE results.
//!
//! The fix filters array equalities from invariant admission in
//! `add_discovered_invariant_impl` (admission.rs) and from fact clause conjunct
//! promotion (fact_joint.rs).

use ay_chc::{engines, ChcParser, PortfolioConfig, PortfolioResult};
use ntest::timeout;
use std::time::Duration;

/// Core regression: array equalities must not produce false SAFE.
///
/// This system has:
/// - Init: obj_size = store(const(0), 0, 64), obj_flags = store(const(0), 0, 1)
/// - Transition: modifies obj_size[1] each iteration (NOT obj_size[0])
/// - Error: reachable when ctr >= 2 AND select(obj_size, 0) != 32
///
/// Since obj_size[0] = 64 and 64 != 32, the error IS reachable (UNSAFE).
/// Before the fix, PDR incorrectly promoted the array equality as inductive
/// and returned SAFE.
#[test]
#[timeout(30_000)]
fn test_no_false_safe_on_array_store_system_8675() {
    let smt = r#"
(set-logic HORN)
(declare-fun Inv ((Array Int Int) (Array Int Int) Int Int) Bool)

; Init: obj_size[0]=64, obj_flags[0]=1, id=0, ctr=0
(assert (forall ((obj_size (Array Int Int)) (obj_flags (Array Int Int)) (id Int) (ctr Int))
  (=> (and (= id 0)
           (= ctr 0)
           (= obj_size (store ((as const (Array Int Int)) 0) 0 64))
           (= obj_flags (store ((as const (Array Int Int)) 0) 0 1)))
      (Inv obj_size obj_flags id ctr))))

; Transition: modify obj_size[1], increment ctr
(assert (forall ((obj_size (Array Int Int)) (obj_flags (Array Int Int))
                 (id Int) (ctr Int)
                 (obj_size2 (Array Int Int)) (ctr2 Int))
  (=> (and (Inv obj_size obj_flags id ctr)
           (< ctr 3)
           (= ctr2 (+ ctr 1))
           (= obj_size2 (store obj_size 1 ctr)))
      (Inv obj_size2 obj_flags id ctr2))))

; Error: reachable when ctr >= 2 and obj_size[id] != 32
(assert (forall ((obj_size (Array Int Int)) (obj_flags (Array Int Int))
                 (id Int) (ctr Int))
  (=> (and (Inv obj_size obj_flags id ctr)
           (>= ctr 2)
           (not (= (select obj_size id) 32)))
      false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt).expect("parse failed");

    // Use test_default() (PDR + BMC + Kind) to reduce thread count from 12 to 3.
    // This is sufficient for this soundness regression test.
    let config = PortfolioConfig::test_default().parallel_timeout(Some(Duration::from_secs(15)));

    let solver = engines::new_portfolio_solver(problem, config);
    let result = solver.solve();

    // Must NOT return Safe. The error is reachable (UNSAFE).
    // Acceptable results: Unsafe (correct) or Unknown (incomplete but sound).
    assert!(
        !matches!(result, PortfolioResult::Safe(_)),
        "SOUNDNESS BUG #8675: Solver returned false SAFE on array system where error is reachable. \
         Array equality invariants were incorrectly promoted as inductive."
    );
}
