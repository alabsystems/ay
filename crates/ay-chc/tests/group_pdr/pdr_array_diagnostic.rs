// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Diagnostic test to check actual PDR results for array-sorted problems.
//! This test prints the verdict (Safe/Unknown/Unsafe) to help diagnose
//! what's blocking Safe verdicts on model-checker-consumer-style benchmarks.

use ay_chc::{testing, PdrConfig, PdrResult};
use ntest::timeout;

#[test]
#[timeout(15_000)]
fn diag_const_index_scalarizable() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ( (Array Int Int) ) Bool)
(assert
  (forall ( (A (Array Int Int)) )
    (=>
      (= A (store ((as const (Array Int Int)) 0) 0 42))
      (inv A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) )
    (=>
      (and (inv A) (not (= (select A 0) 42)))
      false
    )
  )
)
(check-sat)
(exit)
"#;
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match &result {
        Ok(PdrResult::Safe(_)) => eprintln!("diag_const_index: SAFE"),
        Ok(PdrResult::Unknown) => eprintln!("diag_const_index: UNKNOWN"),
        Ok(PdrResult::Unsafe(_)) => eprintln!("diag_const_index: UNSAFE (BUG)"),
        Ok(PdrResult::NotApplicable) => eprintln!("diag_const_index: NOT_APPLICABLE"),
        Err(e) => eprintln!("diag_const_index: ERROR: {e}"),
        Ok(_) => eprintln!("diag_const_index: OTHER"),
    }
    assert!(
        matches!(result, Ok(PdrResult::Safe(_))),
        "Expected Safe for constant-index scalarizable problem, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

#[test]
#[timeout(15_000)]
fn diag_var_index_scalar_invariant() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ( (Array Int Bool) Int ) Bool)
(assert
  (forall ( (V (Array Int Bool)) (C Int) )
    (=>
      (and (= C 0) (= V ((as const (Array Int Bool)) false)))
      (inv V C)
    )
  )
)
(assert
  (forall ( (V (Array Int Bool)) (C Int) (V2 (Array Int Bool)) (C2 Int) )
    (=>
      (and
        (inv V C)
        (>= C 0)
        (<= C 100)
        (= V2 (store V C true))
        (= C2 (+ C 1))
      )
      (inv V2 C2)
    )
  )
)
(assert
  (forall ( (V (Array Int Bool)) (C Int) )
    (=>
      (and (inv V C) (< C 0))
      false
    )
  )
)
(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(10));
    let result = testing::pdr_solve_from_str(input, config);
    match &result {
        Ok(PdrResult::Safe(_)) => eprintln!("diag_var_index_scalar: SAFE"),
        Ok(PdrResult::Unknown) => eprintln!("diag_var_index_scalar: UNKNOWN"),
        Ok(PdrResult::Unsafe(_)) => eprintln!("diag_var_index_scalar: UNSAFE (BUG)"),
        Ok(PdrResult::NotApplicable) => eprintln!("diag_var_index_scalar: NOT_APPLICABLE"),
        Err(e) => eprintln!("diag_var_index_scalar: ERROR: {e}"),
        Ok(_) => eprintln!("diag_var_index_scalar: OTHER"),
    }
    // The invariant is C >= 0, which is purely scalar.
    // PDR should be able to prove this even with array predicate params.
    assert!(
        matches!(result, Ok(PdrResult::Safe(_))),
        "Expected Safe for variable-index problem with scalar invariant (C >= 0), got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

#[test]
#[timeout(30_000)]
fn diag_const_index_array_invariant() {
    // This problem requires an array-content invariant: select(arr, 0) = true
    // The property is about array contents, not just scalars.
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ( (Array Int Bool) Int ) Bool)

; Init: arr[0] = true, count = 1
(assert
  (forall ( (V (Array Int Bool)) (C Int) )
    (=>
      (and (= C 1) (= V (store ((as const (Array Int Bool)) false) 0 true)))
      (inv V C)
    )
  )
)

; Trans: arr' = store(arr, count, true), count' = count + 1
(assert
  (forall ( (V (Array Int Bool)) (C Int) (V2 (Array Int Bool)) (C2 Int) )
    (=>
      (and
        (inv V C)
        (= V2 (store V C true))
        (= C2 (+ C 1))
        (<= C 10)
      )
      (inv V2 C2)
    )
  )
)

; Bad: arr[0] is false
(assert
  (forall ( (V (Array Int Bool)) (C Int) )
    (=>
      (and (inv V C) (not (select V 0)))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(10));
    let result = testing::pdr_solve_from_str(input, config);
    match &result {
        Ok(PdrResult::Safe(_)) => eprintln!("diag_const_index_array_inv: SAFE"),
        Ok(PdrResult::Unknown) => eprintln!("diag_const_index_array_inv: UNKNOWN"),
        Ok(PdrResult::Unsafe(_)) => eprintln!("diag_const_index_array_inv: UNSAFE (BUG)"),
        Ok(PdrResult::NotApplicable) => eprintln!("diag_const_index_array_inv: NOT_APPLICABLE"),
        Err(e) => eprintln!("diag_const_index_array_inv: ERROR: {e}"),
        Ok(_) => eprintln!("diag_const_index_array_inv: OTHER"),
    }
    // Property: select(arr, 0) = true. This requires an array-content invariant.
    // Scalarization converts arr[0] to a scalar variable, making this solvable.
    // PDR successfully proves Safe on this problem (verified 2026-03-06).
    assert!(
        matches!(result, Ok(PdrResult::Safe(_))),
        "Expected Safe for constant-index array invariant problem, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}
