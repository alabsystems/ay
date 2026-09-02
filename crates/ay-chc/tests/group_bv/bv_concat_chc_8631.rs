// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! CHC integration tests for BvConcat parsing and solving (#8631).
//!
//! Verifies that `(concat ...)` is correctly parsed through the ay-chc parser,
//! lowered to the SMT term store, and solved. This is the code path model-checker-consumer uses
//! for memory address construction in loop harnesses.
//!
//! Part of #8631: BvConcat parser support needed by model-checker-consumer.

use ay_chc::{
    AdaptiveConfig, AdaptivePortfolio, ChcParser, ChcSort, SmtValue, VerifiedChcResult,
    MAX_BITVECTOR_WIDTH,
};
use num_bigint::{BigInt, BigUint};
use std::sync::mpsc;
use std::time::Duration;

/// Simple CHC with concat in the transition relation.
/// State has two 8-bit BVs, transition concatenates them and compares to constant.
/// This is safe (SAT) because the invariant can be found (x stays bounded).
const CONCAT_SAFE_BENCHMARK: &str = r#"(set-logic HORN)

(declare-fun |inv| ((_ BitVec 8) (_ BitVec 8)) Bool)

; Initial: x=0, y=0
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=>
      (and (= x #x00) (= y #x00))
      (inv x y)
    )
  )
)

; Transition: if concat(x,y) < #xFF00, increment x
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (x2 (_ BitVec 8)) (y2 (_ BitVec 8)))
    (=>
      (and
        (inv x y)
        (bvult (concat x y) #xFF00)
        (= x2 (bvadd x #x01))
        (= y2 y)
      )
      (inv x2 y2)
    )
  )
)

; Property: concat(x,y) is always <= #xFF00
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=>
      (and (inv x y) (bvugt (concat x y) #xFF00))
      false
    )
  )
)

(check-sat)
"#;

/// CHC with concat that is unsafe (UNSAT).
/// The property claims concat never reaches #x0500 but the loop goes past it.
const CONCAT_UNSAFE_BENCHMARK: &str = r#"(set-logic HORN)

(declare-fun |inv| ((_ BitVec 8) (_ BitVec 8)) Bool)

; Initial: x=0, y=0
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=>
      (and (= x #x00) (= y #x00))
      (inv x y)
    )
  )
)

; Transition: increment x
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (x2 (_ BitVec 8)) (y2 (_ BitVec 8)))
    (=>
      (and
        (inv x y)
        (= x2 (bvadd x #x01))
        (= y2 y)
      )
      (inv x2 y2)
    )
  )
)

; Property: concat(x,y) < #x0500 (this is violated when x >= 5)
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=>
      (and (inv x y) (not (bvult (concat x y) #x0500)))
      false
    )
  )
)

(check-sat)
"#;

/// Soundness test for CHC with concat: safe benchmark.
///
/// Uses a thread+channel timeout like bv_chc_soundness_6848 to handle
/// potential budget overrun in BV portfolio.
#[test]
#[serial_test::serial]
fn test_chc_bv_concat_safe_8631() {
    let problem = ChcParser::parse(CONCAT_SAFE_BENCHMARK)
        .unwrap_or_else(|e| panic!("CHC parse with concat failed: {e}"));

    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(15));
        let solver = AdaptivePortfolio::new(problem, config);
        let result = solver.solve();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(Duration::from_secs(30)) {
        Ok(result) => {
            // Safe or Unknown are both acceptable.
            // Unsafe would be a soundness bug (the property holds).
            assert!(
                !matches!(result, VerifiedChcResult::Unsafe(_)),
                "#8631: concat safe benchmark is SAFE. Got Unsafe — soundness bug."
            );
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Timeout is acceptable — BV CHC solving may be slow.
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("#8631: solver thread panicked or disconnected");
        }
    }
}

/// Soundness test for CHC with concat: unsafe benchmark.
///
/// The property is violated. If the solver returns Safe, that's a soundness bug.
#[test]
#[serial_test::serial]
fn test_chc_bv_concat_unsafe_8631() {
    let problem = ChcParser::parse(CONCAT_UNSAFE_BENCHMARK)
        .unwrap_or_else(|e| panic!("CHC parse with concat failed: {e}"));

    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(15));
        let solver = AdaptivePortfolio::new(problem, config);
        let result = solver.solve();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(Duration::from_secs(30)) {
        Ok(result) => {
            // Unsafe or Unknown are both acceptable.
            // Safe would be a soundness bug.
            assert!(
                !matches!(result, VerifiedChcResult::Safe(_)),
                "#8631: concat unsafe benchmark is UNSAFE. Got Safe — soundness bug."
            );
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Timeout is acceptable
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("#8631: solver thread panicked or disconnected");
        }
    }
}

/// Verify that the CHC parser correctly handles concat at the expression level.
/// This test just checks parsing succeeds — solving is tested above.
#[test]
#[serial_test::serial]
fn test_chc_bv_concat_parsing_8631() {
    let input = r#"(set-logic HORN)
(declare-fun |p| ((_ BitVec 16)) Bool)
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (= (concat x y) #xFFFF) (p (concat x y)))))
(assert (forall ((z (_ BitVec 16))) (=> (p z) (not (= z #x0000)))))
(check-sat)
"#;
    let problem =
        ChcParser::parse(input).unwrap_or_else(|e| panic!("CHC parse with concat failed: {e}"));
    assert!(
        !problem.clauses().is_empty(),
        "Parsed CHC problem should have clauses"
    );
}

#[test]
fn checked_public_wide_model_value_api_is_exact_and_bounded() {
    let value: BigUint = (BigUint::from(1_u8) << 128_usize) | BigUint::from(3_u8);
    let model_value = SmtValue::try_bitvec_from_biguint(value.clone(), 129)
        .expect("129-bit public model values are supported");
    assert_eq!(model_value.bitvec_to_biguint(), Some((value, 129)));
    assert_eq!(
        model_value
            .bitvec_to_chc_expr()
            .expect("bounded model value reconstructs")
            .sort(),
        ChcSort::BitVec(129)
    );

    let negative = SmtValue::try_bitvec_from_bigint(BigInt::from(-1), 129)
        .expect("signed public construction uses modulo semantics");
    assert_eq!(
        negative.bitvec_to_biguint(),
        Some(((BigUint::from(1_u8) << 129) - BigUint::from(1_u8), 129))
    );

    assert!(SmtValue::try_bitvec_from_u128(0, 0).is_err());
    assert!(SmtValue::try_bitvec_from_bigint(BigInt::from(-1), MAX_BITVECTOR_WIDTH + 1,).is_err());
    assert_eq!(SmtValue::BitVec(0, 0).bitvec_to_biguint(), None);
    assert_eq!(
        SmtValue::BigBitVec(
            std::sync::Arc::new(BigUint::from(0_u8)),
            MAX_BITVECTOR_WIDTH + 1,
        )
        .bitvec_to_biguint(),
        None
    );
}
