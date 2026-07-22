// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! HWMCC word-level array track tests for CHC solver (#7971).
//!
//! These tests model patterns from HWMCC BTOR2 array benchmarks translated
//! to CHC in SMT-LIB2 HORN logic (as the model-checker consumer's BTOR2-to-CHC translator would
//! produce). HWMCC array track uses BV-indexed arrays with read/write/const_array.
//!
//! Patterns tested:
//! - BV-indexed memory arrays (Array BV32 BV8) with read-after-write
//! - Register files (Array BV5 BV32) with constant-index access
//! - Counter-controlled array initialization loops
//! - Read-over-write with different indices (ROW2 axiom)
//! - Unsafe array overwrite detection
//! - Multi-array BV memory models (tag + data)
//!
//! Tests verify correctness (no false Safe/Unsafe) and absence of crashes.
//! Safe/Unknown are both acceptable on variable-index problems where array
//! MBP may not generalize; Unsafe on provably-safe problems is a soundness bug.

use ay_chc::{testing, PdrConfig, PdrResult};
use ntest::timeout;

/// HWMCC pattern: byte-addressed memory with constant-index read-after-write.
///
/// Memory: (Array BV32 BV8). Init: store #xAB at address #x00000004.
/// Identity transition. Property: select(mem, #x00000004) = #xAB.
///
/// This is scalarizable (constant index) and should be Safe.
#[test]
#[timeout(15_000)]
fn test_hwmcc_memory_byte_read_after_write() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array (_ BitVec 32) (_ BitVec 8)) ) Bool)

; Init: mem[4] = 0xAB
(assert
  (forall ( (M (Array (_ BitVec 32) (_ BitVec 8))) )
    (=>
      (= M (store ((as const (Array (_ BitVec 32) (_ BitVec 8))) #x00) #x00000004 #xAB))
      (inv M)
    )
  )
)

; Trans: identity
(assert
  (forall ( (M (Array (_ BitVec 32) (_ BitVec 8))) )
    (=> (inv M) (inv M))
  )
)

; Bad: mem[4] != 0xAB
(assert
  (forall ( (M (Array (_ BitVec 32) (_ BitVec 8))) )
    (=>
      (and (inv M) (not (= (select M #x00000004) #xAB)))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "Expected Safe for constant-index BV memory read-after-write, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// HWMCC pattern: register file with constant-index access.
///
/// Register file: (Array BV5 BV32) -- 32 registers x 32-bit.
/// Init: regfile[0] = #x00000000.
/// Identity transition. Property: select(regfile, #b00000) = #x00000000.
///
/// Scalarizable, should be Safe.
#[test]
#[timeout(15_000)]
fn test_hwmcc_register_file_init_and_read() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array (_ BitVec 5) (_ BitVec 32)) ) Bool)

; Init: regfile = const(0), r0 = 0 (redundant store for clarity)
(assert
  (forall ( (R (Array (_ BitVec 5) (_ BitVec 32))) )
    (=>
      (= R (store ((as const (Array (_ BitVec 5) (_ BitVec 32))) #x00000000) #b00000 #x00000000))
      (inv R)
    )
  )
)

; Trans: identity
(assert
  (forall ( (R (Array (_ BitVec 5) (_ BitVec 32))) )
    (=> (inv R) (inv R))
  )
)

; Bad: r0 != 0
(assert
  (forall ( (R (Array (_ BitVec 5) (_ BitVec 32))) )
    (=>
      (and (inv R) (not (= (select R #b00000) #x00000000)))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "Expected Safe for constant-index register file access, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// HWMCC pattern: counter-bounded array fill with scalar property.
///
/// Counter cnt (BV32) + validity array (Array BV32 Bool).
/// Init: cnt = 0, arr = const(false).
/// Transition: arr' = store(arr, cnt, true), cnt' = cnt + 1, while cnt < 4.
/// Property: cnt never exceeds 5 (bvugt cnt #x00000005 is false).
///
/// The property depends only on the scalar counter, not the array contents.
/// PDR should prove Safe via the scalar invariant cnt <= 4, or return Unknown.
#[test]
#[timeout(15_000)]
fn test_hwmcc_counter_bounded_array_fill() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array (_ BitVec 32) Bool) (_ BitVec 32) ) Bool)

; Init: arr = const(false), cnt = 0
(assert
  (forall ( (A (Array (_ BitVec 32) Bool)) (C (_ BitVec 32)) )
    (=>
      (and
        (= C #x00000000)
        (= A ((as const (Array (_ BitVec 32) Bool)) false))
      )
      (inv A C)
    )
  )
)

; Trans: store true at cnt, increment cnt, while cnt < 4
(assert
  (forall (
    (A (Array (_ BitVec 32) Bool)) (C (_ BitVec 32))
    (A2 (Array (_ BitVec 32) Bool)) (C2 (_ BitVec 32))
  )
    (=>
      (and
        (inv A C)
        (bvult C #x00000004)
        (= A2 (store A C true))
        (= C2 (bvadd C #x00000001))
      )
      (inv A2 C2)
    )
  )
)

; Bad: cnt > 5
(assert
  (forall ( (A (Array (_ BitVec 32) Bool)) (C (_ BitVec 32)) )
    (=>
      (and (inv A C) (bvugt C #x00000005))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(5));
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved cnt <= 4 < 5
        }
        Ok(PdrResult::Unknown | PdrResult::NotApplicable) => {
            // Acceptable: BV+Array may cause timeout or imprecision
        }
        Ok(PdrResult::Unsafe(_)) => {
            panic!("PDR returned Unsafe for a safe counter-bounded problem -- soundness bug");
        }
        Err(e) => {
            panic!("Counter-bounded array fill parse/setup error: {e}");
        }
        _ => panic!("unexpected variant"),
    }
}

/// HWMCC pattern: read-over-write with different index (ROW2 axiom).
///
/// Memory: (Array BV32 BV8). Init: store #xAA at addr 0.
/// Transition: store #xBB at addr 1 (different address).
/// Property: select(mem, #x00000000) = #xAA.
///
/// This tests the ROW2 axiom: store at index 1 does not affect index 0.
/// Both indices are constant, so scalarization should handle it. Safe.
#[test]
#[timeout(15_000)]
fn test_hwmcc_array_store_preserves_other() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array (_ BitVec 32) (_ BitVec 8)) ) Bool)

; Init: mem[0] = 0xAA
(assert
  (forall ( (M (Array (_ BitVec 32) (_ BitVec 8))) )
    (=>
      (= M (store ((as const (Array (_ BitVec 32) (_ BitVec 8))) #x00) #x00000000 #xAA))
      (inv M)
    )
  )
)

; Trans: store 0xBB at addr 1 (different from addr 0)
(assert
  (forall ( (M (Array (_ BitVec 32) (_ BitVec 8))) (M2 (Array (_ BitVec 32) (_ BitVec 8))) )
    (=>
      (and
        (inv M)
        (= M2 (store M #x00000001 #xBB))
      )
      (inv M2)
    )
  )
)

; Bad: mem[0] != 0xAA
(assert
  (forall ( (M (Array (_ BitVec 32) (_ BitVec 8))) )
    (=>
      (and (inv M) (not (= (select M #x00000000) #xAA)))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(5));
    let result = testing::pdr_solve_from_str(input, config);
    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "Expected Safe for ROW2 different-index store preservation, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// HWMCC pattern: unsafe array overwrite detection.
///
/// Memory: (Array BV32 BV8). Init: store #x42 at addr 0.
/// Transition: overwrite addr 0 with #x00 (destroys invariant).
/// Property: select(mem, #x00000000) = #x42.
///
/// This is UNSAFE: the transition destroys the value at addr 0.
/// PDR should find Unsafe (depth 1) or return Unknown. Safe is a soundness bug.
#[test]
#[timeout(15_000)]
fn test_hwmcc_unsafe_array_overwrite() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array (_ BitVec 32) (_ BitVec 8)) ) Bool)

; Init: mem[0] = 0x42
(assert
  (forall ( (M (Array (_ BitVec 32) (_ BitVec 8))) )
    (=>
      (= M (store ((as const (Array (_ BitVec 32) (_ BitVec 8))) #x00) #x00000000 #x42))
      (inv M)
    )
  )
)

; Trans: overwrite mem[0] with 0x00
(assert
  (forall ( (M (Array (_ BitVec 32) (_ BitVec 8))) (M2 (Array (_ BitVec 32) (_ BitVec 8))) )
    (=>
      (and
        (inv M)
        (= M2 (store M #x00000000 #x00))
      )
      (inv M2)
    )
  )
)

; Bad: mem[0] != 0x42
(assert
  (forall ( (M (Array (_ BitVec 32) (_ BitVec 8))) )
    (=>
      (and (inv M) (not (= (select M #x00000000) #x42)))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(5));
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            panic!(
                "PDR returned Safe for an unsafe array overwrite problem -- soundness bug. \
                 After transition, mem[0] = 0x00 but property requires mem[0] = 0x42."
            );
        }
        Ok(PdrResult::Unsafe(_)) => {
            // Correct: BMC or PDR found the counterexample at depth 1
        }
        Ok(PdrResult::Unknown | PdrResult::NotApplicable) => {
            // Acceptable: solver may not have found the counterexample
        }
        Err(e) => {
            panic!("Unsafe array overwrite parse/setup error: {e}");
        }
        _ => panic!("unexpected variant"),
    }
}

/// HWMCC pattern: dual-array memory model with tag validity.
///
/// Two arrays: tag_valid (Array BV8 Bool) and data (Array BV8 BV16).
/// Init: tag_valid[0] = true, data[0] = #x1234.
/// Identity transition.
/// Property: tag_valid[0] => data[0] = #x1234.
///
/// Tests cross-array invariant reasoning with BV indices.
/// Scalarizable (constant indices). Safe.
#[test]
#[timeout(15_000)]
fn test_hwmcc_multi_array_bv_memory_model() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array (_ BitVec 8) Bool) (Array (_ BitVec 8) (_ BitVec 16)) ) Bool)

; Init: tag_valid[0] = true, data[0] = 0x1234
(assert
  (forall (
    (TV (Array (_ BitVec 8) Bool))
    (D  (Array (_ BitVec 8) (_ BitVec 16)))
  )
    (=>
      (and
        (= TV (store ((as const (Array (_ BitVec 8) Bool)) false) #x00 true))
        (= D  (store ((as const (Array (_ BitVec 8) (_ BitVec 16))) #x0000) #x00 #x1234))
      )
      (inv TV D)
    )
  )
)

; Trans: identity
(assert
  (forall (
    (TV (Array (_ BitVec 8) Bool))
    (D  (Array (_ BitVec 8) (_ BitVec 16)))
  )
    (=> (inv TV D) (inv TV D))
  )
)

; Bad: tag_valid[0] = true but data[0] != 0x1234
(assert
  (forall (
    (TV (Array (_ BitVec 8) Bool))
    (D  (Array (_ BitVec 8) (_ BitVec 16)))
  )
    (=>
      (and
        (inv TV D)
        (select TV #x00)
        (not (= (select D #x00) #x1234))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(5));
    let result = testing::pdr_solve_from_str(input, config);
    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "Expected Safe for dual-array BV memory model with identity transition, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}
