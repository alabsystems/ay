// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]
#![allow(unreachable_patterns)]

//! Diagnostic test (part 2): harder array cases closer to model-checker-consumer harnesses.

use ay_chc::{testing, PdrConfig, PdrResult};
use ntest::timeout;

/// BV-indexed array with constant index (scalarizable).
/// Models: obj_valid[0] = true, check obj_valid[0] after identity transition.
#[test]
#[timeout(15_000)]
fn diag_bv_const_index() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ( (Array (_ BitVec 32) Bool) ) Bool)

(assert
  (forall ( (V (Array (_ BitVec 32) Bool)) )
    (=>
      (= V (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000000 true))
      (inv V)
    )
  )
)

(assert
  (forall ( (V (Array (_ BitVec 32) Bool)) )
    (=>
      (and (inv V) (not (select V #x00000000)))
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
        Ok(PdrResult::Safe(_)) => eprintln!("diag_bv_const_index: SAFE"),
        Ok(PdrResult::Unknown) => eprintln!("diag_bv_const_index: UNKNOWN"),
        Ok(PdrResult::Unsafe(_)) => eprintln!("diag_bv_const_index: UNSAFE (BUG)"),
        Ok(PdrResult::NotApplicable) => eprintln!("diag_bv_const_index: NOT_APPLICABLE"),
        Err(e) => eprintln!("diag_bv_const_index: ERROR: {e}"),
        Ok(_) => eprintln!("diag_bv_const_index: OTHER"),
    }
    // BV-indexed arrays are not scalarized since #6163 (arity explosion, #6047).
    // Without native BV array support, PDR returns Unknown. Accept Safe or Unknown.
    assert!(
        matches!(result, Ok(PdrResult::Safe(_)) | Ok(PdrResult::Unknown)),
        "Expected Safe or Unknown for BV constant-index problem, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// Two BV-indexed arrays with cross-array invariant.
/// Init: obj_valid[0] = true, mem[0x0] = 0xAA
/// Property: if obj_valid[0] then mem[0x0] = 0xAA
/// All constant indices — should be fully scalarizable.
#[test]
#[timeout(15_000)]
fn diag_two_bv_arrays_const_index() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 64) (_ BitVec 8))
) Bool)

(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
  )
    (=>
      (and
        (= ov (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000000 true))
        (= m  (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) #x0000000000000000 #xAA))
      )
      (inv ov m)
    )
  )
)

; Identity transition
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
  )
    (=> (inv ov m) (inv ov m))
  )
)

; Bad: obj_valid[0] = true but mem[0] != 0xAA
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
  )
    (=>
      (and
        (inv ov m)
        (select ov #x00000000)
        (not (= (select m #x0000000000000000) #xAA))
      )
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
        Ok(PdrResult::Safe(_)) => eprintln!("diag_two_bv_arrays: SAFE"),
        Ok(PdrResult::Unknown) => eprintln!("diag_two_bv_arrays: UNKNOWN"),
        Ok(PdrResult::Unsafe(_)) => eprintln!("diag_two_bv_arrays: UNSAFE (BUG)"),
        Ok(PdrResult::NotApplicable) => eprintln!("diag_two_bv_arrays: NOT_APPLICABLE"),
        Err(e) => eprintln!("diag_two_bv_arrays: ERROR: {e}"),
        Ok(_) => eprintln!("diag_two_bv_arrays: OTHER"),
    }
    // BV-indexed arrays are not scalarized since #6163 (arity explosion, #6047).
    // Without native BV array support, PDR returns Unknown. Accept Safe or Unknown.
    assert!(
        matches!(result, Ok(PdrResult::Safe(_)) | Ok(PdrResult::Unknown)),
        "Expected Safe or Unknown for two-BV-array constant-index problem, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// model-checker-consumer-style harness: allocate object, write to memory, check validity + memory.
/// This is closer to a real model-checker-consumer harness with obj_valid, obj_size, mem arrays.
/// Uses an actual transition (not identity).
#[test]
#[timeout(15_000)]
fn diag_model_checker_consumer_allocate_write_check() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 32) (_ BitVec 32))
  (Array (_ BitVec 64) (_ BitVec 8))
  (_ BitVec 32)
) Bool)

; Init: allocate obj 0, size 4, write 0x42 at mem[0]
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (= ov (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000000 true))
        (= os (store ((as const (Array (_ BitVec 32) (_ BitVec 32))) #x00000000) #x00000000 #x00000004))
        (= m  (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) #x0000000000000000 #x42))
        (= cnt #x00000001)
      )
      (inv ov os m cnt)
    )
  )
)

; Identity transition (no modification)
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=> (inv ov os m cnt) (inv ov os m cnt))
  )
)

; Bad: obj_valid[0] = true but mem[0] != 0x42
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (inv ov os m cnt)
        (select ov #x00000000)
        (not (= (select m #x0000000000000000) #x42))
      )
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
        Ok(PdrResult::Safe(_)) => eprintln!("diag_model_checker_consumer_alloc_write: SAFE"),
        Ok(PdrResult::Unknown) => eprintln!("diag_model_checker_consumer_alloc_write: UNKNOWN"),
        Ok(PdrResult::Unsafe(_)) => {
            eprintln!("diag_model_checker_consumer_alloc_write: UNSAFE (BUG)")
        }
        Ok(PdrResult::NotApplicable) => {
            eprintln!("diag_model_checker_consumer_alloc_write: NOT_APPLICABLE")
        }
        Err(e) => eprintln!("diag_model_checker_consumer_alloc_write: ERROR: {e}"),
        Ok(_) => eprintln!("diag_model_checker_consumer_alloc_write: OTHER"),
    }
    // BV-indexed arrays are not scalarized since #6163 (arity explosion, #6047).
    // Without native BV array support, PDR returns Unknown. Accept Safe or Unknown.
    assert!(
        matches!(result, Ok(PdrResult::Safe(_)) | Ok(PdrResult::Unknown)),
        "Expected Safe or Unknown for model-checker-consumer allocate-write-check problem, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// model-checker-consumer-style: variable-index allocation in a loop with BV arrays.
/// This is NOT scalarizable because the store index is a variable.
/// Init: count = 0, all arrays default
/// Trans: obj_valid' = store(obj_valid, count, true), count' = count + 1
/// Property: count >= 0 (scalar invariant, despite array parameters)
#[test]
#[timeout(15_000)]
fn diag_model_checker_consumer_loop_alloc_scalar_prop() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| (
  (Array (_ BitVec 32) Bool)
  (_ BitVec 32)
) Bool)

; Init: obj_valid = const(false), count = 0
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (= cnt #x00000000)
        (= ov ((as const (Array (_ BitVec 32) Bool)) false))
      )
      (inv ov cnt)
    )
  )
)

; Trans: obj_valid' = store(obj_valid, count, true), count' = bvadd(count, 1)
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (cnt (_ BitVec 32))
    (ov2 (Array (_ BitVec 32) Bool))
    (cnt2 (_ BitVec 32))
  )
    (=>
      (and
        (inv ov cnt)
        (bvult cnt #x0000000A)
        (= ov2 (store ov cnt true))
        (= cnt2 (bvadd cnt #x00000001))
      )
      (inv ov2 cnt2)
    )
  )
)

; Bad: count > 0x0B (impossible — bounded loop 0..0xA)
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (inv ov cnt)
        (bvugt cnt #x0000000B)
      )
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
        Ok(PdrResult::Safe(_)) => eprintln!("diag_model_checker_consumer_loop_scalar: SAFE"),
        Ok(PdrResult::Unknown) => eprintln!("diag_model_checker_consumer_loop_scalar: UNKNOWN"),
        Ok(PdrResult::Unsafe(_)) => {
            eprintln!("diag_model_checker_consumer_loop_scalar: UNSAFE (BUG)")
        }
        Ok(PdrResult::NotApplicable) => {
            eprintln!("diag_model_checker_consumer_loop_scalar: NOT_APPLICABLE")
        }
        Err(e) => eprintln!("diag_model_checker_consumer_loop_scalar: ERROR: {e}"),
        Ok(_) => eprintln!("diag_model_checker_consumer_loop_scalar: OTHER"),
    }
    // Scalar invariant (count <= 0x0B) should be findable even with array params
    assert!(
        matches!(result, Ok(PdrResult::Safe(_))),
        "Expected Safe for model-checker-consumer loop-alloc with scalar property, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// model-checker-consumer-style: symbolic store in transition, ARRAY property at constant index.
/// This is the core model-checker-consumer pattern that drives #6047:
/// - Init: obj_valid = store(const(false), 0, true), mem = store(const(0), 0, 0x42)
/// - Trans: symbolic allocation at variable index (obj_valid' = store(ov, idx, true))
/// - Property: obj_valid[0] still true AND mem[0] still 0x42
///
/// The property only checks constant indices, but the transition uses symbolic
/// indices. Scalarization is blocked because of the symbolic store. This needs
/// the executor adapter + MBP to handle array ops during PDR.
#[test]
#[timeout(15_000)]
fn diag_model_checker_consumer_symbolic_store_const_property() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 32) (_ BitVec 8))
  (_ BitVec 32)
) Bool)

; Init: obj_valid[0] = true, mem[0] = 0x42, count = 1
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 32) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (= ov (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000000 true))
        (= m  (store ((as const (Array (_ BitVec 32) (_ BitVec 8))) #x00) #x00000000 #x42))
        (= cnt #x00000001)
      )
      (inv ov m cnt)
    )
  )
)

; Trans: allocate at index=count (symbolic store), increment count.
; Memory at index 0 is NOT modified — only new indices get written.
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 32) (_ BitVec 8)))
    (cnt (_ BitVec 32))
    (ov2 (Array (_ BitVec 32) Bool))
    (m2  (Array (_ BitVec 32) (_ BitVec 8)))
    (cnt2 (_ BitVec 32))
  )
    (=>
      (and
        (inv ov m cnt)
        (bvult cnt #x0000000A)
        (= ov2 (store ov cnt true))
        (= m2  (store m cnt #xAA))
        (= cnt2 (bvadd cnt #x00000001))
      )
      (inv ov2 m2 cnt2)
    )
  )
)

; Bad: obj_valid[0] = true but mem[0] != 0x42
; This is safe because init sets mem[0]=0x42 and transitions only store
; at index >= 1 (cnt starts at 1, stored at cnt before increment).
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 32) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (inv ov m cnt)
        (select ov #x00000000)
        (not (= (select m #x00000000) #x42))
      )
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
        Ok(PdrResult::Safe(_)) => eprintln!("diag_model_checker_consumer_symbolic_store: SAFE"),
        Ok(PdrResult::Unknown) => eprintln!("diag_model_checker_consumer_symbolic_store: UNKNOWN"),
        Ok(PdrResult::Unsafe(_)) => {
            eprintln!("diag_model_checker_consumer_symbolic_store: UNSAFE (BUG)")
        }
        Ok(PdrResult::NotApplicable) => {
            eprintln!("diag_model_checker_consumer_symbolic_store: NOT_APPLICABLE")
        }
        Err(e) => eprintln!("diag_model_checker_consumer_symbolic_store: ERROR: {e}"),
        Ok(_) => eprintln!("diag_model_checker_consumer_symbolic_store: OTHER"),
    }
    // This is the core model-checker-consumer pattern. With BV arrays, scalarization is blocked.
    // Accept Safe (ideal) or Unknown (current expected behavior until BV array
    // support matures). Unsafe would be a soundness bug.
    assert!(
        matches!(result, Ok(PdrResult::Safe(_)) | Ok(PdrResult::Unknown)),
        "Expected Safe or Unknown for model-checker-consumer symbolic-store test, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// Full model-checker-consumer harness pattern: 3 arrays (obj_valid, obj_size, mem) + scalar count.
/// Init: allocate object 0 (valid=true, size=4, write 0x42 to mem[0]).
/// Trans: allocate object at index=count (cnt >= 1), set valid, size, and mem.
///        The transition stores at cnt (symbolic, >= 1), never touching index 0.
/// Property: obj_valid[0] AND obj_size[0] >= 1 AND mem[0] = 0x42.
///
/// This mirrors the model-checker-consumer --ay-chc-track=mem pattern with cross-array invariant.
#[test]
#[timeout(15_000)]
fn diag_model_checker_consumer_three_arrays_cross_invariant() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 32) (_ BitVec 32))
  (Array (_ BitVec 32) (_ BitVec 8))
  (_ BitVec 32)
) Bool)

; Init: obj 0 is allocated (valid=true, size=4, mem[0]=0x42), count=1
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 32) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (= ov (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000000 true))
        (= os (store ((as const (Array (_ BitVec 32) (_ BitVec 32))) #x00000000) #x00000000 #x00000004))
        (= m  (store ((as const (Array (_ BitVec 32) (_ BitVec 8))) #x00) #x00000000 #x42))
        (= cnt #x00000001)
      )
      (inv ov os m cnt)
    )
  )
)

; Trans: allocate object at index=count (count >= 1)
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 32) (_ BitVec 8)))
    (cnt (_ BitVec 32))
    (ov2 (Array (_ BitVec 32) Bool))
    (os2 (Array (_ BitVec 32) (_ BitVec 32)))
    (m2  (Array (_ BitVec 32) (_ BitVec 8)))
    (cnt2 (_ BitVec 32))
  )
    (=>
      (and
        (inv ov os m cnt)
        (bvult cnt #x0000000A)
        (= ov2 (store ov cnt true))
        (= os2 (store os cnt #x00000008))
        (= m2  (store m cnt #xAA))
        (= cnt2 (bvadd cnt #x00000001))
      )
      (inv ov2 os2 m2 cnt2)
    )
  )
)

; Bad: obj_valid[0] AND (obj_size[0] < 1 OR mem[0] != 0x42)
; This should be safe: init sets size=4 and mem=0x42 for index 0,
; and transitions only write at index >= 1.
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 32) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (inv ov os m cnt)
        (select ov #x00000000)
        (or
          (bvult (select os #x00000000) #x00000001)
          (not (= (select m #x00000000) #x42))
        )
      )
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
        Ok(PdrResult::Safe(_)) => eprintln!("diag_model_checker_consumer_three_arrays: SAFE"),
        Ok(PdrResult::Unknown) => eprintln!("diag_model_checker_consumer_three_arrays: UNKNOWN"),
        Ok(PdrResult::Unsafe(_)) => {
            eprintln!("diag_model_checker_consumer_three_arrays: UNSAFE (BUG)")
        }
        Ok(PdrResult::NotApplicable) => {
            eprintln!("diag_model_checker_consumer_three_arrays: NOT_APPLICABLE")
        }
        Err(e) => eprintln!("diag_model_checker_consumer_three_arrays: ERROR: {e}"),
        Ok(_) => eprintln!("diag_model_checker_consumer_three_arrays: OTHER"),
    }
    // Full cross-array invariant. Accept Safe or Unknown.
    // Unsafe would be a soundness bug.
    assert!(
        matches!(result, Ok(PdrResult::Safe(_)) | Ok(PdrResult::Unknown)),
        "Expected Safe or Unknown for three-array cross-invariant test, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// Same as diag_model_checker_consumer_three_arrays but with BV64 memory indices (real model-checker-consumer pattern).
/// Real model-checker-consumer harnesses use BV64 for memory addresses. Tests whether
/// the BV64 key sort causes bit-blast explosion in the executor adapter.
#[test]
#[timeout(15_000)]
fn diag_model_checker_consumer_bv64_memory_indices() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 64) (_ BitVec 8))
  (_ BitVec 32)
) Bool)

; Init: obj_valid[0] = true, mem[0x0] = 0x42, count = 1
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (= ov (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000000 true))
        (= m  (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) #x0000000000000000 #x42))
        (= cnt #x00000001)
      )
      (inv ov m cnt)
    )
  )
)

; Trans: allocate at index=count with BV64 zero-extension for memory
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
    (ov2 (Array (_ BitVec 32) Bool))
    (m2  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt2 (_ BitVec 32))
  )
    (=>
      (and
        (inv ov m cnt)
        (bvult cnt #x0000000A)
        (= ov2 (store ov cnt true))
        (= m2  (store m ((_ zero_extend 32) cnt) #xAA))
        (= cnt2 (bvadd cnt #x00000001))
      )
      (inv ov2 m2 cnt2)
    )
  )
)

; Bad: obj_valid[0] AND mem[0x0] != 0x42
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (inv ov m cnt)
        (select ov #x00000000)
        (not (= (select m #x0000000000000000) #x42))
      )
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
        Ok(PdrResult::Safe(_)) => eprintln!("diag_model_checker_consumer_bv64_mem: SAFE"),
        Ok(PdrResult::Unknown) => eprintln!("diag_model_checker_consumer_bv64_mem: UNKNOWN"),
        Ok(PdrResult::Unsafe(_)) => eprintln!("diag_model_checker_consumer_bv64_mem: UNSAFE (BUG)"),
        Ok(PdrResult::NotApplicable) => {
            eprintln!("diag_model_checker_consumer_bv64_mem: NOT_APPLICABLE")
        }
        Err(e) => eprintln!("diag_model_checker_consumer_bv64_mem: ERROR: {e}"),
        Ok(_) => eprintln!("diag_model_checker_consumer_bv64_mem: OTHER"),
    }
    // BV64 memory may cause bit-blast explosion in executor adapter.
    // Accept Safe (ideal) or Unknown. Unsafe would be a soundness bug.
    assert!(
        matches!(result, Ok(PdrResult::Safe(_)) | Ok(PdrResult::Unknown)),
        "Expected Safe or Unknown for BV64 memory indices test, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// Multi-predicate BV array test modeled after model-checker-consumer harness structure.
/// Two basic blocks (bb0 → bb1), obj_valid + obj_size + mem arrays,
/// with dead-param-elimination and inlining opportunities.
///
/// bb0: initialize allocation metadata (obj_valid[1]=true, obj_size[1]=4)
/// bb1: write to memory and check property
/// Property: obj_valid[1] should be true (always holds by construction)
///
/// This tests the full PDR pipeline on model-checker-consumer-like BV array problems:
/// sort gate acceptance, scalarization, dead-param-elim, inlining,
/// and either BMC or PDR proving the property.
#[test]
#[timeout(15_000)]
fn diag_model_checker_consumer_multi_bb_alloc_pattern() {
    let input = r#"
(set-logic HORN)
(declare-fun bb0 (Bool (_ BitVec 32) (Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32)) (Array (_ BitVec 64) (_ BitVec 8))) Bool)
(declare-fun bb1 (Bool (_ BitVec 32) (Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32)) (Array (_ BitVec 64) (_ BitVec 8))) Bool)

; Init -> bb0: set up allocation, obj_valid[1]=true, obj_size[1]=4
(assert (forall (
  (v0 Bool) (v1 (_ BitVec 32))
  (ov_out (Array (_ BitVec 32) Bool))
  (os_out (Array (_ BitVec 32) (_ BitVec 32)))
  (m (Array (_ BitVec 64) (_ BitVec 8)))
)
  (=>
    (and
      (= ov_out (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000001 true))
      (= os_out (store ((as const (Array (_ BitVec 32) (_ BitVec 32))) #x00000000) #x00000001 #x00000004))
    )
    (bb0 v0 v1 ov_out os_out m)
  )
))

; bb0 -> bb1: write 0x42 to mem at byte offset 0
(assert (forall (
  (v0 Bool) (v1 (_ BitVec 32))
  (ov (Array (_ BitVec 32) Bool))
  (os (Array (_ BitVec 32) (_ BitVec 32)))
  (m (Array (_ BitVec 64) (_ BitVec 8)))
  (m_out (Array (_ BitVec 64) (_ BitVec 8)))
)
  (=>
    (and
      (bb0 v0 v1 ov os m)
      (select ov #x00000001)
      (= m_out (store m #x0000000000000000 #x42))
    )
    (bb1 v0 v1 ov os m_out)
  )
))

; Property 1: bb1 AND NOT obj_valid[1] => false (should be unreachable)
(assert (forall (
  (v0 Bool) (v1 (_ BitVec 32))
  (ov (Array (_ BitVec 32) Bool))
  (os (Array (_ BitVec 32) (_ BitVec 32)))
  (m (Array (_ BitVec 64) (_ BitVec 8)))
)
  (=>
    (and
      (bb1 v0 v1 ov os m)
      (not (select ov #x00000001))
    )
    false
  )
))

; Property 2: bb1 AND mem[0] != 0x42 => false (should be unreachable)
(assert (forall (
  (v0 Bool) (v1 (_ BitVec 32))
  (ov (Array (_ BitVec 32) Bool))
  (os (Array (_ BitVec 32) (_ BitVec 32)))
  (m (Array (_ BitVec 64) (_ BitVec 8)))
)
  (=>
    (and
      (bb1 v0 v1 ov os m)
      (not (= (select m #x0000000000000000) #x42))
    )
    false
  )
))

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(10));
    let result = testing::pdr_solve_from_str(input, config);
    match &result {
        Ok(PdrResult::Safe(_)) => {
            eprintln!("diag_model_checker_consumer_multi_bb_alloc_pattern: SAFE")
        }
        Ok(PdrResult::Unknown) => {
            eprintln!("diag_model_checker_consumer_multi_bb_alloc_pattern: UNKNOWN")
        }
        Ok(PdrResult::Unsafe(_)) => {
            eprintln!("diag_model_checker_consumer_multi_bb_alloc_pattern: UNSAFE (BUG)")
        }
        Ok(PdrResult::NotApplicable) => {
            eprintln!("diag_model_checker_consumer_multi_bb_alloc_pattern: NOT_APPLICABLE")
        }
        Err(e) => eprintln!("diag_model_checker_consumer_multi_bb_alloc_pattern: ERROR: {e}"),
        Ok(_) => eprintln!("diag_model_checker_consumer_multi_bb_alloc_pattern: OTHER"),
    }
    // This is a safe system (error is unreachable). Unsafe would be a soundness bug.
    assert!(
        matches!(result, Ok(PdrResult::Safe(_)) | Ok(PdrResult::Unknown)),
        "Expected Safe or Unknown for model-checker-consumer multi-BB alloc pattern, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// Single-predicate BV array with property violation (UNSAT expected).
/// Models: obj_valid is all-false by default, never stores true.
/// Property checks obj_valid[1] = true, which should be reachable as error.
///
/// This tests that ay can detect property violations in BV array problems.
#[test]
#[timeout(15_000)]
fn diag_model_checker_consumer_bv_array_property_violation() {
    let input = r#"
(set-logic HORN)
(declare-fun inv ((Array (_ BitVec 32) Bool) (_ BitVec 32)) Bool)

; Init: obj_valid = all-false, cnt = 0
(assert (forall ((ov (Array (_ BitVec 32) Bool)))
  (=> (= ov ((as const (Array (_ BitVec 32) Bool)) false))
      (inv ov #x00000000))))

; Trans: increment counter, do NOT set obj_valid[1] to true
(assert (forall (
  (ov (Array (_ BitVec 32) Bool))
  (cnt (_ BitVec 32))
  (cnt_out (_ BitVec 32))
)
  (=> (and (inv ov cnt) (bvult cnt #x0000000A) (= cnt_out (bvadd cnt #x00000001)))
      (inv ov cnt_out))))

; Error: counter reached 5 but obj_valid[1] is still false
; This IS reachable since we never store true at index 1
(assert (forall (
  (ov (Array (_ BitVec 32) Bool))
  (cnt (_ BitVec 32))
)
  (=> (and (inv ov cnt) (= cnt #x00000005) (not (select ov #x00000001)))
      false)))

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(10));
    let result = testing::pdr_solve_from_str(input, config);
    match &result {
        Ok(PdrResult::Safe(_)) => {
            eprintln!("diag_model_checker_consumer_bv_array_property_violation: SAFE (BUG - should be Unsafe)");
        }
        Ok(PdrResult::Unsafe(_)) => {
            eprintln!("diag_model_checker_consumer_bv_array_property_violation: UNSAFE (correct)");
        }
        Ok(PdrResult::Unknown) => {
            eprintln!("diag_model_checker_consumer_bv_array_property_violation: UNKNOWN");
        }
        Ok(PdrResult::NotApplicable) => {
            eprintln!("diag_model_checker_consumer_bv_array_property_violation: NOT_APPLICABLE");
        }
        Err(e) => eprintln!("diag_model_checker_consumer_bv_array_property_violation: ERROR: {e}"),
        Ok(_) => eprintln!("diag_model_checker_consumer_bv_array_property_violation: OTHER"),
    }
    // Property violation is reachable: counter reaches 5, obj_valid[1] stays false.
    // Safe would be a soundness bug. Unsafe is correct. Unknown acceptable.
    assert!(
        !matches!(result, Ok(PdrResult::Safe(_))),
        "SOUNDNESS BUG: Expected Unsafe (or Unknown), but got Safe for property violation test"
    );
}
