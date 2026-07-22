// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for PDR array-sorted predicate support (#6047).
//!
//! These tests verify that PDR can handle CHC problems with Array-sorted
//! predicate parameters without crashing. Prior to #6047, the PDR sort gate
//! rejected any problem with Array-sorted predicates, returning Unknown.

use ay_chc::{testing, ChcExpr, ChcOp, ChcParser, ChcProblem, ChcSort, PdrConfig, PdrResult};
use ntest::timeout;

/// Test that PDR accepts a CHC problem with Array(Int,Int) predicate parameters
/// and constant-index array access (scalarizable).
///
/// This problem models: store 42 at index 0, then check select(arr, 0) == 42.
/// The scalarization pass should convert this to scalar variables before PDR runs.
///
/// Expected: Safe (the invariant holds trivially).
#[test]
#[timeout(15_000)]
fn test_pdr_array_const_index_scalarizable() {
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
    // Constant-index select/store: scalarization eliminates the array, PDR solves trivially.
    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "Expected Safe for constant-index scalarizable array problem, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// Test that PDR accepts a CHC problem with Array(Int,Int) predicate parameters
/// and variable-index array access (NOT scalarizable).
///
/// This problem models a simple loop that writes x to arr[x] and checks arr[0] == 0.
/// Variable index `x` prevents scalarization, so PDR must handle the array sort directly.
///
/// Expected: Unknown or Safe (either is acceptable; crash is not).
#[test]
#[timeout(15_000)]
fn test_pdr_array_variable_index_no_crash() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array Int Int) Int ) Bool)

(assert
  (forall ( (A (Array Int Int)) (X Int) )
    (=>
      (and (= X 0) (= A (store ((as const (Array Int Int)) 0) 0 0)))
      (inv A X)
    )
  )
)

(assert
  (forall ( (A (Array Int Int)) (X Int) (A2 (Array Int Int)) (X2 Int) )
    (=>
      (and
        (inv A X)
        (= X2 (+ X 1))
        (= A2 (store A X2 X2))
        (<= X2 10)
      )
      (inv A2 X2)
    )
  )
)

(assert
  (forall ( (A (Array Int Int)) (X Int) )
    (=>
      (and (inv A X) (not (= (select A 0) 0)))
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
            // PDR proved the property — arr[0] stays 0 because stores
            // only write at indices 1..=10 and the const array has 0.
        }
        Ok(PdrResult::Unsafe(_)) => {
            // The system is safe (arr[0] is always 0), so Unsafe is a soundness bug
            panic!("PDR returned Unsafe for a safe array problem — soundness bug");
        }
        Ok(other) => {
            // Since #6047, PDR handles Array-sorted predicates. This problem
            // is solvable (verified at commit bc9c77c2b), so Unknown/NotApplicable
            // indicates a regression in array support.
            panic!("PDR returned {other:?} — expected Safe for variable-index array problem");
        }
        Err(e) => {
            panic!("Array CHC parse/setup error — this should parse and run: {e}");
        }
    }
}

/// Test PDR with multiple array-sorted parameters and a scalar state variable.
///
/// Models the model-checker-consumer pattern: Inv(obj_valid, count) where obj_valid is an
/// Array(Int,Bool) tracking which objects are valid, and count tracks the
/// number of valid objects. The loop stores true at index `count` and
/// increments count.
///
/// Invariant: select(obj_valid, 0) = true (slot 0 is always valid after init).
///
/// This tests that PDR handles mixed array + scalar predicate parameters,
/// and that the array MBP properly eliminates clause-local array variables
/// from the transition clause while preserving scalar constraints.
#[test]
#[timeout(30_000)]
fn test_pdr_array_multi_param_scalar_and_array() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array Int Bool) Int ) Bool)

; Init: obj_valid[0] = true, count = 1
(assert
  (forall ( (V (Array Int Bool)) (C Int) )
    (=>
      (and (= C 1) (= V (store ((as const (Array Int Bool)) false) 0 true)))
      (inv V C)
    )
  )
)

; Trans: obj_valid' = store(obj_valid, count, true), count' = count + 1
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

; Bad: inv holds but obj_valid[0] is false
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
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved that obj_valid[0] remains true
        }
        Ok(PdrResult::Unknown | PdrResult::NotApplicable) => {
            // Acceptable: array MBP may be too imprecise
        }
        Ok(PdrResult::Unsafe(_)) => {
            panic!("PDR returned Unsafe for a safe multi-param array problem — soundness bug");
        }
        Err(e) => {
            panic!("Multi-param array CHC parse/setup error: {e}");
        }
        _ => panic!("unexpected variant"),
    }
}

/// Test PDR with two array-sorted parameters (models model-checker-consumer obj_valid + mem pattern).
///
/// Inv(obj_valid, mem) where both are Array(Int,Int). Init stores value 42 in
/// mem[0] and marks obj_valid[0] = 1. Property: if obj_valid[0] = 1 then mem[0] = 42.
///
/// This tests cross-array invariant reasoning and multi-array MBP.
#[test]
#[timeout(15_000)]
fn test_pdr_array_two_array_params() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array Int Int) (Array Int Int) ) Bool)

; Init: obj_valid[0] = 1, mem[0] = 42
(assert
  (forall ( (OV (Array Int Int)) (M (Array Int Int)) )
    (=>
      (and
        (= OV (store ((as const (Array Int Int)) 0) 0 1))
        (= M (store ((as const (Array Int Int)) 0) 0 42))
      )
      (inv OV M)
    )
  )
)

; Trans: identity (no modification)
(assert
  (forall ( (OV (Array Int Int)) (M (Array Int Int)) )
    (=> (inv OV M) (inv OV M))
  )
)

; Bad: obj_valid[0] = 1 but mem[0] != 42
(assert
  (forall ( (OV (Array Int Int)) (M (Array Int Int)) )
    (=>
      (and (inv OV M) (= (select OV 0) 1) (not (= (select M 0) 42)))
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
    // Both arrays use constant index 0 — scalarization converts to scalar variables.
    // Identity transition with init constraints makes the invariant trivial.
    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "Expected Safe for two-array constant-index problem (scalarizable), got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// #8667 regression: the model-checker-consumer-style two-array fixture should be proved safe by
/// PDR itself, not only by the top-level CHC portfolio.
#[test]
#[timeout(30_000)]
fn test_pdr_array_2param_int_8667_fixture_is_safe() {
    let input = include_str!("../../../../benchmarks/chc/array_2param_int_8660.smt2");
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(20));
    let result = testing::pdr_solve_from_str(input, config);

    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "Expected PDR Safe for #8667 two-array fixture, got {result:#?}"
    );
}

/// #8667 regression: direct PDR may be inconclusive or produce an
/// unpromoted counterexample here; the production portfolio must still prove
/// this SAFE fixture.
#[test]
#[timeout(30_000)]
fn test_pdr_array_le_counter_8667_fixture_is_not_unsafe() {
    let input = include_str!("../../../../benchmarks/chc/array_le_counter_8660.smt2");
    let problem = ChcParser::parse(input).expect("array fixture should parse");
    let result = ay_chc::AdaptivePortfolio::new(
        problem,
        ay_chc::AdaptiveConfig::test_default().with_time_budget(std::time::Duration::from_secs(20)),
    )
    .solve();
    assert!(
        matches!(&result, ay_chc::VerifiedChcResult::Safe(_)),
        "Expected portfolio Safe for #8667 counter-array fixture, got {result:#?}"
    );
}

/// Test PDR with BV-indexed arrays doesn't crash (models model-checker-consumer harness pattern).
///
/// This models the model-checker-consumer pattern: (Array (_ BitVec 32) Bool) for obj_valid tracking.
/// Scalarization may or may not handle this depending on index patterns.
///
/// Expected: doesn't crash. Safe/Unknown both acceptable.
#[test]
#[timeout(15_000)]
fn test_pdr_array_bv_index_no_crash() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array (_ BitVec 32) Bool) (_ BitVec 32) ) Bool)

(assert
  (forall ( (V (Array (_ BitVec 32) Bool)) (P (_ BitVec 32)) )
    (=>
      (and
        (= P #x00000000)
        (= V (store ((as const (Array (_ BitVec 32) Bool)) false) P true))
      )
      (inv V P)
    )
  )
)

(assert
  (forall ( (V (Array (_ BitVec 32) Bool)) (P (_ BitVec 32)) )
    (=>
      (and (inv V P) (not (select V P)))
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
            // Correct
        }
        Ok(PdrResult::Unknown | PdrResult::NotApplicable) => {
            // Acceptable
        }
        Ok(PdrResult::Unsafe(_)) => {
            panic!("PDR returned Unsafe for a safe BV-array problem — soundness bug");
        }
        Err(e) => {
            panic!("BV-array CHC parse/setup error — this should parse and run: {e}");
        }
        _ => panic!("unexpected variant"),
    }
}

/// Test PDR with model-checker-consumer's full 3-array BV pattern: obj_valid, obj_size, mem.
///
/// This models the exact signature model-checker-consumer generates with `--ay-chc-track=mem`:
/// - `obj_valid: (Array (_ BitVec 32) Bool)` — object validity map
/// - `obj_size: (Array (_ BitVec 32) (_ BitVec 32))` — object size map
/// - `mem: (Array (_ BitVec 64) (_ BitVec 8))` — byte-level memory
///
/// Init: allocate object 0 with size 4, write 0xAA to mem[0].
/// Property: obj_valid[0] = true implies mem[0] = 0xAA.
///
/// Expected: doesn't crash. Safe/Unknown both acceptable.
#[test]
#[timeout(15_000)]
fn test_pdr_array_model_checker_consumer_three_array_bv_pattern() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 32) (_ BitVec 32))
  (Array (_ BitVec 64) (_ BitVec 8))
) Bool)

; Init: obj_valid[0] = true, obj_size[0] = 4, mem[0] = 0xAA
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
  )
    (=>
      (and
        (= ov (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000000 true))
        (= os (store ((as const (Array (_ BitVec 32) (_ BitVec 32))) #x00000000) #x00000000 #x00000004))
        (= m  (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) #x0000000000000000 #xAA))
      )
      (inv ov os m)
    )
  )
)

; Trans: identity (no modification)
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
  )
    (=> (inv ov os m) (inv ov os m))
  )
)

; Bad: obj_valid[0] = true but mem[0] != 0xAA
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
  )
    (=>
      (and
        (inv ov os m)
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
    // All indices are constant BV literals — scalarization converts the problem
    // to pure BV scalars, and k-induction solves at k=0.
    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "Expected Safe for 3-array BV constant-index problem (scalarizable), got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

// #6047: test_pdr_array_model_checker_consumer_bvmul_variable_store removed.
// It was passing on unsound scalarization that silently eliminated BV32-indexed
// arrays. After the fix, three BV32-indexed arrays are kept as Array-sorted
// params, causing bit-blast blowup that makes PDR timeout. Testing a timeout
// is not useful. The underlying problem (efficient BV-array PDR) is tracked
// by #6047.

/// Test PDR with variable-index store in transition (non-trivial MBP elimination).
///
/// This models a loop that allocates objects at variable positions:
/// Init: count = 0, obj_valid is all false.
/// Trans: obj_valid' = store(obj_valid, count, true), count' = count + 1.
/// Property: count >= 0.
///
/// The array variable in the transition is clause-local (bound by forall in the
/// transition clause). MBP must eliminate it via select factoring + Ackermannization.
///
/// Expected: Safe or Unknown (crash is a bug).
#[test]
#[timeout(15_000)]
fn test_pdr_array_variable_index_store_transition() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array Int Bool) Int ) Bool)

; Init: obj_valid = const(false), count = 0
(assert
  (forall ( (V (Array Int Bool)) (C Int) )
    (=>
      (and (= C 0) (= V ((as const (Array Int Bool)) false)))
      (inv V C)
    )
  )
)

; Trans: obj_valid' = store(obj_valid, count, true), count' = count + 1
; The pre-state array V is clause-local — MBP must project it out.
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

; Bad: count < 0
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
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved count >= 0 despite array-sorted predicate parameter
        }
        Ok(PdrResult::Unknown | PdrResult::NotApplicable) => {
            // Acceptable
        }
        Ok(PdrResult::Unsafe(_)) => {
            panic!("PDR returned Unsafe for a safe variable-index store problem — soundness bug");
        }
        Err(e) => {
            panic!("Variable-index store CHC parse/setup error: {e}");
        }
        _ => panic!("unexpected variant"),
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct LiaArrayFirstSmokeRouteStats {
    predicate_array_args: usize,
    selects: usize,
    stores: usize,
    constant_indices: usize,
    symbolic_affine_indices: usize,
    requires_original_problem_validation: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LiaArrayFirstSmokeRoute {
    Candidate(LiaArrayFirstSmokeRouteStats),
    NotApplicable(LiaArrayFirstSmokeRouteStats),
    Unsupported(LiaArrayFirstSmokeRouteStats, &'static str),
}

fn parse_valid_chc(input: &str) -> ChcProblem {
    let problem = ChcParser::parse(input).expect("fixture should parse");
    problem.validate().expect("fixture should validate");
    problem
}

fn recognize_lia_array_first_smoke_route(problem: &ChcProblem) -> LiaArrayFirstSmokeRoute {
    let mut stats = LiaArrayFirstSmokeRouteStats::default();

    for pred in problem.predicates() {
        for sort in &pred.arg_sorts {
            match sort {
                ChcSort::Array(key, value)
                    if matches!(key.as_ref(), ChcSort::Int)
                        && matches!(value.as_ref(), ChcSort::Int) =>
                {
                    stats.predicate_array_args += 1;
                }
                ChcSort::Array(_, _) => {
                    return LiaArrayFirstSmokeRoute::Unsupported(
                        stats,
                        "non-Array-Int-Int predicate argument",
                    );
                }
                ChcSort::Bool | ChcSort::Int => {}
                _ => return LiaArrayFirstSmokeRoute::Unsupported(stats, "non-LIA predicate sort"),
            }
        }
    }

    for clause in problem.clauses() {
        for (_, args) in &clause.body.predicates {
            for arg in args {
                if let Err(reason) = scan_lia_array_expr(arg, &mut stats) {
                    return LiaArrayFirstSmokeRoute::Unsupported(stats, reason);
                }
            }
        }
        if let Some(constraint) = &clause.body.constraint {
            if let Err(reason) = scan_lia_array_expr(constraint, &mut stats) {
                return LiaArrayFirstSmokeRoute::Unsupported(stats, reason);
            }
        }
        if let ay_chc::ClauseHead::Predicate(_, args) = &clause.head {
            for arg in args {
                if let Err(reason) = scan_lia_array_expr(arg, &mut stats) {
                    return LiaArrayFirstSmokeRoute::Unsupported(stats, reason);
                }
            }
        }
    }

    if stats.predicate_array_args == 0 || stats.symbolic_affine_indices == 0 {
        return LiaArrayFirstSmokeRoute::NotApplicable(stats);
    }

    stats.requires_original_problem_validation = true;
    LiaArrayFirstSmokeRoute::Candidate(stats)
}

fn scan_lia_array_expr(
    expr: &ChcExpr,
    stats: &mut LiaArrayFirstSmokeRouteStats,
) -> Result<(), &'static str> {
    match expr {
        ChcExpr::Bool(_) | ChcExpr::Int(_) => Ok(()),
        ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => Err("non-LIA literal"),
        ChcExpr::Var(v) => match &v.sort {
            ChcSort::Bool | ChcSort::Int => Ok(()),
            sort if is_array_int_int(sort) => Ok(()),
            ChcSort::Array(_, _) => Err("non-Array-Int-Int expression"),
            _ => Err("non-LIA variable sort"),
        },
        ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
            if !is_array_int_int(&args[0].sort()) {
                return Err("non-Array-Int-Int select");
            }
            record_lia_array_index(&args[1], stats)?;
            stats.selects += 1;
            scan_lia_array_expr(&args[0], stats)?;
            scan_lia_array_expr(&args[1], stats)
        }
        ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
            if !is_array_int_int(&args[0].sort()) {
                return Err("non-Array-Int-Int store");
            }
            if args[2].sort() != ChcSort::Int {
                return Err("non-Int store value");
            }
            record_lia_array_index(&args[1], stats)?;
            stats.stores += 1;
            for arg in args {
                scan_lia_array_expr(arg, stats)?;
            }
            Ok(())
        }
        ChcExpr::Op(op, args) => {
            if is_bv_op(op) {
                return Err("bit-vector operator");
            }
            for arg in args {
                scan_lia_array_expr(arg, stats)?;
            }
            Ok(())
        }
        ChcExpr::PredicateApp(_, _, args) => {
            for arg in args {
                scan_lia_array_expr(arg, stats)?;
            }
            Ok(())
        }
        ChcExpr::FuncApp(_, _, _) => Err("uninterpreted function application"),
        ChcExpr::ConstArray(key_sort, value) => {
            if !matches!(key_sort, ChcSort::Int) || value.sort() != ChcSort::Int {
                return Err("non-Array-Int-Int const array");
            }
            scan_lia_array_expr(value, stats)
        }
        ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => Err("unsupported marker"),
        _ => Err("unsupported expression"),
    }
}

fn record_lia_array_index(
    index: &ChcExpr,
    stats: &mut LiaArrayFirstSmokeRouteStats,
) -> Result<(), &'static str> {
    let Some(has_symbolic_var) = is_lia_affine_index(index) else {
        return Err("non-affine array index");
    };
    if has_symbolic_var {
        stats.symbolic_affine_indices += 1;
    } else {
        stats.constant_indices += 1;
    }
    Ok(())
}

fn is_lia_affine_index(expr: &ChcExpr) -> Option<bool> {
    match expr {
        ChcExpr::Int(_) => Some(false),
        ChcExpr::Var(v) if v.sort == ChcSort::Int => Some(true),
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => is_lia_affine_index(&args[0]),
        ChcExpr::Op(ChcOp::Add | ChcOp::Sub, args) => {
            let mut has_var = false;
            for arg in args {
                has_var |= is_lia_affine_index(arg)?;
            }
            Some(has_var)
        }
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => match (&*args[0], &*args[1]) {
            (ChcExpr::Int(_), rhs) => is_lia_affine_index(rhs),
            (lhs, ChcExpr::Int(_)) => is_lia_affine_index(lhs),
            _ => None,
        },
        _ => None,
    }
}

fn is_array_int_int(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Array(key, value)
        if matches!(key.as_ref(), ChcSort::Int) && matches!(value.as_ref(), ChcSort::Int))
}

fn is_bv_op(op: &ChcOp) -> bool {
    matches!(
        op,
        ChcOp::BvAdd
            | ChcOp::BvSub
            | ChcOp::BvMul
            | ChcOp::BvUDiv
            | ChcOp::BvURem
            | ChcOp::BvSDiv
            | ChcOp::BvSRem
            | ChcOp::BvSMod
            | ChcOp::BvAnd
            | ChcOp::BvOr
            | ChcOp::BvXor
            | ChcOp::BvNand
            | ChcOp::BvNor
            | ChcOp::BvXnor
            | ChcOp::BvNot
            | ChcOp::BvNeg
            | ChcOp::BvShl
            | ChcOp::BvLShr
            | ChcOp::BvAShr
            | ChcOp::BvULt
            | ChcOp::BvULe
            | ChcOp::BvUGt
            | ChcOp::BvUGe
            | ChcOp::BvSLt
            | ChcOp::BvSLe
            | ChcOp::BvSGt
            | ChcOp::BvSGe
            | ChcOp::BvComp
            | ChcOp::BvConcat
            | ChcOp::Bv2Nat
            | ChcOp::BvExtract(_, _)
            | ChcOp::BvZeroExtend(_)
            | ChcOp::BvSignExtend(_)
            | ChcOp::BvRotateLeft(_)
            | ChcOp::BvRotateRight(_)
            | ChcOp::BvRepeat(_)
            | ChcOp::Int2Bv(_)
    )
}

#[test]
fn lia_arrays_first_smoke_compact_shape_is_a_guarded_symbolic_route_candidate() {
    let input = r#"
(set-logic HORN)
(declare-fun |main@_bb| ( Int Int (Array Int Int) Int ) Bool)
(declare-fun |main@_bb2| ( Int (Array Int Int) Int Int ) Bool)
(declare-fun |main@entry| ( (Array Int Int) ) Bool)

(assert
  (forall ( (A (Array Int Int)) )
    (=>
      true
      (main@entry A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Bool) (D Bool)
            (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) )
    (=>
      (and
        (main@entry A)
        (= C true)
        (= D true)
        (= E 0)
        (= G E)
        (= B A)
        (= H B))
      (main@_bb F G H I)
    )
  )
)
(assert
  (forall ( (A Bool) (C (Array Int Int)) (D Int) (E Int) (F Int)
            (G (Array Int Int)) (H Int) (M Int) (P Int) )
    (=>
      (and
        (main@_bb M F C P)
        (= A (and (not (<= 102400 F)) (>= F 0)))
        (not A)
        (not (<= M 0))
        (= D (+ M F))
        (= G (store C D E))
        (= H (+ 1 F)))
      (main@_bb M H G P)
    )
  )
)
(assert
  (forall ( (B (Array Int Int)) (C Int) (D Int) (E Bool)
            (G Int) (H Int) (L Int) (O Int) )
    (=>
      (and
        (main@_bb2 L B G O)
        (= C (+ L G))
        (= D (select B C))
        (= E (= D O))
        (not E))
      false
    )
  )
)
(check-sat)
"#;

    let problem = parse_valid_chc(input);
    let route = recognize_lia_array_first_smoke_route(&problem);

    let LiaArrayFirstSmokeRoute::Candidate(stats) = route else {
        panic!("compact first-smoke shape should be a guarded candidate, got {route:?}");
    };
    assert_eq!(stats.predicate_array_args, 3);
    assert_eq!(stats.stores, 1);
    assert_eq!(stats.selects, 1);
    assert_eq!(stats.symbolic_affine_indices, 2);
    assert!(stats.requires_original_problem_validation);
}

#[test]
fn lia_arrays_first_smoke_eureka_shape_accepts_scaled_affine_indices() {
    let input = r#"
(set-logic HORN)
(declare-fun |main@_bb15| ( Int (Array Int Int) Int (Array Int Int) Int (Array Int Int) Int ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C (Array Int Int)) )
    (=>
      true
      (main@_bb15 0 A 0 B 0 C 0)
    )
  )
)
(assert
  (forall ( (C Int) (D Int) (E Int) (F Int) (I Int) (P Int)
            (U Int) (V (Array Int Int)) (W Int) (X (Array Int Int))
            (Y Int) (Z (Array Int Int)) (P2 Int) (X2 (Array Int Int)) )
    (=>
      (and
        (main@_bb15 U V W X Y Z P)
        (= C (+ Y (* 4 P)))
        (= D (+ U (* 4 I)))
        (= E (select Z C))
        (= F (select V D))
        (= X2 (store X C (+ E F)))
        (= P2 (+ P 1)))
      (main@_bb15 U V W X2 Y Z P2)
    )
  )
)
(assert
  (forall ( (J Int) (K Int) (P Int) (U Int) (X (Array Int Int)) )
    (=>
      (and
        (main@_bb15 U X 0 X 0 X P)
        (= J (+ U (* 4 P)))
        (= K (select X J))
        (< K 0))
      false
    )
  )
)
(check-sat)
"#;

    let problem = parse_valid_chc(input);
    let route = recognize_lia_array_first_smoke_route(&problem);

    let LiaArrayFirstSmokeRoute::Candidate(stats) = route else {
        panic!("eureka first-smoke shape should be a guarded candidate, got {route:?}");
    };
    assert_eq!(stats.predicate_array_args, 3);
    assert_eq!(stats.stores, 1);
    assert_eq!(stats.selects, 3);
    assert_eq!(stats.symbolic_affine_indices, 4);
    assert!(stats.requires_original_problem_validation);
}

#[test]
fn lia_arrays_first_smoke_route_rejects_non_affine_indices_fail_closed() {
    let input = r#"
(set-logic HORN)
(declare-fun Inv ( (Array Int Int) Int Int ) Bool)

(assert
  (forall ( (A (Array Int Int)) (I Int) (J Int) )
    (=>
      (Inv A I J)
      (Inv A (+ I 1) J)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (I Int) (J Int) (V Int) )
    (=>
      (and
        (Inv A I J)
        (= V (select A (* I J)))
        (< V 0))
      false
    )
  )
)
(check-sat)
"#;

    let problem = parse_valid_chc(input);
    let route = recognize_lia_array_first_smoke_route(&problem);

    assert!(matches!(
        route,
        LiaArrayFirstSmokeRoute::Unsupported(_, "non-affine array index")
    ));
}
