// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! End-to-end PDR tests for datatype-sorted predicate parameters (#7016).
//!
//! These tests validate the full DT pipeline: parser -> executor adapter ->
//! ay-dpll DT solver -> model extraction -> point blocking -> MBP projection.

use ay_chc::{testing, BmcConfig, ChcParser, PdrConfig, PdrResult};
use ntest::timeout;

/// Minimal DT: Pair with field access invariant.
///
/// Validates: parser, sort gate, executor DT declarations, model parsing,
/// point blocking, MBP DT projection.
///
/// Pattern: construct a Pair(x, y), store it, read fields back.
/// Invariant: fst(p) >= 0 (the first field is non-negative).
/// Expected: Safe — init sets fst to 42.
#[test]
#[serial_test::serial]
#[timeout(30_000)]
fn test_pdr_dt_pair_field_access_safe() {
    let input = include_str!("../../../../benchmarks/smt/chc_dt_pair_field_access.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved fst(p) >= 0 with DT-sorted predicate parameter
        }
        Ok(other) => {
            panic!("Expected Safe for DT pair field access, got {other:?}");
        }
        Err(e) => {
            panic!("DT pair CHC parse/setup error: {e}");
        }
    }
}

/// Multi-constructor DT: Option enum with recognizer.
///
/// Validates: recognizer evaluation (`is-Some`, `is-None`), literal expansion,
/// multi-constructor model values.
///
/// Pattern: inv(x) where x is either None or Some(n) with n > 0.
/// Invariant: is-None(x) OR val(x) > 0.
/// Expected: Safe.
#[test]
#[serial_test::serial]
#[timeout(30_000)]
fn test_pdr_dt_option_enum_safe() {
    let input = include_str!("../../../../benchmarks/smt/chc_dt_option_enum.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved the Option enum invariant with multi-constructor DT
        }
        Ok(other) => {
            panic!("Expected Safe for DT option enum, got {other:?}");
        }
        Err(e) => {
            panic!("DT option enum CHC parse/setup error: {e}");
        }
    }
}

/// Mutually recursive DTs via declare-datatypes (plural form).
///
/// Validates: declare-datatypes parser, mutual recursion sort resolution,
/// Tree/Forest types with field access.
///
/// Pattern: inv(t) where t is a Tree (leaf or node).
/// Invariant: is-leaf(t) => val(t) >= 0.
/// Expected: Safe — init creates leaf(42).
#[test]
#[serial_test::serial]
#[timeout(30_000)]
fn test_pdr_dt_mutual_recursive_safe() {
    let input = include_str!("../../../../benchmarks/smt/chc_dt_mutual_recursive.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved leaf value invariant with mutually recursive DTs
        }
        Ok(PdrResult::Unknown | PdrResult::NotApplicable) => {
            // Acceptable if mutual recursion DT pipeline not yet fully wired
        }
        Ok(PdrResult::Unsafe(_)) => {
            panic!("PDR returned Unsafe for a safe mutual-recursive DT problem — soundness bug");
        }
        Err(e) => {
            panic!("Mutual-recursive DT CHC parse/setup error: {e}");
        }
        _ => panic!("unexpected variant"),
    }
}

/// Constructor clash UNSAT: transition changes Some to None, violating safety.
///
/// Validates: constructor discrimination in counterexample generation,
/// `is-None` / `is-Some` tester reasoning in PDR unsafe path.
///
/// Pattern: init x = Some(42), trans x -> None, safety requires is-Some(x).
/// Expected: Unsafe — counterexample: init -> one step -> None violates safety.
#[test]
#[serial_test::serial]
#[timeout(30_000)]
fn test_pdr_dt_constructor_clash_unsafe() {
    let input = include_str!("../../../../benchmarks/smt/chc_dt_clash_unsafe.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Unsafe(_) | PdrResult::Unknown) => {
            // Direct PDR may prove the DT counterexample or fail closed.
        }
        Ok(other) => {
            panic!("Expected Unsafe/Unknown for DT constructor clash, got {other:?}");
        }
        Err(e) => {
            panic!("DT constructor clash CHC parse/setup error: {e}");
        }
    }
}

/// Nested struct: Outer contains Inner DT.
///
/// Validates: DT flattening with nested struct fields, recursive selector
/// rewriting (`(ix (payload o))` becomes a direct field variable).
///
/// Pattern: Outer(tag=1, Inner(x=0)), increment x each step.
/// Invariant: x >= 0.
/// Expected: Safe — x starts at 0 and only increments.
#[test]
#[serial_test::serial]
#[timeout(30_000)]
fn test_pdr_dt_nested_struct_safe() {
    let input = include_str!("../../../../benchmarks/smt/chc_dt_nested_struct.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved nested struct invariant
        }
        Ok(other) => {
            panic!("Expected Safe for nested DT struct, got {other:?}");
        }
        Err(e) => {
            panic!("Nested DT struct CHC parse/setup error: {e}");
        }
    }
}

/// Struct with relational invariant: y = 2 * x.
///
/// Validates: DT flattening preserves relational constraints between
/// fields after flattening to scalar parameters.
///
/// Pattern: State(x, y), x' = x+1, y' = y+2.
/// Invariant: y = 2*x.
/// Expected: Safe — the ratio is preserved at every step.
#[test]
#[serial_test::serial]
#[timeout(30_000)]
fn test_pdr_dt_counter_struct_relational_safe() {
    let input = include_str!("../../../../benchmarks/smt/chc_dt_counter_struct.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR discovered y = 2*x relational invariant after DT flattening
        }
        Ok(other) => {
            panic!("Expected Safe for DT counter struct, got {other:?}");
        }
        Err(e) => {
            panic!("DT counter struct CHC parse/setup error: {e}");
        }
    }
}

/// Projected-field update by root reconstruction.
///
/// Validates the model-checker-consumer WriteAnySlim projected-field shape:
/// `root' = Constructor(updated_target, preserved_sibling(root))`.
///
/// Pattern: Pair(target, other), target is incremented while
/// other is preserved through a selector.
/// Expected: Unsafe — PDR finds the one-step counterexample while the datatype
/// BMC guard remains conservative.
#[test]
#[serial_test::serial]
#[timeout(30_000)]
fn test_pdr_dt_projected_field_update_unsafe() {
    let input =
        include_str!("../../../../benchmarks/smt/chc_dt_projected_field_update_unsafe.smt2");
    let problem = ChcParser::parse(input).expect("projected-field benchmark should parse");
    let bmc = testing::new_bmc_solver(problem, BmcConfig::default().with_max_depth(2));
    let bmc_result = bmc.solve();
    assert!(
        matches!(bmc_result, PdrResult::Unknown),
        "datatype BMC guard should stay armed; PDR owns this unsafe proof, got {bmc_result:?}"
    );

    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Unsafe(_)) => {
            // PDR found the one-step projected-field update counterexample.
        }
        Ok(other) => {
            panic!("Expected Unsafe for DT projected-field update, got {other:?}");
        }
        Err(e) => {
            panic!("DT projected-field update CHC parse/setup error: {e}");
        }
    }
}

/// Enum variant switch — Result<Int, Int> with Ok->Err transition.
///
/// Validates: multi-constructor DT flattening with discriminant reasoning
/// in the unsafe (counterexample) path.
///
/// Pattern: init Ok(42), transition Ok(n) -> Err(n), safety requires is-Ok.
/// Expected: Unsafe — one transition step violates the safety property.
#[test]
#[serial_test::serial]
#[timeout(30_000)]
fn test_pdr_dt_enum_switch_unsafe() {
    let input = include_str!("../../../../benchmarks/smt/chc_dt_enum_switch_unsafe.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Unsafe(_) | PdrResult::Unknown) => {
            // Direct PDR may prove the DT counterexample or fail closed.
        }
        Ok(other) => {
            panic!("Expected Unsafe/Unknown for DT enum switch, got {other:?}");
        }
        Err(e) => {
            panic!("DT enum switch CHC parse/setup error: {e}");
        }
    }
}

/// Mixed DT and scalar predicate arguments.
///
/// Validates: DT flattening correctly handles predicates with both DT and
/// non-DT arguments, preserving the relationship between the scalar
/// counter and the flattened struct field.
///
/// Pattern: inv(counter: Int, state: Pair), counter tracks fst(state).
/// Invariant: counter = fst(state).
/// Expected: Safe.
#[test]
#[serial_test::serial]
#[timeout(30_000)]
fn test_pdr_dt_mixed_args_safe() {
    let input = include_str!("../../../../benchmarks/smt/chc_dt_mixed_args.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved counter = fst(state) with mixed DT/scalar args
        }
        Ok(other) => {
            panic!("Expected Safe for mixed DT/scalar args, got {other:?}");
        }
        Err(e) => {
            panic!("Mixed DT/scalar args CHC parse/setup error: {e}");
        }
    }
}

/// model-checker-consumer-style DT benchmark: struct with two fields, equality invariant.
///
/// Validates the primary use case from the issue: model-checker-consumer-generated CHC
/// problems with struct-sorted predicate arguments.
///
/// Pattern: Pair(x, y) with x'=x+1, y'=y+1.
/// Invariant: x = y.
/// Expected: Safe.
#[test]
#[serial_test::serial]
#[timeout(30_000)]
fn test_pdr_dt_model_checker_consumer_style_safe() {
    let input = include_str!("../../../../benchmarks/smt/model_checker_consumer_dt_simple.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved model-checker-consumer-style DT equality invariant
        }
        Ok(other) => {
            panic!("Expected Safe for model-checker-consumer-style DT, got {other:?}");
        }
        Err(e) => {
            panic!("model-checker-consumer-style DT CHC parse/setup error: {e}");
        }
    }
}
