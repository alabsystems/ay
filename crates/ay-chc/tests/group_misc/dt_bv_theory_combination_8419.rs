// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! DT+BV theory combination tests for CHC solving (#8419).
//!
//! These tests verify that the DT-flatten + BV dual-lane pipeline correctly
//! handles CHC problems with Datatype-sorted predicate arguments containing
//! BV fields. This is the pattern model-checker-consumer generates from Rust code like
//! `Option<u32>`, `Result<u8, u8>`, etc.
//!
//! Test categories:
//! 1. Accessor invariants: safe invariant MUST mention DT accessor terms
//! 2. Nested DT+BV: struct containing enum containing BV fields
//! 3. Injectivity: same constructor, different fields

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

const DT_BV_ACCESSOR_INVARIANT: &str =
    include_str!("../../../../benchmarks/smt/chc_dt_bv_accessor_invariant.smt2");

const DT_BV_NESTED_STRUCT_ENUM: &str =
    include_str!("../../../../benchmarks/smt/chc_dt_bv_nested_struct_enum.smt2");

const DT_BV_INJECTIVITY: &str =
    include_str!("../../../../benchmarks/smt/chc_dt_bv_injectivity.smt2");

// Existing benchmark from #7930
const DT_BV_OPTION_EQ: &str = include_str!("../../../../benchmarks/smt/chc_dt_bv_option_eq.smt2");

fn solve_with_budget(smt2: &str, budget_secs: u64) -> VerifiedChcResult {
    let problem = ChcParser::parse(smt2).expect("benchmark should parse");
    problem.validate().expect("benchmark should validate");

    assert!(
        problem.has_datatype_sorts(),
        "Test problem must have datatype sorts"
    );
    assert!(problem.has_bv_sorts(), "Test problem must have BV sorts");

    let budget = if cfg!(debug_assertions) {
        Duration::from_secs(budget_secs * 3)
    } else {
        Duration::from_secs(budget_secs)
    };

    let solver = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(budget),
    );
    solver.solve()
}

/// DT+BV accessor invariant: the safe invariant must mention (val8 x).
///
/// This tests the key pattern model-checker-consumer's workarounds currently avoid: a CHC
/// where the invariant cannot be expressed without DT accessor terms.
/// Two Option(BV8) values are incremented in lockstep, and the invariant
/// must express val8(x) == val8(y).
///
/// The DT flattener must expand this to scalar variables and expose the
/// payload equality strongly enough for the solver to prove the benchmark safe.
#[test]
#[timeout(120_000)]
fn dt_bv_accessor_invariant_parses_correctly_8419() {
    let problem = ChcParser::parse(DT_BV_ACCESSOR_INVARIANT).expect("should parse");
    problem.validate().expect("should validate");
    assert!(problem.has_datatype_sorts(), "Must have DT sorts");
    assert!(problem.has_bv_sorts(), "Must have BV sorts");

    // Verify the predicate has 2 DT-sorted arguments (x, y : OptBV8)
    let pred = &problem.predicates()[0];
    assert_eq!(pred.arg_sorts.len(), 2, "inv should have 2 arguments");
    for (i, sort) in pred.arg_sorts.iter().enumerate() {
        assert!(
            matches!(sort, ay_chc::ChcSort::Datatype { name, .. } if name == "OptBV8"),
            "Argument {i} should be Datatype OptBV8, got: {sort:?}"
        );
    }

    let result = solve_with_budget(DT_BV_ACCESSOR_INVARIANT, 30);
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "#8419: DT+BV accessor invariant benchmark should be safe. Got: {result:?}"
    );
}

/// Nested DT+BV: struct containing enum containing BV fields.
///
/// Pattern from Rust: struct State { tag: Result<u8, u8>, counter: u8 }
/// The invariant must reason about nested accessors:
///   (ok_val (tag state)) == (counter state)
///
/// The DT flattener must resolve nested selectors (ok_val(tag(s)) ->
/// s_tag_ok_val) and expose the BV payload/counter equality strongly enough
/// for the solver to prove the benchmark safe.
///
/// This is the critical test: `declare-datatypes` with `Result8` inside
/// `State`'s selectors. The parser must resolve the cross-reference from
/// `Uninterpreted("Result8")` to `Datatype{name: "Result8", ...}`.
#[test]
#[timeout(120_000)]
fn dt_bv_nested_struct_enum_mutual_dt_refs_resolved_8419() {
    let problem = ChcParser::parse(DT_BV_NESTED_STRUCT_ENUM).expect("should parse");
    problem.validate().expect("should validate");
    assert!(problem.has_datatype_sorts(), "Must have DT sorts");
    assert!(problem.has_bv_sorts(), "Must have BV sorts");

    // The predicate inv(s: State) should have 1 argument of sort State.
    let pred = &problem.predicates()[0];
    assert_eq!(pred.arg_sorts.len(), 1, "inv should have 1 argument");

    // State's `tag` selector should have sort Datatype{name: "Result8"},
    // NOT Uninterpreted("Result8"). This is the mutual DT reference fix.
    if let ay_chc::ChcSort::Datatype { name, constructors } = &pred.arg_sorts[0] {
        assert_eq!(name, "State", "First argument should be State");
        let mk_state = &constructors[0];
        let tag_sel = &mk_state.selectors[0];
        assert_eq!(tag_sel.name, "tag", "First selector should be 'tag'");
        assert!(
            matches!(&tag_sel.sort, ay_chc::ChcSort::Datatype { name, .. } if name == "Result8"),
            "#8419 FIX: tag selector sort must be Datatype{{Result8}}, not Uninterpreted. \
             Got: {:?}",
            tag_sel.sort
        );
    } else {
        panic!(
            "First argument should be Datatype State, got: {:?}",
            pred.arg_sorts[0]
        );
    }

    let result = solve_with_budget(DT_BV_NESTED_STRUCT_ENUM, 30);
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "#8419: nested DT+BV struct/enum benchmark should be safe. Got: {result:?}"
    );
}

/// DT+BV injectivity: two Option(BV16) values always equal.
///
/// Requires injectivity reasoning: some16(val_x) = some16(val_y) => val_x = val_y.
/// The DT axiom generator must produce injectivity axioms (F) for this.
///
/// Expected: Safe.
#[test]
#[timeout(120_000)]
fn dt_bv_injectivity_safe_8419() {
    let result = solve_with_budget(DT_BV_INJECTIVITY, 30);
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "#8419: DT+BV injectivity benchmark should be safe. \
         Requires some16(a) = some16(b) => a = b reasoning. Got: {result:?}"
    );
}

/// Existing DT+BV Option<BV8> equality benchmark (#7930).
///
/// Verifies that the existing benchmark still works with the current routing.
/// This was the original regression test for the DT+BV dual-lane guard.
///
/// Expected: Safe.
#[test]
#[timeout(120_000)]
fn dt_bv_option_eq_still_works_8419() {
    let result = solve_with_budget(DT_BV_OPTION_EQ, 30);
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "#8419: Existing DT+BV Option<BV8> equality benchmark should be safe. Got: {result:?}"
    );
}

/// DT flattener correctness: verify the DT-flatten + parse round-trip
/// preserves the problem structure for DT+BV problems.
#[test]
fn dt_bv_problem_has_expected_sorts_8419() {
    let problem =
        ChcParser::parse(DT_BV_ACCESSOR_INVARIANT).expect("accessor invariant should parse");
    problem
        .validate()
        .expect("accessor invariant should validate");

    assert!(
        problem.has_datatype_sorts(),
        "Accessor invariant problem must have DT sorts"
    );
    assert!(
        problem.has_bv_sorts(),
        "Accessor invariant problem must have BV sorts"
    );

    // Check that predicates have DT-sorted arguments
    let preds = problem.predicates();
    assert!(
        !preds.is_empty(),
        "Problem must declare at least one predicate"
    );
    let has_dt_arg = preds.iter().any(|pred| {
        pred.arg_sorts
            .iter()
            .any(|sort| matches!(sort, ay_chc::ChcSort::Datatype { .. }))
    });
    assert!(
        has_dt_arg,
        "At least one predicate must have a DT-sorted argument"
    );
}

/// Nested DT problem parsing: verify multi-DT declaration parsing.
#[test]
fn dt_bv_nested_problem_parses_correctly_8419() {
    let problem =
        ChcParser::parse(DT_BV_NESTED_STRUCT_ENUM).expect("nested struct/enum should parse");
    problem
        .validate()
        .expect("nested struct/enum should validate");

    assert!(
        problem.has_datatype_sorts(),
        "Nested problem must have DT sorts"
    );
    assert!(problem.has_bv_sorts(), "Nested problem must have BV sorts");
}
