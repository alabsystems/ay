// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native-intended fill controls, each under ONE original 20-second end.

use super::*;

fn input(lo: u64, hi: u64, full: bool, query: &str) -> String {
    let value = if full {
        "#x09".to_owned()
    } else {
        format!("(ite (and (bvule (_ bv{lo} 64) i) (bvult i (_ bv{hi} 64))) #x09 (select d i))")
    };
    format!("(set-logic HORN)
      (declare-fun Filled ((Array (_ BitVec 64) (_ BitVec 8))) Bool)
      (assert (forall ((d (Array (_ BitVec 64) (_ BitVec 8))) (w (Array (_ BitVec 64) (_ BitVec 8))))
        (=> (and (= (select d (_ bv0 64)) #x07)
          (forall ((i (_ BitVec 64))) (= (select w i) {value}))) (Filled w))))
      (assert (forall ((w (Array (_ BitVec 64) (_ BitVec 8)))) (=> (and (Filled w) {query}) false)))
      (check-sat)")
}

fn unsafe_fill(text: &str, key: u64, expected: u8) {
    unsafe_model(text, key, ModelValue::bitvec(expected.into(), 8));
}

fn unsafe_model(text: &str, key: u64, expected: ModelValue) {
    let end = Instant::now() + WALL;
    let _wall = ScopedSmtDeadline::install_until(end);
    let token = CancellationToken::new();
    let problem = source(text);
    let QuantifiedChcCompleteResult::Unsafe(trace) =
        problem.solve_with_complete_trace(remaining(end), Some(TERMS), &token)
    else {
        panic!("full original fill counterexample required within original 20s");
    };
    assert_eq!(trace.source_smtlib(), problem.source_smtlib());
    assert!(trace.replay_obligation().contains("(forall "));
    let query = trace
        .bindings()
        .iter()
        .find(|binding| binding.occurrence() == 1)
        .expect("same query array");
    let QuantifiedChcCompleteValue::FunctionalArray(array) = query.value() else {
        panic!("complete whole fill assignment required");
    };
    let value = array
        .read_with_stop(
            &ModelValue::bitvec(key.into(), 64),
            &mut 100_000,
            &mut || token.is_cancelled() || Instant::now() >= end,
        )
        .expect("same original end");
    assert_scalar_eq(&value, &expected);
    assert!(trace.recheck(&problem, remaining(end), &token));
    assert!(Instant::now() < end);
}

#[test]
#[timeout(30000)]
fn partial_fill_safe_keeps_original_forall_and_frame_with_one_twenty_second_end() {
    original_safe(&input(1, 3, false, "(not (= (select w (_ bv1 64)) #x09))"));
}

#[test]
#[timeout(30000)]
fn partial_fill_unsafe_publishes_only_full_original_pinned_same_model_trace() {
    unsafe_fill(&input(1, 3, false, "(= (select w (_ bv1 64)) #x09)"), 1, 9);
}

#[test]
#[timeout(30000)]
fn huge_fill_never_enumerates_lanes_and_keeps_max_bv64_frame() {
    unsafe_fill(
        &input(
            1,
            u64::MAX,
            false,
            "(= (select w (_ bv18446744073709551615 64)) #x00)",
        ),
        u64::MAX,
        0,
    );
}

#[test]
#[timeout(30000)]
fn full_domain_fill_includes_max_bv64_key_without_wrapped_upper_endpoint() {
    unsafe_fill(
        &input(
            0,
            0,
            true,
            "(= (select w (_ bv18446744073709551615 64)) #x09)",
        ),
        u64::MAX,
        9,
    );
}

#[test]
#[timeout(30000)]
fn empty_fill_native_safe_cannot_write_lane_zero() {
    original_safe(&input(0, 0, false, "(= (select w (_ bv0 64)) #x09)"));
}

#[test]
#[timeout(30000)]
fn reversed_fill_native_safe_cannot_write_lane_zero() {
    original_safe(&input(9, 3, false, "(= (select w (_ bv0 64)) #x09)"));
}

fn uniform(cell: &str, value: &str) -> String {
    format!("(set-logic HORN) (declare-fun Filled ((Array (_ BitVec 64) {cell})) Bool)
        (assert (forall ((w (Array (_ BitVec 64) {cell})))
          (=> (forall ((i (_ BitVec 64))) (= (select w i) {value})) (Filled w))))
        (assert (forall ((w (Array (_ BitVec 64) {cell})))
          (=> (and (Filled w) (= (select w (_ bv18446744073709551615 64)) {value})) false))) (check-sat)")
}

#[test]
#[timeout(30000)]
fn bool_full_fill_unsafe_retains_entire_bool_array_and_canonical_original_replay() {
    unsafe_model(&uniform("Bool", "true"), u64::MAX, ModelValue::Bool(true));
}

#[test]
#[timeout(30000)]
fn bv128_full_fill_unsafe_preserves_all_bits_in_original_same_model_pins() {
    let value = format!("(_ bv{} 128)", u128::MAX);
    unsafe_model(
        &uniform("(_ BitVec 128)", &value),
        u64::MAX,
        ModelValue::bitvec(u128::MAX.into(), 128),
    );
}
