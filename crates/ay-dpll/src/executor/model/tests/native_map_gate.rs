// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which shapes the native-map fail-closed gate classifies
//! (`native_map_gate.rs`), independently of what the solver answers for them.
//! The end-to-end verdicts live in `executor_tests/map_value_semantics.rs`.

use super::super::native_map_gate::NativeMapGap;
use super::*;
use ay_frontend::parse;

fn gap_after_check_sat(input: &str) -> Option<NativeMapGap> {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("execute succeeds");
    exec.native_map_gap()
}

/// "Maps with equal values are equal" holds over value arrays and fails over
/// (value, domain) pairs; a quantifier over maps that compares them is out.
#[test]
fn quantified_map_comparison_is_classified() {
    let gap = gap_after_check_sat(
        "(set-logic MAPLIA)
         (declare-const a (Map Bool Bool))
         (assert (forall ((x (Map Bool Bool)))
           (=> (and (= (map.get x true) (map.get a true))
                    (= (map.get x false) (map.get a false)))
               (= x a))))
         (assert (map.contains_key a true))
         (check-sat)",
    );
    assert_eq!(gap, Some(NativeMapGap::QuantifiedMapComparison));
}

/// The comparison can hide in a datatype that holds a map.
#[test]
fn quantified_comparison_of_a_datatype_holding_a_map_is_classified() {
    let gap = gap_after_check_sat(
        "(set-logic ALL)
         (declare-datatypes ((Box 0)) (((box (unbox (Map Bool Int))))))
         (assert (forall ((b Box) (c Box))
           (=> (and (= (map.get (unbox b) true) (map.get (unbox c) true))
                    (= (map.get (unbox b) false) (map.get (unbox c) false)))
               (= b c))))
         (check-sat)",
    );
    assert_eq!(gap, Some(NativeMapGap::QuantifiedMapComparison));
}

/// A quantifier over maps that only reads their values is faithful: every
/// reader sees the value array alone.
#[test]
fn quantified_map_reads_are_not_classified() {
    let gap = gap_after_check_sat(
        "(set-logic ALL)
         (declare-const a (Map Bool Bool))
         (assert (forall ((x (Map Bool Bool))) (= (map.get x true) (select x true))))
         (assert (map.contains_key a true))
         (check-sat)",
    );
    assert_eq!(gap, None);
}

/// `map.get` of the empty map is a `select` of its value array: a read.
#[test]
fn a_read_of_the_empty_map_is_not_a_use_as_a_value() {
    let gap = gap_after_check_sat(
        "(set-logic QF_MAPLIA)
         (assert (= 5 (map.get (as map.empty (Map Int Int)) 1)))
         (check-sat)",
    );
    assert_eq!(gap, None);
}

#[test]
fn the_empty_map_as_a_value_is_classified() {
    let gap = gap_after_check_sat(
        "(set-logic QF_MAPLIA)
         (declare-const n (Map Int Int))
         (assert (= n (as map.empty (Map Int Int))))
         (check-sat)",
    );
    assert_eq!(gap, Some(NativeMapGap::EmptyMapAsValue));
}

#[test]
fn a_constant_array_at_a_map_sort_is_classified() {
    let gap = gap_after_check_sat(
        "(set-logic QF_MAPLIA)
         (declare-const n (Map Int Int))
         (assert (= n ((as const (Map Int Int)) 0)))
         (assert (map.contains_key n 1))
         (check-sat)",
    );
    assert_eq!(gap, Some(NativeMapGap::ConstantArrayMap));
}

#[test]
fn a_constant_array_beside_a_map_is_not_classified() {
    let gap = gap_after_check_sat(
        "(set-logic QF_MAPLIA)
         (declare-const n (Map Int Int))
         (declare-const a (Array Int Int))
         (assert (= a ((as const (Array Int Int)) 0)))
         (assert (map.contains_key n 1))
         (check-sat)",
    );
    assert_eq!(gap, None);
}
