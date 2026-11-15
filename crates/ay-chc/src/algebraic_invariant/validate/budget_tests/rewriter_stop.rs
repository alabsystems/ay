// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn cancellation_stops_wide_siblings_for_every_rewriter_container() {
    const WIDTH: usize = 4096;
    let args = vec![Arc::new(ChcExpr::Int(1)); WIDTH];
    let cases = [
        (
            ChcExpr::Op(ChcOp::Add, args.clone()),
            ChcExpr::Int(WIDTH as i128),
        ),
        (
            ChcExpr::FuncApp("wide".into(), ChcSort::Int, args.clone()),
            ChcExpr::FuncApp("wide".into(), ChcSort::Int, args.clone()),
        ),
        (
            ChcExpr::PredicateApp("wide".into(), PredicateId(0), args.clone()),
            ChcExpr::PredicateApp("wide".into(), PredicateId(0), args),
        ),
    ];
    for (input, simplified) in cases {
        let mut calls = 0;
        let (result, polls) = input.simplify_with_poll_count(|| {
            calls += 1;
            calls >= 12
        });
        assert!(result.is_none());
        assert_eq!(calls, 12);
        assert!(
            polls <= 20,
            "cancelled simplifier visited remaining siblings: {polls}"
        );
        assert_eq!(input.simplify_constants_checked(|| false), Some(simplified));
        let mut calls = 0;
        let (result, polls) = input.substitute_with_poll_count(|| {
            calls += 1;
            calls >= 12
        });
        assert!(result.is_none());
        assert_eq!(calls, 12);
        assert!(
            polls <= 20,
            "cancelled substitution visited remaining siblings: {polls}"
        );
        assert_eq!(input.substitute_checked(&[], || false), Some(input.clone()));
    }
}

#[test]
fn shared_array_value_respects_current_depth_and_node_limits() {
    let value = Arc::new(ChcExpr::add(ChcExpr::Int(1), ChcExpr::Int(2)));
    let array = ChcExpr::ConstArray(ChcSort::Int, value.clone());
    let cancelled_array = array.clone();
    let mut deep = array.clone();
    // Root depth 0, first wrapper depth 1, array depth 499, value depth 500.
    for _ in 0..MAX_EXPR_RECURSION_DEPTH - 2 {
        deep = ChcExpr::FuncApp("keep".into(), ChcSort::Int, vec![Arc::new(deep)]);
    }
    let input = ChcExpr::FuncApp(
        "root".into(),
        ChcSort::Int,
        vec![value.clone(), Arc::new(deep.clone())],
    );
    let expected = ChcExpr::FuncApp(
        "root".into(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Int(3)), Arc::new(deep)],
    );
    assert_eq!(input.simplify_constants_checked(|| false), Some(expected));
    let input = ChcExpr::FuncApp(
        "root".into(),
        ChcSort::Int,
        vec![value, Arc::new(array.clone())],
    );
    let expected = ChcExpr::FuncApp(
        "root".into(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Int(3)), Arc::new(array)],
    );
    // Root + Add + two leaves + two collect_add_terms visits consume six
    // nodes; the seventh enters the array, leaving zero for its value.
    assert_eq!(input.simplify_constants_at_node_limit(7), Some(expected));
    let mut calls = 0;
    assert!(cancelled_array
        .simplify_constants_checked(|| {
            calls += 1;
            calls >= 5
        })
        .is_none());
    assert_eq!(calls, 5);
}
