// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_flatzinc_parser::ast::FznModel;
use ay_fzn2smt::{solve_cp, Fzn2smtError};

fn parse_model(source: &str) -> FznModel {
    ay_flatzinc_parser::parse_flatzinc(source).expect("test FlatZinc should parse")
}

fn assert_both_translators_accept(name: &str, source: &str) {
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .unwrap_or_else(|err| panic!("{name}: SMT translator rejected model: {err}"));
    assert!(
        smt.smtlib.contains("(check-sat)"),
        "{name}: SMT translator did not emit a check-sat command"
    );

    let unsupported = solve_cp::unsupported_constraints(&model)
        .unwrap_or_else(|err| panic!("{name}: CP translator rejected model: {err}"));
    assert!(
        unsupported.is_empty(),
        "{name}: CP translator marked constraints unsupported: {unsupported:?}"
    );
}

fn count_eq_oracle(values: &[i64], target: i64) -> i64 {
    values.iter().filter(|&&value| value == target).count() as i64
}

#[test]
fn smt_solve_facade_consumes_canonical_translation_result() {
    let _: fn(
        &ay_flatzinc_smt::TranslationResult,
        Option<u64>,
        bool,
        bool,
    ) -> ay_fzn2smt::Result<()> = ay_fzn2smt::solve::cmd_solve;
}

#[test]
fn shared_core_constraints_are_visible_to_both_translators() {
    let cases = [
        (
            "linear_int",
            r#"
            var 0..10: x;
            var 0..10: y;
            constraint int_lin_eq([1, -1], [x, y], 0);
            solve satisfy;
            "#,
        ),
        (
            "bool_logic",
            r#"
            var bool: a;
            var bool: b;
            var bool: r;
            constraint bool_or(a, b, r);
            solve satisfy;
            "#,
        ),
        (
            "all_different",
            r#"
            var 1..3: x;
            var 1..3: y;
            var 1..3: z;
            constraint all_different_int([x, y, z]);
            solve satisfy;
            "#,
        ),
        (
            "set_cardinality",
            r#"
            var set of 1..3: s;
            constraint set_card(s, 2);
            solve satisfy;
            "#,
        ),
        (
            "inverse",
            r#"
            var 1..2: x1;
            var 1..2: x2;
            var 1..2: y1;
            var 1..2: y2;
            constraint inverse([x1, x2], [y1, y2]);
            solve satisfy;
            "#,
        ),
        (
            "circuit",
            r#"
            var 1..3: x1;
            var 1..3: x2;
            var 1..3: x3;
            constraint circuit([x1, x2, x3]);
            solve satisfy;
            "#,
        ),
    ];

    for (name, source) in cases {
        assert_both_translators_accept(name, source);
    }
}

#[test]
fn set_diff_overlap_is_supported_and_aligns_domains() {
    let source = r#"
        var set of 0..2: left;
        var set of 1..2: right;
        var set of 0..2: result;
        constraint set_diff(left, right, result);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_diff overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_diff overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_diff unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib
            .contains("(assert (= result__bit__0 (and left__bit__0 (not false))))"),
        "SMT set_diff should treat right-set values outside its domain as absent"
    );
    assert!(
        smt.smtlib
            .contains("(assert (= result__bit__1 (and left__bit__1 (not right__bit__0))))"),
        "SMT set_diff should align mismatched set domains by element value"
    );
}

#[test]
fn set_symdiff_overlap_is_supported_and_aligns_domains() {
    let source = r#"
        var set of 0..2: left;
        var set of 1..3: right;
        var set of 0..3: result;
        constraint set_symdiff(left, right, result);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_symdiff overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_symdiff overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_symdiff unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib
            .contains("(assert (= result__bit__0 (xor left__bit__0 false)))"),
        "SMT set_symdiff should treat right-set values outside its domain as absent"
    );
    assert!(
        smt.smtlib
            .contains("(assert (= result__bit__1 (xor left__bit__1 right__bit__0)))"),
        "SMT set_symdiff should align mismatched set domains by element value"
    );
    assert!(
        smt.smtlib
            .contains("(assert (= result__bit__3 (xor false right__bit__2)))"),
        "SMT set_symdiff should treat left-set values outside its domain as absent"
    );
}

#[test]
fn set_subset_overlap_is_supported_and_aligns_domains() {
    let source = r#"
        var set of 0..2: left;
        var set of 1..3: right;
        constraint set_subset(left, right);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_subset overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_subset overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_subset unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (=> left__bit__0 false))"),
        "SMT set_subset should forbid left-only values outside the right domain"
    );
    assert!(
        smt.smtlib
            .contains("(assert (=> left__bit__1 right__bit__0))"),
        "SMT set_subset should align mismatched set domains by element value"
    );
    assert!(
        smt.smtlib.contains("(assert (=> false right__bit__2))"),
        "SMT set_subset should treat right-only values as unconstrained by left"
    );
}

#[test]
fn set_superset_overlap_is_supported_and_aligns_domains() {
    let source = r#"
        var set of 0..2: left;
        var set of 1..3: right;
        constraint set_superset(left, right);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_superset overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_superset overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_superset unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (=> false left__bit__0))"),
        "SMT set_superset should treat left-only values as unconstrained by right"
    );
    assert!(
        smt.smtlib
            .contains("(assert (=> right__bit__0 left__bit__1))"),
        "SMT set_superset should align mismatched set domains by element value"
    );
    assert!(
        smt.smtlib.contains("(assert (=> right__bit__2 false))"),
        "SMT set_superset should forbid right-only values outside the left domain"
    );
}

#[test]
fn set_eq_overlap_is_supported_and_aligns_domains() {
    let source = r#"
        var set of 0..2: left;
        var set of 1..3: right;
        constraint set_eq(left, right);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_eq overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_eq overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_eq unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (= left__bit__0 false))"),
        "SMT set_eq should forbid left-only values outside the right domain"
    );
    assert!(
        smt.smtlib
            .contains("(assert (= left__bit__1 right__bit__0))"),
        "SMT set_eq should align mismatched set domains by element value"
    );
    assert!(
        smt.smtlib.contains("(assert (= false right__bit__2))"),
        "SMT set_eq should forbid right-only values outside the left domain"
    );
}

#[test]
fn set_ne_overlap_is_supported_and_aligns_domains() {
    let source = r#"
        var set of 0..2: left;
        var set of 1..3: right;
        constraint set_ne(left, right);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_ne overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_ne overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_ne unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(xor left__bit__0 false)"),
        "SMT set_ne should include left-only values outside the right domain"
    );
    assert!(
        smt.smtlib.contains("(xor left__bit__1 right__bit__0)"),
        "SMT set_ne should align mismatched set domains by element value"
    );
    assert!(
        smt.smtlib.contains("(xor false right__bit__2)"),
        "SMT set_ne should include right-only values outside the left domain"
    );
}

#[test]
fn set_lt_overlap_uses_sorted_list_lexicographic_order() {
    let source = r#"
        var set of 1..2: left;
        var set of 1..2: right;
        constraint set_lt(left, right);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_lt overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_lt overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_lt unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("_setlex"),
        "SMT set_lt should emit the sorted-list lexicographic recurrence"
    );
    assert!(
        !smt.smtlib
            .contains("(assert (=> left__bit__0 right__bit__0))"),
        "SMT set_lt must remain distinct from strict-subset encoding"
    );
}

#[test]
fn set_eq_reif_overlap_is_supported_and_aligns_domains() {
    let source = r#"
        var set of 0..2: left;
        var set of 1..3: right;
        var bool: same;
        constraint set_eq_reif(left, right, same);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_eq_reif overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_eq_reif overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_eq_reif unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (=> same"),
        "SMT set_eq_reif should emit result-to-equality implication"
    );
    assert!(
        smt.smtlib.contains("(= left__bit__0 false)"),
        "SMT set_eq_reif should compare left-only values against false"
    );
    assert!(
        smt.smtlib.contains("(= left__bit__1 right__bit__0)"),
        "SMT set_eq_reif should align mismatched set domains by element value"
    );
    assert!(
        smt.smtlib.contains("(= false right__bit__2)"),
        "SMT set_eq_reif should compare right-only values against false"
    );
}

#[test]
fn set_ne_reif_overlap_is_supported_and_aligns_domains() {
    let source = r#"
        var set of 0..2: left;
        var set of 1..3: right;
        var bool: different;
        constraint set_ne_reif(left, right, different);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_ne_reif overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_ne_reif overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_ne_reif unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (=> different"),
        "SMT set_ne_reif should emit result-to-difference implication"
    );
    assert!(
        smt.smtlib.contains("(xor left__bit__0 false)"),
        "SMT set_ne_reif should compare left-only values against false"
    );
    assert!(
        smt.smtlib.contains("(xor left__bit__1 right__bit__0)"),
        "SMT set_ne_reif should align mismatched set domains by element value"
    );
    assert!(
        smt.smtlib.contains("(xor false right__bit__2)"),
        "SMT set_ne_reif should compare right-only values against false"
    );
}

#[test]
fn set_subset_reif_overlap_is_supported_and_aligns_domains() {
    let source = r#"
        var set of 0..2: left;
        var set of 1..3: right;
        var bool: subset;
        constraint set_subset_reif(left, right, subset);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_subset_reif overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_subset_reif overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_subset_reif unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (=> subset"),
        "SMT set_subset_reif should emit result-to-subset implication"
    );
    assert!(
        smt.smtlib.contains("(=> left__bit__0 false)"),
        "SMT set_subset_reif should reject left-only values"
    );
    assert!(
        smt.smtlib.contains("(=> left__bit__1 right__bit__0)"),
        "SMT set_subset_reif should align mismatched set domains by element value"
    );
    assert!(
        smt.smtlib.contains("(=> false right__bit__2)"),
        "SMT set_subset_reif should treat right-only values as non-violating"
    );
}

#[test]
fn set_superset_reif_overlap_is_supported_and_aligns_domains() {
    let source = r#"
        var set of 0..2: left;
        var set of 1..3: right;
        var bool: superset;
        constraint set_superset_reif(left, right, superset);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_superset_reif overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_superset_reif overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_superset_reif unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (=> superset"),
        "SMT set_superset_reif should emit result-to-superset implication"
    );
    assert!(
        smt.smtlib.contains("(=> false left__bit__0)"),
        "SMT set_superset_reif should treat left-only values as non-violating"
    );
    assert!(
        smt.smtlib.contains("(=> right__bit__0 left__bit__1)"),
        "SMT set_superset_reif should align mismatched set domains by element value"
    );
    assert!(
        smt.smtlib.contains("(=> right__bit__2 false)"),
        "SMT set_superset_reif should reject right-only values"
    );
}

#[test]
fn set_le_reif_overlap_is_supported_and_aligns_domains() {
    let source = r#"
        var set of 0..2: left;
        var set of 1..3: right;
        var bool: le;
        constraint set_le_reif(left, right, le);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_le_reif overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_le_reif overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_le_reif unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (= le _setlex"),
        "SMT set_le_reif should equate the result with sorted-list lex order"
    );
    assert!(
        smt.smtlib.contains("_any1"),
        "SMT set_le_reif should track whether the left suffix is non-empty"
    );
    assert!(
        smt.smtlib.contains("_any2"),
        "SMT set_le_reif should track whether the right suffix is non-empty"
    );
    assert!(
        !smt.smtlib.contains("(=> left__bit__0 false)"),
        "SMT set_le_reif must not delegate to subset reification"
    );
}

#[test]
fn set_lt_reif_overlap_uses_sorted_list_lexicographic_order() {
    let source = r#"
        var set of 0..2: left;
        var set of 1..3: right;
        var bool: lt;
        constraint set_lt_reif(left, right, lt);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept set_lt_reif overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect set_lt_reif overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked set_lt_reif unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (= lt _setlex"),
        "SMT set_lt_reif should equate the result with strict sorted-list lex order"
    );
    assert!(
        smt.smtlib.contains("_any1"),
        "SMT set_lt_reif should track the left suffix"
    );
    assert!(
        smt.smtlib.contains("_any2"),
        "SMT set_lt_reif should track the right suffix"
    );
    assert!(
        !smt.smtlib.contains("(=> left__bit__0 false)"),
        "SMT set_lt_reif must remain distinct from strict-subset reification"
    );
}

#[test]
fn shared_counting_constraints_are_visible_to_both_translators() {
    let cases = [
        (
            "count_variants",
            r#"
            var 1..3: x1;
            var 1..3: x2;
            var 1..3: x3;
            var 1..3: target;
            var 0..3: count;
            array [1..3] of var int: xs = [x1, x2, x3];
            constraint fzn_count_eq(xs, target, count);
            constraint fzn_count_neq(xs, 1, 3);
            constraint fzn_count_lt(xs, 2, 3);
            constraint fzn_count_gt(xs, 2, 0);
            constraint fzn_count_leq(xs, 3, 0);
            constraint fzn_count_geq(xs, 3, 3);
            solve satisfy;
            "#,
        ),
        (
            "global_cardinality",
            r#"
            var 1..2: x1;
            var 1..2: x2;
            var 1..2: x3;
            var 0..3: c1;
            var 0..3: c2;
            array [1..3] of var int: xs = [x1, x2, x3];
            array [1..2] of var int: counts = [c1, c2];
            constraint fzn_global_cardinality(xs, [1, 2], counts);
            solve satisfy;
            "#,
        ),
        (
            "nvalue",
            r#"
            var 1..3: x1;
            var 1..3: x2;
            var 1..3: x3;
            var 0..3: n;
            array [1..3] of var int: xs = [x1, x2, x3];
            constraint fzn_nvalue(n, xs);
            solve satisfy;
            "#,
        ),
    ];

    for (name, source) in cases {
        assert_both_translators_accept(name, source);
    }
}

#[test]
fn count_eq_overlap_has_expected_tiny_semantics() {
    let source = r#"
        var 1..3: x1;
        var 1..3: x2;
        var 1..3: x3;
        var 0..3: count :: output_var;
        constraint fzn_count_eq([x1, x2, x3], 2, count);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept count_eq overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect count_eq overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked count_eq unsupported: {unsupported:?}"
    );

    assert!(smt.smtlib.contains("(assert (= (+"));
    assert!(smt.smtlib.contains("(ite (= x1 2) 1 0)"));
    assert!(smt.smtlib.contains("(ite (= x2 2) 1 0)"));
    assert!(smt.smtlib.contains("(ite (= x3 2) 1 0)"));
    assert!(smt.smtlib.contains(" count))"));

    for (values, expected_count) in [
        ([1, 1, 1], 0),
        ([2, 1, 3], 1),
        ([1, 2, 2], 2),
        ([2, 2, 2], 3),
    ] {
        assert_eq!(count_eq_oracle(&values, 2), expected_count);
    }
}

#[test]
fn count_leq_geq_overlap_uses_minizinc_argument_order() {
    let source = r#"
        var 1..3: x1;
        var 1..3: x2;
        var 1..3: x3;
        var 0..3: lower;
        var 0..3: upper;
        constraint fzn_count_leq([x1, x2, x3], 2, lower);
        constraint fzn_count_geq([x1, x2, x3], 2, upper);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept count_leq/geq overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect count_leq/geq overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked count_leq/geq unsupported: {unsupported:?}"
    );

    let occurrence_count = "(+ (ite (= x1 2) 1 0) (ite (= x2 2) 1 0) (ite (= x3 2) 1 0))";
    assert!(smt
        .smtlib
        .contains(&format!("(assert (<= lower {occurrence_count}))")));
    assert!(smt
        .smtlib
        .contains(&format!("(assert (>= upper {occurrence_count}))")));

    assert!(1 <= count_eq_oracle(&[2, 2, 2], 2));
    assert!(2 >= count_eq_oracle(&[2, 2, 5], 2));
}

#[test]
fn inverse_overlap_enforces_one_based_index_ranges() {
    let source = r#"
        var 0..3: f1;
        var 0..3: f2;
        var 0..3: g1;
        var 0..3: g2;
        constraint fzn_inverse([f1, f2], [g1, g2]);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept inverse overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect inverse overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked inverse unsupported: {unsupported:?}"
    );

    for var in ["f1", "f2", "g1", "g2"] {
        assert!(
            smt.smtlib
                .contains(&format!("(assert (and (>= {var} 1) (<= {var} 2)))")),
            "SMT inverse encoding should constrain {var} to the 1..2 index range"
        );
    }

    for value in [1, 2] {
        assert!((1..=2).contains(&value));
    }
    assert!(!(1..=2).contains(&0));
}

#[test]
fn circuit_overlap_enforces_one_based_successor_ranges() {
    let source = r#"
        var 0..4: s1;
        var 0..4: s2;
        var 0..4: s3;
        constraint fzn_circuit([s1, s2, s3]);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept circuit overlap model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect circuit overlap model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked circuit unsupported: {unsupported:?}"
    );

    for var in ["s1", "s2", "s3"] {
        assert!(
            smt.smtlib
                .contains(&format!("(assert (and (>= {var} 1) (<= {var} 3)))")),
            "SMT circuit encoding should constrain {var} to the 1..3 successor range"
        );
    }

    for value in [1, 2, 3] {
        assert!((1..=3).contains(&value));
    }
    assert!(!(1..=3).contains(&4));
}

#[test]
fn nvalue_overlap_empty_array_is_zero() {
    let source = r#"
        var 0..1: n;
        constraint fzn_nvalue(n, []);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept empty nvalue model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect empty nvalue model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked empty nvalue unsupported: {unsupported:?}"
    );
    assert!(smt.smtlib.contains("(assert (= n 0))"));
}

#[test]
fn global_cardinality_overlap_rejects_cover_count_length_mismatch() {
    let source = r#"
        var 1..2: x;
        var 0..1: c;
        constraint fzn_global_cardinality([x], [1, 2], [c]);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt_err = ay_flatzinc_smt::translate(&model)
        .expect_err("SMT translator should reject global_cardinality length mismatch");
    assert!(
        smt_err
            .to_string()
            .contains("cover and counts length mismatch"),
        "unexpected SMT error: {smt_err}"
    );

    let cp_err = solve_cp::unsupported_constraints(&model)
        .expect_err("CP translator should reject global_cardinality length mismatch");
    match cp_err {
        Fzn2smtError::GlobalCardinalityLengthMismatch { cover, counts } => {
            assert_eq!(cover, 2);
            assert_eq!(counts, 1);
        }
        other => panic!("expected GlobalCardinalityLengthMismatch, got {other:?}"),
    }
}

#[test]
fn table_int_overlap_rejects_tuple_length_mismatch() {
    let source = r#"
        var 1..3: x;
        var 1..3: y;
        constraint table_int([x, y], [1, 2, 3]);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt_err = ay_flatzinc_smt::translate(&model)
        .expect_err("SMT translator should reject table_int tuple length mismatch");
    assert!(
        smt_err
            .to_string()
            .contains("tuple array length 3 not divisible by arity 2"),
        "unexpected SMT error: {smt_err}"
    );

    let cp_err = solve_cp::unsupported_constraints(&model)
        .expect_err("CP translator should reject table_int tuple length mismatch");
    match cp_err {
        Fzn2smtError::TableTupleLengthMismatch { values, arity } => {
            assert_eq!(values, 3);
            assert_eq!(arity, 2);
        }
        other => panic!("expected TableTupleLengthMismatch, got {other:?}"),
    }
}

#[test]
fn cumulative_overlap_rejects_array_length_mismatch() {
    let source = r#"
        var 0..5: s;
        constraint fzn_cumulative([s], [1, 2], [1], 2);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt_err = ay_flatzinc_smt::translate(&model)
        .expect_err("SMT translator should reject cumulative length mismatch");
    assert!(
        smt_err
            .to_string()
            .contains("cumulative: array length mismatch"),
        "unexpected SMT error: {smt_err}"
    );

    let cp_err = solve_cp::unsupported_constraints(&model)
        .expect_err("CP translator should reject cumulative length mismatch");
    match cp_err {
        Fzn2smtError::CumulativeArrayLengthMismatch {
            starts,
            durations,
            resources,
        } => {
            assert_eq!(starts, 1);
            assert_eq!(durations, 2);
            assert_eq!(resources, 1);
        }
        other => panic!("expected CumulativeArrayLengthMismatch, got {other:?}"),
    }
}

#[test]
fn diffn_overlap_rejects_array_length_mismatch() {
    let source = r#"
        var 0..5: x;
        var 0..5: y;
        constraint fzn_diffn([x], [y], [1, 2], [1]);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt_err = ay_flatzinc_smt::translate(&model)
        .expect_err("SMT translator should reject diffn length mismatch");
    assert!(
        smt_err.to_string().contains("diffn: array length mismatch"),
        "unexpected SMT error: {smt_err}"
    );

    let cp_err = solve_cp::unsupported_constraints(&model)
        .expect_err("CP translator should reject diffn length mismatch");
    match cp_err {
        Fzn2smtError::DiffnArrayLengthMismatch { x, y, dx, dy } => {
            assert_eq!(x, 1);
            assert_eq!(y, 1);
            assert_eq!(dx, 2);
            assert_eq!(dy, 1);
        }
        other => panic!("expected DiffnArrayLengthMismatch, got {other:?}"),
    }
}

#[test]
fn array_int_element_overlap_rejects_empty_array() {
    let source = r#"
        var 1..1: idx;
        var 0..1: val;
        constraint array_int_element(idx, [], val);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt_err = ay_flatzinc_smt::translate(&model)
        .expect_err("SMT translator should reject empty array element");
    assert!(
        smt_err
            .to_string()
            .contains("array_int_element: empty array"),
        "unexpected SMT error: {smt_err}"
    );

    let cp_err = solve_cp::unsupported_constraints(&model)
        .expect_err("CP translator should reject empty array element");
    match cp_err {
        Fzn2smtError::ArrayElementEmptyArray { constraint } => {
            assert_eq!(constraint, "array_int_element");
        }
        other => panic!("expected ArrayElementEmptyArray, got {other:?}"),
    }
}

#[test]
fn array_int_element_overlap_enforces_one_based_index_range() {
    let source = r#"
        var 0..4: idx;
        var 0..40: val;
        constraint array_int_element(idx, [10, 20, 30], val);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept array_int_element range guard model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect array_int_element range guard model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked array_int_element unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (and (>= idx 1) (<= idx 3)))"),
        "SMT array element encoding should constrain idx to the 1..3 index range"
    );
}

#[test]
fn array_var_int_element_overlap_enforces_one_based_index_range() {
    let source = r#"
        var 0..4: idx;
        var 0..40: x;
        var 0..40: y;
        var 0..40: z;
        var 0..40: val;
        constraint array_var_int_element(idx, [x, y, z], val);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept array_var_int_element range guard model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect array_var_int_element range guard model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked array_var_int_element unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (and (>= idx 1) (<= idx 3)))"),
        "SMT array var element encoding should constrain idx to the 1..3 index range"
    );
}

#[test]
fn array_var_int_element_overlap_rejects_zero_index_by_guard() {
    let source = r#"
        var 0..3: idx;
        var 0..40: x;
        var 0..40: y;
        var 0..40: z;
        var 0..40: val;
        constraint int_eq(idx, 0);
        constraint array_var_int_element(idx, [x, y, z], val);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept guarded out-of-range index model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect guarded out-of-range index model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked array_var_int_element unsupported: {unsupported:?}"
    );

    assert!(smt.smtlib.contains("(assert (= idx 0))"));
    assert!(
        smt.smtlib.contains("(assert (and (>= idx 1) (<= idx 3)))"),
        "SMT array var element encoding should preserve the contradiction for idx=0"
    );
}

#[test]
fn named_array_var_int_element_fixed_slots_proxy_is_cp_supported() {
    let source =
        include_str!("../../../benchmarks/minizinc/challenge/array_var_element_fallback_proxy.fzn");
    let model = parse_model(source);

    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect named array_var_int_element proxy");
    assert!(
        unsupported.is_empty(),
        "CP translator should support fixed-slot named array_var_int_element proxy, got {unsupported:?}"
    );
}

#[test]
fn named_array_var_int_element_materialized_slot_is_cp_supported() {
    let source = r#"
        array [1..3] of var 1..3: xs;
        var 1..3: idx;
        var 1..3: val;
        constraint int_eq(xs[1], 1);
        constraint int_eq(xs[3], 3);
        constraint array_var_int_element(idx, xs, val);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect materialized array element model");
    assert!(
        unsupported.is_empty(),
        "bounded uninitialized slots should be materialized for named array elements, got {unsupported:?}"
    );
}

#[test]
fn array_bool_element_overlap_enforces_one_based_index_range() {
    let source = r#"
        var 0..3: idx;
        var bool: val;
        constraint array_bool_element(idx, [true, false], val);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept array_bool_element range guard model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect array_bool_element range guard model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked array_bool_element unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (and (>= idx 1) (<= idx 2)))"),
        "SMT array bool element encoding should constrain idx to the 1..2 index range"
    );
}

#[test]
fn array_var_bool_element_overlap_rejects_zero_index_by_guard() {
    let source = r#"
        var 0..3: idx;
        var bool: a;
        var bool: b;
        var bool: val;
        constraint int_eq(idx, 0);
        constraint array_var_bool_element(idx, [a, b], val);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept guarded bool out-of-range index model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect guarded bool out-of-range index model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked array_var_bool_element unsupported: {unsupported:?}"
    );

    assert!(smt.smtlib.contains("(assert (= idx 0))"));
    assert!(
        smt.smtlib.contains("(assert (and (>= idx 1) (<= idx 2)))"),
        "SMT array var bool element encoding should preserve the contradiction for idx=0"
    );
}

#[test]
fn array_set_element_overlap_rejects_empty_array() {
    let source = r#"
        array [1..0] of set of int: arr = [];
        var 1..1: idx;
        var set of 0..1: result;
        constraint array_set_element(idx, arr, result);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt_err = ay_flatzinc_smt::translate(&model)
        .expect_err("SMT translator should reject empty set array element");
    assert!(
        smt_err
            .to_string()
            .contains("array_set_element: empty array"),
        "unexpected SMT error: {smt_err}"
    );

    let cp_err = solve_cp::unsupported_constraints(&model)
        .expect_err("CP translator should reject empty set array element");
    match cp_err {
        Fzn2smtError::ArrayElementEmptyArray { constraint } => {
            assert_eq!(constraint, "array_set_element");
        }
        other => panic!("expected ArrayElementEmptyArray, got {other:?}"),
    }
}

#[test]
fn array_set_element_overlap_uses_declared_index_range() {
    let source = r#"
        array [0..1] of set of int: arr = [{0}, {1}];
        var -1..2: idx;
        var set of 0..1: result;
        constraint array_set_element(idx, arr, result);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept array_set_element range guard model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect array_set_element range guard model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked array_set_element unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (and (>= idx 0) (<= idx 1)))"),
        "SMT array set element encoding should constrain idx to the declared 0..1 index range"
    );
    assert!(
        smt.smtlib
            .contains("(assert (= result__bit__0 (ite (= idx 0) true false)))"),
        "SMT array set element encoding should select the first entry at FlatZinc index 0"
    );
}

#[test]
fn array_set_element_set_var_literal_overlap_is_supported() {
    let source = r#"
        var set of 0..1: a;
        var set of 0..1: b;
        var 0..3: idx;
        var set of 0..1: result;
        constraint array_set_element(idx, [a, b], result);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept array_set_element set-var literal model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect array_set_element set-var literal model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked array_set_element set-var literal unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (and (>= idx 1) (<= idx 2)))"),
        "SMT array set element encoding should constrain idx to the 1..2 index range"
    );
    assert!(
        smt.smtlib
            .contains("(assert (= result__bit__0 (ite (= idx 1) a__bit__0 b__bit__0)))"),
        "SMT array set element encoding should select source set bits by index"
    );
}

#[test]
fn array_set_element_empty_literal_overlap_rejects_empty_array() {
    let source = r#"
        var 1..1: idx;
        var set of 0..1: result;
        constraint array_set_element(idx, [], result);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt_err = ay_flatzinc_smt::translate(&model)
        .expect_err("SMT translator should reject empty set array literal element");
    assert!(
        smt_err
            .to_string()
            .contains("array_set_element: empty array"),
        "unexpected SMT error: {smt_err}"
    );

    let cp_err = solve_cp::unsupported_constraints(&model)
        .expect_err("CP translator should reject empty set array literal element");
    match cp_err {
        Fzn2smtError::ArrayElementEmptyArray { constraint } => {
            assert_eq!(constraint, "array_set_element");
        }
        other => panic!("expected ArrayElementEmptyArray, got {other:?}"),
    }
}

#[test]
fn array_set_element_named_set_var_array_overlap_is_supported() {
    let source = r#"
        var set of 0..1: a;
        var set of 0..1: b;
        array [1..2] of var set of 0..1: arr = [a, b];
        var 0..3: idx;
        var set of 0..1: result;
        constraint array_set_element(idx, arr, result);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt = ay_flatzinc_smt::translate(&model)
        .expect("SMT translator should accept named set-var array element model");
    let unsupported = solve_cp::unsupported_constraints(&model)
        .expect("CP translator should inspect named set-var array element model");
    assert!(
        unsupported.is_empty(),
        "CP translator marked named set-var array element unsupported: {unsupported:?}"
    );

    assert!(
        smt.smtlib.contains("(assert (and (>= idx 1) (<= idx 2)))"),
        "SMT array set element encoding should constrain idx to the 1..2 index range"
    );
    assert!(
        smt.smtlib
            .contains("(assert (= result__bit__0 (ite (= idx 1) a__bit__0 b__bit__0)))"),
        "SMT named set array encoding should select source set bits by index"
    );
}

#[test]
fn array_set_element_empty_named_set_var_array_overlap_rejects_empty_array() {
    let source = r#"
        array [1..0] of var set of 0..1: arr = [];
        var 1..1: idx;
        var set of 0..1: result;
        constraint array_set_element(idx, arr, result);
        solve satisfy;
    "#;
    let model = parse_model(source);

    let smt_err = ay_flatzinc_smt::translate(&model)
        .expect_err("SMT translator should reject empty named set-var array element");
    assert!(
        smt_err
            .to_string()
            .contains("array_set_element: empty array"),
        "unexpected SMT error: {smt_err}"
    );

    let cp_err = solve_cp::unsupported_constraints(&model)
        .expect_err("CP translator should reject empty named set-var array element");
    match cp_err {
        Fzn2smtError::ArrayElementEmptyArray { constraint } => {
            assert_eq!(constraint, "array_set_element");
        }
        other => panic!("expected ArrayElementEmptyArray, got {other:?}"),
    }
}

#[test]
fn shared_reified_constraints_are_visible_to_both_translators() {
    let cases = [
        (
            "int_comparison_reification",
            r#"
            var 0..5: x;
            var 0..5: y;
            var bool: eq;
            var bool: ne;
            var bool: lt;
            var bool: le;
            var bool: gt;
            var bool: ge;
            constraint int_eq_reif(x, y, eq);
            constraint int_ne_reif(x, y, ne);
            constraint int_lt_reif(x, y, lt);
            constraint int_le_reif(x, y, le);
            constraint int_gt_reif(x, y, gt);
            constraint int_ge_reif(x, y, ge);
            solve satisfy;
            "#,
        ),
        (
            "linear_reification",
            r#"
            var 0..5: x;
            var 0..5: y;
            var bool: eq;
            var bool: le;
            var bool: ne;
            array [1..2] of var int: xs = [x, y];
            constraint int_lin_eq_reif([1, 1], xs, 5, eq);
            constraint int_lin_le_reif([1, -1], xs, 0, le);
            constraint int_lin_ne_reif([2, 1], xs, 3, ne);
            solve satisfy;
            "#,
        ),
        (
            "bool_and_set_membership_reification",
            r#"
            var bool: a;
            var bool: b;
            var bool: same;
            var 1..5: x;
            var bool: in_sparse_set;
            constraint bool_eq_reif(a, b, same);
            constraint set_in_reif(x, {1, 3, 5}, in_sparse_set);
            solve satisfy;
            "#,
        ),
    ];

    for (name, source) in cases {
        assert_both_translators_accept(name, source);
    }
}
