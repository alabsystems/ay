// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! OMT (Optimization Modulo Theories) tests for direct execution (#6702).
//!
//! Verifies that maximize/minimize/get-objectives go through the OMT
//! executor bridge without returning NeedsFallback.

use super::*;

/// Maximize on Int objective returns SAT and does not fall back.
#[test]
fn test_omt_maximize_int_sat_6702() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(x.clone().int_le(Expr::int(10)));
    program.assert(x.clone().int_ge(Expr::int(0)));
    program.maximize(x);
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "OMT maximize should not fall back after #6702, got: {result:?}"
    );
    assert!(
        matches!(
            result,
            ExecuteResult::Counterexample { .. } | ExecuteResult::Unknown(_)
        ),
        "expected SAT or Unknown for OMT maximize, got: {result:?}"
    );
}

/// Minimize on Real objective returns SAT and does not fall back.
#[test]
fn test_omt_minimize_real_sat_6702() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");
    let y = program.declare_const("y", Sort::real());
    program.assert(y.clone().real_ge(Expr::real(1))); // y >= 1
    program.assert(y.clone().real_le(Expr::real(5))); // y <= 5
    program.minimize(y);
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "OMT minimize should not fall back after #6702, got: {result:?}"
    );
    assert!(
        matches!(
            result,
            ExecuteResult::Counterexample { .. } | ExecuteResult::Unknown(_)
        ),
        "expected SAT or Unknown for OMT minimize, got: {result:?}"
    );
}

/// Two-objective lexicographic optimization preserves declaration order.
#[test]
fn test_omt_lexicographic_two_objectives_6702() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    let y = program.declare_const("y", Sort::int());
    // x in [0, 10], y in [0, 10], x + y <= 15
    program.assert(x.clone().int_ge(Expr::int(0)));
    program.assert(x.clone().int_le(Expr::int(10)));
    program.assert(y.clone().int_ge(Expr::int(0)));
    program.assert(y.clone().int_le(Expr::int(10)));
    program.assert(x.clone().int_add(y.clone()).int_le(Expr::int(15)));
    // Maximize x first, then maximize y
    program.maximize(x);
    program.maximize(y);
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "OMT lexicographic should not fall back, got: {result:?}"
    );
}

/// get-objectives after optimization returns non-empty output.
#[test]
fn test_omt_get_objectives_output_6702() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(x.clone().int_ge(Expr::int(0)));
    program.assert(x.clone().int_le(Expr::int(42)));
    program.maximize(x);
    program.check_sat();
    program.get_objectives();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "OMT with get-objectives should not fall back, got: {result:?}"
    );
}

/// SoftAssert still returns NeedsFallback (not handled by OMT bridge).
#[test]
fn test_omt_soft_assert_still_fallback_6702() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.soft_assert(x.int_ge(Expr::int(0)), 1);
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        matches!(result, ExecuteResult::NeedsFallback(_)),
        "SoftAssert should still fall back, got: {result:?}"
    );
}

/// The model of an OMT program over a list datatype named `sort_name`, read
/// back through `execute_typed`.
///
/// `list_nil` is the list's nullary constructor and `other_nil` the nullary
/// constructor of a second datatype, `Other`. The program also asserts a
/// record `r` holding a string with `|`, `)` and the text of an ascription
/// and the constructors `|x` and `y|`, negative integers, and `p`, a value of
/// a constructor named `as`. `as_over_list` makes the second field of `as` a
/// list instead of an enumeration.
fn omt_list_model(
    sort_name: &str,
    list_nil: &str,
    other_nil: &str,
    as_over_list: bool,
) -> ExecuteValueMap<ModelValue> {
    let no_fields = Vec::<(&str, Sort)>::new;
    let list = Sort::enum_type(
        sort_name,
        [
            (list_nil, no_fields()),
            (
                "cons",
                vec![("hd", Sort::int()), ("tl", Sort::datatype_ref(sort_name))],
            ),
        ],
    );
    let other = Sort::enum_type(
        "Other",
        [
            (other_nil, no_fields()),
            ("omk", vec![("ofst", Sort::int())]),
        ],
    );
    let enumeration = Sort::enum_type("E", [("e1", no_fields()), ("e2", no_fields())]);
    let odd = Sort::enum_type("Odd", [("|x", no_fields()), ("y|", no_fields())]);
    let second = if as_over_list {
        list.clone()
    } else {
        enumeration.clone()
    };
    let pair = Sort::enum_type(
        "P",
        [("as", vec![("f1", list.clone()), ("f2", second.clone())])],
    );
    let record = Sort::enum_type(
        "Rec",
        [(
            "rec",
            vec![
                ("label", Sort::string()),
                ("o1", odd.clone()),
                ("tail", list.clone()),
                ("o2", odd.clone()),
                ("last", list.clone()),
                ("count", Sort::int()),
            ],
        )],
    );
    let mut program = AYProgram::new();
    for sort in [&list, &other, &enumeration, &odd, &pair, &record] {
        program.declare_datatype(sort.datatype_sort().expect("a datatype").clone());
    }
    let nil = || Expr::datatype_constructor(sort_name, list_nil, vec![], list.clone());
    let cons = |head: i64, tail: Expr| {
        Expr::datatype_constructor(sort_name, "cons", vec![Expr::int(head), tail], list.clone())
    };
    let odd_value = |name: &str| Expr::datatype_constructor("Odd", name, vec![], odd.clone());
    let top = program.declare_const("top", list.clone());
    let two = program.declare_const("two", list.clone());
    let r = program.declare_const("r", record.clone());
    let p = program.declare_const("p", pair.clone());
    let o = program.declare_const("o", other.clone());
    let n = program.declare_const("n", Sort::int());
    program.assert(top.eq(nil()));
    program.assert(two.eq(cons(1, cons(-2, nil()))));
    program.assert(r.eq(Expr::datatype_constructor(
        "Rec",
        "rec",
        vec![
            Expr::string_const("| (as nil L1) )"),
            odd_value("|x"),
            nil(),
            odd_value("y|"),
            nil(),
            Expr::int(-7),
        ],
        record.clone(),
    )));
    // `p` is pinned through its selectors, not built by applying `as`.
    program.assert(p.clone().field_select("P", "f1", list.clone()).eq(nil()));
    let second_value = if as_over_list {
        cons(1, nil())
    } else {
        Expr::datatype_constructor("E", "e1", vec![], enumeration.clone())
    };
    program.assert(p.field_select("P", "f2", second).eq(second_value));
    program.assert(o.eq(Expr::datatype_constructor(
        "Other",
        other_nil,
        vec![],
        other.clone(),
    )));
    program.assert(n.clone().int_le(Expr::int(-5)));
    program.maximize(n);
    program.check_sat();
    program.get_model();

    match execute_typed(&program).expect("the OMT bridge runs") {
        ExecuteTypedResult::Counterexample(counterexample) => counterexample.model,
        other => panic!("expected a model for {list_nil}/{other_nil}, got {other:?}"),
    }
}

/// End to end through `execute_typed`, with `Other` sharing the list's
/// constructor name: here `top`, `two`, `r`, `n` and `o` read as the values
/// asserted below.
#[test]
fn test_omt_quoted_sort_with_space_reads_at_token_boundaries() {
    let string = |text: &str| ModelValue::String(text.to_string());
    for sort in ["My List", "L1", "L (1"] {
        for constructor in ["nil", "pop", "a#b", "my nil", "a|b"] {
            let model = omt_list_model(sort, constructor, constructor, false);
            assert_eq!(model.get("top"), Some(&string(constructor)), "{model:?}");
            assert_eq!(
                model.get("two"),
                Some(&string(&format!("(cons 1 (cons -2 {constructor}))"))),
                "{model:?}"
            );
            assert_eq!(
                model.get("r"),
                Some(&string(&format!(
                    "(rec \"| (as nil L1) )\" |x {constructor} y| {constructor} -7)"
                ))),
                "{model:?}"
            );
            assert_eq!(model.get("n"), Some(&ModelValue::Int((-5).into())));
            assert_eq!(model.get("o"), Some(&string(constructor)), "{model:?}");
        }
    }
}

/// End to end through `execute_typed` (#overloaded-nil-surface): for each
/// sort and name below, the values other than `o`, the partner itself, are
/// the same whether or not `Other` shares the list's constructor name.
#[test]
fn test_omt_overloaded_constructor_reads_as_when_the_partner_is_renamed() {
    for sort in ["My List", "L1"] {
        for constructor in [
            "nil", "pop", "a#b", "my nil", "a|b", "|x", "true", "false", ":k",
        ] {
            for as_over_list in [false, true] {
                let mut overloaded = omt_list_model(sort, constructor, constructor, as_over_list);
                let mut renamed = omt_list_model(sort, constructor, "unshared", as_over_list);
                let context = format!("{sort} {constructor} {as_over_list}: {overloaded:?}");
                // `o` is the partner itself, named differently by the two
                // programs.
                assert!(overloaded.remove("o").is_some(), "{context}");
                assert_eq!(
                    renamed.remove("o"),
                    Some(ModelValue::String("unshared".to_string()))
                );
                assert_eq!(overloaded.len(), 5, "{context}");
                assert_eq!(overloaded, renamed, "{context}");
            }
        }
    }
}

/// End to end through `execute_typed`: a constructor named
/// `x (as nil L1) y` reads back as that name, whole, whether or not a second
/// datatype shares it.
#[test]
fn test_omt_constructor_name_holding_ascription_text_is_returned_whole() {
    let name = "x (as nil L1) y";
    for sort in ["L1", "My List"] {
        let mut overloaded = omt_list_model(sort, name, name, false);
        let mut renamed = omt_list_model(sort, name, "unshared", false);
        assert_eq!(
            overloaded.get("top"),
            Some(&ModelValue::String(name.to_string())),
            "{overloaded:?}"
        );
        assert_eq!(overloaded.remove("o"), overloaded.get("top").cloned());
        assert_eq!(
            renamed.remove("o"),
            Some(ModelValue::String("unshared".to_string()))
        );
        assert_eq!(overloaded, renamed);
    }
}
