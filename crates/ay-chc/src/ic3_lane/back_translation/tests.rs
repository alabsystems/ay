// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_sat::{Literal, Variable};

use super::*;

fn literal(index: u32, positive: bool) -> Literal {
    let variable = Variable::new(index);
    if positive {
        Literal::positive(variable)
    } else {
        Literal::negative(variable)
    }
}

fn bool_fixture() -> (Vec<ChcVar>, Vec<LatchMeaning>) {
    (
        vec![
            ChcVar::new("a", ChcSort::Bool),
            ChcVar::new("b", ChcSort::Bool),
        ],
        vec![
            LatchMeaning { arg: 0, bit: None },
            LatchMeaning { arg: 1, bit: None },
        ],
    )
}

fn translated_formula(
    params: &[ChcVar],
    latches: &[LatchMeaning],
    clauses: &[Vec<Literal>],
) -> ChcExpr {
    let predicate = PredicateId::new(0);
    let Some(model) = back_translate(predicate, params, latches, clauses) else {
        panic!("the fixture must back-translate");
    };
    let Some(interpretation) = model.get(&predicate) else {
        panic!("the translated model must contain its predicate");
    };
    interpretation.formula.clone()
}

fn expected_iff(params: &[ChcVar]) -> ChcExpr {
    ChcExpr::Op(
        ChcOp::Iff,
        vec![
            Arc::new(ChcExpr::Var(params[0].clone())),
            Arc::new(ChcExpr::Var(params[1].clone())),
        ],
    )
}

fn operation_count(expr: &ChcExpr, wanted: ChcOp) -> usize {
    match expr {
        ChcExpr::Op(operator, args) => {
            usize::from(*operator == wanted)
                + args
                    .iter()
                    .map(|arg| operation_count(arg, wanted))
                    .sum::<usize>()
        }
        ChcExpr::FuncApp(_, _, args) | ChcExpr::PredicateApp(_, _, args) => {
            args.iter().map(|arg| operation_count(arg, wanted)).sum()
        }
        ChcExpr::ConstArray(_, value) => operation_count(value, wanted),
        _ => 0,
    }
}

fn evaluate_two_bool_formula(expr: &ChcExpr, a: bool, b: bool) -> bool {
    match expr {
        ChcExpr::Bool(value) => *value,
        ChcExpr::Var(var) if var.name == "a" => a,
        ChcExpr::Var(var) if var.name == "b" => b,
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            !evaluate_two_bool_formula(args[0].as_ref(), a, b)
        }
        ChcExpr::Op(ChcOp::And, args) => {
            args.iter().all(|arg| evaluate_two_bool_formula(arg, a, b))
        }
        ChcExpr::Op(ChcOp::Or, args) => args.iter().any(|arg| evaluate_two_bool_formula(arg, a, b)),
        ChcExpr::Op(ChcOp::Iff, args) if args.len() == 2 => {
            evaluate_two_bool_formula(args[0].as_ref(), a, b)
                == evaluate_two_bool_formula(args[1].as_ref(), a, b)
        }
        other => panic!("unexpected Boolean fixture expression: {other:?}"),
    }
}

#[test]
fn complementary_implications_compact_to_truth_table_equivalent_iff() {
    let (params, latches) = bool_fixture();
    let clauses = vec![
        vec![literal(0, false), literal(1, true)],
        vec![literal(0, true), literal(1, false)],
    ];
    let formula = translated_formula(&params, &latches, &clauses);
    assert_eq!(formula, expected_iff(&params));

    for a in [false, true] {
        for b in [false, true] {
            assert_eq!(evaluate_two_bool_formula(&formula, a, b), a == b);
        }
    }
}

#[test]
fn complementary_implication_order_does_not_affect_compaction() {
    let (params, latches) = bool_fixture();
    let reordered = vec![
        vec![literal(1, false), literal(0, true)],
        vec![literal(1, true), literal(0, false)],
    ];
    assert_eq!(
        translated_formula(&params, &latches, &reordered),
        expected_iff(&params)
    );
}

#[test]
fn same_sign_and_noncomplementary_near_misses_remain_cnf() {
    let (params, latches) = bool_fixture();
    for clauses in [
        vec![
            vec![literal(0, false), literal(1, false)],
            vec![literal(0, true), literal(1, true)],
        ],
        vec![
            vec![literal(0, false), literal(1, true)],
            vec![literal(0, true), literal(1, true)],
        ],
    ] {
        let formula = translated_formula(&params, &latches, &clauses);
        assert!(matches!(&formula, ChcExpr::Op(ChcOp::And, _)));
        assert_eq!(operation_count(&formula, ChcOp::Iff), 0);
    }
}

#[test]
fn semantically_equal_atoms_do_not_replace_structural_literal_identity() {
    let (params, mut latches) = bool_fixture();
    // Deliberately map two different SAT variables to the same word-level atom.
    // Exact compaction still requires the literal IDs themselves to match.
    latches.push(LatchMeaning { arg: 1, bit: None });
    let clauses = vec![
        vec![literal(0, false), literal(1, true)],
        vec![literal(0, true), literal(2, false)],
    ];
    let formula = translated_formula(&params, &latches, &clauses);

    assert!(matches!(&formula, ChcExpr::Op(ChcOp::And, _)));
    assert_eq!(operation_count(&formula, ChcOp::Iff), 0);
}

#[test]
fn parity_compaction_keeps_one_word_level_mod_occurrence() {
    let params = vec![
        ChcVar::new("acc", ChcSort::Bool),
        ChcVar::new("count", ChcSort::Int),
    ];
    let latches = vec![
        LatchMeaning { arg: 0, bit: None },
        LatchMeaning {
            arg: 1,
            bit: Some(0),
        },
    ];
    let clauses = vec![
        vec![literal(0, false), literal(1, true)],
        vec![literal(0, true), literal(1, false)],
    ];
    let formula = translated_formula(&params, &latches, &clauses);

    assert!(matches!(&formula, ChcExpr::Op(ChcOp::Eq, _)));
    assert_eq!(operation_count(&formula, ChcOp::Iff), 0);
    assert_eq!(operation_count(&formula, ChcOp::Mod), 1);

    for count in -4i128..=4 {
        for acc in [false, true] {
            let value = formula
                .substitute(&[
                    (params[0].clone(), ChcExpr::Bool(acc)),
                    (params[1].clone(), ChcExpr::Int(count)),
                ])
                .simplify_constants();
            assert_eq!(
                value,
                ChcExpr::Bool(acc == (count.rem_euclid(2) == 1)),
                "acc={acc}, count={count}"
            );
        }
    }
}
