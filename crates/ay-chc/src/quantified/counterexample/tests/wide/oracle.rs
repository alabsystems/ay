// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source evaluation independent of native solving, key parsing and pin output.

use super::*;
use ay_core::kani_compat::DetHashMap;

pub(super) fn arguments(source: &QuantifiedChcProblem, occurrence: usize) -> &[ChcExpr] {
    let clause = &source.source_problem().clauses()[occurrence];
    if occurrence == 0 {
        let ClauseHead::Predicate(_, arguments) = &clause.head else {
            panic!("fact head")
        };
        arguments
    } else {
        &clause.body.predicates[0].1
    }
}

pub(super) fn unsigned(value: &SmtValue) -> (BigUint, u32) {
    match value {
        SmtValue::BitVec(value, width) => (BigUint::from(*value), *width),
        SmtValue::BigBitVec(value, width) => (value.as_ref().clone(), *width),
        _ => panic!("complete exact unsigned bitvector"),
    }
}

pub(super) fn read(array: &SmtValue, key: &SmtValue) -> SmtValue {
    match array {
        SmtValue::ConstArray(default) => default.as_ref().clone(),
        SmtValue::ArrayMap { default, entries } => entries
            .iter()
            .rev()
            .find(|(index, _)| unsigned(index) == unsigned(key))
            .map_or_else(|| default.as_ref().clone(), |(_, value)| value.clone()),
        _ => panic!("complete array"),
    }
}

fn values(table: Table, cells: Cells) -> Vec<SmtValue> {
    let (low, high) = table.keys();
    let low = SmtValue::try_bitvec_from_biguint(low, table.width()).unwrap();
    let high = SmtValue::try_bitvec_from_biguint(high, table.width()).unwrap();
    let table = SmtValue::ArrayMap {
        default: Box::new(SmtValue::BitVec(0, 8)),
        entries: vec![
            (low.clone(), SmtValue::BitVec(7, 8)),
            (high.clone(), SmtValue::BitVec(9, 8)),
        ],
    };
    let data = match cells {
        Cells::Filled => SmtValue::ConstArray(Box::new(SmtValue::BitVec(7, 8))),
        Cells::CorruptLast => SmtValue::ArrayMap {
            default: Box::new(SmtValue::BitVec(7, 8)),
            entries: vec![(SmtValue::BitVec(64, 64), SmtValue::BitVec(8, 8))],
        },
    };
    vec![table, low, high, data]
}

fn environment(arguments: &[ChcExpr], values: &[SmtValue]) -> DetHashMap<String, SmtValue> {
    assert_eq!(arguments.len(), values.len());
    arguments
        .iter()
        .zip(values)
        .map(|(argument, value)| {
            let ChcExpr::Var(variable) = argument else {
                panic!("source argument")
            };
            (variable.name.clone(), value.clone())
        })
        .collect()
}

pub(super) fn check_sources() {
    for table in [Table::Float32, Table::Call, Table::Float64] {
        let (low, high) = table.keys();
        let distinguishing_bit = match table {
            Table::Float32 => 66usize,
            Table::Call => 127,
            Table::Float64 => 130,
        };
        assert_eq!(&high ^ &low, BigUint::from(1u8) << distinguishing_bit);
        assert_eq!(high.bits(), distinguishing_bit as u64 + 1);
        if table.width() == 136 {
            let mask = (BigUint::from(1u8) << 128usize) - BigUint::from(1u8);
            assert_eq!(&low & &mask, &high & &mask);
            assert_ne!(low, high);
        }
        for (cells, expected, query_truth) in [
            (Cells::Filled, 9, true),
            (Cells::CorruptLast, 9, true),
            (Cells::Filled, 7, false),
        ] {
            let source = source(table, cells, expected);
            check_source(&source, table, cells, query_truth);
        }
    }
}

pub(super) fn check_source(
    source: &QuantifiedChcProblem,
    table: Table,
    cells: Cells,
    query_truth: bool,
) {
    assert_eq!(source.source_problem().clauses().len(), 2);
    assert_eq!(source.premises()[0].len(), 1);
    assert!(source.premises()[1].is_empty());
    let values = values(table, cells);
    let mut fact = environment(arguments(source, 0), &values);
    assert_eq!(
        crate::expr::evaluate_expr(
            source.source_problem().clauses()[0]
                .body
                .constraint
                .as_ref()
                .unwrap(),
            &fact
        ),
        Some(SmtValue::Bool(true))
    );
    assert_eq!(read(&values[0], &values[1]), SmtValue::BitVec(7, 8));
    assert_eq!(read(&values[0], &values[2]), SmtValue::BitVec(9, 8));
    let premise = &source.premises()[0][0];
    assert_eq!(premise.binder_count(), 1);
    assert_eq!(premise.binder().sort, ChcSort::BitVec(64));
    let ChcExpr::Op(ChcOp::Implies, matrix) = premise.matrix() else {
        panic!("guard")
    };
    let ChcExpr::Op(ChcOp::BvULt, guard) = matrix[0].as_ref() else {
        panic!("unsigned guard")
    };
    assert_eq!(guard[0].as_ref(), &ChcExpr::Var(premise.binder().clone()));
    assert_eq!(guard[1].as_ref(), &ChcExpr::BitVec(65, 64));
    let mut false_indices = Vec::new();
    for index in 0..67 {
        fact.insert(premise.binder().name.clone(), SmtValue::BitVec(index, 64));
        let result = crate::expr::evaluate_expr(premise.matrix(), &fact);
        assert!(matches!(result, Some(SmtValue::Bool(_))));
        if result == Some(SmtValue::Bool(false)) {
            false_indices.push(index);
        }
    }
    assert_eq!(
        false_indices,
        match cells {
            Cells::Filled => vec![],
            Cells::CorruptLast => vec![64],
        }
    );
    // Every other BV64 value has i>=65, so the exact guard is false.
    let query = environment(arguments(source, 1), &values);
    assert_eq!(
        crate::expr::evaluate_expr(
            source.source_problem().clauses()[1]
                .body
                .constraint
                .as_ref()
                .unwrap(),
            &query
        ),
        Some(SmtValue::Bool(query_truth))
    );
}
