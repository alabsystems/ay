// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent TEST-ONLY total finite-array semantics. No producer rule,
//! metadata or ordinary term rewrite is consulted to evaluate a clause.

use super::*;
use ay_core::Constant;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Bits(u128, u32),
    Array(Vec<Value>),
}

fn index(value: Value) -> usize {
    match value {
        Value::Bool(value) => usize::from(value),
        Value::Bits(value, 2) => usize::try_from(value).unwrap(),
        _ => panic!("test index must be Bool or BV2"),
    }
}

fn evaluate(terms: &TermStore, term: TermId, bindings: &[(TermId, Value)]) -> Value {
    if let Some((_, value)) = bindings.iter().find(|(id, _)| *id == term) {
        return value.clone();
    }
    match terms.get(term) {
        TermData::Const(Constant::Bool(value)) => Value::Bool(*value),
        TermData::Const(Constant::BitVec { value, width }) => {
            Value::Bits(value.to_string().parse().unwrap(), *width)
        }
        TermData::Not(child) => {
            let Value::Bool(value) = evaluate(terms, *child, bindings) else {
                panic!("not Bool");
            };
            Value::Bool(!value)
        }
        TermData::Ite(condition, yes, no) => {
            let Value::Bool(value) = evaluate(terms, *condition, bindings) else {
                panic!("ite guard");
            };
            evaluate(terms, if value { *yes } else { *no }, bindings)
        }
        TermData::App(symbol, args) => match (symbol.name(), args.as_slice()) {
            ("=", [left, right]) => {
                Value::Bool(evaluate(terms, *left, bindings) == evaluate(terms, *right, bindings))
            }
            ("select", [array, at]) => {
                let Value::Array(cells) = evaluate(terms, *array, bindings) else {
                    panic!("select array");
                };
                cells[index(evaluate(terms, *at, bindings))].clone()
            }
            ("store", [array, at, value]) => {
                let Value::Array(mut cells) = evaluate(terms, *array, bindings) else {
                    panic!("store array");
                };
                cells[index(evaluate(terms, *at, bindings))] = evaluate(terms, *value, bindings);
                Value::Array(cells)
            }
            ("const-array", [fill]) => {
                let length = match terms.sort(term).array_index().unwrap() {
                    Sort::Bool => 2,
                    Sort::BitVec(bits) if bits.width == 2 => 4,
                    _ => panic!("bounded test carrier"),
                };
                Value::Array(vec![evaluate(terms, *fill, bindings); length])
            }
            _ => panic!("unsupported oracle application: {symbol:?}"),
        },
        _ => panic!("unbound or unsupported oracle term: {term:?}"),
    }
}

fn holds(terms: &TermStore, clause: &[TermId], binding: &[(TermId, Value)]) -> bool {
    clause
        .iter()
        .any(|literal| match evaluate(terms, *literal, binding) {
            Value::Bool(value) => value,
            _ => panic!("non-Boolean emitted clause"),
        })
}

fn cells(mask: usize) -> Value {
    Value::Array(
        (0..4)
            .map(|at| Value::Bits(((mask >> at) & 1) as u128, 8))
            .collect(),
    )
}

fn binding(f: &Fixture, mask: usize, i: u128, j: u128, v: u128) -> Vec<(TermId, Value)> {
    vec![
        (f.base, cells(mask)),
        (f.write_index, Value::Bits(i, 2)),
        (f.read_index, Value::Bits(j, 2)),
        (f.value, Value::Bits(v, 8)),
    ]
}

#[test]
fn symbolic_rows_hold_for_equal_and_distinct_indices_over_all_bounded_arrays() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let closure = derive_fixture(&mut f, &original);
    let mut equal_cases = 0;
    let mut distinct_cases = 0;
    for mask in 0..16 {
        for i in 0..4 {
            for j in 0..4 {
                for value in 0..2 {
                    let assignment = binding(&f, mask, i, j, value);
                    for step in closure.steps() {
                        assert!(holds(&f.terms, step.literals(), &assignment));
                    }
                    if i == j {
                        equal_cases += 1;
                    } else {
                        distinct_cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!((equal_cases, distinct_cases), (128, 384));
    closure.finish().unwrap();
}

#[test]
fn guard_removal_has_concrete_countermodels_in_both_directions() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let closure = derive_fixture(&mut f, &original);
    let (hit, miss) = row_steps(&closure);
    let equal = binding(&f, 0, 1, 1, 1);
    assert!(holds(&f.terms, miss.literals(), &equal));
    assert!(
        !holds(&f.terms, &miss.literals()[1..], &equal),
        "unguarded ROW2 fails at i=j"
    );
    let different = binding(&f, 0, 1, 2, 1);
    assert!(holds(&f.terms, hit.literals(), &different));
    assert!(
        !holds(&f.terms, &hit.literals()[1..], &different),
        "unguarded ROW1 fails at i!=j"
    );
    closure.finish().unwrap();
}

#[test]
fn nested_same_index_store_closure_reads_the_newest_value() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let mut builder = CountedTermBuilder::new(&mut f.terms, &original).unwrap();
    let newest = builder.variable("newest", &Sort::bitvec(8)).unwrap();
    let array = builder
        .apply(CountedBuiltin::Store, &[f.stored, f.write_index, newest])
        .unwrap();
    let read = builder
        .apply(CountedBuiltin::Select, &[array, f.read_index])
        .unwrap();
    let root = builder.apply(CountedBuiltin::Eq, &[read, newest]).unwrap();
    builder.finish().unwrap();
    let closure = CountedArrayReadClosure::derive(&mut f.terms, &[root], &original).unwrap();
    assert_eq!((closure.reads().len(), closure.steps().len()), (3, 4));
    for i in 0..4 {
        for j in 0..4 {
            let mut assignment = binding(&f, 0, i, j, 1);
            assignment.push((newest, Value::Bits(2, 8)));
            assert_eq!(
                evaluate(&f.terms, read, &assignment),
                Value::Bits(if i == j { 2 } else { 0 }, 8)
            );
            for step in closure.steps() {
                assert!(holds(&f.terms, step.literals(), &assignment));
            }
            if i == j {
                assert_ne!(
                    evaluate(&f.terms, read, &assignment),
                    evaluate(&f.terms, f.value, &assignment)
                );
            }
        }
    }
    closure.finish().unwrap();
}

#[test]
fn bool_const_array_ite_checks_both_branches_without_folded_fixtures() {
    let original = ample();
    let mut terms = TermStore::try_new_with_admission(&original).unwrap();
    let mut builder = CountedTermBuilder::new(&mut terms, &original).unwrap();
    let condition = builder.variable("condition", &Sort::Bool).unwrap();
    let at = builder.variable("at", &Sort::Bool).unwrap();
    let yes = builder.boolean(true).unwrap();
    let no = builder.boolean(false).unwrap();
    let filled_yes = builder.constant_array(&Sort::Bool, yes).unwrap();
    let filled_no = builder.constant_array(&Sort::Bool, no).unwrap();
    let array = builder
        .apply(CountedBuiltin::Ite, &[condition, filled_yes, filled_no])
        .unwrap();
    let root = builder.apply(CountedBuiltin::Select, &[array, at]).unwrap();
    builder.finish().unwrap();
    let closure = CountedArrayReadClosure::derive(&mut terms, &[root], &original).unwrap();
    assert_eq!((closure.reads().len(), closure.steps().len()), (3, 4));
    assert!(closure.unresolved().is_empty());
    for guard in [false, true] {
        for index in [false, true] {
            let assignment = [(condition, Value::Bool(guard)), (at, Value::Bool(index))];
            assert_eq!(evaluate(&terms, root, &assignment), Value::Bool(guard));
            for step in closure.steps() {
                assert!(holds(&terms, step.literals(), &assignment));
            }
        }
    }
    let assignment = [(condition, Value::Bool(false)), (at, Value::Bool(true))];
    assert!(!holds(
        &terms,
        &closure.steps()[0].literals()[1..],
        &assignment
    ));
    closure.finish().unwrap();
}
