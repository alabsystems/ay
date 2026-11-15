// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn fixture(original: &CountedAdmission, count: usize) -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::try_new_with_admission(original).unwrap();
    let mut builder = CountedTermBuilder::new(&mut terms, original).unwrap();
    let sort = Sort::array(Sort::Bool, Sort::Bool);
    let array = builder.variable("a", &sort).unwrap();
    let other = builder.variable("b", &sort).unwrap();
    let mut roots = Vec::new();
    for index in 0..count {
        let key = builder.variable(&format!("i{index}"), &Sort::Bool).unwrap();
        roots.push(
            builder
                .apply(CountedBuiltin::Select, &[array, key])
                .unwrap(),
        );
    }
    let key = builder.boolean(false).unwrap();
    roots.push(
        builder
            .apply(CountedBuiltin::Select, &[other, key])
            .unwrap(),
    );
    builder.finish().unwrap();
    (terms, roots)
}

#[test]
fn all_distinct_free_pairs_survive_the_ordinary_sixteen_read_cap() {
    let original = ample();
    let (mut terms, roots) = fixture(&original, 18);
    let closure = CountedArrayReadClosure::derive(&mut terms, &roots, &original).unwrap();
    assert_eq!(closure.roots(), roots);
    assert_eq!(closure.reads().len(), 19);
    assert_eq!(closure.unresolved().len(), 19);
    assert_eq!(closure.steps().len(), 18 * 17 / 2);
    let mut pairs = std::collections::BTreeSet::new();
    for step in closure.steps() {
        let Derivation::FreeReadCongruence {
            array,
            left_read,
            right_read,
        } = step.derivation()
        else {
            panic!("free inputs cannot acquire unrelated theory premises");
        };
        assert!(left_read < right_read);
        assert!(pairs.insert((left_read, right_read)));
        let left = closure.reads()[left_read];
        let right = closure.reads()[right_read];
        assert_eq!((left.array, right.array), (array, array));
        assert_ne!(left.index, right.index);
        let [guard, conclusion] = step.literals() else {
            panic!("binary clause")
        };
        let TermData::Not(equality) = terms.get(*guard) else {
            panic!("negative guard")
        };
        assert_eq!(
            application(&terms, *equality, "="),
            &[left.index, right.index]
        );
        assert_eq!(
            application(&terms, *conclusion, "="),
            &[left.select, right.select]
        );
    }
    closure.validate_source(&terms).unwrap();
    closure.finish().unwrap();
}

#[test]
fn generated_free_equality_is_validated_before_any_derived_terms_and_retained() {
    for before in [false, true] {
        let original = ample();
        let (mut terms, roots) = fixture(&original, 2);
        if before {
            terms.register_declared_function("=");
            let stamp = terms.snapshot_stamp();
            assert!(matches!(
                CountedArrayReadClosure::derive(&mut terms, &roots, &original),
                Err(Error::Unsupported)
            ));
            assert_eq!(terms.snapshot_stamp(), stamp);
        } else {
            let closure = CountedArrayReadClosure::derive(&mut terms, &roots, &original).unwrap();
            assert_eq!(closure.steps().len(), 1);
            terms.register_declared_function("=");
            assert_eq!(closure.validate_source(&terms), Err(Error::Unsupported));
            closure.finish().unwrap();
        }
        original.check().unwrap();
    }
}

#[test]
fn free_congruence_guard_is_valid_for_every_boolean_array_and_index_pair() {
    let original = ample();
    let (mut terms, roots) = fixture(&original, 2);
    let closure = CountedArrayReadClosure::derive(&mut terms, &roots, &original).unwrap();
    assert_eq!(closure.steps().len(), 1);
    let step = &closure.steps()[0];
    let Derivation::FreeReadCongruence {
        array,
        left_read,
        right_read,
    } = step.derivation()
    else {
        unreachable!()
    };
    let left_source = closure.reads()[left_read];
    let right_source = closure.reads()[right_read];
    for table in 0..4 {
        for left in 0..2 {
            for right in 0..2 {
                let indices = [
                    (left_source.index, left != 0),
                    (right_source.index, right != 0),
                ];
                let cells = [(array, [table & 1 != 0, table & 2 != 0])];
                assert!(step
                    .literals()
                    .iter()
                    .any(|literal| evaluate(&terms, *literal, &indices, &cells)));
            }
        }
    }
    // Removing the guard would falsely equate two distinct cells.
    let indices = [(left_source.index, false), (right_source.index, true)];
    let cells = [(array, [false, true])];
    assert!(evaluate(&terms, step.literals()[0], &indices, &cells));
    assert!(!evaluate(&terms, step.literals()[1], &indices, &cells));
    closure.finish().unwrap();
}

fn evaluate(
    terms: &TermStore,
    term: TermId,
    indices: &[(TermId, bool)],
    arrays: &[(TermId, [bool; 2])],
) -> bool {
    match terms.get(term) {
        TermData::Var(..) => indices.iter().find(|(id, _)| *id == term).unwrap().1,
        TermData::Not(child) => !evaluate(terms, *child, indices, arrays),
        TermData::App(symbol, args) if symbol.name() == "=" => {
            evaluate(terms, args[0], indices, arrays) == evaluate(terms, args[1], indices, arrays)
        }
        TermData::App(symbol, args) if symbol.name() == "select" => {
            let array = &arrays.iter().find(|(id, _)| *id == args[0]).unwrap().1;
            array[usize::from(evaluate(terms, args[1], indices, arrays))]
        }
        _ => panic!("outside the independent Boolean-array test evaluator"),
    }
}

#[test]
fn exact_and_every_short_work_grant_cover_the_actual_pair_pass_and_restricted_subsetup() {
    let construction = ample();
    let (terms, roots) = fixture(&construction, 2);
    let measured = ample();
    let mut full = terms.clone();
    let closure = CountedArrayReadClosure::derive(&mut full, &roots, &measured).unwrap();
    closure.validate_source(&full).unwrap();
    closure.finish().unwrap();
    let usage = measured.usage().unwrap();
    for work in 0..=usage.work_admitted {
        let original = owner(work, usage.storage_admitted);
        let mut fresh = terms.clone();
        let result =
            CountedArrayReadClosure::derive(&mut fresh, &roots, &original).and_then(|closure| {
                let result = closure.validate_source(&fresh);
                closure.finish()?;
                result
            });
        if work == usage.work_admitted {
            result.unwrap();
            assert_eq!(original.usage().unwrap().work_remaining, 0);
        } else {
            assert_eq!(
                result,
                Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
            );
            assert_eq!(original.check(), Err(CountedAdmissionError::WorkExhausted));
        }
    }
    let original = owner(usage.work_admitted, usage.storage_admitted - 1);
    let mut fresh = terms.clone();
    assert!(matches!(
        CountedArrayReadClosure::derive(&mut fresh, &roots, &original),
        Err(Error::Stopped(CountedAdmissionError::StorageExhausted))
    ));
}
