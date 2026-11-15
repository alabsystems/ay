// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn raw_same_index_keeps_both_guarded_rows_and_the_exact_source() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Same).unwrap();
    assert_eq!(
        application(&f.terms, f.read, "select"),
        &[f.stored, f.write_index]
    );
    assert_ne!(f.read, f.value, "fixture must not pre-fold read-over-write");
    let closure = derive_fixture(&mut f, &original);
    assert_eq!(closure.roots(), &[f.root]);
    assert_eq!(closure.reads().len(), 2);
    assert_eq!(closure.steps().len(), 2);
    let (hit, miss) = row_steps(&closure);
    assert_eq!(
        hit.derivation(),
        Derivation::Row1 {
            read: 0,
            store: f.stored,
            write_index: f.write_index,
            value: f.value,
        }
    );
    assert_eq!(
        miss.derivation(),
        Derivation::Row2 {
            read: 0,
            store: f.stored,
            base_read: 1
        }
    );
    let guard = miss.literals()[0];
    assert_eq!(
        application(&f.terms, guard, "="),
        &[f.write_index, f.write_index]
    );
    assert_eq!(f.terms.get(hit.literals()[0]), &TermData::Not(guard));
    assert_eq!(
        application(&f.terms, hit.literals()[1], "="),
        &[f.read, f.value]
    );
    assert_eq!(closure.unresolved(), &[Unresolved::FreeRead { read: 1 }]);
    closure.finish().unwrap();
}

#[test]
fn symbolic_rows_link_the_actual_read_guard_and_base_read() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let closure = derive_fixture(&mut f, &original);
    let (hit, miss) = row_steps(&closure);
    let guard = miss.literals()[0];
    assert_eq!(
        application(&f.terms, guard, "="),
        &[f.write_index, f.read_index]
    );
    assert_eq!(f.terms.get(hit.literals()[0]), &TermData::Not(guard));
    let base = closure.reads()[1];
    assert_eq!((base.array, base.index), (f.base, f.read_index));
    assert_eq!(
        application(&f.terms, base.select, "select"),
        &[f.base, f.read_index]
    );
    assert_eq!(
        application(&f.terms, miss.literals()[1], "="),
        &[f.read, base.select]
    );
    assert_eq!(closure.reads()[0].select, f.read);
    assert_eq!(closure.reads()[0].index_sort, ScalarSort::BitVec(2));
    assert_eq!(closure.reads()[0].element_sort, ScalarSort::BitVec(8));
    closure.validate_source(&f.terms).unwrap();
    closure.finish().unwrap();
}

#[test]
fn constant_array_emits_a_fill_unit_not_a_default_operator() {
    let original = ample();
    let mut terms = TermStore::try_new_with_admission(&original).unwrap();
    let mut builder = CountedTermBuilder::new(&mut terms, &original).unwrap();
    let index = builder.variable("at", &Sort::Bool).unwrap();
    let fill = builder.bitvector(&BigInt::from(u64::MAX), 64).unwrap();
    let array = builder.constant_array(&Sort::Bool, fill).unwrap();
    let read = builder
        .apply(CountedBuiltin::Select, &[array, index])
        .unwrap();
    let root = builder.apply(CountedBuiltin::Eq, &[read, fill]).unwrap();
    builder.finish().unwrap();
    let closure = CountedArrayReadClosure::derive(&mut terms, &[root], &original).unwrap();
    assert_eq!(closure.reads().len(), 1);
    assert_eq!(closure.steps().len(), 1);
    assert_eq!(closure.reads()[0].index_sort, ScalarSort::Bool);
    assert_eq!(closure.reads()[0].element_sort, ScalarSort::BitVec(64));
    assert_eq!(
        closure.steps()[0].derivation(),
        Derivation::ConstFill {
            read: 0,
            array,
            fill
        }
    );
    assert_eq!(closure.steps()[0].literals(), &[root]);
    assert_eq!(application(&terms, read, "select"), &[array, index]);
    assert!(closure.unresolved().is_empty());
    closure.finish().unwrap();
}

#[test]
fn array_ite_preserves_both_condition_polarities_and_branch_links() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let mut builder = CountedTermBuilder::new(&mut f.terms, &original).unwrap();
    let condition = builder.variable("condition", &Sort::Bool).unwrap();
    let array = builder
        .apply(CountedBuiltin::Ite, &[condition, f.stored, f.base])
        .unwrap();
    let select = builder
        .apply(CountedBuiltin::Select, &[array, f.read_index])
        .unwrap();
    let root = builder
        .apply(CountedBuiltin::Eq, &[select, f.value])
        .unwrap();
    builder.finish().unwrap();
    let closure = CountedArrayReadClosure::derive(&mut f.terms, &[root], &original).unwrap();
    let then = &closure.steps()[0];
    let otherwise = &closure.steps()[1];
    assert!(matches!(then.derivation(), Derivation::IteThen {
        read: 0, array: actual, condition: guard, branch_read: 1, ..
    } if actual == array && guard == condition));
    assert!(matches!(otherwise.derivation(), Derivation::IteElse {
        read: 0, array: actual, condition: guard, branch_read: 2, ..
    } if actual == array && guard == condition));
    assert_eq!(f.terms.get(then.literals()[0]), &TermData::Not(condition));
    assert_eq!(otherwise.literals()[0], condition);
    for (step, branch) in [(then, 1), (otherwise, 2)] {
        let (equality, negation) = match step.derivation() {
            Derivation::IteThen {
                array_equality,
                not_array_equality,
                ..
            }
            | Derivation::IteElse {
                array_equality,
                not_array_equality,
                ..
            } => (array_equality, not_array_equality),
            _ => panic!("actual array ITE derivation"),
        };
        assert_eq!(
            application(&f.terms, equality, "="),
            &[array, closure.reads()[branch].array]
        );
        assert_eq!(f.terms.get(negation), &TermData::Not(equality));
        assert_eq!(
            application(&f.terms, step.literals()[1], "="),
            &[select, closure.reads()[branch].select]
        );
        assert_eq!(closure.reads()[branch].index, f.read_index);
    }
    assert_eq!(
        closure.reads().len(),
        3,
        "store base reuses the existing else read"
    );
    assert_eq!(closure.steps().len(), 4);
    closure.finish().unwrap();
}

#[test]
fn shared_ite_dag_expands_each_array_index_pair_once() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let mut builder = CountedTermBuilder::new(&mut f.terms, &original).unwrap();
    let condition = builder.variable("condition", &Sort::Bool).unwrap();
    let mut array = f.base;
    for _ in 0..24 {
        array = builder
            .apply(CountedBuiltin::Ite, &[condition, array, array])
            .unwrap();
    }
    let read = builder
        .apply(CountedBuiltin::Select, &[array, f.read_index])
        .unwrap();
    let root = builder.apply(CountedBuiltin::Eq, &[read, f.value]).unwrap();
    builder.finish().unwrap();
    assert!(matches!(f.terms.get(array), TermData::Ite(_, left, right) if left == right));
    let closure = CountedArrayReadClosure::derive(&mut f.terms, &[root, root], &original).unwrap();
    assert_eq!(closure.roots(), &[root, root]);
    assert_eq!(closure.reads().len(), 25);
    assert_eq!(closure.steps().len(), 48);
    assert_eq!(closure.unresolved(), &[Unresolved::FreeRead { read: 24 }]);
    for pair in closure.steps().chunks_exact(2) {
        let Derivation::IteThen {
            branch_read: left, ..
        } = pair[0].derivation()
        else {
            panic!("then");
        };
        let Derivation::IteElse {
            branch_read: right, ..
        } = pair[1].derivation()
        else {
            panic!("else");
        };
        assert_eq!(left, right);
    }
    closure.finish().unwrap();
}

#[test]
fn free_reads_and_array_equality_or_disequality_remain_explicit_obligations() {
    for relation in [CountedBuiltin::Eq, CountedBuiltin::Distinct] {
        let original = ample();
        let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
        let mut builder = CountedTermBuilder::new(&mut f.terms, &original).unwrap();
        let other = builder.variable("other", &array_sort()).unwrap();
        let array_relation = builder.apply(relation, &[f.base, other]).unwrap();
        let read = builder
            .apply(CountedBuiltin::Select, &[f.base, f.read_index])
            .unwrap();
        let scalar = builder.apply(CountedBuiltin::Eq, &[read, f.value]).unwrap();
        let root = builder
            .apply(CountedBuiltin::And, &[array_relation, scalar])
            .unwrap();
        builder.finish().unwrap();
        let closure = CountedArrayReadClosure::derive(&mut f.terms, &[root], &original).unwrap();
        assert_eq!(closure.reads().len(), 1);
        assert!(closure.steps().is_empty());
        assert_eq!(
            closure.unresolved(),
            &[
                Unresolved::ArrayRelation {
                    source: array_relation,
                    left: f.base,
                    right: other
                },
                Unresolved::FreeRead { read: 0 },
            ]
        );
        closure.finish().unwrap();
    }
}

#[test]
fn wide_element_sort_is_preserved_without_scalar_truncation() {
    let original = ample();
    let mut terms = TermStore::try_new_with_admission(&original).unwrap();
    let mut builder = CountedTermBuilder::new(&mut terms, &original).unwrap();
    let fill = builder.variable("wide", &Sort::bitvec(257)).unwrap();
    let array = builder.constant_array(&Sort::Bool, fill).unwrap();
    let index = builder.boolean(false).unwrap();
    let read = builder
        .apply(CountedBuiltin::Select, &[array, index])
        .unwrap();
    let root = builder.apply(CountedBuiltin::Eq, &[read, fill]).unwrap();
    builder.finish().unwrap();
    let closure = CountedArrayReadClosure::derive(&mut terms, &[root], &original).unwrap();
    assert_eq!(closure.reads()[0].element_sort, ScalarSort::BitVec(257));
    assert_eq!(
        application(&terms, closure.steps()[0].literals()[0], "="),
        &[read, fill]
    );
    closure.finish().unwrap();
}

#[test]
fn nested_array_elements_decline_instead_of_claiming_a_closed_scalar_read() {
    let original = ample();
    let mut terms = TermStore::try_new_with_admission(&original).unwrap();
    let mut builder = CountedTermBuilder::new(&mut terms, &original).unwrap();
    let leaf = builder.boolean(true).unwrap();
    let inner = builder.constant_array(&Sort::Bool, leaf).unwrap();
    let outer = builder.constant_array(&Sort::Bool, inner).unwrap();
    let selected = builder
        .apply(CountedBuiltin::Select, &[outer, leaf])
        .unwrap();
    let root = builder
        .apply(CountedBuiltin::Eq, &[selected, inner])
        .unwrap();
    builder.finish().unwrap();
    assert!(matches!(
        CountedArrayReadClosure::derive(&mut terms, &[root], &original),
        Err(Error::Unsupported)
    ));
    original.check().unwrap();
}

#[test]
fn indexed_spellings_cannot_impersonate_array_or_equality_primitives() {
    for name in ["store", "select", "const-array", "=", "distinct"] {
        let original = ample();
        let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
        let (args, sort) = match name {
            "store" => (vec![f.base, f.write_index, f.value], array_sort()),
            "select" => (vec![f.base, f.read_index], Sort::bitvec(8)),
            "const-array" => (vec![f.value], array_sort()),
            _ => (vec![f.base, f.base], Sort::Bool),
        };
        // The one malicious node intentionally bypasses the closed builtin
        // vocabulary; all genuine surrounding nodes still use the raw builder.
        let spoof = f
            .terms
            .mk_app(ay_core::Symbol::indexed(name, vec![7]), args, sort);
        let mut builder = CountedTermBuilder::new(&mut f.terms, &original).unwrap();
        let root = match name {
            "=" | "distinct" => spoof,
            "select" => builder
                .apply(CountedBuiltin::Eq, &[spoof, f.value])
                .unwrap(),
            _ => {
                let read = builder
                    .apply(CountedBuiltin::Select, &[spoof, f.read_index])
                    .unwrap();
                builder.apply(CountedBuiltin::Eq, &[read, f.value]).unwrap()
            }
        };
        builder.finish().unwrap();
        assert!(
            matches!(
                CountedArrayReadClosure::derive(&mut f.terms, &[root], &original),
                Err(Error::Unsupported)
            ),
            "indexed {name} is not a primitive"
        );
        original.check().unwrap();
    }
}

#[test]
fn legitimate_indexed_bitvector_operators_do_not_hide_their_array_reads() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let mut builder = CountedTermBuilder::new(&mut f.terms, &original).unwrap();
    let low = builder
        .apply(CountedBuiltin::BvExtract(3, 0), &[f.read])
        .unwrap();
    let zero = builder.bitvector(&BigInt::from(0), 4).unwrap();
    let root = builder.apply(CountedBuiltin::Eq, &[low, zero]).unwrap();
    builder.finish().unwrap();
    let closure = CountedArrayReadClosure::derive(&mut f.terms, &[root], &original).unwrap();
    assert_eq!(closure.roots(), &[root]);
    assert_eq!(closure.reads()[0].select, f.read);
    assert_eq!(closure.steps().len(), 2);
    closure.finish().unwrap();
}
