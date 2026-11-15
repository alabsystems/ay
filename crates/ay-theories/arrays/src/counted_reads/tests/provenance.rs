// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn primitive_source(original: &CountedAdmission, name: &str) -> (TermStore, TermId) {
    let mut f = fixture(original, IndexRelation::Symbolic).unwrap();
    let mut builder = CountedTermBuilder::new(&mut f.terms, original).unwrap();
    let root = match name {
        "const-array" => {
            let constant = builder.constant_array(&Sort::bitvec(2), f.value).unwrap();
            let read = builder
                .apply(CountedBuiltin::Select, &[constant, f.read_index])
                .unwrap();
            builder.apply(CountedBuiltin::Eq, &[read, f.value]).unwrap()
        }
        "=" => builder
            .apply(CountedBuiltin::Eq, &[f.base, f.stored])
            .unwrap(),
        "distinct" => builder
            .apply(CountedBuiltin::Distinct, &[f.base, f.stored])
            .unwrap(),
        _ => f.root,
    };
    builder.finish().unwrap();
    (f.terms, root)
}

fn boolean_constant_read(original: &CountedAdmission) -> (TermStore, TermId) {
    let mut terms = TermStore::try_new_with_admission(original).unwrap();
    let mut builder = CountedTermBuilder::new(&mut terms, original).unwrap();
    let fill = builder.boolean(true).unwrap();
    let index = builder.variable("i", &Sort::Bool).unwrap();
    let array = builder.constant_array(&Sort::Bool, fill).unwrap();
    let root = builder
        .apply(CountedBuiltin::Select, &[array, index])
        .unwrap();
    builder.finish().unwrap();
    // The authored source contains only this read, its constructor/index and
    // the fill. No Eq was constructed; its identity is needed only by the lemma.
    assert_eq!(application(&terms, root, "select"), &[array, index]);
    assert_eq!(application(&terms, array, "const-array"), &[fill]);
    (terms, root)
}

#[test]
fn registered_array_and_relation_heads_refuse_before_derived_terms() {
    for name in ["store", "select", "const-array", "=", "distinct"] {
        let original = ample();
        let (mut terms, root) = primitive_source(&original, name);
        let stamp = terms.snapshot_stamp();
        terms.register_declared_function(name);
        // This reproduces the hole: the physical stamp alone cannot see it.
        assert_eq!(terms.snapshot_stamp(), stamp);
        assert!(
            matches!(
                CountedArrayReadClosure::derive(&mut terms, &[root], &original),
                Err(Error::Unsupported)
            ),
            "registered {name} is uninterpreted"
        );
        assert_eq!(terms.snapshot_stamp(), stamp, "no partial derived terms");
        original.check().unwrap();
    }
}

#[test]
fn registering_a_retained_primitive_invalidates_an_unchanged_physical_source() {
    for name in ["store", "select", "const-array", "=", "distinct"] {
        let original = ample();
        let (mut terms, root) = primitive_source(&original, name);
        let closure = CountedArrayReadClosure::derive(&mut terms, &[root], &original).unwrap();
        closure.validate_source(&terms).unwrap();
        let stamp = terms.snapshot_stamp();
        terms.register_declared_function(name);
        assert_eq!(terms.snapshot_stamp(), stamp);
        assert_eq!(closure.validate_source(&terms), Err(Error::Unsupported));
        original.check().unwrap();
        closure.finish().unwrap();
    }
}

#[test]
fn generated_only_equality_is_checked_before_a_boolean_const_read_expands() {
    let original = ample();
    let (mut terms, root) = boolean_constant_read(&original);
    terms.register_declared_function("=");
    let stamp = terms.snapshot_stamp();
    assert!(matches!(
        CountedArrayReadClosure::derive(&mut terms, &[root], &original),
        Err(Error::Unsupported)
    ));
    assert_eq!(terms.snapshot_stamp(), stamp);
    original.check().unwrap();
}

#[test]
fn generated_only_equality_is_rechecked_after_derivation() {
    let original = ample();
    let (mut terms, root) = boolean_constant_read(&original);
    let closure = CountedArrayReadClosure::derive(&mut terms, &[root], &original).unwrap();
    assert_eq!(closure.steps().len(), 1);
    let literal = closure.steps()[0].literals()[0];
    assert_eq!(application(&terms, literal, "=")[0], root);
    closure.validate_source(&terms).unwrap();
    let stamp = terms.snapshot_stamp();
    terms.register_declared_function("=");
    assert_eq!(terms.snapshot_stamp(), stamp);
    assert_eq!(closure.validate_source(&terms), Err(Error::Unsupported));
    closure.finish().unwrap();
}

#[test]
fn unrelated_registry_appends_do_not_retire_original_derivations() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let closure = derive_fixture(&mut f, &original);
    let stamp = f.terms.snapshot_stamp();
    // Distinct and const-array are absent. Not/Ite are intrinsic TermData
    // variants, not named application identities in these derivations.
    for name in ["unrelated", "distinct", "const-array", "not", "ite"] {
        f.terms.register_declared_function(name);
        assert_eq!(f.terms.snapshot_stamp(), stamp);
        closure.validate_source(&f.terms).unwrap();
    }
    assert_eq!(closure.steps().len(), 2);
    closure.finish().unwrap();
}

#[test]
fn an_unused_equality_identity_does_not_block_a_free_boolean_read() {
    let original = ample();
    let mut terms = TermStore::try_new_with_admission(&original).unwrap();
    let mut builder = CountedTermBuilder::new(&mut terms, &original).unwrap();
    let array = builder
        .variable("a", &Sort::array(Sort::Bool, Sort::Bool))
        .unwrap();
    let index = builder.variable("i", &Sort::Bool).unwrap();
    let root = builder
        .apply(CountedBuiltin::Select, &[array, index])
        .unwrap();
    builder.finish().unwrap();
    terms.register_declared_function("=");
    let closure = CountedArrayReadClosure::derive(&mut terms, &[root], &original).unwrap();
    assert_eq!(closure.reads().len(), 1);
    assert!(closure.steps().is_empty());
    assert_eq!(closure.unresolved(), &[Unresolved::FreeRead { read: 0 }]);
    closure.validate_source(&terms).unwrap();
    closure.finish().unwrap();
}

#[test]
fn declared_scalar_indices_and_genuine_indexed_bv_operators_stay_opaque() {
    // A declaration whose name resembles a relation is still a legal opaque
    // scalar index when no array relation of that identity is interpreted.
    for name in ["user_index", "distinct"] {
        let original = ample();
        let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
        f.terms.register_declared_function(name);
        let index = f.terms.mk_app(
            ay_core::Symbol::named(name),
            [f.read_index],
            Sort::bitvec(2),
        );
        let mut builder = CountedTermBuilder::new(&mut f.terms, &original).unwrap();
        let read = builder
            .apply(CountedBuiltin::Select, &[f.stored, index])
            .unwrap();
        let low = builder
            .apply(CountedBuiltin::BvExtract(3, 0), &[read])
            .unwrap();
        let zero = builder.bitvector(&BigInt::from(0), 4).unwrap();
        let root = builder.apply(CountedBuiltin::Eq, &[low, zero]).unwrap();
        builder.finish().unwrap();
        let closure = CountedArrayReadClosure::derive(&mut f.terms, &[root], &original).unwrap();
        assert_eq!(closure.reads()[0].index, index);
        assert_eq!(closure.reads()[0].select, read);
        assert_eq!(closure.steps().len(), 2);
        closure.validate_source(&f.terms).unwrap();
        closure.finish().unwrap();
    }
}

#[test]
fn every_registry_revalidation_cut_is_paid_by_the_same_sticky_owner() {
    let measured = ample();
    let mut f = fixture(&measured, IndexRelation::Symbolic).unwrap();
    let closure = derive_fixture(&mut f, &measured);
    let before = measured.usage().unwrap();
    closure.validate_source(&f.terms).unwrap();
    let after = measured.usage().unwrap();
    // Source stamp visit, five fixed dependency visits, three exact dictionary
    // lookups and their name bytes: 1 + 5 + (1+6) + (1+5) + (1+1).
    assert_eq!(after.work_admitted - before.work_admitted, 21);
    assert_eq!(after.storage_admitted, before.storage_admitted);
    closure.finish().unwrap();
    for extra in 0..=21 {
        let original = owner(before.work_admitted + extra, before.storage_admitted);
        let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
        let closure = derive_fixture(&mut f, &original);
        let result = closure.validate_source(&f.terms);
        if extra == 21 {
            result.unwrap();
            assert_eq!(original.usage().unwrap().work_remaining, 0);
            closure.finish().unwrap();
        } else {
            let error = CountedAdmissionError::WorkExhausted;
            assert_eq!(result, Err(Error::Stopped(error)));
            assert_eq!(original.clone().check(), Err(error));
            assert_eq!(closure.finish(), Err(Error::Stopped(error)));
        }
    }
}
