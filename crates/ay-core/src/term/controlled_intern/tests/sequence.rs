// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn controlled_seq_empty_preserves_nested_live_sort_data_and_exact_interning() {
    let mut store = TermStore::new();
    let term = TermData::App(Symbol::named("seq.empty"), vec![]);
    let sort = Sort::seq(Sort::array(
        Sort::Int,
        Sort::seq(Sort::Uninterpreted("private_live_carrier".to_owned())),
    ));
    let id = intern(&mut store, &term, &sort).unwrap();
    assert_eq!(store.sort(id), &sort);
    assert_eq!(store.get(id), &term);
    assert_eq!(intern(&mut store, &term, &sort), Ok(id));
    assert_eq!(store.finite_field_presence(id), Some(false));
    let other = intern(&mut store, &term, &Sort::seq(Sort::Int)).unwrap();
    assert_ne!(id, other);
}

#[test]
fn controlled_seq_empty_does_not_admit_general_seq_or_malformed_metadata() {
    let mut store = TermStore::new();
    let before = store.len();
    let empty = TermData::App(Symbol::named("seq.empty"), vec![]);
    let malformed = [
        Sort::seq(Sort::bitvec(0)),
        Sort::seq(Sort::FloatingPoint(1, 2)),
        Sort::seq(Sort::Datatype(crate::sort::DatatypeSort::new(
            "raw",
            vec![],
        ))),
    ];
    for sort in malformed {
        assert_eq!(
            intern(&mut store, &empty, &sort),
            Err(ControlledTermInternError::UnsupportedFragment)
        );
    }
    let args = TermData::App(Symbol::named("seq.empty"), vec![store.true_term()]);
    assert_eq!(
        intern(&mut store, &args, &Sort::seq(Sort::Bool)),
        Err(ControlledTermInternError::UnsupportedFragment)
    );
    let other = TermData::App(Symbol::named("seq.unit"), vec![store.true_term()]);
    assert_eq!(
        intern(&mut store, &other, &Sort::seq(Sort::Bool)),
        Err(ControlledTermInternError::UnsupportedFragment)
    );
    assert_eq!(store.len(), before);
}

#[test]
fn controlled_seq_empty_prices_physical_names_sort_copies_and_collision_polls() {
    let mut store = TermStore::new();
    let term = TermData::App(Symbol::named("seq.empty"), vec![]);
    for width in 1..=16 {
        intern(&mut store, &term, &Sort::seq(Sort::bitvec(width))).unwrap();
    }
    let before = store.len();
    let mut collisions = 0;
    assert_eq!(
        store.try_intern_with_progress(&term, &Sort::seq(Sort::Int), &mut |work, _| {
            if work == 258 {
                collisions += 1;
            }
            collisions < 3
        }),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(collisions, 3);
    assert_eq!(store.len(), before);
    let sort = Sort::seq(Sort::Uninterpreted("q".repeat(32_768)));
    let mut saw_copy = false;
    let copy_bytes = 8192 + 2 * std::mem::size_of::<Sort>() + 32_768;
    assert_eq!(
        store.try_intern_with_progress(&term, &sort, &mut |_, bytes| {
            if bytes == copy_bytes {
                saw_copy = true;
                return false;
            }
            true
        }),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert!(saw_copy);
    assert_eq!(store.len(), before);
    let admitted = intern(&mut store, &term, &sort).unwrap();
    assert_eq!(store.sort(admitted), &sort);
}

#[test]
fn controlled_seq_extension_preserves_existing_boolean_child_dispatch_metadata() {
    let mut store = TermStore::new();
    let field = crate::FiniteFieldSort::new(7).unwrap();
    let value = store.mk_var("field_value", Sort::FiniteField(field));
    let one = store.mk_finite_field(1, field);
    let equal = store.mk_app(Symbol::named("="), [value, one], Sort::Bool);
    assert_eq!(store.finite_field_presence(equal), Some(true));
    let not = intern(&mut store, &TermData::Not(equal), &Sort::Bool).unwrap();
    assert_eq!(store.finite_field_presence(not), Some(true));
}
