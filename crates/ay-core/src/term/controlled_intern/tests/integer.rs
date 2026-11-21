// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn controlled_integer_producer_retains_unbounded_signed_magnitude_and_credit() {
    for sign in [-1i32, 1] {
        let mut store = TermStore::new();
        let value: BigInt = (BigInt::from(1u8) << 100_000usize) * sign + 7;
        let source = TermData::Const(Constant::Int(value.clone()));
        let heap_before = store.heap_data_bytes;
        let id = intern(&mut store, &source, &Sort::Int).expect("prepaid complete integer");
        assert_eq!(store.get(id), &source);
        assert_eq!(store.sort(id), &Sort::Int);
        assert_eq!(
            store.heap_data_bytes - heap_before,
            TermStore::heap_size(&source)
        );
        assert_eq!(store.mk_int(value), id);
        let length = store.len();
        assert_eq!(intern(&mut store, &source, &Sort::Int), Ok(id));
        assert_eq!(store.len(), length);
    }
}

#[test]
fn controlled_integer_payload_is_paid_before_hash_and_again_on_duplicate_comparison() {
    let mut store = TermStore::new();
    let source = TermData::Const(Constant::Int(BigInt::from(1u8) << 100_000usize));
    let payload = shape::owned_payload_bytes(&source).unwrap();
    let original = store.len();
    let mut observed = false;
    assert_eq!(
        store.try_intern_with_progress(&source, &Sort::Int, &mut |work, _| {
            if work >= payload {
                observed = true;
                false
            } else {
                true
            }
        }),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert!(observed);
    assert_eq!(store.len(), original);
    let id = intern(&mut store, &source, &Sort::Int).unwrap();
    let mut payload_charges = 0;
    assert_eq!(
        store.try_intern_with_progress(&source, &Sort::Int, &mut |work, _| {
            if work >= payload {
                payload_charges += 1;
            }
            true
        }),
        Ok(id)
    );
    assert!(payload_charges >= 2, "hash and exact candidate comparison");
}

#[test]
fn controlled_integer_payload_storage_refuses_before_owned_copy() {
    let mut store = TermStore::new();
    let source = TermData::Const(Constant::Int(BigInt::from(1u8) << 100_000usize));
    let payload = shape::owned_payload_bytes(&source).unwrap();
    let original = store.len();
    let mut refused_payload = false;
    assert_eq!(
        store.try_intern_with_progress(&source, &Sort::Int, &mut |work, bytes| {
            if work == payload + 512 && bytes == payload * 2 + 8192 {
                refused_payload = true;
                false
            } else {
                true
            }
        }),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert!(refused_payload);
    assert_eq!(store.len(), original);
    assert!(store.find_interned(&source).is_none());
}

#[test]
fn controlled_integer_sort_and_flat_array_fragment_remain_exact() {
    let mut store = TermStore::new();
    let source = TermData::Const(Constant::Int(BigInt::from(-5)));
    assert_eq!(
        intern(&mut store, &source, &Sort::Bool),
        Err(ControlledTermInternError::InvalidInput)
    );
    let value = intern(&mut store, &source, &Sort::Int).unwrap();
    let data = TermData::App(Symbol::named("const-array"), vec![value]);
    let sort = Sort::array(Sort::Int, Sort::Int);
    let id = intern(&mut store, &data, &sort).unwrap();
    assert_eq!(store.sort(id), &sort);
    for unsupported in [
        Sort::array(Sort::Int, Sort::bitvec(8)),
        Sort::array(Sort::bitvec(64), Sort::Int),
        Sort::array(Sort::Int, Sort::array(Sort::Int, Sort::Int)),
    ] {
        assert_eq!(
            intern(&mut store, &data, &unsupported),
            Err(ControlledTermInternError::UnsupportedFragment)
        );
    }
}
