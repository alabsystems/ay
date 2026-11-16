// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

fn sequence(original: &CountedAdmission) -> Result<()> {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let y = terms.mk_var("y", Sort::bitvec(4));
    let add = operation(&mut terms, "bvadd", x, y, 4);
    let root = terms.mk_app(Symbol::named("="), [add, x], Sort::Bool);
    let mut encoder = CountedBvEncoder::new(&terms, original)?;
    encoder.assert_roots(&[root])?;
    let _ = encoder.bits(add)?;
    let clauses = encoder.take_clauses()?;
    drop(clauses);
    encoder.finish()
}

#[test]
fn exact_and_one_short_cover_construction_gates_memos_clauses_and_restricted_subsetup() {
    let original = ample();
    sequence(&original).unwrap();
    let used = original.usage().unwrap();
    for (work, bytes, expected) in [
        (used.work_admitted, used.storage_admitted, None),
        (
            used.work_admitted - 1,
            used.storage_admitted,
            Some(CountedAdmissionError::WorkExhausted),
        ),
        (
            used.work_admitted,
            used.storage_admitted - 1,
            Some(CountedAdmissionError::StorageExhausted),
        ),
    ] {
        let original = owner(work, bytes);
        let result = sequence(&original);
        if let Some(expected) = expected {
            assert_eq!(result, Err(CountedBvError::Stopped(expected)));
            assert_eq!(original.check(), Err(expected));
        } else {
            result.unwrap();
            let used = original.usage().unwrap();
            assert_eq!((used.work_remaining, used.storage_remaining), (0, 0));
        }
    }
}

#[test]
fn fresh_receipts_are_identical_and_have_no_invented_deadline() {
    let a = ample();
    let b = ample();
    sequence(&a).unwrap();
    sequence(&b).unwrap();
    assert_eq!(a.usage().unwrap(), b.usage().unwrap());
    assert_eq!(a.deadline(), None);
    assert_eq!(COUNTED_BV_WORK_VERSION, 2);
}

fn zero_padded_division_sequence(original: &CountedAdmission) -> Result<()> {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(3));
    let y = terms.mk_var("y", Sort::bitvec(3));
    let x = terms.mk_bvzero_extend(29, x);
    let y = terms.mk_bvzero_extend(29, y);
    let q = operation(&mut terms, "bvudiv", x, y, 32);
    let r = operation(&mut terms, "bvurem", x, y, 32);
    let mut encoder = CountedBvEncoder::new(&terms, original)?;
    encoder.encode_terms(&[q, r])?;
    let clauses = encoder.take_clauses()?;
    drop(clauses);
    encoder.finish()
}

#[test]
fn zero_padded_division_keeps_exact_original_work_and_storage_limits() {
    let original = ample();
    zero_padded_division_sequence(&original).unwrap();
    let used = original.usage().unwrap();
    for (work, bytes, expected) in [
        (used.work_admitted, used.storage_admitted, None),
        (
            used.work_admitted - 1,
            used.storage_admitted,
            Some(CountedAdmissionError::WorkExhausted),
        ),
        (
            used.work_admitted,
            used.storage_admitted - 1,
            Some(CountedAdmissionError::StorageExhausted),
        ),
    ] {
        let original = owner(work, bytes);
        let actual = zero_padded_division_sequence(&original);
        if let Some(expected) = expected {
            assert_eq!(actual, Err(CountedBvError::Stopped(expected)));
            assert_eq!(original.check(), Err(expected));
        } else {
            actual.unwrap();
            let used = original.usage().unwrap();
            assert_eq!((used.work_remaining, used.storage_remaining), (0, 0));
        }
    }
}

#[test]
fn zero_grants_refuse_before_any_empty_or_constant_circuit() {
    let terms = TermStore::new();
    for original in [owner(0, usize::MAX), owner(u64::MAX, 0)] {
        assert!(matches!(
            CountedBvEncoder::new(&terms, &original),
            Err(CountedBvError::Stopped(_))
        ));
        assert!(original.check().is_err());
    }
}

#[test]
fn callback_refusal_cannot_resume_after_encoder_drop_or_new_handle() {
    let enabled = Arc::new(AtomicBool::new(false));
    let calls = Arc::new(AtomicUsize::new(0));
    let active = enabled.clone();
    let seen = calls.clone();
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 1 << 30),
        None,
        Arc::new(move || {
            active.load(Ordering::SeqCst) && seen.fetch_add(1, Ordering::SeqCst) == 40
        }),
    )
    .unwrap();
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(8));
    let rem = operation(&mut terms, "bvurem", x, y, 8);
    let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    enabled.store(true, Ordering::SeqCst);
    assert!(encoder.encode_terms(&[rem]).is_err());
    enabled.store(false, Ordering::SeqCst);
    assert!(encoder.clauses().is_err());
    assert!(encoder.and_gates().is_err());
    assert!(encoder.xor_gates().is_err());
    assert!(encoder.mux_gates().is_err());
    assert!(encoder.finish().is_err());
    assert!(CountedBvEncoder::new(&terms, &original.clone()).is_err());
}

#[test]
fn retained_original_callback_survives_tls_replacement() {
    let cancelled = Arc::new(AtomicBool::new(false));
    let active = cancelled.clone();
    let scope =
        ay_core::resource::enter_check_stop(Arc::new(move || active.load(Ordering::SeqCst)));
    let original = ample();
    let terms = TermStore::new();
    let encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    drop(scope);
    let _replacement = ay_core::resource::enter_check_stop(Arc::new(|| false));
    cancelled.store(true, Ordering::SeqCst);
    assert!(encoder.check().is_err());
    cancelled.store(false, Ordering::SeqCst);
    assert!(encoder.finish().is_err());
}

#[test]
fn shared_dag_memo_continues_without_new_gates_or_replenished_credit() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(8));
    let q = operation(&mut terms, "bvudiv", x, y, 8);
    let r = operation(&mut terms, "bvurem", x, y, 8);
    let original = ample();
    let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    encoder.encode_terms(&[q]).unwrap();
    let vars = encoder.num_vars().unwrap();
    let clauses = encoder.clauses().unwrap().len();
    let before = original.usage().unwrap();
    encoder.encode_terms(&[q, q, r]).unwrap();
    assert_eq!(encoder.num_vars().unwrap(), vars);
    assert_eq!(encoder.clauses().unwrap().len(), clauses);
    let after = original.usage().unwrap();
    assert!(after.work_admitted > before.work_admitted);
    assert!(after.storage_admitted > before.storage_admitted);
    encoder.finish().unwrap();
}

#[test]
fn symbolic_signed_cache_copies_remain_on_the_same_original_grant() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let y = terms.mk_var("y", Sort::bitvec(4));
    let q = operation(&mut terms, "bvsdiv", x, y, 4);
    let r = operation(&mut terms, "bvsrem", x, y, 4);
    let original = ample();
    let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    encoder.encode_terms(&[q]).unwrap();
    let before = original.usage().unwrap();
    encoder.encode_terms(&[r]).unwrap();
    assert_eq!(encoder.solver.signed_div_cache.len(), 1);
    assert!(original.usage().unwrap().storage_admitted > before.storage_admitted);
    assert!(!encoder.xor_gates().unwrap().is_empty());
    assert!(!encoder.mux_gates().unwrap().is_empty());
    encoder.finish().unwrap();
}

#[test]
fn deep_shared_source_uses_paid_postorder_not_segmented_recursive_unfolding() {
    let mut terms = TermStore::new();
    let leaf = terms.mk_var("leaf", Sort::Bool);
    let mut root = leaf;
    for _ in 0..4096 {
        root = terms.mk_app(Symbol::named("and"), [root, root], Sort::Bool);
    }
    let original = ample();
    let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    encoder.encode_terms(&[root]).unwrap();
    assert_eq!(
        encoder.literal(root).unwrap(),
        encoder.literal(leaf).unwrap()
    );
    assert_eq!(encoder.num_vars().unwrap(), 1);
    assert_eq!(encoder.clauses().unwrap(), &[] as &[CnfClause]);
    encoder.finish().unwrap();
}

#[test]
fn panicking_captured_callback_latches_owner_before_encoder_is_discarded() {
    let enabled = Arc::new(AtomicBool::new(false));
    let active = enabled.clone();
    let scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        assert!(!active.load(Ordering::SeqCst), "test observer panic");
        false
    }));
    let original = ample();
    let mut terms = TermStore::new();
    let root = terms.mk_var("root", Sort::Bool);
    let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    encoder.encode_terms(&[root]).unwrap();
    drop(scope);
    enabled.store(true, Ordering::SeqCst);
    assert!(encoder.assert_roots(&[root]).is_err());
    drop(encoder);
    enabled.store(false, Ordering::SeqCst);
    assert!(original.check().is_err());
}
