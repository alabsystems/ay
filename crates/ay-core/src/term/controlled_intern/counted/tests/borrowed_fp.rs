// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use num_bigint::BigUint;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};

struct Borrowed<'a>(&'a CountedAdmission);
impl TermConstructionAdmission for Borrowed<'_> {
    fn admit(&self, work: usize, bytes: usize) -> std::result::Result<(), CountedAdmissionError> {
        self.0.admit(work, bytes)
    }
    fn refuse(&self, error: CountedAdmissionError) -> CountedAdmissionError {
        self.0.refuse(error)
    }
}

#[test]
fn borrowed_owner_constructs_exact_fields_and_fp_arrays_in_the_same_store() {
    let original = ample();
    let mut store = TermStore::try_new_with_admission(&original).unwrap();
    let sink = Borrowed(&original);
    let fraction = (BigUint::from(1u8) << 198usize) | BigUint::from(1u8);
    let before = original.usage().unwrap();
    let mut builder = CountedTermBuilder::with_admission(&mut store, &sink).unwrap();
    let sign = builder.bitvector_unsigned(&BigUint::from(1u8), 1).unwrap();
    let exponent = builder
        .bitvector_unsigned(&BigUint::from(127u8), 8)
        .unwrap();
    let fraction_term = builder.bitvector_unsigned(&fraction, 199).unwrap();
    let fp = builder
        .floating_point_fields(sign, exponent, fraction_term)
        .unwrap();
    let array = builder.constant_array(&Sort::bitvec(64), fp).unwrap();
    let index = builder.bitvector_unsigned(&BigUint::from(0u8), 64).unwrap();
    let read = builder
        .apply(CountedBuiltin::Select, &[array, index])
        .unwrap();
    let equality = builder.apply(CountedBuiltin::Eq, &[read, fp]).unwrap();
    builder.finish().unwrap();
    assert_eq!(store.sort(fp), &Sort::FloatingPoint(8, 200));
    assert_eq!(store.sort(read), store.sort(fp));
    assert_eq!(store.sort(equality), &Sort::Bool);
    assert!(
        matches!(store.get(fraction_term), TermData::Const(Constant::BitVec {value,width:199})
        if value == &BigInt::from(fraction.clone()))
    );
    assert!(
        matches!(store.get(fp),TermData::App(Symbol::Named(name),args)
        if name == "fp" && args == &[sign,exponent,fraction_term])
    );
    assert_ne!(original.usage().unwrap(), before);
    // Reopening the same store/owner reuses actual producer identities.
    let mut reopened = CountedTermBuilder::new(&mut store, &original).unwrap();
    assert_eq!(
        reopened
            .floating_point_fields(sign, exponent, fraction_term)
            .unwrap(),
        fp
    );
    reopened.finish().unwrap();
}

#[test]
fn field_types_precision_overflow_and_unsigned_overflow_refuse_without_modular_folding() {
    let original = ample();
    let mut store = TermStore::try_new_with_admission(&original).unwrap();
    let sink = Borrowed(&original);
    let mut builder = CountedTermBuilder::with_admission(&mut store, &sink).unwrap();
    let sign = builder.bitvector_unsigned(&0u8.into(), 1).unwrap();
    let bad_sign = builder.bitvector_unsigned(&0u8.into(), 2).unwrap();
    let exponent = builder.bitvector_unsigned(&127u8.into(), 8).unwrap();
    let fraction = builder.bitvector_unsigned(&1u8.into(), 199).unwrap();
    let yes = builder.boolean(true).unwrap();
    let huge = builder.bitvector_unsigned(&0u8.into(), u32::MAX).unwrap();
    for args in [
        [bad_sign, exponent, fraction],
        [sign, yes, fraction],
        [sign, exponent, huge],
        [sign, TermId(u32::MAX), fraction],
    ] {
        assert_eq!(
            builder.floating_point_fields(args[0], args[1], args[2]),
            Err(CountedTermError::InvalidInput)
        );
    }
    let overflow = BigUint::from(1u8) << 199usize;
    assert_eq!(
        builder.bitvector_unsigned(&overflow, 199),
        Err(CountedTermError::InvalidInput)
    );
    assert_eq!(
        builder.bitvector_unsigned(&0u8.into(), 0),
        Err(CountedTermError::InvalidInput)
    );
    // Core validates data signatures; it does not claim the source solver's
    // narrower namespace or rounded-arithmetic admission.
    let wide_exp = builder
        .bitvector_unsigned(&(BigUint::from(1u8) << 79usize), 80)
        .unwrap();
    let fp = builder
        .floating_point_fields(sign, wide_exp, fraction)
        .unwrap();
    assert_eq!(builder.store.sort(fp), &Sort::FloatingPoint(80, 200));
    builder.finish().unwrap();
}

#[test]
fn refusal_at_unsigned_copy_keeps_original_cause_and_cannot_be_renewed_by_another_sink() {
    struct StopOnCopy<'a> {
        original: &'a CountedAdmission,
        stop: Arc<AtomicBool>,
        armed: Cell<bool>,
    }
    impl TermConstructionAdmission for StopOnCopy<'_> {
        fn admit(
            &self,
            work: usize,
            bytes: usize,
        ) -> std::result::Result<(), CountedAdmissionError> {
            if self.armed.get() && bytes != 0 {
                self.stop.store(true, Ordering::Release);
            }
            self.original.admit(work, bytes)
        }
        fn refuse(&self, error: CountedAdmissionError) -> CountedAdmissionError {
            self.original.refuse(error)
        }
    }
    let stop = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&stop);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 256 * 1024 * 1024),
        None,
        Arc::new(move || observed.load(Ordering::Acquire)),
    )
    .unwrap();
    let mut store = TermStore::try_new_with_admission(&original).unwrap();
    let sink = StopOnCopy {
        original: &original,
        stop: Arc::clone(&stop),
        armed: Cell::new(false),
    };
    let mut builder = CountedTermBuilder::with_admission(&mut store, &sink).unwrap();
    let before = builder.store.len();
    sink.armed.set(true);
    let fraction = (BigUint::from(1u8) << 198usize) | BigUint::from(1u8);
    assert!(matches!(
        builder.bitvector_unsigned(&fraction, 199),
        Err(CountedTermError::Stopped(_))
    ));
    assert_eq!(builder.store.len(), before);
    drop(builder);
    let refused = original.usage().unwrap();
    assert!(refused.refusal.is_some());
    stop.store(false, Ordering::Release);
    let another = Borrowed(&original);
    assert!(matches!(
        CountedTermBuilder::with_admission(&mut store, &another),
        Err(CountedTermError::Stopped(_))
    ));
    assert_eq!(original.usage().unwrap(), refused);
}

#[test]
fn existing_default_builder_retains_its_send_contract() {
    fn assert_send<T: Send>() {}
    assert_send::<CountedTermBuilder<'static, 'static>>();
}
