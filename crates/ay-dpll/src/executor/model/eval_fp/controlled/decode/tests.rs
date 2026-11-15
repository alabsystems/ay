// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_fp::FpPrecision;
use num_bigint::BigInt;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn quad_fixture() -> (TermStore, TermId, FpDecomposed, Vec<bool>) {
    let mut terms = TermStore::new();
    let term = terms.mk_var("quad", Sort::FloatingPoint(15, 113));
    // Complete decoder-only assignment, not a SAT-search/certificate fixture.
    let value = FpDecomposed {
        sign: 1,
        exponent: (2..17).collect(),
        significand: (17..129).collect(),
        precision: FpPrecision::Float128,
    };
    let mut model = vec![false; 128];
    for (i, &lit) in value.exponent.iter().enumerate() {
        model[lit as usize - 1] = (16383u64 >> i) & 1 != 0;
    }
    model[value.significand[0] as usize - 1] = true;
    model[value.significand[111] as usize - 1] = true;
    (terms, term, value, model)
}

fn control<'a>(executor: &'a Executor, observe: &'a dyn Fn(FpEvalPhase)) -> Control<'a> {
    let attempt = executor.evaluation_attempt();
    Control {
        executor,
        stop: FpStop::from_executor(executor),
        arena: attempt.temporary_arena().unwrap(),
        attempt,
        observe,
    }
}

#[test]
fn controlled_binary128_decode_keeps_exact_bits_and_unavailable_is_not_stopped() {
    let executor = Executor::new();
    let _read = executor.begin_external_evaluation_read();
    let phases = Cell::new(0);
    let observe = |phase| {
        assert!(matches!(phase, FpEvalPhase::Decode));
        phases.set(phases.get() + 1);
    };
    let owner = control(&executor, &observe);
    let (terms, term, value, model) = quad_fixture();
    let exact = root(&terms, term, value.clone(), &model, &owner)
        .unwrap()
        .unwrap();
    assert_eq!(phases.get(), 2);
    assert_eq!(
        exact.to_ieee_bv(),
        (
            BigInt::parse_bytes(b"3fff8000000000000000000000000001", 16).unwrap(),
            128,
        )
    );
    assert!(root(&terms, term, value.clone(), &model[..127], &owner)
        .unwrap()
        .is_none());
    let mut wrong_precision = value.clone();
    wrong_precision.precision = FpPrecision::Float64;
    assert!(root(&terms, term, wrong_precision, &model, &owner)
        .unwrap()
        .is_none());
    let mut bad_literal = value.clone();
    bad_literal.sign = i32::MIN;
    assert!(root(&terms, term, bad_literal, &model, &owner)
        .unwrap()
        .is_none());
    assert!(
        root(&terms, TermId(u32::MAX), value.clone(), &model, &owner)
            .unwrap()
            .is_none()
    );
    assert_eq!(executor.evaluation_stop_origin(), None);
    let retry = root(&terms, term, value, &model, &owner).unwrap().unwrap();
    assert!(retry.structural_eq(&exact));
}

#[test]
fn controlled_decode_entry_and_final_refusal_are_sticky_until_fresh_read() {
    for target in [1, 2] {
        let mut executor = Executor::new();
        let interrupt = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(Arc::clone(&interrupt));
        let read = executor.begin_external_evaluation_read();
        let phases = Cell::new(0);
        let observe = |phase| {
            assert!(matches!(phase, FpEvalPhase::Decode));
            phases.set(phases.get() + 1);
            if phases.get() == target {
                interrupt.store(true, Ordering::Relaxed);
            }
        };
        let owner = control(&executor, &observe);
        let (terms, term, value, model) = quad_fixture();
        assert!(matches!(
            root(&terms, term, value.clone(), &model, &owner),
            Err(UnknownOrigin::InterruptFlag)
        ));
        assert_eq!(phases.get(), target);
        interrupt.store(false, Ordering::Relaxed);
        assert!(matches!(
            root(&terms, term, value.clone(), &model, &owner),
            Err(UnknownOrigin::InterruptFlag)
        ));
        assert_eq!(phases.get(), target, "refusal cannot revisit the observer");
        assert_eq!(
            executor.evaluation_stop_origin(),
            Some(UnknownOrigin::InterruptFlag)
        );
        drop(owner);
        drop(read);
        let _fresh = executor.begin_external_evaluation_read();
        let noop = |_| {};
        let healthy = control(&executor, &noop);
        let decoded = root(&terms, term, value, &model, &healthy)
            .unwrap()
            .unwrap();
        assert_eq!(
            decoded.to_ieee_bv().0,
            BigInt::parse_bytes(b"3fff8000000000000000000000000001", 16).unwrap()
        );
        assert_eq!(executor.evaluation_stop_origin(), None);
    }
}
