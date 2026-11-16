// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn fp_clone_rejects_wrong_sort_and_namespace_before_any_construction() {
    let huge =
        FpModelValue::from_exact_fields(false, 0u32.into(), 1u32.into(), 2, u32::MAX - 2).unwrap();
    for expected in [
        Sort::FloatingPoint(5, 11),
        Sort::FloatingPoint(2, u32::MAX - 2),
    ] {
        let (executor, model, term) = pinned_fp(expected, huge.clone());
        let _read = executor.begin_external_evaluation_read();
        let constructions = Cell::new(0);
        let result = executor
            .evaluate_fp_term_via_bitblast_controlled(&model, term, &|phase| {
                if matches!(phase, FpEvalPhase::Construction(_)) {
                    constructions.set(constructions.get() + 1);
                }
            })
            .unwrap();
        assert!(result.is_none());
        assert_eq!(constructions.get(), 0);
        assert_eq!(executor.evaluation_stop_origin(), None);
    }
}

#[test]
fn fp_clone_prepays_owned_fields_on_the_same_original_arena() {
    let fraction = (BigInt::from(1) << 198usize) | BigInt::from(1);
    let value = FpModelValue::from_exact_fields(
        false,
        127u32.into(),
        fraction.to_biguint().unwrap(),
        8,
        200,
    )
    .unwrap();
    let expected = value.to_ieee_bv();
    let (mut executor, model, term) = pinned_fp(Sort::FloatingPoint(8, 200), value);
    let cap = executor.ctx.terms.true_memory_bytes() + TermStore::new().true_memory_bytes() + 128;
    executor.set_term_memory_limit(Some(cap));
    let read = executor.begin_external_evaluation_read();
    let constructions = Cell::new(0);
    let result = executor.evaluate_fp_term_via_bitblast_controlled(&model, term, &|phase| {
        if matches!(phase, FpEvalPhase::Construction(_)) {
            constructions.set(constructions.get() + 1);
        }
    });
    assert!(matches!(result, Err(UnknownOrigin::MemoryBudget)));
    assert_eq!(constructions.get(), 0);
    executor.set_term_memory_limit(None);
    assert!(matches!(
        executor.evaluate_fp_term_via_bitblast_controlled(&model, term, &|_| {}),
        Err(UnknownOrigin::MemoryBudget)
    ));
    drop(read);
    let _fresh = executor.begin_external_evaluation_read();
    let result = executor
        .evaluate_fp_term_via_bitblast_controlled(&model, term, &|_| {})
        .unwrap()
        .unwrap();
    assert_eq!(result.to_ieee_bv(), expected);
}

#[test]
fn source_and_remaining_temporary_term_caps_are_cold_checked_without_rearming() {
    for cold in [true, false] {
        let (mut executor, model, term) = division("RTP");
        let cap = if cold {
            0
        } else {
            executor.ctx.terms.true_memory_bytes() + TermStore::new().true_memory_bytes()
        };
        executor.set_term_memory_limit(Some(cap));
        let read = executor.begin_external_evaluation_read();
        let visits = Cell::new(0);
        let result = executor.evaluate_fp_term_via_bitblast_controlled(&model, term, &|phase| {
            if matches!(phase, FpEvalPhase::Concretize) {
                visits.set(visits.get() + 1);
            }
        });
        assert!(matches!(result, Err(UnknownOrigin::MemoryBudget)));
        assert_eq!(visits.get() == 0, cold);
        executor.set_term_memory_limit(None);
        assert_eq!(
            executor.evaluation_stop_origin(),
            Some(UnknownOrigin::MemoryBudget)
        );
        drop(read);
        let _fresh = executor.begin_external_evaluation_read();
        healthy(&executor, &model, term, 0x3556);
    }
}

#[test]
fn unpinned_rounding_modes_and_actual_condition_gaps_remain_unavailable_not_stopped() {
    let (mut executor, model, _) = division("RTP");
    let terms = &mut executor.ctx.terms;
    let one = fp(terms, 15, 0);
    let three = fp(terms, 16, 512);
    let rm = terms.mk_var(
        "unbound_rm",
        Sort::Uninterpreted("RoundingMode".to_string()),
    );
    let term = terms.mk_app(
        Symbol::named("fp.div"),
        [rm, one, three],
        Sort::FloatingPoint(5, 11),
    );
    let opaque = terms.mk_app(Symbol::named("opaque"), [one], Sort::Bool);
    let ite = terms.mk_ite(opaque, one, three);
    let _read = executor.begin_external_evaluation_read();
    for term in [term, ite] {
        assert!(executor
            .evaluate_fp_term_via_bitblast_controlled(&model, term, &|_| {})
            .unwrap()
            .is_none());
        assert_eq!(executor.evaluation_stop_origin(), None);
    }
}

#[test]
fn root_decoder_checks_format_and_missing_bits_without_inventing_assignments() {
    let executor = Executor::new();
    let _read = executor.begin_external_evaluation_read();
    let attempt = executor.evaluation_attempt();
    let control = Control {
        executor: &executor,
        stop: FpStop::from_executor(&executor),
        arena: attempt.temporary_arena().unwrap(),
        attempt,
        observe: &|_| {},
    };
    for (eb, sb, present, valid) in [
        (5, 11, true, true),
        (5, 11, false, false),
        (64, 11, true, false),
        (5, 66, true, true),
        (63, 129, true, true),
        (63, 129, false, false),
        (64, 129, true, false),
        (15, 130, true, true),
        (8, 200, true, true),
    ] {
        let mut terms = TermStore::new();
        let term = terms.mk_var("decoded", Sort::FloatingPoint(eb, sb));
        // Decoder-only metadata fixture, not a constructed SAT certificate.
        let decomposition = ay_fp::FpDecomposed {
            sign: 1,
            exponent: vec![1; eb as usize],
            significand: vec![1; (sb - 1) as usize],
            precision: ay_fp::FpPrecision::Custom { eb, sb },
        };
        let model: &[bool] = if present { &[false] } else { &[] };
        let value = decode::root(&terms, term, decomposition, model, &control).unwrap();
        assert_eq!(value.is_some(), valid);
        if let Some(value) = value {
            assert!(value.is_zero() && !value.is_negative());
        }
        assert_eq!(executor.evaluation_stop_origin(), None);
    }
}
