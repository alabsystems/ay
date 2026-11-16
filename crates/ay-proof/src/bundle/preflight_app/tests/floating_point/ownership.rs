// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn specimens() -> Vec<(Symbol, Vec<TermId>, Sort)> {
    vec![
        (Symbol::named("RNE"), ids(&[]), rounding()),
        (
            Symbol::named("fp.add"),
            ids(&[0, 1, 1]),
            Sort::FloatingPoint(8, 24),
        ),
        (
            Symbol::named("fp.sqrt"),
            ids(&[0, 1]),
            Sort::FloatingPoint(8, 24),
        ),
        (
            Symbol::named("fp.fma"),
            ids(&[0, 1, 1, 1]),
            Sort::FloatingPoint(8, 24),
        ),
        (
            Symbol::named("fp.rem"),
            ids(&[1, 1]),
            Sort::FloatingPoint(8, 24),
        ),
        (Symbol::named("fp.to_real"), ids(&[1]), Sort::Real),
        (Symbol::named("fp.to_ieee_bv"), ids(&[1]), bv(32)),
        (
            Symbol::indexed("to_fp", vec![8, 24]),
            ids(&[6]),
            Sort::FloatingPoint(8, 24),
        ),
        (
            Symbol::indexed("to_fp", vec![8, 24]),
            ids(&[0, 5]),
            Sort::FloatingPoint(8, 24),
        ),
        (
            Symbol::indexed("to_fp_unsigned", vec![8, 24]),
            ids(&[0, 6]),
            Sort::FloatingPoint(8, 24),
        ),
        (Symbol::indexed("fp.to_sbv", vec![8]), ids(&[0, 1]), bv(8)),
    ]
}

fn trace(symbol: &Symbol, args: &[TermId], result: &Sort) -> Vec<(usize, usize)> {
    let values = fp_entries();
    let mut charges = Vec::new();
    validate_app_signature_with_progress(
        &values,
        values.len(),
        symbol,
        args,
        result,
        &mut |work, bytes| {
            charges.push((work, bytes));
            true
        },
    )
    .expect("valid measured FP signature");
    charges
}

#[test]
fn every_arithmetic_conversion_and_final_poll_refusal_stops_immediately() {
    let values = fp_entries();
    let before = values.clone();
    for (symbol, args, result) in specimens() {
        let charges = trace(&symbol, &args, &result);
        assert_eq!(charges.first(), Some(&(0, 0)));
        assert_eq!(charges.last(), Some(&(0, 0)));
        for reject_at in 1..=charges.len() {
            let mut calls = 0;
            let answer = validate_app_signature_with_progress(
                &values,
                values.len(),
                &symbol,
                &args,
                &result,
                &mut |_, _| {
                    calls += 1;
                    calls != reject_at
                },
            );
            assert!(matches!(answer, Err(ProofCheckError::ResourceLimit)));
            assert_eq!(calls, reject_at);
            assert_eq!(values, before);
        }
    }
}

#[test]
fn aggregate_fp_signature_work_reuses_the_callers_original_budget() {
    let values = fp_entries();
    let symbol = Symbol::named("fp.mul");
    let args = ids(&[0, 1, 1]);
    let result = Sort::FloatingPoint(8, 24);
    let mut remaining: usize = trace(&symbol, &args, &result)
        .iter()
        .map(|(work, _)| work)
        .sum();
    let mut stopped = false;
    let mut owner = |work, _| {
        if stopped || work > remaining {
            stopped = true;
            return false;
        }
        remaining -= work;
        true
    };
    validate_app_signature_with_progress(
        &values,
        values.len(),
        &symbol,
        &args,
        &result,
        &mut owner,
    )
    .expect("exact first aggregate allowance");
    assert!(matches!(
        validate_app_signature_with_progress(
            &values,
            values.len(),
            &symbol,
            &args,
            &result,
            &mut owner
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert!(matches!(
        validate_app_signature_with_progress(
            &values,
            values.len(),
            &Symbol::named("RNE"),
            &[],
            &rounding(),
            &mut owner
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn malformed_fp_diagnostics_are_charged_before_string_allocation() {
    let values = fp_entries();
    for (symbol, args, result) in [
        (
            Symbol::named("fp.add"),
            ids(&[3, 1, 1]),
            Sort::FloatingPoint(8, 24),
        ),
        (Symbol::named("RNE"), ids(&[]), Sort::Bool),
        (
            Symbol::indexed("to_fp", vec![8, 23]),
            ids(&[6]),
            Sort::FloatingPoint(8, 24),
        ),
        (Symbol::indexed("fp.to_sbv", vec![0]), ids(&[0, 1]), bv(8)),
        (
            Symbol::named("to_fp"),
            ids(&[6]),
            Sort::FloatingPoint(8, 24),
        ),
    ] {
        let mut allocation_requests = 0;
        let answer = validate_app_signature_with_progress(
            &values,
            values.len(),
            &symbol,
            &args,
            &result,
            &mut |_, bytes| {
                if bytes > 0 {
                    allocation_requests += 1;
                    false
                } else {
                    true
                }
            },
        );
        assert!(matches!(answer, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(allocation_requests, 1);
    }
}

#[test]
fn whole_term_preflight_checks_arithmetic_before_any_repair_or_interning() {
    let original = fp_entries();
    let valid = (
        TermData::App(Symbol::named("fp.add"), ids(&[0, 1, 1])),
        Sort::FloatingPoint(8, 24),
    );
    let mut values = original.clone();
    values.push(valid);
    let before = serde_json::to_vec(&values).expect("source snapshot serialization");
    preflight_term::validate_term_snapshot_with_progress(&values, &mut |_, _| true)
        .expect("valid native source shape");
    assert_eq!(serde_json::to_vec(&values).expect("same snapshot"), before);
    for data in [
        TermData::App(Symbol::named("fp.add"), ids(&[0, 1, 2])),
        TermData::App(Symbol::named("fp.add"), ids(&[3, 1, 1])),
        TermData::App(Symbol::indexed("fp.add", vec![0]), ids(&[0, 1, 1])),
    ] {
        let mut malformed = original.clone();
        malformed.push((data, Sort::FloatingPoint(8, 24)));
        let captured = serde_json::to_vec(&malformed).expect("negative snapshot");
        assert!(matches!(
            preflight_term::validate_term_snapshot_with_progress(&malformed, &mut |_, _| true),
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
        assert_eq!(
            serde_json::to_vec(&malformed).expect("unchanged malformed snapshot"),
            captured
        );
    }
}

#[test]
fn missing_handles_are_rejected_in_both_named_and_indexed_fp_forms() {
    for (symbol, mut args, result) in specimens() {
        if let Some(last) = args.last_mut() {
            *last = TermId::SENTINEL;
            assert!(matches!(
                run(&fp_entries(), &symbol, &args, &result),
                Err(ProofCheckError::MalformedProofBundle { .. })
            ));
        }
    }
}

#[test]
fn callback_unwind_cannot_mutate_the_borrowed_fp_source_snapshot() {
    let values = fp_entries();
    let before = values.clone();
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        validate_app_signature_with_progress(
            &values,
            values.len(),
            &Symbol::named("fp.add"),
            &ids(&[0, 1, 1]),
            &Sort::FloatingPoint(8, 24),
            &mut |_, _| panic!("caller owner stopped"),
        )
    }));
    assert!(outcome.is_err());
    assert_eq!(values, before);
}
