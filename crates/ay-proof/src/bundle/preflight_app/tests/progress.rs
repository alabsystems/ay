// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort};

use super::*;

fn usage(
    entries: &[(TermData, Sort)],
    symbol: &Symbol,
    args: &[TermId],
    result: &Sort,
) -> Vec<(usize, usize)> {
    let mut trace = Vec::new();
    validate_app_signature_with_progress(
        entries,
        entries.len(),
        symbol,
        args,
        result,
        &mut |w, b| {
            trace.push((w, b));
            true
        },
    )
    .expect("valid measured app");
    trace
}

#[test]
fn refusal_at_every_callback_and_final_poll_propagates_without_input_mutation() {
    let entries = entries();
    let expected_entries = entries.clone();
    for (symbol, args, result) in [
        (
            Symbol::named("store"),
            vec![TermId(5), TermId(1), TermId(0)],
            array(),
        ),
        (
            Symbol::indexed("NaN", vec![8, 24]),
            vec![],
            Sort::FloatingPoint(8, 24),
        ),
        (
            Symbol::indexed("extract", vec![7, 0]),
            vec![TermId(3)],
            bv(8),
        ),
        (Symbol::named("unknown"), vec![TermId(2)], Sort::Real),
    ] {
        let trace = usage(&entries, &symbol, &args, &result);
        assert_eq!(trace.first(), Some(&(0, 0)));
        assert_eq!(trace.last(), Some(&(0, 0)));
        for reject_at in 1..=trace.len() {
            let mut calls = 0;
            let answer = validate_app_signature_with_progress(
                &entries,
                entries.len(),
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
            assert_eq!(entries, expected_entries);
        }
    }
}

#[test]
fn wide_distinct_and_boolean_args_are_metered_per_operand() {
    let entries = entries();
    for name in ["distinct", "and", "or", "xor", "=>"] {
        let symbol = Symbol::named(name);
        let short = [TermId(0); 2];
        let long = vec![TermId(0); 4096];
        let baseline: usize = usage(&entries, &symbol, &short, &Sort::Bool)
            .iter()
            .map(|charge| charge.0)
            .sum();
        let wide: usize = usage(&entries, &symbol, &long, &Sort::Bool)
            .iter()
            .map(|charge| charge.0)
            .sum();
        assert!(wide >= baseline + 2 * (long.len() - short.len()));
        let mut left = baseline + 100;
        let answer = validate_app_signature_with_progress(
            &entries,
            entries.len(),
            &symbol,
            &long,
            &Sort::Bool,
            &mut |work, _| {
                if work > left {
                    false
                } else {
                    left -= work;
                    true
                }
            },
        );
        assert!(matches!(answer, Err(ProofCheckError::ResourceLimit)));
    }
}

#[test]
fn aggregate_callback_budget_is_not_reset_between_signature_calls() {
    let entries = entries();
    let symbol = Symbol::named("=");
    let args = [TermId(5); 2];
    let mut left: usize = usage(&entries, &symbol, &args, &Sort::Bool)
        .iter()
        .map(|charge| charge.0)
        .sum();
    let mut progress = |work, _| {
        if work > left {
            false
        } else {
            left -= work;
            true
        }
    };
    assert!(validate_app_signature_with_progress(
        &entries,
        entries.len(),
        &symbol,
        &args,
        &Sort::Bool,
        &mut progress
    )
    .is_ok());
    assert!(matches!(
        validate_app_signature_with_progress(
            &entries,
            entries.len(),
            &symbol,
            &args,
            &Sort::Bool,
            &mut progress
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn recursive_sort_equality_is_guarded_at_the_inclusive_depth_boundary() {
    let symbol = Symbol::named("=");
    let args = [TermId(0), TermId(1)];
    let mut sort = Sort::Int;
    for _ in 0..MAX_BUNDLE_SORT_DEPTH {
        sort = Sort::Seq(Box::new(sort));
    }
    let mut entries = vec![
        (TermData::Var("a".into(), 0), sort.clone()),
        (TermData::Var("b".into(), 1), sort),
    ];
    assert!(compare(&entries, &symbol, &args, &Sort::Bool));
    let trace = usage(&entries, &symbol, &args, &Sort::Bool);
    assert!(trace.len() > 2 * MAX_BUNDLE_SORT_DEPTH);
    entries[1].1 = Sort::Seq(Box::new(entries[1].1.clone()));
    assert!(matches!(
        run(&entries, &symbol, &args, &Sort::Bool),
        Err(ProofCheckError::MalformedProofBundle { .. })
    ));
    // Unknown UF validation does not recursively compare this sort. Full
    // snapshot sort validation is still required independently before replay.
    assert!(compare(
        &entries,
        &Symbol::named("opaque"),
        &args,
        &entries[1].1
    ));
}

#[test]
fn nested_datatype_names_are_priced_before_exact_sort_comparison() {
    let large = "long_field".repeat(8192);
    let sort = Sort::Datatype(DatatypeSort::new(
        "D",
        vec![DatatypeConstructor::new(
            "C",
            vec![DatatypeField::new(
                &large,
                Sort::Array(Box::new(ArraySort::new(
                    Sort::Int,
                    Sort::Seq(Box::new(Sort::Bool)),
                ))),
            )],
        )],
    ));
    let entries = vec![
        (TermData::Var("a".into(), 0), sort.clone()),
        (TermData::Var("b".into(), 1), sort),
    ];
    let symbol = Symbol::named("=");
    let args = [TermId(0), TermId(1)];
    assert!(compare(&entries, &symbol, &args, &Sort::Bool));
    let trace = usage(&entries, &symbol, &args, &Sort::Bool);
    assert!(trace.iter().map(|charge| charge.0).sum::<usize>() >= 4 * large.len());
    assert_eq!(trace.iter().map(|charge| charge.1).sum::<usize>(), 0);
    let answer = validate_app_signature_with_progress(
        &entries,
        entries.len(),
        &symbol,
        &args,
        &Sort::Bool,
        &mut |work, _| work < large.len(),
    );
    assert!(matches!(answer, Err(ProofCheckError::ResourceLimit)));
}

#[test]
fn invalid_signature_diagnostics_are_priced_before_formatting() {
    let entries = entries();
    for (symbol, args, result) in [
        (Symbol::named("select"), vec![TermId(5)], Sort::Bool),
        (Symbol::indexed("str.len", vec![0]), vec![], Sort::Int),
        (Symbol::named("="), vec![TermId(0), TermId(1)], Sort::Bool),
    ] {
        let mut allocations = 0;
        let answer = validate_app_signature_with_progress(
            &entries,
            entries.len(),
            &symbol,
            &args,
            &result,
            &mut |_, bytes| {
                if bytes > 0 {
                    allocations += 1;
                    false
                } else {
                    true
                }
            },
        );
        assert!(matches!(answer, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(allocations, 1);
    }
    let error = run(
        &entries,
        &Symbol::named("="),
        &[TermId(0), TermId(1)],
        &Sort::Bool,
    )
    .unwrap_err();
    assert!(error
        .to_string()
        .contains("`=` must return Bool and compare equal-sorted"));
    let error = run(
        &entries,
        &Symbol::indexed("str.len", vec![0]),
        &[],
        &Sort::Int,
    )
    .unwrap_err();
    assert!(error
        .to_string()
        .contains("builtin `str.len` must be a named symbol without indices"));
}
