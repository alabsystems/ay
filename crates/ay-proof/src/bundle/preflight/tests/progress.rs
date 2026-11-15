// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn trace(bundle: &SerializableProofBundle) -> Vec<(usize, usize)> {
    let mut trace = Vec::new();
    preflight_bundle_with_progress(bundle, &mut |work, bytes| {
        trace.push((work, bytes));
        true
    })
    .expect("valid measured bundle");
    trace
}

#[test]
fn cancellation_at_every_callback_including_final_never_returns_a_namespace() {
    let bundle = with_context();
    let original = serde_json::to_vec(&bundle).unwrap();
    let trace = trace(&bundle);
    assert_eq!(trace.first(), Some(&(0, 0)));
    assert_eq!(trace.last(), Some(&(0, 0)));
    for stop in 1..=trace.len() {
        let mut calls = 0usize;
        assert_resource(preflight_bundle_with_progress(&bundle, &mut |_, _| {
            calls += 1;
            calls < stop
        }));
        assert_eq!(calls, stop, "the first refusal propagates immediately");
    }
    assert_eq!(serde_json::to_vec(&bundle).unwrap(), original);
    compare(&bundle).expect("unchanged valid input");
}

#[test]
fn one_cumulative_work_and_byte_budget_covers_all_composed_phases() {
    let bundle = with_context();
    let totals = trace(&bundle)
        .iter()
        .fold((0usize, 0usize), |(work, bytes), next| {
            (work + next.0, bytes + next.1)
        });
    for (limits, accepted) in [
        (totals, true),
        ((0, usize::MAX), false),
        ((usize::MAX, 0), false),
        ((totals.0 - 1, totals.1), false),
        ((totals.0, totals.1 - 1), false),
    ] {
        let mut remaining = limits;
        let result = preflight_bundle_with_progress(&bundle, &mut |work, bytes| {
            if work > remaining.0 || bytes > remaining.1 {
                return false;
            }
            remaining.0 -= work;
            remaining.1 -= bytes;
            true
        });
        if accepted {
            assert_eq!(result.expect("exact allowance").len(), 5);
        } else {
            assert_resource(result);
        }
    }
}

#[test]
fn repeated_obligations_and_wide_signature_arguments_cannot_hide_in_phase_reserves() {
    let baseline_bundle = with_context();
    let baseline: usize = trace(&baseline_bundle).iter().map(|charge| charge.0).sum();
    for signature_arguments in [false, true] {
        let mut bundle = with_context();
        if signature_arguments {
            bundle.datatype_member_signatures[0].argument_sorts = vec![Sort::Int; 4_096];
        } else {
            bundle.obligation_assertions = vec![bundle.obligation_assertions[0]; 4_096];
        }
        let wide: usize = trace(&bundle).iter().map(|charge| charge.0).sum();
        assert!(wide > baseline + 4_000);
        let mut left = baseline + 100;
        assert_resource(preflight_bundle_with_progress(&bundle, &mut |work, _| {
            if work > left {
                return false;
            }
            left -= work;
            true
        }));
    }
}

#[test]
fn metadata_and_obligation_diagnostics_allocate_only_after_permission() {
    let bundle = fixture();
    for expected in [false, true] {
        for id in [
            None,
            Some(TermId::SENTINEL),
            bundle.obligation_assertions.first().copied(),
        ] {
            let mut attempted = 0usize;
            assert_resource(validate_bool_constant_id(
                &bundle.term_entries,
                id,
                expected,
                &mut |_, bytes| {
                    attempted += usize::from(bytes != 0);
                    bytes == 0
                },
            ));
            assert_eq!(attempted, 1);
        }
    }
    let mut bundle = fixture();
    bundle.obligation_assertions.push(TermId::SENTINEL);
    let mut attempted = 0usize;
    assert_resource(validate_obligations(&bundle, &mut |_, bytes| {
        attempted += usize::from(bytes != 0);
        bytes == 0
    }));
    assert_eq!(attempted, 1);
}

#[test]
fn errors_after_declaration_construction_do_not_return_a_checked_prefix() {
    let mut bundle = with_context();
    let ordinary_int = TermId(bundle.term_entries.len() as u32);
    bundle
        .term_entries
        .push((TermData::Const(Constant::Int(7.into())), Sort::Int));
    bundle.steps.push(ProofStep::Assume(ordinary_int));
    // The declaration phase alone can construct its complete five-name map.
    assert_eq!(
        validate_declaration_context_with_progress(&bundle, &mut |_, _| true)
            .unwrap()
            .len(),
        5
    );
    assert_malformed(compare(&bundle), "assumption");
}
