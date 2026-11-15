// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn refusal_at_every_callback_including_final_poll_is_sticky() {
    let mut values = entries();
    let (then_form, else_form) = branches(&mut values);
    let combined = app(&mut values, "and", &[then_form, else_form]);
    let terms = store(values);
    let snapshot = terms.entries_snapshot();
    for (assumed, authored) in [(combined, vec![ITE]), (X, vec![ITE]), (X, vec![])] {
        let mut charges = Vec::new();
        let expected = assumed_is_authored_bool_ite_consequence_with_progress(
            &terms,
            assumed,
            &authored,
            &mut |work, bytes| {
                charges.push((work, bytes));
                true
            },
        );
        assert!(expected.is_ok());
        assert_eq!(charges.first(), Some(&(0, 0)));
        assert_eq!(charges.last(), Some(&(0, 0)));
        for refusal in 1..=charges.len() {
            let mut calls = 0;
            let result = assumed_is_authored_bool_ite_consequence_with_progress(
                &terms,
                assumed,
                &authored,
                &mut |_, _| {
                    calls += 1;
                    calls != refusal
                },
            );
            assert_eq!(result, Err(ProofCheckError::ResourceLimit));
            assert_eq!(calls, refusal, "no callback may recover after refusal");
            assert_eq!(terms.entries_snapshot(), snapshot);
        }
    }
}

#[test]
fn branch_storage_is_charged_before_allocation() {
    let mut values = entries();
    let (then_form, _) = branches(&mut values);
    let terms = store(values);
    let mut allocated = false;
    let result = assumed_is_authored_bool_ite_consequence_with_progress(
        &terms,
        then_form,
        &[ITE],
        &mut |_, bytes| {
            allocated |= bytes != 0;
            bytes == 0
        },
    );
    assert!(allocated);
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
}

#[test]
fn wide_branches_and_borrowed_views_poll_before_unbounded_work() {
    let mut values = entries();
    let branch = app(&mut values, "or", &vec![T; 4096]);
    let condition = app(&mut values, "and", &vec![C; 4096]);
    let assumed = app(&mut values, "or", &vec![X; 4096]);
    let terms = store(values);
    for (assumed, ite) in [(X, (C, branch, E)), (X, (condition, T, E)), (assumed, ITE)] {
        let mut work = 0;
        let result = assumed_is_authored_bool_ite_consequence_with_progress(
            &terms,
            assumed,
            &[ite],
            &mut |amount, _| {
                work += amount;
                work <= 128
            },
        );
        assert_eq!(result, Err(ProofCheckError::ResourceLimit));
        assert!(work <= 192, "no whole-fanout bulk scan before callback");
    }
}

#[test]
fn caller_allowance_spans_multiple_matches_without_reset() {
    let mut values = entries();
    let (then_form, _) = branches(&mut values);
    let terms = store(values);
    let mut total = (0, 0);
    assert_eq!(
        assumed_is_authored_bool_ite_consequence_with_progress(
            &terms,
            then_form,
            &[ITE],
            &mut |work, bytes| {
                total.0 += work;
                total.1 += bytes;
                true
            },
        ),
        Ok(true)
    );
    let mut spent = (0, 0);
    let mut progress = |work, bytes| {
        spent.0 += work;
        spent.1 += bytes;
        spent.0 <= total.0 && spent.1 <= total.1
    };
    assert_eq!(
        assumed_is_authored_bool_ite_consequence_with_progress(
            &terms,
            then_form,
            &[ITE],
            &mut progress
        ),
        Ok(true)
    );
    assert_eq!(
        assumed_is_authored_bool_ite_consequence_with_progress(
            &terms,
            then_form,
            &[ITE],
            &mut progress
        ),
        Err(ProofCheckError::ResourceLimit)
    );
}

#[test]
fn malformed_diagnostic_is_charged_before_string_creation() {
    let terms = store(entries());
    let mut diagnostic_bytes = 0;
    let result = assumed_is_authored_bool_ite_consequence_with_progress(
        &terms,
        TermId::SENTINEL,
        &[ITE],
        &mut |_, bytes| {
            diagnostic_bytes += bytes;
            bytes == 0
        },
    );
    assert!(diagnostic_bytes > 0);
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
}
