// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn fixture() -> (TermStore, TermId, TermId) {
    let mut terms = TermStore::new();
    let body = terms.mk_var("choice_source_bound", Sort::Bool);
    let witness = terms
        .try_fresh_var_with_progress("native_choice", &Sort::Bool, &mut |_, _| true)
        .unwrap();
    (terms, witness, body)
}

#[test]
fn controlled_new_choice_registers_exact_metadata_without_an_assertion() {
    let (mut terms, witness, body) = fixture();
    let prefix = terms.snapshot_stamp();
    let generation = terms.checker_visible_metadata_generation();
    terms
        .try_register_new_skolem_choice_with_progress(
            witness,
            "choice_source_bound",
            &Sort::Bool,
            body,
            &mut |_, _| true,
        )
        .unwrap();
    let TermData::Var(name, _) = terms.get(witness) else {
        panic!("witness")
    };
    assert!(terms.is_skolem_symbol(name));
    let choice = terms.skolem_choice(witness).unwrap();
    assert_eq!(choice.binder, "choice_source_bound");
    assert_eq!(choice.sort, Sort::Bool);
    assert_eq!(choice.body, body);
    assert!(
        terms.snapshot_stamp() == prefix,
        "registration does not rewrite source terms"
    );
    assert_eq!(terms.checker_visible_metadata_generation(), generation + 2);
    assert!(terms
        .try_register_new_skolem_choice_with_progress(
            witness,
            "other_source",
            &Sort::Bool,
            body,
            &mut |_, _| true
        )
        .is_err());
    assert_eq!(
        terms.skolem_choice(witness).unwrap().binder,
        "choice_source_bound"
    );
}

#[test]
fn controlled_new_choice_refuses_invalid_handles_sorts_and_existing_names_before_registration() {
    for change in 0..4 {
        let (mut terms, mut witness, mut body) = fixture();
        let sort = if change == 1 { Sort::Int } else { Sort::Bool };
        if change == 0 {
            witness = TermId(u32::MAX);
        }
        if change == 2 {
            body = terms.mk_int(0.into());
        }
        if change == 3 {
            let TermData::Var(name, _) = terms.get(witness) else {
                panic!("witness")
            };
            let name = name.clone();
            terms.mark_skolem_symbol(name);
        }
        let generation = terms.checker_visible_metadata_generation();
        assert!(terms
            .try_register_new_skolem_choice_with_progress(
                witness,
                "choice_source_bound",
                &sort,
                body,
                &mut |_, _| true
            )
            .is_err());
        assert_eq!(terms.checker_visible_metadata_generation(), generation);
        assert!(terms.skolem_choice(witness).is_none());
    }
}

#[test]
fn controlled_new_choice_cancellation_never_leaves_partial_authority() {
    let (mut terms, witness, body) = fixture();
    let mut trace = Vec::new();
    terms
        .try_register_new_skolem_choice_with_progress(
            witness,
            "choice_source_bound",
            &Sort::Bool,
            body,
            &mut |w, b| {
                trace.push((w, b));
                true
            },
        )
        .unwrap();
    for stop in 1..=trace.len() {
        let (mut terms, witness, body) = fixture();
        let mut calls = 0;
        let result = terms.try_register_new_skolem_choice_with_progress(
            witness,
            "choice_source_bound",
            &Sort::Bool,
            body,
            &mut |_, _| {
                calls += 1;
                calls < stop
            },
        );
        assert_eq!(result, Err(ControlledTermInternError::ResourceLimit));
        assert_eq!(calls, stop);
        let TermData::Var(name, _) = terms.get(witness) else {
            panic!("witness")
        };
        assert_eq!(
            terms.is_skolem_symbol(name),
            terms.skolem_choice(witness).is_some()
        );
        if terms.skolem_choice(witness).is_some() {
            assert_eq!(
                stop,
                trace.len(),
                "only the final refusal can retain a coherent new choice"
            );
        }
    }
}

#[test]
fn controlled_new_choice_original_work_and_storage_are_cumulative() {
    let (mut terms, witness, body) = fixture();
    let mut cost = (0usize, 0usize);
    terms
        .try_register_new_skolem_choice_with_progress(
            witness,
            "choice_source_bound",
            &Sort::Bool,
            body,
            &mut |w, b| {
                cost.0 += w;
                cost.1 += b;
                true
            },
        )
        .unwrap();
    for (work, bytes) in [(cost.0 - 1, usize::MAX), (usize::MAX, cost.1 - 1)] {
        let (mut terms, witness, body) = fixture();
        let mut left = (work, bytes);
        assert_eq!(
            terms.try_register_new_skolem_choice_with_progress(
                witness,
                "choice_source_bound",
                &Sort::Bool,
                body,
                &mut |w, b| {
                    let Some(work) = left.0.checked_sub(w) else {
                        return false;
                    };
                    let Some(bytes) = left.1.checked_sub(b) else {
                        return false;
                    };
                    left = (work, bytes);
                    true
                }
            ),
            Err(ControlledTermInternError::ResourceLimit)
        );
    }
}
