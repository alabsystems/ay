// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::proof_validation::verify_farkas_conflict_lits_full;
use crate::{Sort, Symbol};

fn equality_chain_fixture() -> (TermStore, Vec<TheoryLit>, FarkasAnnotation) {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let variables: Vec<_> = (0..22)
        .map(|index| terms.mk_var(format!("metered_span_{index}"), Sort::Int))
        .collect();
    let negated_endpoint = terms.mk_app(Symbol::named("-"), [variables[21]], Sort::Int);
    let endpoint_difference = terms.mk_app(
        Symbol::named("+"),
        [variables[0], negated_endpoint],
        Sort::Int,
    );
    let endpoint_equality = terms.mk_eq(endpoint_difference, zero);
    let mut conflict = vec![TheoryLit::new(endpoint_equality, false)];
    for pair in variables.windows(2) {
        let equality = terms.mk_eq(pair[0], pair[1]);
        conflict.push(TheoryLit::new(equality, true));
    }
    (terms, conflict, FarkasAnnotation::from_ints(&[1; 22]))
}

fn metered_result(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> Result<(), FarkasValidationError> {
    verify_affine_equality_farkas_with_progress(terms, conflict, farkas, &mut |_, _| true)
}

fn assert_differential(terms: &TermStore, conflict: &[TheoryLit], farkas: &FarkasAnnotation) {
    assert_eq!(
        metered_result(terms, conflict, farkas),
        verify_farkas_conflict_lits_full(terms, conflict, farkas)
    );
}

#[test]
fn equality_chain_accepts_and_exact_envelope_replays() {
    let (terms, conflict, farkas) = equality_chain_fixture();
    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("the legacy validator accepts the 21-equality chain");

    let (mut total_work, mut total_bytes) = (0usize, 0usize);
    verify_affine_equality_farkas_with_progress(&terms, &conflict, &farkas, &mut |work, bytes| {
        total_work = total_work.checked_add(work).expect("test work fits");
        total_bytes = total_bytes.checked_add(bytes).expect("test bytes fit");
        true
    })
    .expect("the progress path accepts the production-shaped chain");
    assert!(total_work > conflict.len());
    assert!(total_bytes > 0);

    let (mut work_left, mut bytes_left) = (total_work, total_bytes);
    verify_affine_equality_farkas_with_progress(&terms, &conflict, &farkas, &mut |work, bytes| {
        let (Some(work), Some(bytes)) =
            (work_left.checked_sub(work), bytes_left.checked_sub(bytes))
        else {
            return false;
        };
        work_left = work;
        bytes_left = bytes;
        true
    })
    .expect("the exact measured envelope accepts");
    assert_eq!((work_left, bytes_left), (0, 0));

    for limit_bytes in [false, true] {
        let limit = if limit_bytes { total_bytes } else { total_work };
        let mut used = 0usize;
        let error = verify_affine_equality_farkas_with_progress(
            &terms,
            &conflict,
            &farkas,
            &mut |work, bytes| {
                let charge = if limit_bytes { bytes } else { work };
                let Some(next) = used.checked_add(charge) else {
                    return false;
                };
                if next >= limit {
                    return false;
                }
                used = next;
                true
            },
        )
        .expect_err("one-unit-short envelopes must refuse");
        assert_eq!(error, FarkasValidationError::ResourceLimit);
    }
}

#[test]
fn equality_and_disequality_spellings_preserve_effective_polarity() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("metered_polarity_x", Sort::Int);
    let y = terms.mk_var("metered_polarity_y", Sort::Int);
    let equality = terms.mk_eq(x, y);
    let distinct = terms.mk_app(Symbol::named("distinct"), [x, y], Sort::Bool);
    let not_equality = terms.mk_not_raw(equality);
    let not_distinct = terms.mk_not_raw(distinct);

    let disequalities = [
        TheoryLit::new(equality, false),
        TheoryLit::new(not_equality, true),
        TheoryLit::new(distinct, true),
        TheoryLit::new(not_distinct, false),
    ];
    let positive_equalities = [
        TheoryLit::new(equality, true),
        TheoryLit::new(not_equality, false),
        TheoryLit::new(distinct, false),
        TheoryLit::new(not_distinct, true),
    ];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    for disequality in disequalities {
        for positive_equality in positive_equalities {
            assert_differential(
                &terms,
                &[disequality.clone(), positive_equality.clone()],
                &farkas,
            );
        }
    }
}

#[test]
fn both_disequality_branches_are_required() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let x = terms.mk_var("metered_branch_x", Sort::Int);
    let x_eq_zero = terms.mk_eq(x, zero);
    let x_eq_one = terms.mk_eq(x, one);
    let conflict = [
        TheoryLit::new(x_eq_zero, false),
        TheoryLit::new(x_eq_one, true),
    ];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let legacy = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect_err("one satisfiable disequality branch must reject");
    let metered = metered_result(&terms, &conflict, &farkas)
        .expect_err("the metered path must require the same second branch");
    assert!(matches!(
        legacy,
        FarkasValidationError::VariablesNotEliminated { .. }
            | FarkasValidationError::NoContradiction { .. }
    ));
    assert!(matches!(
        metered,
        FarkasValidationError::VariablesNotEliminated { .. }
            | FarkasValidationError::NoContradiction { .. }
    ));
}

#[test]
fn congruence_changes_only_rejected_diagnostic_detail() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("metered_diag_x", Sort::Int);
    let y = terms.mk_var("metered_diag_y", Sort::Int);
    let z = terms.mk_var("metered_diag_z", Sort::Int);
    let x_eq_z = terms.mk_eq(x, z);
    let x_eq_y = terms.mk_eq(x, y);
    let conflict = [TheoryLit::new(x_eq_z, false), TheoryLit::new(x_eq_y, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let legacy = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect_err("the affine set is satisfiable");
    let metered = metered_result(&terms, &conflict, &farkas)
        .expect_err("the metered path must reject the same set");
    assert!(matches!(
        legacy,
        FarkasValidationError::VariablesNotEliminated { .. }
    ));
    assert!(matches!(
        metered,
        FarkasValidationError::VariablesNotEliminated { .. }
    ));
}

#[test]
fn signed_rows_and_second_disequality_fail_closed() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let x = terms.mk_var("metered_signed_x", Sort::Int);
    let y = terms.mk_var("metered_signed_y", Sort::Int);
    let x_eq_zero = terms.mk_eq(x, zero);
    let x_eq_y = terms.mk_eq(x, y);
    let y_eq_zero = terms.mk_eq(y, zero);
    let conflict = [
        TheoryLit::new(x_eq_zero, false),
        TheoryLit::new(x_eq_zero, true),
    ];

    assert_differential(&terms, &conflict, &FarkasAnnotation::from_ints(&[1, -7]));
    assert_differential(&terms, &conflict, &FarkasAnnotation::from_ints(&[-1, 1]));

    let two_disequalities = [
        TheoryLit::new(x_eq_y, false),
        TheoryLit::new(y_eq_zero, false),
        TheoryLit::new(x_eq_zero, true),
    ];
    assert!(matches!(
        verify_farkas_conflict_lits_full(
            &terms,
            &two_disequalities,
            &FarkasAnnotation::from_ints(&[1, 1, 1]),
        ),
        Err(FarkasValidationError::DisequalityLiteral { term, .. }) if term == y_eq_zero
    ));
}

#[test]
fn affine_classifier_rejects_every_opaque_parser_fallback() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let x = terms.mk_var("metered_surface_x", Sort::Int);
    let y = terms.mk_var("metered_surface_y", Sort::Int);
    let opaque = terms.mk_app(Symbol::named("surface_opaque"), [x], Sort::Int);
    let nonlinear = terms.mk_app(Symbol::named("*"), [x, y], Sort::Int);
    let zero_quotient = terms.mk_app(Symbol::named("/"), [x, zero], Sort::Int);
    let symbolic_quotient = terms.mk_app(Symbol::named("/"), [x, y], Sort::Int);
    for expression in [opaque, nonlinear, zero_quotient, symbolic_quotient] {
        let equality = terms.mk_eq(expression, zero);
        assert_eq!(
            farkas_progress_row_kind(&terms, &TheoryLit::new(equality, true)),
            None
        );
        assert_eq!(
            farkas_progress_row_kind(&terms, &TheoryLit::new(equality, false)),
            None
        );
    }

    let scaled = terms.mk_app(Symbol::named("*"), [zero, x], Sort::Int);
    let affine_equality = terms.mk_eq(scaled, zero);
    assert_eq!(
        farkas_progress_row_kind(&terms, &TheoryLit::new(affine_equality, true)),
        Some(FarkasProgressRowKind::PositiveEquality)
    );
}
