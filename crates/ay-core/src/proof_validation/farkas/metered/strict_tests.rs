// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::proof_validation::{
    verify_affine_equality_farkas_with_progress, verify_farkas_conflict_lits_linear_holds,
};
use crate::Sort;

fn independent_equalities(n: usize) -> (TermStore, Vec<TheoryLit>, FarkasAnnotation) {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let mut variables = Vec::new();
    let mut conflict = Vec::new();
    for index in 0..n {
        let x = terms.mk_var(format!("strict_orientation_{index}"), Sort::Int);
        variables.push(x);
        // Raw ordered expressions make the last exhaustive orientation
        // essential in the positive disequality branch.
        let eq = terms.mk_app(Symbol::named("="), [x, zero], Sort::Bool);
        conflict.push(TheoryLit::new(eq, true));
    }
    let sum = terms.mk_app(Symbol::named("+"), variables, Sort::Int);
    let neq = terms.mk_app(Symbol::named("distinct"), [sum, zero], Sort::Bool);
    conflict.push(TheoryLit::new(neq, true));
    let annotation = FarkasAnnotation::from_ints(&vec![1; n + 1]);
    (terms, conflict, annotation)
}

fn strict(terms: &TermStore, conflict: &[TheoryLit], annotation: &FarkasAnnotation) -> bool {
    farkas_conflict_lits_linear_holds_with_progress(terms, conflict, annotation, &mut |_, _| true)
        .expect("unrestricted test meter must not exhaust")
}

#[test]
fn exact_orientation_boundary_matches_legacy_without_span_completion() {
    for (n, expected) in [(10, true), (11, false)] {
        let (terms, conflict, annotation) = independent_equalities(n);
        assert_eq!(
            verify_farkas_conflict_lits_linear_holds(&terms, &conflict, &annotation),
            expected
        );
        assert_eq!(strict(&terms, &conflict, &annotation), expected);
    }
}

#[test]
fn large_orientation_search_accepts_first_and_single_flip_but_not_two_flips() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("strict_large_x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let eq = terms.mk_app(Symbol::named("="), [x, zero], Sort::Bool);
    let ge = terms.mk_app(Symbol::named(">="), [x, one], Sort::Bool);
    let mut conflict = vec![TheoryLit::new(eq, true); 11];
    conflict.push(TheoryLit::new(ge, true));
    for (last, expected) in [(11, true), (9, true), (7, false)] {
        let mut weights = vec![1; 11];
        weights.push(last);
        let annotation = FarkasAnnotation::from_ints(&weights);
        assert_eq!(
            verify_farkas_conflict_lits_linear_holds(&terms, &conflict, &annotation),
            expected
        );
        assert_eq!(strict(&terms, &conflict, &annotation), expected);
    }
}

#[test]
fn actual_magnitudes_are_not_replaced_by_affine_span_authority() {
    let (terms, conflict, mut annotation) = independent_equalities(11);
    annotation.coefficients[0] = Rational64::from_integer(2);
    // The support entails the disequality's negation regardless of weights.
    // A strict positional witness with this magnitude cannot cancel x_0.
    verify_affine_equality_farkas_with_progress(&terms, &conflict, &annotation, &mut |_, _| true)
        .expect("the deliberately broader span decision accepts this support");
    assert!(!verify_farkas_conflict_lits_linear_holds(
        &terms,
        &conflict,
        &annotation
    ));
    assert!(!strict(&terms, &conflict, &annotation));
}

#[test]
fn signed_equalities_zero_causes_and_both_disequality_branches_preserve_decisions() {
    let (mut terms, conflict, annotation) = independent_equalities(3);
    for sign in [1, -1] {
        let mut weights = annotation.clone();
        weights.coefficients[0] = Rational64::from_integer(sign);
        assert!(verify_farkas_conflict_lits_linear_holds(
            &terms, &conflict, &weights
        ));
        assert!(strict(&terms, &conflict, &weights));
    }
    let mut with_zero = conflict.clone();
    let irrelevant = terms.mk_var("strict_zero_bool", Sort::Bool);
    with_zero.push(TheoryLit::new(irrelevant, true));
    let mut zero_weights = annotation.clone();
    zero_weights.coefficients.push(Rational64::zero());
    assert!(strict(&terms, &with_zero, &zero_weights));
    // Only the positive branch contradicts; accepting one branch is unsound.
    let x = terms.mk_var("strict_one_sided", Sort::Real);
    let zero = terms.mk_int(0.into());
    let le = terms.mk_app(Symbol::named("<="), [x, zero], Sort::Bool);
    let neq = terms.mk_app(Symbol::named("distinct"), [x, zero], Sort::Bool);
    let rows = [TheoryLit::new(le, true), TheoryLit::new(neq, true)];
    assert!(!strict(
        &terms,
        &rows,
        &FarkasAnnotation::from_ints(&[1, 1])
    ));
}

#[test]
fn integer_tightening_real_strictness_and_negative_inequalities_match_legacy() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    for sort in [Sort::Int, Sort::Real] {
        let x = terms.mk_var(format!("strict_rounding_{sort:?}"), sort);
        let lt = terms.mk_app(Symbol::named("<"), [x, zero], Sort::Bool);
        let ge = terms.mk_app(Symbol::named(">="), [x, zero], Sort::Bool);
        let rows = [TheoryLit::new(lt, true), TheoryLit::new(ge, true)];
        for weights in [[1, 1], [0, 1], [-1, 1]] {
            let annotation = FarkasAnnotation::from_ints(&weights);
            let expected = verify_farkas_conflict_lits_linear_holds(&terms, &rows, &annotation);
            assert_eq!(strict(&terms, &rows, &annotation), expected);
        }
    }
}

fn doubling_dag(depth: usize) -> (TermStore, Vec<TheoryLit>, FarkasAnnotation) {
    let mut terms = TermStore::new();
    let mut term = terms.mk_var("strict_shared_dag", Sort::Int);
    for _ in 0..depth {
        let previous = term;
        term = terms.mk_app(Symbol::named("+"), [previous, previous], Sort::Int);
        let TermData::App(_, children) = terms.get(term) else {
            panic!("raw shared addition retained");
        };
        assert_eq!(children.as_slice(), &[previous, previous]);
    }
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let le = terms.mk_app(Symbol::named("<="), [term, zero], Sort::Bool);
    let ge = terms.mk_app(Symbol::named(">="), [term, one], Sort::Bool);
    (
        terms,
        vec![TheoryLit::new(le, true), TheoryLit::new(ge, true)],
        FarkasAnnotation::from_ints(&[1, 1]),
    )
}

#[test]
fn shared_dag_exhausts_during_parse_and_same_owner_stays_spent() {
    let (terms, conflict, annotation) = doubling_dag(32);
    // Reach the parser with the real shared DAG, then deny an edge visit.
    // Counting work alone suffices to deny long before exponential expansion.
    let mut remaining = 256usize;
    let mut spent = false;
    let mut positive_visits = 0usize;
    let mut progress = |work: usize, _: usize| {
        if spent {
            return false;
        }
        positive_visits += usize::from(work > 0);
        let Some(next) = remaining.checked_sub(work) else {
            spent = true;
            return false;
        };
        remaining = next;
        true
    };
    // Direct normalization proves this is inside parsing rather than a
    // fixed up-front clause-length refusal.
    assert!(matches!(
        normalize(
            &terms,
            &conflict[0],
            &annotation.coefficients[0],
            &mut ProgressMeter::new(&mut progress)
        ),
        Err(FarkasValidationError::ResourceLimit)
    ));
    assert!(matches!(
        farkas_conflict_lits_linear_holds_with_progress(
            &terms,
            &conflict,
            &annotation,
            &mut progress
        ),
        Err(FarkasValidationError::ResourceLimit)
    ));
    drop(progress);
    assert!(spent);
    assert!(
        positive_visits > 32,
        "the parser entered the shared subtree"
    );
}

#[test]
fn cancellation_interrupts_real_dag_visits_without_spending_a_fresh_grant() {
    let (terms, conflict, annotation) = doubling_dag(32);
    let mut polls = 0usize;
    let mut cancelled = false;
    let mut progress = |_: usize, _: usize| {
        polls += 1;
        cancelled |= polls >= 80;
        !cancelled
    };
    for _ in 0..2 {
        assert!(matches!(
            farkas_conflict_lits_linear_holds_with_progress(
                &terms,
                &conflict,
                &annotation,
                &mut progress
            ),
            Err(FarkasValidationError::ResourceLimit)
        ));
    }
    drop(progress);
    assert!(cancelled);
    assert_eq!(
        polls, 81,
        "the second call observes the same cancelled owner immediately"
    );
}

#[test]
fn orientation_engine_can_be_cancelled_after_preparation_and_cannot_refill_work() {
    let (terms, conflict, annotation) = independent_equalities(10);
    let mut unlimited = |_: usize, _: usize| true;
    let mut preparation = ProgressMeter::new(&mut unlimited);
    let plan = prepare_plan(&terms, &conflict, &annotation, &mut preparation)
        .unwrap()
        .unwrap();
    let base = branch_base(&plan, 0, &mut preparation).unwrap();
    let mut polls = 0usize;
    let mut cancelled = false;
    let mut progress = |_: usize, _: usize| {
        polls += 1;
        cancelled |= polls >= 200;
        !cancelled
    };
    // The actual prepared positive branch needs the last of 1024 choices.
    assert!(matches!(
        orientations_hold(
            &base,
            true,
            &plan.equalities,
            &mut ProgressMeter::new(&mut progress)
        ),
        Err(FarkasValidationError::ResourceLimit)
    ));
    assert!(matches!(
        farkas_conflict_lits_linear_holds_with_progress(
            &terms,
            &conflict,
            &annotation,
            &mut progress
        ),
        Err(FarkasValidationError::ResourceLimit)
    ));
    drop(progress);
    assert!(cancelled);
    assert_eq!(polls, 201);
}

#[test]
fn strict_verifier_refuses_space_before_allocating_certificate_scratch() {
    let (terms, conflict, annotation) = independent_equalities(2);
    let mut refused_bytes = 0;
    let result = farkas_conflict_lits_linear_holds_with_progress(
        &terms,
        &conflict,
        &annotation,
        &mut |_, bytes| {
            if bytes > 0 {
                refused_bytes = bytes;
                false
            } else {
                true
            }
        },
    );
    assert_eq!(result, Err(FarkasValidationError::ResourceLimit));
    assert!(refused_bytes > 0);
}

#[test]
fn wrong_counts_and_satisfiable_rows_are_rejected_without_certificate_authority() {
    let (terms, conflict, _) = independent_equalities(2);
    assert!(matches!(
        farkas_conflict_lits_linear_holds_with_progress(
            &terms,
            &conflict,
            &FarkasAnnotation::from_ints(&[1]),
            &mut |_, _| true
        ),
        Err(FarkasValidationError::CoefficientCountMismatch { .. })
    ));
    assert!(!strict(
        &terms,
        &conflict[..2],
        &FarkasAnnotation::from_ints(&[1, 1])
    ));
}
