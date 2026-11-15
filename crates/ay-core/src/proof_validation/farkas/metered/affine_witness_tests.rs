// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::proof_validation::{
    farkas_conflict_lits_full_holds_with_progress, farkas_conflict_lits_linear_holds_with_progress,
};

fn fixture(scale: i64, target: i64) -> (TermStore, Vec<TheoryLit>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("derived_x", Sort::Real);
    let y = terms.mk_var("derived_y", Sort::Real);
    let z = terms.mk_var("derived_z", Sort::Real);
    let c = terms.mk_int(scale.into());
    let three = terms.mk_int(3.into());
    let goal = terms.mk_int(target.into());
    let cy = terms.mk_app(Symbol::named("*"), [c, y], Sort::Real);
    let cz = terms.mk_app(Symbol::named("*"), [three, z], Sort::Real);
    let gz = terms.mk_app(Symbol::named("*"), [goal, z], Sort::Real);
    let eq0 = terms.mk_app(Symbol::named("="), [x, cy], Sort::Bool);
    let eq1 = terms.mk_app(Symbol::named("="), [y, cz], Sort::Bool);
    let diseq = terms.mk_app(Symbol::named("distinct"), [x, gz], Sort::Bool);
    (
        terms,
        vec![
            TheoryLit::new(eq0, true),
            TheoryLit::new(eq1, true),
            TheoryLit::new(diseq, true),
        ],
    )
}

fn derive(terms: &TermStore, conflict: &[TheoryLit]) -> Option<FarkasAnnotation> {
    derive_affine_equality_farkas_with_progress(terms, conflict, &mut |_, _| true).unwrap()
}

#[test]
fn constructs_actual_nonunit_multipliers_then_replays_both_cases() {
    let (terms, conflict) = fixture(2, 6);
    let unit = FarkasAnnotation::from_ints(&[1, 1, 1]);
    assert!(!farkas_conflict_lits_linear_holds_with_progress(
        &terms,
        &conflict,
        &unit,
        &mut |_, _| true
    )
    .unwrap());
    let witness = construct(&terms, &conflict, &mut ProgressMeter::new(&mut |_, _| true))
        .unwrap()
        .unwrap();
    assert_eq!(
        witness.annotation.coefficients,
        FarkasAnnotation::from_ints(&[1, 2, 1]).coefficients
    );
    assert_eq!(witness.branches.len(), 2);
    assert_eq!(
        witness.branches[0].coefficients,
        FarkasAnnotation::from_ints(&[-1, -2, 1]).coefficients
    );
    assert_eq!(
        witness.branches[1].coefficients,
        FarkasAnnotation::from_ints(&[1, 2, 1]).coefficients
    );
    assert!(replay(&witness, &mut ProgressMeter::new(&mut |_, _| true)).unwrap());
    let actual = derive(&terms, &conflict).unwrap();
    assert_eq!(actual.coefficients, witness.annotation.coefficients);
    assert!(farkas_conflict_lits_linear_holds_with_progress(
        &terms,
        &conflict,
        &actual,
        &mut |_, _| true
    )
    .unwrap());
}

#[test]
fn explicit_large_witness_does_not_relax_the_old_strict_search_boundary() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let mut rows = Vec::new();
    let mut summands = Vec::new();
    for index in 1..=11 {
        let variable = terms.mk_var(format!("derived_large_{index}"), Sort::Int);
        let weight = terms.mk_int(index.into());
        summands.push(terms.mk_app(Symbol::named("*"), [weight, variable], Sort::Int));
        let eq = terms.mk_app(Symbol::named("="), [variable, zero], Sort::Bool);
        rows.push(TheoryLit::new(eq, true));
    }
    let sum = terms.mk_app(Symbol::named("+"), summands, Sort::Int);
    let diseq = terms.mk_app(Symbol::named("distinct"), [sum, zero], Sort::Bool);
    rows.push(TheoryLit::new(diseq, true));
    let expected = FarkasAnnotation::from_ints(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1]);
    assert_eq!(
        derive(&terms, &rows).unwrap().coefficients,
        expected.coefficients
    );
    assert!(!farkas_conflict_lits_linear_holds_with_progress(
        &terms,
        &rows,
        &expected,
        &mut |_, _| true
    )
    .unwrap());
    assert!(!farkas_conflict_lits_full_holds_with_progress(
        &terms,
        &rows,
        &expected,
        &mut |_, _| true
    )
    .unwrap());
    // The new path supplies and directly replays BOTH sign vectors. It does
    // not ask the old capped search to treat a failed search as acceptance.
    let witness = construct(&terms, &rows, &mut ProgressMeter::new(&mut |_, _| true))
        .unwrap()
        .unwrap();
    assert!(replay(&witness, &mut ProgressMeter::new(&mut |_, _| true)).unwrap());
}

#[test]
fn rational_and_signed_coefficients_are_exact_not_rounded_or_absolutized() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("derived_half_x", Sort::Real);
    let y = terms.mk_var("derived_half_y", Sort::Real);
    let two = terms.mk_int(2.into());
    let tx = terms.mk_app(Symbol::named("*"), [two, x], Sort::Real);
    let half_y = terms.mk_app(Symbol::named("/"), [y, two], Sort::Real);
    let equality = terms.mk_app(Symbol::named("="), [y, tx], Sort::Bool);
    let disequality = terms.mk_app(Symbol::named("distinct"), [x, half_y], Sort::Bool);
    let rows = [
        TheoryLit::new(equality, true),
        TheoryLit::new(disequality, true),
    ];
    assert_eq!(
        derive(&terms, &rows).unwrap().coefficients,
        vec![Rational64::new(-1, 2), Rational64::one()]
    );
    let distinct = terms.mk_app(Symbol::named("distinct"), [y, tx], Sort::Bool);
    let not_equality = terms.mk_not_raw(equality);
    let not_distinct = terms.mk_not_raw(distinct);
    let goal_eq = terms.mk_app(Symbol::named("="), [x, half_y], Sort::Bool);
    let not_goal = terms.mk_not_raw(goal_eq);
    for equality in [
        rows[0],
        TheoryLit::new(not_equality, false),
        TheoryLit::new(distinct, false),
        TheoryLit::new(not_distinct, true),
    ] {
        let exact = [equality, TheoryLit::new(not_goal, true)];
        assert_eq!(
            derive(&terms, &exact).unwrap().coefficients,
            vec![Rational64::new(-1, 2), Rational64::one()]
        );
        assert!(derive(
            &terms,
            &[TheoryLit::new(equality.term, !equality.value), exact[1]]
        )
        .is_none());
    }
}

#[test]
fn equality_only_contradiction_has_a_replayed_positive_constant() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("derived_clash_x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let x0 = terms.mk_app(Symbol::named("="), [x, zero], Sort::Bool);
    let x1 = terms.mk_app(Symbol::named("="), [x, one], Sort::Bool);
    let rows = [TheoryLit::new(x0, true), TheoryLit::new(x1, true)];
    let annotation = derive(&terms, &rows).unwrap();
    assert_eq!(
        annotation.coefficients,
        FarkasAnnotation::from_ints(&[1, -1]).coefficients
    );
    assert!(farkas_conflict_lits_linear_holds_with_progress(
        &terms,
        &rows,
        &annotation,
        &mut |_, _| true
    )
    .unwrap());
    assert!(derive(&terms, &[rows[0], rows[0]]).is_none());
}

#[test]
fn satisfiable_and_one_sided_twins_cannot_acquire_a_witness() {
    let (mut terms, rows) = fixture(2, 7);
    // x=6,y=3,z=1 is a model of these equalities and x!=7z.
    assert!(derive(&terms, &rows).is_none());
    let x = terms.mk_var("one_sided_x", Sort::Real);
    let zero = terms.mk_int(0.into());
    let le = terms.mk_app(Symbol::named("<="), [x, zero], Sort::Bool);
    let neq = terms.mk_app(Symbol::named("distinct"), [x, zero], Sort::Bool);
    assert!(derive(
        &terms,
        &[TheoryLit::new(le, true), TheoryLit::new(neq, true)]
    )
    .is_none());
    let (terms, rows) = fixture(2, 6);
    assert!(
        derive(&terms, &rows[1..]).is_none(),
        "an unused arena equality is not a premise"
    );
}

#[test]
fn duplicate_positions_and_zero_context_causes_are_kept_in_the_output() {
    let (mut terms, rows) = fixture(2, 6);
    let context = terms.mk_var("derived_context", Sort::Bool);
    let conflict = [
        rows[1],
        rows[2],
        rows[0],
        TheoryLit::new(context, true),
        rows[0],
    ];
    let annotation = derive(&terms, &conflict).unwrap();
    assert_eq!(
        annotation.coefficients,
        FarkasAnnotation::from_ints(&[2, 1, 1, 0, 0]).coefficients
    );
    assert_eq!(annotation.coefficients.len(), conflict.len());
}

#[test]
fn independent_replay_rejects_wrong_magnitudes_even_with_consistent_branch_links() {
    let (terms, conflict) = fixture(2, 6);
    let mut witness = construct(&terms, &conflict, &mut ProgressMeter::new(&mut |_, _| true))
        .unwrap()
        .unwrap();
    witness.annotation.coefficients[1] = Rational64::one();
    witness.branches[0].coefficients[1] = -Rational64::one();
    witness.branches[1].coefficients[1] = Rational64::one();
    assert!(!replay(&witness, &mut ProgressMeter::new(&mut |_, _| true)).unwrap());
    let mut ordered = construct(&terms, &conflict, &mut ProgressMeter::new(&mut |_, _| true))
        .unwrap()
        .unwrap();
    let reordered = [conflict[1], conflict[0], conflict[2]];
    ordered.conflict = &reordered;
    assert!(!replay(&ordered, &mut ProgressMeter::new(&mut |_, _| true)).unwrap());
    ordered.conflict = &reordered[..2];
    assert!(!replay(&ordered, &mut ProgressMeter::new(&mut |_, _| true)).unwrap());
}

#[test]
fn branch_erasure_zero_target_and_wrong_source_position_fail_closed() {
    let (terms, conflict) = fixture(2, 6);
    for corruption in 0..4 {
        let mut witness = construct(&terms, &conflict, &mut ProgressMeter::new(&mut |_, _| true))
            .unwrap()
            .unwrap();
        match corruption {
            0 => {
                witness.branches.pop();
            }
            1 => {
                witness.annotation.coefficients[2] = Rational64::zero();
                for branch in &mut witness.branches {
                    branch.coefficients[2] = Rational64::zero();
                }
            }
            2 => {
                witness.branches[1].coefficients[0] = Rational64::from_integer(2);
            }
            _ => {
                witness.branches[0].kind = Branch::DisequalityLess { source_position: 0 };
                witness.branches[1].kind = Branch::DisequalityGreater { source_position: 0 };
            }
        }
        assert!(!replay(&witness, &mut ProgressMeter::new(&mut |_, _| true)).unwrap());
    }
}

#[test]
fn equal_numeric_ids_and_names_do_not_replace_actual_owner_term_meanings() {
    let (terms, conflict) = fixture(2, 6);
    let (other, other_conflict) = fixture(4, 6);
    assert_eq!(
        conflict, other_conflict,
        "the hostile store has identical numeric IDs"
    );
    let mut witness = construct(&terms, &conflict, &mut ProgressMeter::new(&mut |_, _| true))
        .unwrap()
        .unwrap();
    // Private cfg-only corruption: production callers cannot replace either
    // borrowed owner field. Reparse still rejects the foreign arithmetic.
    witness.terms = &other;
    assert!(!replay(&witness, &mut ProgressMeter::new(&mut |_, _| true)).unwrap());
}

#[test]
fn unrepresentable_multiplier_is_refused_without_truncation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("overflow_x", Sort::Int);
    let y = terms.mk_var("overflow_y", Sort::Int);
    let zero = terms.mk_int(0.into());
    let huge = terms.mk_int(num_bigint::BigInt::one() << 80usize);
    let hy = terms.mk_app(Symbol::named("*"), [huge, y], Sort::Int);
    let e0 = terms.mk_app(Symbol::named("="), [x, hy], Sort::Bool);
    let e1 = terms.mk_app(Symbol::named("="), [y, zero], Sort::Bool);
    let d = terms.mk_app(Symbol::named("distinct"), [x, zero], Sort::Bool);
    assert!(derive(
        &terms,
        &[
            TheoryLit::new(e0, true),
            TheoryLit::new(e1, true),
            TheoryLit::new(d, true)
        ]
    )
    .is_none());
}

#[test]
fn elimination_and_independent_replay_observe_the_same_cancelled_owner() {
    let (terms, conflict) = fixture(2, 6);
    let mut unlimited = |_, _| true;
    let mut setup = ProgressMeter::new(&mut unlimited);
    let pivot = Pivot {
        variable: row(&terms, &conflict[0], &mut setup)
            .unwrap()
            .unwrap()
            .1
            .leading_variable(&mut setup)
            .unwrap()
            .unwrap(),
        row: TrackedRow {
            expression: row(&terms, &conflict[0], &mut setup).unwrap().unwrap().1,
            combination: combination(conflict.len(), Some(0), &mut setup).unwrap(),
        },
    };
    let mut target = TrackedRow {
        expression: row(&terms, &conflict[2], &mut setup).unwrap().unwrap().1,
        combination: combination(conflict.len(), None, &mut setup).unwrap(),
    };
    let mut polls = 0;
    let mut cancelled = false;
    let mut progress = |_: usize, _: usize| {
        polls += 1;
        cancelled |= polls >= 8;
        !cancelled
    };
    assert!(matches!(
        eliminate(&mut target, &pivot, &mut ProgressMeter::new(&mut progress)),
        Err(FarkasValidationError::ResourceLimit)
    ));
    assert!(matches!(
        derive_affine_equality_farkas_with_progress(&terms, &conflict, &mut progress),
        Err(FarkasValidationError::ResourceLimit)
    ));
    drop(progress);
    assert!(cancelled);
    assert_eq!(polls, 9);
    let witness = construct(&terms, &conflict, &mut setup).unwrap().unwrap();
    let mut replay_polls = 0;
    let mut denied = false;
    let mut progress = |_: usize, _: usize| {
        replay_polls += 1;
        denied |= replay_polls >= 12;
        !denied
    };
    assert!(matches!(
        replay(&witness, &mut ProgressMeter::new(&mut progress)),
        Err(FarkasValidationError::ResourceLimit)
    ));
    assert!(matches!(
        derive_affine_equality_farkas_with_progress(&terms, &conflict, &mut progress),
        Err(FarkasValidationError::ResourceLimit)
    ));
    drop(progress);
    assert!(denied);
    assert_eq!(replay_polls, 13);
}

#[test]
fn shared_dag_and_space_exhaustion_do_not_open_another_grant() {
    let mut terms = TermStore::new();
    let mut expression = terms.mk_var("constructive_dag", Sort::Int);
    for _ in 0..30 {
        expression = terms.mk_app(Symbol::named("+"), [expression, expression], Sort::Int);
    }
    let zero = terms.mk_int(0.into());
    let eq = terms.mk_app(Symbol::named("="), [expression, zero], Sort::Bool);
    let neq = terms.mk_app(Symbol::named("distinct"), [expression, zero], Sort::Bool);
    let rows = [TheoryLit::new(eq, true), TheoryLit::new(neq, true)];
    let mut remaining = 256usize;
    let mut spent = false;
    let mut visits = 0;
    let mut progress = |work: usize, _: usize| {
        if spent {
            return false;
        }
        visits += usize::from(work > 0);
        match remaining.checked_sub(work) {
            Some(next) => {
                remaining = next;
                true
            }
            None => {
                spent = true;
                false
            }
        }
    };
    assert!(matches!(
        row(&terms, &rows[0], &mut ProgressMeter::new(&mut progress)),
        Err(FarkasValidationError::ResourceLimit)
    ));
    assert!(matches!(
        derive_affine_equality_farkas_with_progress(&terms, &rows, &mut progress),
        Err(FarkasValidationError::ResourceLimit)
    ));
    drop(progress);
    assert!(spent);
    assert!(visits > 30);
    let mut refused_bytes = false;
    assert!(matches!(
        derive_affine_equality_farkas_with_progress(&terms, &rows, &mut |_, bytes| {
            refused_bytes |= bytes > 0;
            bytes == 0
        }),
        Err(FarkasValidationError::ResourceLimit)
    ));
    assert!(refused_bytes);
}
