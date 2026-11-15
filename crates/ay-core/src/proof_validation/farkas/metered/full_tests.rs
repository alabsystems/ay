// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::proof_validation::{
    verify_farkas_conflict_lits_full_holds, verify_farkas_conflict_lits_linear_holds,
};
use crate::{Sort, TermId};

fn full(terms: &TermStore, rows: &[TheoryLit], weights: &[i64]) -> bool {
    farkas_conflict_lits_full_holds_with_progress(
        terms,
        rows,
        &FarkasAnnotation::from_ints(weights),
        &mut |_, _| true,
    )
    .unwrap()
}

fn zero_cause() -> (TermStore, Vec<TheoryLit>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("full_shared_x", Sort::Real);
    let a = terms.mk_var("full_a", Sort::Real);
    let b = terms.mk_var("full_b", Sort::Real);
    let five = terms.mk_int(5.into());
    let ax = terms.mk_app(Symbol::named("="), [a, x], Sort::Bool);
    let a5 = terms.mk_app(Symbol::named("="), [a, five], Sort::Bool);
    let bx = terms.mk_app(Symbol::named("="), [b, x], Sort::Bool);
    let b5 = terms.mk_app(Symbol::named("distinct"), [b, five], Sort::Bool);
    (
        terms,
        vec![
            TheoryLit::new(ax, true),
            TheoryLit::new(a5, true),
            TheoryLit::new(bx, true),
            TheoryLit::new(b5, true),
        ],
    )
}

#[test]
fn full_checks_whole_conflict_congruence_including_zero_weight_causes() {
    let (terms, mut rows) = zero_cause();
    let weights = FarkasAnnotation::from_ints(&[1, 1, 0, 1]);
    assert!(verify_farkas_conflict_lits_full_holds(
        &terms, &rows, &weights
    ));
    assert!(!verify_farkas_conflict_lits_linear_holds(
        &terms, &rows, &weights
    ));
    assert!(full(&terms, &rows, &[1, 1, 0, 1]));
    rows[2].value = false;
    // Satisfiable twin: a=x=5, b=6. A negative equality cannot fund union.
    assert!(!full(&terms, &rows, &[1, 1, 0, 1]));
    rows[2].value = true;
    assert!(
        full(&terms, &rows, &[1, 1, 0, 1]),
        "each call derives its own closure"
    );
    assert!(!full(&terms, &rows, &[0, 0, 0, 0]));
}

fn nested(symbol: Symbol) -> (TermStore, Vec<TheoryLit>, TermId, TermId) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("full_arg_a", Sort::Int);
    let b = terms.mk_var("full_arg_b", Sort::Int);
    let ga = terms.mk_app(Symbol::named("g"), [a], Sort::Int);
    let gb = terms.mk_app(Symbol::named("g"), [b], Sort::Int);
    let fa = terms.mk_app(symbol.clone(), [ga], Sort::Int);
    let fb = terms.mk_app(symbol, [gb], Sort::Int);
    let eq = terms.mk_app(Symbol::named("="), [a, b], Sort::Bool);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let low = terms.mk_app(Symbol::named("<="), [fa, zero], Sort::Bool);
    let high = terms.mk_app(Symbol::named(">="), [fb, one], Sort::Bool);
    (
        terms,
        vec![
            TheoryLit::new(eq, true),
            TheoryLit::new(low, true),
            TheoryLit::new(high, true),
        ],
        fa,
        fb,
    )
}

#[test]
fn nested_application_fixed_point_is_exact_and_uses_no_ambient_equalities() {
    let (terms, rows, _, _) = nested(Symbol::named("f"));
    assert!(
        !full(&terms, &rows[1..], &[1, 1]),
        "an unused arena equality is not a premise"
    );
    assert!(!verify_farkas_conflict_lits_linear_holds(
        &terms,
        &rows,
        &FarkasAnnotation::from_ints(&[0, 1, 1])
    ));
    assert!(full(&terms, &rows, &[0, 1, 1]));
    assert!(
        !full(&terms, &rows, &[0, 1, 2]),
        "actual inequality magnitudes must cancel"
    );
    assert!(!full(&terms, &rows, &[0, 1, -1]));
}

#[test]
fn all_signed_positive_equality_forms_agree_and_opposite_polarities_refuse() {
    let (mut terms, rows, _, _) = nested(Symbol::named("signed_f"));
    let TermData::App(_, args) = terms.get(rows[0].term) else {
        unreachable!()
    };
    let [a, b] = [args[0], args[1]];
    let distinct = terms.mk_app(Symbol::named("distinct"), [a, b], Sort::Bool);
    let not_eq = terms.mk_not_raw(rows[0].term);
    let not_distinct = terms.mk_not_raw(distinct);
    for lit in [
        rows[0],
        TheoryLit::new(not_eq, false),
        TheoryLit::new(distinct, false),
        TheoryLit::new(not_distinct, true),
    ] {
        let mut exact = rows.clone();
        exact[0] = lit;
        assert!(full(&terms, &exact, &[0, 1, 1]));
        exact[0].value = !exact[0].value;
        assert!(!full(&terms, &exact, &[0, 1, 1]));
    }
}

#[test]
fn function_heads_indices_and_arity_do_not_alias() {
    let (mut terms, rows, _, fb) = nested(Symbol::indexed("full_indexed", vec![7, 4]));
    assert!(full(&terms, &rows, &[0, 1, 1]));
    let TermData::App(_, args) = terms.get(fb) else {
        unreachable!()
    };
    let arg = args[0];
    let one = terms.mk_int(1.into());
    for (head, arguments) in [
        (Symbol::indexed("full_indexed", vec![7, 3]), vec![arg]),
        (Symbol::named("full_indexed"), vec![arg]),
        (Symbol::indexed("full_indexed", vec![7, 4]), vec![arg, arg]),
        (Symbol::indexed("different", vec![7, 4]), vec![arg]),
    ] {
        let other = terms.mk_app(head, arguments, Sort::Int);
        let high = terms.mk_app(Symbol::named(">="), [other, one], Sort::Bool);
        let mut twin = rows.clone();
        twin[2] = TheoryLit::new(high, true);
        assert!(!full(&terms, &twin, &[0, 1, 1]));
    }
}

#[test]
fn full_preserves_positions_duplicates_and_denies_count_mismatch() {
    let (terms, rows, _, _) = nested(Symbol::named("position_f"));
    let ordered = [rows[2], rows[0], rows[1], rows[0]];
    assert!(full(&terms, &ordered, &[1, 0, 1, 0]));
    assert!(!full(&terms, &ordered, &[0, 1, 1, 0]));
    assert!(matches!(
        farkas_conflict_lits_full_holds_with_progress(
            &terms,
            &ordered,
            &FarkasAnnotation::from_ints(&[1, 0, 1]),
            &mut |_, _| true
        ),
        Err(FarkasValidationError::CoefficientCountMismatch { .. })
    ));
}

#[test]
fn full_keeps_actual_magnitudes_and_the_strict_orientation_boundary() {
    for n in [10usize, 11] {
        let mut terms = TermStore::new();
        let zero = terms.mk_int(0.into());
        let mut variables = Vec::new();
        let mut rows = Vec::new();
        for index in 0..n {
            let variable = terms.mk_var(format!("full_orientation_{index}"), Sort::Int);
            variables.push(variable);
            let eq = terms.mk_app(Symbol::named("="), [variable, zero], Sort::Bool);
            rows.push(TheoryLit::new(eq, true));
        }
        let sum = terms.mk_app(Symbol::named("+"), variables, Sort::Int);
        let neq = terms.mk_app(Symbol::named("distinct"), [sum, zero], Sort::Bool);
        rows.push(TheoryLit::new(neq, true));
        let mut weights = vec![1; n + 1];
        assert_eq!(full(&terms, &rows, &weights), n == 10);
        if n == 11 {
            weights[0] = 2;
            // Legacy FULL's broader equality-span completion accepts the
            // support. This API must still check the exact scaled rows.
            assert!(verify_farkas_conflict_lits_full_holds(
                &terms,
                &rows,
                &FarkasAnnotation::from_ints(&weights)
            ));
            assert!(!full(&terms, &rows, &weights));
        }
    }
}

#[test]
fn congruence_can_be_cancelled_inside_discovery_and_owner_stays_cancelled() {
    let (terms, rows, _, _) = nested(Symbol::named("cancel_f"));
    let mut visits = 0usize;
    let mut cancelled = false;
    let mut progress = |_: usize, _: usize| {
        visits += 1;
        cancelled |= visits >= 30;
        !cancelled
    };
    assert!(matches!(
        Congruence::build(&terms, &rows, &mut ProgressMeter::new(&mut progress)),
        Err(FarkasValidationError::ResourceLimit)
    ));
    assert!(matches!(
        farkas_conflict_lits_full_holds_with_progress(
            &terms,
            &rows,
            &FarkasAnnotation::from_ints(&[0, 1, 1]),
            &mut progress
        ),
        Err(FarkasValidationError::ResourceLimit)
    ));
    drop(progress);
    assert!(cancelled);
    assert_eq!(
        visits, 31,
        "a repeated call observes the same cancelled owner immediately"
    );
}

#[test]
fn signature_payload_comparison_is_charged_before_bytes_are_compared() {
    let (terms, rows, _, _) = nested(Symbol::named("s".repeat(8192)));
    let mut refused_payload = false;
    let result = farkas_conflict_lits_full_holds_with_progress(
        &terms,
        &rows,
        &FarkasAnnotation::from_ints(&[0, 1, 1]),
        &mut |work, _| {
            if work >= 8192 {
                refused_payload = true;
                false
            } else {
                true
            }
        },
    );
    assert!(matches!(result, Err(FarkasValidationError::ResourceLimit)));
    assert!(
        refused_payload,
        "the real borrowed symbol comparison must be metered"
    );
}

#[test]
fn shared_dag_parsing_and_scratch_refuse_without_a_fresh_allowance() {
    let (mut terms, mut rows, _, _) = nested(Symbol::named("dag_f"));
    let mut expression = terms.mk_var("full_shared_dag", Sort::Int);
    for _ in 0..28 {
        expression = terms.mk_app(Symbol::named("+"), [expression, expression], Sort::Int);
    }
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let low = terms.mk_app(Symbol::named("<="), [expression, zero], Sort::Bool);
    let high = terms.mk_app(Symbol::named(">="), [expression, one], Sort::Bool);
    rows[1] = TheoryLit::new(low, true);
    rows[2] = TheoryLit::new(high, true);
    let mut discovery_work = 0usize;
    Congruence::build(
        &terms,
        &rows,
        &mut ProgressMeter::new(&mut |work, _| {
            discovery_work += work;
            true
        }),
    )
    .unwrap();
    let mut remaining = discovery_work + 256;
    let mut spent = false;
    let mut consumed = 0usize;
    let mut meter = |work: usize, _: usize| {
        if spent {
            return false;
        }
        match remaining.checked_sub(work) {
            Some(next) => {
                remaining = next;
                consumed += work;
                true
            }
            None => {
                spent = true;
                false
            }
        }
    };
    for _ in 0..2 {
        assert!(matches!(
            farkas_conflict_lits_full_holds_with_progress(
                &terms,
                &rows,
                &FarkasAnnotation::from_ints(&[0, 1, 1]),
                &mut meter
            ),
            Err(FarkasValidationError::ResourceLimit)
        ));
    }
    drop(meter);
    assert!(spent);
    assert!(
        consumed > discovery_work,
        "the real parser was reached after paid DAG discovery"
    );
    let mut space_denied = false;
    assert!(matches!(
        farkas_conflict_lits_full_holds_with_progress(
            &terms,
            &rows,
            &FarkasAnnotation::from_ints(&[0, 1, 1]),
            &mut |_, bytes| {
                space_denied |= bytes != 0;
                bytes == 0
            }
        ),
        Err(FarkasValidationError::ResourceLimit)
    ));
    assert!(space_denied);
}

#[test]
fn application_admission_keeps_the_existing_full_boundary() {
    for (extra, admitted) in [(4087, true), (4088, false)] {
        let (mut terms, rows, fa, fb) = nested(Symbol::named("bound_f"));
        let mut arguments = Vec::new();
        for index in 0..extra {
            arguments.push(terms.mk_app(Symbol::named(format!("bound_{index}")), [fa], Sort::Int));
        }
        let wide = terms.mk_app(Symbol::named("wide"), arguments, Sort::Int);
        let carrier = terms.mk_app(Symbol::named("="), [wide, wide], Sort::Bool);
        let mut conflict = rows.clone();
        conflict.push(TheoryLit::new(carrier, true));
        // Seven raw applications in nested(), plus wide/carrier and the
        // explicitly distinct filler heads: exactly 4096 and 4097 apps.
        let closure =
            Congruence::build(&terms, &conflict, &mut ProgressMeter::new(&mut |_, _| true))
                .unwrap();
        let a = closure
            .representative(fa, &mut ProgressMeter::new(&mut |_, _| true))
            .unwrap();
        let b = closure
            .representative(fb, &mut ProgressMeter::new(&mut |_, _| true))
            .unwrap();
        assert_eq!(
            a == b,
            admitted,
            "the existing 4096 application admission must remain exact"
        );
    }
}
