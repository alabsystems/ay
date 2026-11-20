// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive};
use std::collections::BTreeSet;

fn bounded(solver: &mut Solver, name: &str, lo: i64, hi: i64) -> Term {
    let value = solver.try_declare_const(name, Sort::Int).unwrap();
    let lower = solver.int_const(lo);
    let upper = solver.int_const(hi);
    let lower = solver.try_ge(value, lower).unwrap();
    let upper = solver.try_le(value, upper).unwrap();
    solver.try_assert_term(lower).unwrap();
    solver.try_assert_term(upper).unwrap();
    value
}

fn solver() -> Solver {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    solver.set_timeout(Some(std::time::Duration::from_secs(60)));
    solver
}

fn exhaustive(report: &FiniteEnumerationReport) {
    assert_eq!(
        report.outcome(),
        Outcome::Exhaustive,
        "{:?}",
        report.diagnostic()
    );
    assert_eq!(report.statistics().final_source_solve_calls, 1);
    assert!(report
        .completeness_proof()
        .unwrap()
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .is_ok());
}

fn integer(value: &Scalar) -> i64 {
    match value {
        Scalar::Int(value) => value.to_i64().unwrap(),
        other => panic!("expected Int, got {other:?}"),
    }
}

#[test]
fn finite_mixed_bool_int_rows_match_original_mathematical_family() {
    let mut solver = solver();
    let p = solver.try_declare_const("p", Sort::Bool).unwrap();
    let x = bounded(&mut solver, "x", -2, 2);
    let one = solver.int_const(1);
    let minus_one = solver.int_const(-1);
    let choice = solver.try_ite(p, one, minus_one).unwrap();
    let sum = solver.try_add(x, choice).unwrap();
    let zero = solver.int_const(0);
    let root = solver.try_ge(sum, zero).unwrap();
    solver.try_assert_term(root).unwrap();
    let report = solver.try_enumerate_finite(&[p, x], 100).unwrap();
    exhaustive(&report);
    assert!(report.is_current_for(&solver));
    let actual: BTreeSet<_> = report
        .rows()
        .iter()
        .map(|row| {
            let Scalar::Bool(p) = &row.values()[0] else {
                panic!("Bool projection")
            };
            (*p, integer(&row.values()[1]))
        })
        .collect();
    let expected: BTreeSet<_> = [false, true]
        .into_iter()
        .flat_map(|p| {
            (-2..=2)
                .filter(move |&x| x + if p { 1 } else { -1 } >= 0)
                .map(move |x| (p, x))
        })
        .collect();
    assert_eq!(report.rows().len(), 6);
    assert_eq!(actual, expected);
    #[cfg(any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    if let Some(reference) = crate::api::solving::tactic_model::bounded_reference(
        &format!(
            "{}\n(check-sat)\n",
            report
                .completeness_proof()
                .unwrap()
                .alethe_problem_smt2
                .as_deref()
                .unwrap()
        ),
        "native-finite-projection-mixed-source-completeness",
    ) {
        assert!(!reference.is_empty());
        assert!(
            reference.split_whitespace().all(|value| value == "unsat"),
            "{reference}"
        );
    }
}

#[test]
fn finite_integer_expression_projection_deduplicates_extensions() {
    let mut solver = solver();
    let x = bounded(&mut solver, "x", 0, 2);
    let y = bounded(&mut solver, "y", 0, 2);
    let sum = solver.try_add(x, y).unwrap();
    let report = solver.try_enumerate_finite(&[sum], 100).unwrap();
    exhaustive(&report);
    let actual: BTreeSet<_> = report
        .rows()
        .iter()
        .map(|row| integer(&row.values()[0]))
        .collect();
    assert_eq!(report.rows().len(), 5);
    assert_eq!(actual, (0..=4).collect());
    let empty = solver.try_enumerate_finite(&[], 1).unwrap();
    exhaustive(&empty);
    assert_eq!(empty.rows().len(), 1);
    assert!(empty.rows()[0].values().is_empty());
}

#[test]
fn finite_choices_and_equalities_supply_source_derived_domains() {
    let mut solver = solver();
    let x = solver.try_declare_const("x", Sort::Int).unwrap();
    let y = solver.try_declare_const("y", Sort::Int).unwrap();
    let mut choices = Vec::new();
    for n in [-7, 0, 9] {
        let value = solver.int_const(n);
        choices.push(solver.try_eq(x, value).unwrap());
    }
    let membership = solver.try_or_many(&choices).unwrap();
    solver.try_assert_term(membership).unwrap();
    let one = solver.int_const(1);
    let successor = solver.try_add(x, one).unwrap();
    let equal = solver.try_eq(y, successor).unwrap();
    solver.try_assert_term(equal).unwrap();
    let report = solver.try_enumerate_finite(&[x, y], 10).unwrap();
    exhaustive(&report);
    let actual: BTreeSet<_> = report
        .rows()
        .iter()
        .map(|row| (integer(&row.values()[0]), integer(&row.values()[1])))
        .collect();
    assert_eq!(actual, BTreeSet::from([(-7, -6), (0, 1), (9, 10)]));
    assert_eq!(report.rows().len(), 3);
}

#[test]
fn finite_signed_values_beyond_128_bits_decode_without_narrowing() {
    let mut solver = solver();
    let x = solver.try_declare_const("wide", Sort::Int).unwrap();
    let lo = -(BigInt::one() << 140usize);
    let hi = &lo + BigInt::one();
    let lower = solver.int_const_bigint(&lo);
    let upper = solver.int_const_bigint(&hi);
    let lower = solver.try_ge(x, lower).unwrap();
    let upper = solver.try_le(x, upper).unwrap();
    solver.try_assert_term(lower).unwrap();
    solver.try_assert_term(upper).unwrap();
    let report = solver.try_enumerate_finite(&[x], 10).unwrap();
    exhaustive(&report);
    let actual: BTreeSet<_> = report
        .rows()
        .iter()
        .map(|row| {
            let Scalar::Int(value) = &row.values()[0] else {
                panic!("Int projection")
            };
            value.clone()
        })
        .collect();
    assert_eq!(actual, BTreeSet::from([lo, hi]));
    assert_eq!(report.rows().len(), 2);
    assert!(report.statistics().signed_integer_width >= 142);
}

#[test]
fn finite_caps_prior_model_and_source_binding_remain_distinct() {
    let mut solver = solver();
    let x = bounded(&mut solver, "x", -2, 2);
    assert!(solver.try_check_sat().unwrap().is_sat());
    let result = format!("{:?}", solver.executor.last_result());
    let model = solver.try_get_model().unwrap();
    let assertions = solver.assertions();
    let capped = solver.try_enumerate_finite(&[x], 2).unwrap();
    assert_eq!(capped.outcome(), Outcome::Capped);
    assert_eq!(capped.rows().len(), 2);
    assert!(capped.completeness_proof().is_none());
    assert_eq!(capped.statistics().final_source_solve_calls, 0);
    let report = solver.try_enumerate_finite(&[x], 5).unwrap();
    exhaustive(&report);
    assert_eq!(report.rows().len(), 5);
    assert_eq!(result, format!("{:?}", solver.executor.last_result()));
    assert_eq!(model, solver.try_get_model().unwrap());
    assert_eq!(assertions, solver.assertions());
    assert!(report.is_current_for(&solver));
    solver.try_declare_const("later", Sort::Bool).unwrap();
    assert!(!report.is_current_for(&solver));
}

#[test]
fn finite_unbounded_unsupported_and_foreign_inputs_are_refused() {
    let mut solver = solver();
    let x = solver.try_declare_const("unbounded", Sort::Int).unwrap();
    let before = solver.terms().snapshot_stamp();
    assert!(matches!(
        solver.try_enumerate_finite(&[x], 10),
        Err(SolverError::InvalidArgument { .. })
    ));
    assert_eq!(before, solver.terms().snapshot_stamp());
    let mut other = super::finite_tests::solver();
    let foreign = bounded(&mut other, "x", 0, 1);
    assert!(matches!(
        solver.try_enumerate_finite(&[foreign], 1),
        Err(SolverError::InvalidTermHandle { .. })
    ));
    assert!(solver.try_enumerate_finite(&[x, x], 1).is_err());
}

#[test]
fn finite_original_source_refutes_an_omitted_integer_projection_blocker() {
    let mut solver = solver();
    let x = bounded(&mut solver, "x", 0, 2);
    let roots = solver.executor.ctx.assertions.clone();
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 1 << 30),
        None,
        Arc::new(|| false),
    )
    .unwrap();
    let compiled = finite_bool::compile_finite(solver.terms(), &roots, &[x.id()], &owner).unwrap();
    let mut source = source::copy(solver.terms(), &roots, &compiled, &owner).unwrap();
    source
        .block(&[x.id()], &[Scalar::Int(0.into())], &owner)
        .unwrap();
    source
        .block(&[x.id()], &[Scalar::Int(1.into())], &owner)
        .unwrap();
    let mut report = solver
        .enumeration_common(&[x], ProjectionKind::Finite, &owner)
        .unwrap();
    source.finish(&owner, &mut report).unwrap();
    assert_eq!(
        report.outcome,
        Outcome::Incomplete(UnknownReason::SelfCheckRejected)
    );
    assert!(report.completeness_proof.is_none());
    assert!(report
        .diagnostic
        .as_deref()
        .unwrap()
        .contains("remains satisfiable"));
}

#[test]
fn finite_inherited_budget_and_cancellation_publish_no_completeness() {
    let mut solver = solver();
    let x = bounded(&mut solver, "x", 0, 10);
    solver.interrupt();
    match solver.try_enumerate_finite(&[x], 20) {
        Err(SolverError::FiniteEnumerationStopped(reason)) => {
            assert_eq!(reason, UnknownReason::Interrupted)
        }
        Ok(report) => {
            assert_eq!(
                report.outcome(),
                Outcome::Incomplete(UnknownReason::Interrupted)
            );
            assert!(report.completeness_proof().is_none());
        }
        other => panic!("unexpected cancellation: {other:?}"),
    }
    let run = Guard::root_child(ChildSpec::new(NodeLabel::Run).with_rlimit(Some(1_000_000)));
    {
        let _scope = run.enter();
        assert!(matches!(
            solver.try_enumerate_finite(&[x], 20),
            Err(SolverError::InvalidArgument { .. })
        ));
    }
    let mut fresh = super::finite_tests::solver();
    let x = bounded(&mut fresh, "bounded_budget", 0, 10);
    let check = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(500)));
    let _scope = check.enter();
    match fresh.try_enumerate_finite(&[x], 20) {
        Err(SolverError::FiniteEnumerationStopped(reason)) => {
            assert_eq!(reason, UnknownReason::ResourceLimit)
        }
        Ok(report) => {
            assert_eq!(
                report.outcome(),
                Outcome::Incomplete(UnknownReason::ResourceLimit)
            );
            assert!(report.completeness_proof().is_none());
        }
        other => panic!("unexpected original budget result: {other:?}"),
    }
    assert!(check.remaining().unwrap() < 500);
}

#[test]
fn finite_reversed_strict_and_negative_bounds_preserve_exact_integer_sets() {
    for mode in 0..4 {
        let mut solver = solver();
        let x = solver.try_declare_const("bound_forms", Sort::Int).unwrap();
        let lo = solver.int_const(-2);
        let hi = solver.int_const(2);
        let (lower, upper) = match mode {
            0 => (solver.try_le(lo, x).unwrap(), solver.try_ge(hi, x).unwrap()),
            1 => {
                let below = solver.int_const(-3);
                let above = solver.int_const(3);
                (
                    solver.try_lt(below, x).unwrap(),
                    solver.try_gt(above, x).unwrap(),
                )
            }
            2 => {
                let below = solver.try_lt(x, lo).unwrap();
                let above = solver.try_gt(x, hi).unwrap();
                (
                    solver.try_not(below).unwrap(),
                    solver.try_not(above).unwrap(),
                )
            }
            _ => {
                let below = solver.try_gt(lo, x).unwrap();
                let above = solver.try_lt(hi, x).unwrap();
                (
                    solver.try_not(below).unwrap(),
                    solver.try_not(above).unwrap(),
                )
            }
        };
        solver.try_assert_term(lower).unwrap();
        solver.try_assert_term(upper).unwrap();
        let report = solver.try_enumerate_finite(&[x], 10).unwrap();
        exhaustive(&report);
        let actual: BTreeSet<_> = report
            .rows()
            .iter()
            .map(|row| integer(&row.values()[0]))
            .collect();
        assert_eq!(actual, (-2..=2).collect(), "mode={mode}");
        assert_eq!(report.rows().len(), 5);
    }
}

#[test]
fn finite_projection_and_leaf_type_corruption_cannot_publish_a_row() {
    let mut solver = solver();
    let x = bounded(&mut solver, "checked_integer", 0, 1);
    let one = solver.int_const(1);
    let next = solver.try_add(x, one).unwrap();
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 1 << 30),
        None,
        Arc::new(|| false),
    )
    .unwrap();
    let wrong_projection = candidate::CandidateMap {
        projection: vec![candidate::Encoding::Int(vec![1, 2])],
        leaves: vec![(x.id(), candidate::Encoding::Int(vec![1, 2]))],
    };
    assert!(matches!(
        wrong_projection.validate(
            &solver,
            &solver.executor.ctx.assertions,
            &[next],
            &[false, false],
            &owner
        ),
        Err(Failure::Incomplete(UnknownReason::SelfCheckRejected))
    ));
    let wrong_leaf_type = candidate::CandidateMap {
        projection: vec![candidate::Encoding::Int(vec![1, 2])],
        leaves: vec![(x.id(), candidate::Encoding::Bool(1))],
    };
    assert!(matches!(
        wrong_leaf_type.validate(
            &solver,
            &solver.executor.ctx.assertions,
            &[x],
            &[false, false],
            &owner
        ),
        Err(Failure::Incomplete(UnknownReason::SelfCheckRejected))
    ));
}

#[test]
fn finite_constant_and_inconsistent_domains_keep_source_authority() {
    let mut solver = solver();
    let seven = solver.int_const(7);
    let report = solver.try_enumerate_finite(&[seven], 1).unwrap();
    exhaustive(&report);
    assert_eq!(report.rows().len(), 1);
    assert_eq!(report.rows()[0].values(), &[Scalar::Int(7.into())]);
    let x = bounded(&mut solver, "empty_interval", 1, 0);
    let empty = solver.try_enumerate_finite(&[x], 0).unwrap();
    exhaustive(&empty);
    assert!(empty.rows().is_empty());
}

#[test]
fn finite_lowered_char_and_finite_domain_carriers_are_not_plain_ints() {
    for sort in [Sort::Char, Sort::FiniteDomain("SmallDomain".to_string(), 2)] {
        let mut solver = solver();
        let x = solver.try_declare_const("nonprimitive", sort).unwrap();
        let zero = solver.int_const(0);
        let one = solver.int_const(1);
        let lower = solver.terms_mut().mk_ge(x.id(), zero.id());
        let upper = solver.terms_mut().mk_le(x.id(), one.id());
        let lower = solver.wrap_term(lower);
        let upper = solver.wrap_term(upper);
        solver.try_assert_term(lower).unwrap();
        solver.try_assert_term(upper).unwrap();
        let original = solver.terms().snapshot_stamp();
        assert!(
            matches!(solver.try_enumerate_finite(&[x], 3), Err(SolverError::InvalidArgument { message, .. }) if message.contains("carrier"))
        );
        assert_eq!(original, solver.terms().snapshot_stamp());
    }
}

#[test]
fn finite_euclidean_div_mod_match_all_signed_pairs_with_fixed_divisors() {
    let divisors = [-3_i64, -2, -1, 1, 2, 3];
    let mut actual = BTreeSet::new();
    for divisor in divisors {
        // Separate original queries qualify each signed divisor. This is a
        // semantic test, never a production decomposition or renewed grant.
        let mut solver = solver();
        let a = bounded(&mut solver, "dividend", -7, 7);
        let b = solver.try_declare_const("divisor", Sort::Int).unwrap();
        let literal = solver.int_const(divisor);
        let fixed = solver.try_eq(b, literal).unwrap();
        solver.try_assert_term(fixed).unwrap();
        let quotient = solver.try_int_div(a, b).unwrap();
        let remainder = solver.try_modulo(a, b).unwrap();
        let report = solver
            .try_enumerate_finite(&[a, b, quotient, remainder], 15)
            .unwrap();
        exhaustive(&report);
        assert_eq!(report.rows().len(), 15);
        for row in report.rows() {
            assert!(actual.insert((
                integer(&row.values()[0]),
                integer(&row.values()[1]),
                integer(&row.values()[2]),
                integer(&row.values()[3]),
            )));
        }
        #[cfg(any(
            target_os = "macos",
            all(target_os = "linux", not(target_env = "uclibc"))
        ))]
        if let Some(reference) = crate::api::solving::tactic_model::bounded_reference(
            &format!(
                "{}\n(check-sat)\n",
                report
                    .completeness_proof()
                    .unwrap()
                    .alethe_problem_smt2
                    .as_deref()
                    .unwrap()
            ),
            "native-finite-fixed-divisor-source-completeness",
        ) {
            assert!(!reference.is_empty());
            assert!(
                reference.split_whitespace().all(|value| value == "unsat"),
                "{reference}"
            );
        }
    }
    let expected: BTreeSet<_> = (-7_i64..=7)
        .flat_map(|a| {
            divisors.into_iter().map(move |b| {
                let remainder = a.rem_euclid(b.abs());
                (a, b, (a - remainder) / b, remainder)
            })
        })
        .collect();
    assert_eq!(actual, expected);
    assert_eq!(actual.len(), 90);
}

#[test]
fn finite_variable_divisors_produce_checked_capped_rows_without_completeness() {
    let mut solver = solver();
    let a = bounded(&mut solver, "dividend", -7, 7);
    let b = solver.try_declare_const("divisor", Sort::Int).unwrap();
    let mut choices = Vec::new();
    for value in [-3_i64, -2, -1, 1, 2, 3] {
        let value = solver.int_const(value);
        choices.push(solver.try_eq(b, value).unwrap());
    }
    let domain = solver.try_or_many(&choices).unwrap();
    solver.try_assert_term(domain).unwrap();
    let quotient = solver.try_int_div(a, b).unwrap();
    let remainder = solver.try_modulo(a, b).unwrap();
    let source = solver.terms().snapshot_stamp();
    let report = solver
        .try_enumerate_finite(&[a, b, quotient, remainder], 50)
        .unwrap();
    assert_eq!(report.outcome(), Outcome::Capped);
    assert_eq!(report.rows().len(), 50);
    assert_eq!(report.statistics().candidate_solve_calls, 51);
    assert_eq!(report.statistics().final_source_solve_calls, 0);
    assert!(report.completeness_proof().is_none());
    let mut seen = BTreeSet::new();
    for row in report.rows() {
        let a = integer(&row.values()[0]);
        let b = integer(&row.values()[1]);
        let q = integer(&row.values()[2]);
        let r = integer(&row.values()[3]);
        assert!((-7..=7).contains(&a));
        assert!([-3, -2, -1, 1, 2, 3].contains(&b));
        assert_eq!(r, a.rem_euclid(b.abs()));
        assert_eq!(q, (a - r) / b);
        assert!(seen.insert((a, b, q, r)));
    }
    assert_eq!(source, solver.terms().snapshot_stamp());
}

#[test]
fn finite_nonzero_equalities_and_ite_divisors_keep_original_values() {
    let mut solver = solver();
    let x = bounded(&mut solver, "x", -2, 2);
    let y = solver
        .try_declare_const("nonzero_choice", Sort::Int)
        .unwrap();
    let minus_one = solver.int_const(-1);
    let one = solver.int_const(1);
    let negative = solver.try_eq(y, minus_one).unwrap();
    let positive = solver.try_eq(y, one).unwrap();
    let domain = solver.try_or(negative, positive).unwrap();
    let same = solver.try_eq(x, y).unwrap();
    solver.try_assert_term(domain).unwrap();
    solver.try_assert_term(same).unwrap();
    let p = solver.try_declare_const("sign", Sort::Bool).unwrap();
    let zero = solver.int_const(0);
    let opposite = solver.try_sub(zero, x).unwrap();
    let divisor = solver.try_ite(p, x, opposite).unwrap();
    let seven = solver.int_const(7);
    let quotient = solver.try_int_div(seven, divisor).unwrap();
    let report = solver.try_enumerate_finite(&[p, x, quotient], 10).unwrap();
    exhaustive(&report);
    let actual: BTreeSet<_> = report
        .rows()
        .iter()
        .map(|row| {
            let Scalar::Bool(p) = &row.values()[0] else {
                panic!("Bool projection")
            };
            (*p, integer(&row.values()[1]), integer(&row.values()[2]))
        })
        .collect();
    assert_eq!(
        actual,
        BTreeSet::from([(false, -1, 7), (false, 1, -7), (true, -1, -7), (true, 1, 7)])
    );
    assert_eq!(report.rows().len(), 4);
}

#[test]
fn finite_tla_floor_adjustment_uses_euclidean_native_division() {
    let mut solver = solver();
    let x = bounded(&mut solver, "floor_dividend", -7, 7);
    let divisor = solver.int_const(-3);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let quotient = solver.try_int_div(x, divisor).unwrap();
    let product = solver.try_mul(quotient, divisor).unwrap();
    let exact = solver.try_eq(product, x).unwrap();
    let has_remainder = solver.try_not(exact).unwrap();
    let negative = solver.try_lt(divisor, zero).unwrap();
    let adjust = solver.try_and(negative, has_remainder).unwrap();
    let lower = solver.try_sub(quotient, one).unwrap();
    let floor = solver.try_ite(adjust, lower, quotient).unwrap();
    let report = solver.try_enumerate_finite(&[x, floor], 20).unwrap();
    exhaustive(&report);
    let actual: BTreeSet<_> = report
        .rows()
        .iter()
        .map(|row| (integer(&row.values()[0]), integer(&row.values()[1])))
        .collect();
    let expected: BTreeSet<_> = (-7_i64..=7)
        .map(|x| {
            let quotient = x / -3;
            let floor = if x > 0 && x % -3 != 0 {
                quotient - 1
            } else {
                quotient
            };
            (x, floor)
        })
        .collect();
    assert_eq!(actual, expected);
    assert_eq!(report.rows().len(), 15);
}

#[test]
fn finite_possible_zero_divisors_are_refused_without_source_mutation() {
    let mut solver = solver();
    let a = bounded(&mut solver, "zero_dividend", -2, 2);
    let b = bounded(&mut solver, "possibly_zero", 0, 1);
    let quotient = solver.try_int_div(a, b).unwrap();
    let original = solver.terms().snapshot_stamp();
    assert!(matches!(
        solver.try_enumerate_finite(&[quotient], 100),
        Err(SolverError::InvalidArgument { .. })
    ));
    assert_eq!(original, solver.terms().snapshot_stamp());
}

#[test]
fn finite_correlated_tuple_alternatives_bound_every_component_without_cross_products() {
    let mut solver = solver();
    let x = solver.try_declare_const("tuple__1", Sort::Int).unwrap();
    let y = solver.try_declare_const("tuple__2", Sort::Int).unwrap();
    let expected = BTreeSet::from([(1, 9), (2, 8), (3, 7)]);
    let mut alternatives = Vec::new();
    for &(a, b) in &expected {
        let a = solver.int_const(a);
        let b = solver.int_const(b);
        let first = solver.try_eq(x, a).unwrap();
        let second = solver.try_eq(y, b).unwrap();
        // Include an equivalent negated disjunction to exercise polarity,
        // then build the left-associated OR emitted by TY tuple membership.
        let branch = if alternatives.len() == 1 {
            let first = solver.try_not(first).unwrap();
            let second = solver.try_not(second).unwrap();
            let either = solver.try_or(first, second).unwrap();
            solver.try_not(either).unwrap()
        } else {
            solver.try_and(first, second).unwrap()
        };
        alternatives.push(branch);
    }
    let left = solver.try_or(alternatives[0], alternatives[1]).unwrap();
    let domain = solver.try_or(left, alternatives[2]).unwrap();
    solver.try_assert_term(domain).unwrap();
    let report = solver.try_enumerate_finite(&[x, y], 3).unwrap();
    exhaustive(&report);
    let actual: BTreeSet<_> = report
        .rows()
        .iter()
        .map(|row| (integer(&row.values()[0]), integer(&row.values()[1])))
        .collect();
    assert_eq!(actual, expected);
    assert_eq!(report.rows().len(), 3);
}

#[test]
fn finite_alternative_missing_a_component_cannot_manufacture_its_domain() {
    let mut solver = solver();
    let x = solver.try_declare_const("tuple__1", Sort::Int).unwrap();
    let y = solver.try_declare_const("tuple__2", Sort::Int).unwrap();
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let x_one = solver.try_eq(x, one).unwrap();
    let y_two = solver.try_eq(y, two).unwrap();
    let complete = solver.try_and(x_one, y_two).unwrap();
    let x_two = solver.try_eq(x, two).unwrap();
    let incomplete = solver.try_or(complete, x_two).unwrap();
    solver.try_assert_term(incomplete).unwrap();
    let source = solver.terms().snapshot_stamp();
    assert!(matches!(
        solver.try_enumerate_finite(&[x, y], 20),
        Err(SolverError::InvalidArgument { .. })
    ));
    assert_eq!(source, solver.terms().snapshot_stamp());
}

#[test]
fn finite_variable_divisors_have_exact_90_rows_and_one_checked_original_source_solve() {
    let mut solver = solver();
    let a = bounded(&mut solver, "dividend", -7, 7);
    let b = solver.try_declare_const("divisor", Sort::Int).unwrap();
    let divisors = [-3_i64, -2, -1, 1, 2, 3];
    let mut choices = Vec::new();
    for value in divisors {
        let value = solver.int_const(value);
        choices.push(solver.try_eq(b, value).unwrap());
    }
    let domain = solver.try_or_many(&choices).unwrap();
    solver.try_assert_term(domain).unwrap();
    let quotient = solver.try_int_div(a, b).unwrap();
    let remainder = solver.try_modulo(a, b).unwrap();
    let projection = [a, b, quotient, remainder];
    let original = solver.terms().snapshot_stamp();
    let report = solver.try_enumerate_finite(&projection, 90).unwrap();
    eprintln!(
        "finite variable-divisor90 rows={} outcome={:?} stats={:?} detail={:?}",
        report.rows().len(),
        report.outcome(),
        report.statistics(),
        report.diagnostic()
    );
    exhaustive(&report);
    assert_eq!(report.statistics().candidate_solve_calls, 91);
    assert_eq!(report.rows().len(), 90);
    let actual: BTreeSet<_> = report
        .rows()
        .iter()
        .map(|row| {
            (
                integer(&row.values()[0]),
                integer(&row.values()[1]),
                integer(&row.values()[2]),
                integer(&row.values()[3]),
            )
        })
        .collect();
    let expected: BTreeSet<_> = (-7_i64..=7)
        .flat_map(|a| {
            divisors.into_iter().map(move |b| {
                let r = a.rem_euclid(b.abs());
                (a, b, (a - r) / b, r)
            })
        })
        .collect();
    assert_eq!(actual, expected);
    assert_eq!(original, solver.terms().snapshot_stamp());
    assert!(report.is_current_for(&solver));
    #[cfg(any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    reference_finite_source(
        report
            .completeness_proof()
            .unwrap()
            .alethe_problem_smt2
            .as_deref()
            .unwrap(),
        "native-variable-divisor90-exact-source",
        "unsat",
    );

    let ids: Vec<_> = projection.iter().map(|term| term.id()).collect();
    // Counterfactual source queries are separate test obligations. They use
    // the real alpha-copy/blocker path and the SAME independent checker that
    // supplies the ordinary funnel's source authority, with no forged Model.
    for omit_whole_choice in [false, true] {
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(20_000_000, 64 << 20),
            None,
            Arc::new(|| false),
        )
        .unwrap();
        let compiled = finite_bool::compile_finite(
            solver.terms(),
            &solver.executor.ctx.assertions,
            &ids,
            &owner,
        )
        .unwrap();
        let mut source = source::copy(
            solver.terms(),
            &solver.executor.ctx.assertions,
            &compiled,
            &owner,
        )
        .unwrap();
        for (index, row) in report.rows().iter().enumerate() {
            let omit = if omit_whole_choice {
                integer(&row.values()[1]) == -3
            } else {
                index == 0
            };
            if !omit {
                source.block(&ids, row.values(), &owner).unwrap();
            }
        }
        assert!(matches!(
            ay_proof::authenticate_bv_lia_unsat_query(
                source.solver.terms(),
                &source.solver.executor.ctx.assertions,
                Some(Instant::now() + std::time::Duration::from_secs(5))
            ),
            Err(ay_proof::BvLiaUnsatAuthenticationError::Satisfiable)
        ));
        #[cfg(any(
            target_os = "macos",
            all(target_os = "linux", not(target_env = "uclibc"))
        ))]
        reference_finite_source(
            &source.solver.query_dump_script(&[]),
            if omit_whole_choice {
                "native-variable-divisor90-missing-choice"
            } else {
                "native-variable-divisor90-missing-blocker"
            },
            "sat",
        );
    }
}

#[cfg(any(
    target_os = "macos",
    all(target_os = "linux", not(target_env = "uclibc"))
))]
fn reference_finite_source(script: &str, label: &str, expected: &str) {
    if let Some(reference) = crate::api::solving::tactic_model::bounded_reference(
        &format!("{script}\n(check-sat)\n"),
        label,
    ) {
        assert!(!reference.is_empty());
        assert!(
            reference.split_whitespace().all(|value| value == expected),
            "{reference}"
        );
    }
}
