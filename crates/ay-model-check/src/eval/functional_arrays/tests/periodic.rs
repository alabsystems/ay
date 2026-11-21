// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

struct PeriodicCase {
    terms: TermStore,
    view: View,
    target: TermId,
    lambda: TermId,
    bound: TermId,
    definition: TermId,
}

fn periodic_case(modulus: i64, table: &[i64]) -> PeriodicCase {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Int, Sort::Int);
    let bound = terms.mk_fresh_named_var("periodic_index", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let modulus = terms.mk_int(modulus.into());
    let residue = app(&mut terms, "mod", &[bound, modulus], Sort::Int);
    let even = terms.mk_eq(residue, zero);
    let body = terms.mk_ite(even, one, zero);
    let lambda = terms.mk_lambda_array(bound, body);
    let target = terms.mk_fresh_named_var("periodic_target", sort.clone());
    let definition = terms.mk_eq(target, lambda);
    let values: Vec<_> = table
        .iter()
        .map(|value| ModelValue::Int((*value).into()))
        .collect();
    let snapshot = ArraySnapshot::periodic(&values, &sort, &mut 100_000).unwrap();
    let mut view = View {
        left: Cell::new(1_000_000),
        ..View::default()
    };
    view.arrays.insert(target, snapshot);
    PeriodicCase {
        terms,
        view,
        target,
        lambda,
        bound,
        definition,
    }
}

#[test]
fn periodic_int_complete_model_checks_every_original_read_and_negative_index() {
    let mut case = periodic_case(2, &[1, 0]);
    let mut roots = vec![case.definition];
    for (index, expected) in [(-7, 0), (-6, 1), (0, 1), (1, 0), (300, 1)] {
        let index = case.terms.mk_int(index.into());
        let read = app(&mut case.terms, "select", &[case.target, index], Sort::Int);
        let expected = case.terms.mk_int(expected.into());
        roots.push(case.terms.mk_eq(read, expected));
    }
    assert!(matches!(
        confirm_completed_model(&case.terms, &case.view, &roots),
        GateVerdict::ConfirmedSat
    ));
    let wrong = case.terms.mk_int(1.into());
    let at_one = case.terms.mk_int(1.into());
    let read = app(&mut case.terms, "select", &[case.target, at_one], Sort::Int);
    roots.push(case.terms.mk_eq(read, wrong));
    assert!(!matches!(
        confirm_completed_model(&case.terms, &case.view, &roots),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn periodic_int_wrong_residue_and_wrong_period_cannot_confirm_the_source() {
    for table in [&[0, 1][..], &[1, 0, 0][..]] {
        let case = periodic_case(2, table);
        assert!(!matches!(
            confirm_completed_model(&case.terms, &case.view, &[case.definition]),
            GateVerdict::ConfirmedSat
        ));
    }
}

#[test]
fn periodic_int_disequality_requires_an_actual_difference() {
    for (table, differs) in [([0, 1], true), ([1, 0], false)] {
        let mut case = periodic_case(2, &table);
        let disequality = case.terms.mk_not(case.definition);
        assert_eq!(
            matches!(
                confirm_completed_model(&case.terms, &case.view, &[disequality]),
                GateVerdict::ConfirmedSat
            ),
            differs
        );
    }
}

#[test]
fn periodic_int_modulus_and_raw_binder_admission_fail_closed() {
    for modulus in [0, -2] {
        let case = periodic_case(modulus, &[1, 0]);
        let evaluator = Evaluator::new(&case.terms, &case.view);
        assert!(evaluator.capture_array_snapshot(case.lambda).is_err());
    }
    let mut case = periodic_case(2, &[1, 0]);
    let one = case.terms.mk_int(1.into());
    let body = app(&mut case.terms, "+", &[case.bound, one], Sort::Int);
    let lambda = case.terms.mk_lambda_array(case.bound, body);
    assert!(Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(lambda)
        .is_err());
}

#[test]
fn periodic_int_multiple_moduli_are_an_exhaustive_common_quotient() {
    let mut case = periodic_case(2, &[1, 0]);
    let two = case.terms.mk_int(2.into());
    let three = case.terms.mk_int(3.into());
    let first = app(&mut case.terms, "mod", &[case.bound, two], Sort::Int);
    let second = app(&mut case.terms, "mod", &[case.bound, three], Sort::Int);
    let body = app(&mut case.terms, "+", &[first, second], Sort::Int);
    let lambda = case.terms.mk_lambda_array(case.bound, body);
    let captured = Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(lambda)
        .unwrap();
    for (index, expected) in [
        (-1, 3),
        (0, 0),
        (1, 2),
        (2, 2),
        (3, 1),
        (4, 1),
        (5, 3),
        (6, 0),
    ] {
        let value = captured
            .read(&ModelValue::Int(index.into()), &mut 10_000)
            .unwrap();
        assert!(matches!(value, ModelValue::Int(value) if value == BigInt::from(expected)));
    }
}

#[test]
fn periodic_int_capture_is_validated_under_the_same_independent_model() {
    let mut case = periodic_case(2, &[1, 0]);
    let captured = case.terms.mk_fresh_named_var("captured_cell", Sort::Int);
    let raw = match case.terms.get(case.lambda) {
        TermData::App(_, args) => args[1],
        _ => unreachable!(),
    };
    let zero = case.terms.mk_int(0.into());
    let condition = case.terms.mk_eq(raw, zero);
    let body = case.terms.mk_ite(condition, captured, raw);
    let lambda = case.terms.mk_lambda_array(case.bound, body);
    case.view
        .scalars
        .insert(captured, ModelValue::Int(9.into()));
    let selected = Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(lambda)
        .unwrap();
    case.view.arrays.insert(case.target, selected);
    let definition = case.terms.mk_eq(case.target, lambda);
    assert!(matches!(
        confirm_completed_model(&case.terms, &case.view, &[definition]),
        GateVerdict::ConfirmedSat
    ));
    case.view
        .scalars
        .insert(captured, ModelValue::Int(8.into()));
    assert!(!matches!(
        confirm_completed_model(&case.terms, &case.view, &[definition]),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn periodic_int_boolean_cell_negation_keeps_native_binder_scope() {
    let mut case = periodic_case(2, &[1, 0]);
    let modulus = case.terms.mk_int(3.into());
    let residue = app(&mut case.terms, "mod", &[case.bound, modulus], Sort::Int);
    let zero = case.terms.mk_int(0.into());
    let divisible = case.terms.mk_eq(residue, zero);
    let body = case.terms.mk_not(divisible);
    let lambda = case.terms.mk_lambda_array(case.bound, body);
    let value = Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(lambda)
        .unwrap();
    for (index, expected) in [(-3, false), (-2, true), (0, false), (1, true), (3, false)] {
        assert!(
            matches!(value.read(&ModelValue::Int(index.into()), &mut 10_000).unwrap(), ModelValue::Bool(actual) if actual == expected)
        );
    }
}

#[test]
fn periodic_int_topology_native_term_and_printing_preserve_all_cells() {
    let case = periodic_case(2, &[1, 0]);
    let snapshot = case.view.arrays.get(&case.target).unwrap();
    let printed = snapshot.to_smtlib(&mut 100_000).unwrap();
    assert!(printed.contains("(lambda ((ay!model!index Int))"));
    assert!(printed.contains("(mod ay!model!index 2)"));
    let topology = snapshot.topology(&mut 100_000, &mut || false).unwrap();
    let rebuilt =
        ArraySnapshot::from_topology(topology.nodes(), topology.root(), &mut 100_000, &mut || {
            false
        })
        .unwrap();
    assert!(snapshot.same_function(&rebuilt, &mut 100_000).unwrap());
    let mut terms = TermStore::new();
    let lambda = topology
        .try_to_term_with_progress(&mut terms, &mut |_, _| true)
        .unwrap();
    let view = View {
        left: Cell::new(100_000),
        ..View::default()
    };
    for (index, expected) in [(-3, 0), (-2, 1), (0, 1), (1, 0)] {
        let index = terms.mk_int(index.into());
        let read = app(&mut terms, "select", &[lambda, index], Sort::Int);
        assert!(
            matches!(Evaluator::new(&terms, &view).evaluate(read), EvalOutcome::Value(ModelValue::Int(value)) if value == BigInt::from(expected))
        );
    }
}

#[test]
fn periodic_int_comparison_checks_base_classes_and_all_finite_exceptions() {
    let sort = Sort::array(Sort::Int, Sort::Int);
    let values = |numbers: &[i64]| {
        numbers
            .iter()
            .map(|number| ModelValue::Int((*number).into()))
            .collect::<Vec<_>>()
    };
    let first = ArraySnapshot::periodic(&values(&[1, 0]), &sort, &mut 100_000).unwrap();
    let same = ArraySnapshot::periodic(&values(&[1, 0, 1, 0]), &sort, &mut 100_000).unwrap();
    assert!(first.same_function(&same, &mut 100_000).unwrap());
    let changed = ArraySnapshot::periodic(&values(&[0, 0]), &sort, &mut 100_000).unwrap();
    let masked = ArraySnapshot::store(
        changed,
        &ModelValue::Int(0.into()),
        &ModelValue::Int(1.into()),
        &mut 100_000,
    )
    .unwrap();
    assert!(!first.same_function(&masked, &mut 100_000).unwrap());
    let changed = ArraySnapshot::store(
        first.clone(),
        &ModelValue::Int((-3).into()),
        &ModelValue::Int(9.into()),
        &mut 100_000,
    )
    .unwrap();
    assert!(!first.same_function(&changed, &mut 100_000).unwrap());
}

#[test]
fn periodic_int_work_cancellation_and_malformed_topology_cannot_gain_data() {
    let case = periodic_case(2, &[1, 0]);
    let evaluator = Evaluator::new(&case.terms, &case.view);
    assert!(evaluator
        .capture_array_snapshot_with_work(case.lambda, &mut 1)
        .is_err());
    let mut wide = periodic_case(2, &[1, 0]);
    let body =
        wide.terms
            .mk_app_structural(Symbol::named("+"), vec![wide.bound; 10_000], Sort::Int);
    let lambda = wide.terms.mk_lambda_array(wide.bound, body);
    let mut work = 100;
    assert!(Evaluator::new(&wide.terms, &wide.view)
        .capture_array_snapshot_with_work(lambda, &mut work)
        .is_err());
    assert_eq!(work, 0);
    case.view.stopped.set(true);
    assert!(Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(case.lambda)
        .is_err());
    let sort = Sort::array(Sort::Int, Sort::Int);
    let node = crate::SnapshotNode {
        sort: &sort,
        kind: crate::SnapshotKind::Periodic(&[]),
    };
    let mut work = 100_000;
    assert!(ArraySnapshot::from_topology(&[node], 0, &mut work, &mut || false).is_err());
    assert_eq!(work, 0);
    let left =
        ArraySnapshot::periodic(&vec![ModelValue::Int(0.into()); 97], &sort, &mut 100_000).unwrap();
    let right = ArraySnapshot::periodic(&vec![ModelValue::Int(0.into()); 101], &sort, &mut 100_000)
        .unwrap();
    let mut work = 512;
    assert!(left.same_function(&right, &mut work).is_err());
    assert_eq!(work, 0);
    let wrong = [ModelValue::Bool(true)];
    let node = crate::SnapshotNode {
        sort: &sort,
        kind: crate::SnapshotKind::Periodic(&wrong),
    };
    assert!(ArraySnapshot::from_topology(&[node], 0, &mut 100_000, &mut || false).is_err());
}

#[test]
fn periodic_int_large_exception_payload_is_admitted_before_copy_or_comparison() {
    let sort = Sort::array(Sort::Int, Sort::Int);
    let snapshot = ArraySnapshot::periodic(
        &[ModelValue::Int(1.into()), ModelValue::Int(0.into())],
        &sort,
        &mut 100_000,
    )
    .unwrap();
    let key = ModelValue::Int(BigInt::from(1) << 100_000);
    let mut work = 100;
    assert!(ArraySnapshot::store(
        Arc::clone(&snapshot),
        &key,
        &ModelValue::Int(3.into()),
        &mut work,
    )
    .is_err());
    assert_eq!(work, 0);
    let mut work = 100;
    assert!(snapshot.read(&key, &mut work).is_err());
    assert_eq!(work, 0);
}
