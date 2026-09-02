// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn preserved_authored_distinct_survives_preprocessed_root_replacement() {
    let mut exec = loaded(
        r#"
            (declare-datatype U ((mk (tag (_ BitVec 1)) (n Int))))
            (declare-fun f (Int) U)
        "#,
    );
    let datatype_sort = Sort::Uninterpreted("U".to_string());
    let mut applications = Vec::new();
    for value in 0..3 {
        let argument = exec.ctx.terms.mk_int(BigInt::from(value));
        applications.push(exec.ctx.terms.mk_app(
            ay_core::Symbol::named("f"),
            [argument],
            datatype_sort.clone(),
        ));
    }
    let authored =
        exec.ctx
            .terms
            .mk_app(ay_core::Symbol::named("distinct"), applications, Sort::Bool);
    exec.independent_gate_authored_assertions = Some(vec![authored]);
    exec.ctx.assertions.clear();

    let model = Model::empty();
    let mut builder = exec
        .dt_collect(&model, &[])
        .expect("preserved authored roots collect");
    assert_eq!(builder.diseq.values().map(Vec::len).sum::<usize>(), 6);
    assert!(builder.force_constructors());
    let f_roots: HashSet<_> = builder
        .terms
        .iter()
        .enumerate()
        .filter_map(|(index, &term)| {
            matches!(
                exec.ctx.terms.get(term),
                TermData::App(symbol, _) if symbol.name() == "f"
            )
            .then_some(builder.class_of[index])
        })
        .collect();
    assert_eq!(f_roots.len(), 3);
    assert!(f_roots.iter().all(|root| {
        builder.info[root]
            .forced
            .as_ref()
            .is_some_and(|force| force.vary_free_fields)
    }));
}

#[test]
fn preserved_authored_conjunction_keeps_positive_and_negative_tester_polarity() {
    let mut exec = loaded(
        r#"
            (declare-datatype U ((mk (n Int)) (other)))
            (declare-fun f (Int) U)
            (assert (and (is-mk (f 0)) (not (is-other (f 1)))))
        "#,
    );
    let authored = *exec
        .ctx
        .assertions
        .first()
        .expect("fixture has one authored conjunction");
    assert!(matches!(
        exec.ctx.terms.get(authored),
        TermData::App(symbol, args) if symbol.name() == "and" && args.len() == 2
    ));
    exec.independent_gate_authored_assertions = Some(vec![authored]);
    exec.ctx.assertions.clear();

    let model = Model::empty();
    let mut builder = exec
        .dt_collect(&model, &[])
        .expect("preserved conjunction collects");
    let positive = builder
        .tester_apps
        .iter()
        .find(|(_, ctor, _)| ctor == "mk")
        .cloned()
        .expect("positive tester is collected");
    let negative = builder
        .tester_apps
        .iter()
        .find(|(_, ctor, _)| ctor == "other")
        .cloned()
        .expect("negative tester is collected");
    assert_eq!(builder.committed(positive.0), Some(true));
    assert_eq!(builder.committed(negative.0), Some(false));

    assert!(builder.force_constructors());
    let positive_root = class_for_term(&builder, positive.2);
    let positive_force = forced_constructor(&builder, positive_root);
    assert_eq!(positive_force.ctor, "mk");
    assert_eq!(
        positive_force.origin,
        ConstructorForceOrigin::PositiveTester
    );
    let negative_root = class_for_term(&builder, negative.2);
    assert!(builder.info[&negative_root]
        .excluded
        .contains(&"other".to_string()));
    let negative_force = forced_constructor(&builder, negative_root);
    assert_eq!(negative_force.ctor, "mk");
    assert_eq!(negative_force.origin, ConstructorForceOrigin::InferredSole);
}

#[test]
fn tester_under_authored_disjunction_is_not_a_hard_literal() {
    let mut exec = loaded(
        r#"
            (declare-datatype U ((mk) (other)))
            (declare-const x U)
            (assert (or (is-mk x) (is-other x)))
        "#,
    );
    let authored = *exec
        .ctx
        .assertions
        .first()
        .expect("fixture has one authored disjunction");
    exec.independent_gate_authored_assertions = Some(vec![authored]);
    exec.ctx.assertions.clear();

    let model = Model::empty();
    let mut builder = exec.dt_collect(&model, &[]).expect("fixture collects");
    assert!(builder
        .tester_apps
        .iter()
        .all(|(tester, _, _)| builder.committed(*tester).is_none()));
    assert!(builder.force_constructors());
    let root = class_for_term(
        &builder,
        builder
            .tester_apps
            .first()
            .map(|(_, _, argument)| *argument)
            .expect("fixture has tester applications"),
    );
    assert!(builder.info[&root].forced.is_none());
    assert!(builder.info[&root].excluded.is_empty());
}

#[test]
fn contradictory_hard_literal_polarities_fail_closed() {
    let mut exec = loaded(
        r#"
            (declare-datatype U ((mk)))
            (declare-const x U)
            (assert (is-mk x))
        "#,
    );
    let tester = *exec.ctx.assertions.first().expect("fixture has a tester");
    let negated = exec.ctx.terms.mk_not_raw(tester);
    assert!(bounded_hard_literal_truth(&exec.ctx.terms, &[tester, negated]).is_none());
}

#[test]
fn collection_roots_include_active_assumption_but_not_inactive_retained_term() {
    let mut exec = loaded(
        r#"
            (declare-datatype U ((mk (n Int))))
            (declare-fun f (Int) U)
        "#,
    );
    let datatype_sort = Sort::Uninterpreted("U".to_string());
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let first = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("f"), [zero], datatype_sort.clone());
    let second = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("f"), [one], datatype_sort);
    let inactive = exec.ctx.terms.mk_app(
        ay_core::Symbol::named("distinct"),
        [first, second],
        Sort::Bool,
    );
    assert!(!exec
        .datatype_model_collection_roots(&[])
        .contains(&inactive));

    exec.last_assumptions = Some(vec![inactive]);
    assert!(exec
        .datatype_model_collection_roots(&[])
        .contains(&inactive));
    exec.last_assumptions = None;
    assert!(!exec
        .datatype_model_collection_roots(&[])
        .contains(&inactive));
}
