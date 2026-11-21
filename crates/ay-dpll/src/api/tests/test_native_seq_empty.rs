// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::api::*;

fn datatype() -> DatatypeSort {
    DatatypeSort::new(
        "EmptyElement",
        vec![DatatypeConstructor::unit("empty_element")],
    )
}

fn budget(work: usize) -> NativeDeclarationBudget {
    NativeDeclarationBudget::new(NativeDeclarationLimits::new(work, 1 << 20, 128))
}

#[test]
fn native_seq_empty_uses_the_constructor_and_declaration_live_carrier() {
    let mut solver = Solver::new(Logic::All);
    let dt = datatype();
    solver.try_declare_datatypes(&[dt.clone()]).unwrap();
    let element = solver
        .try_datatype_constructor(&dt, "empty_element", &[])
        .unwrap();
    let singleton = solver.try_seq_unit(element).unwrap();
    let empty = solver.try_seq_empty(Sort::Datatype(dt.clone())).unwrap();
    let legacy_wrapper = solver.seq_empty(Sort::Datatype(dt.clone()));
    let declared = solver.declare_const("empty_native_sequence", Sort::seq(Sort::Datatype(dt)));
    assert_eq!(solver.get_sort(empty), solver.get_sort(singleton));
    assert_eq!(solver.get_sort(legacy_wrapper), solver.get_sort(declared));
    let concat = solver.try_seq_concat(empty, singleton).unwrap();
    let length = solver.try_seq_len(concat).unwrap();
    let one = solver.int_const(1);
    let right_length = solver.eq(length, one);
    solver.assert_term(right_length);
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat() && details.result.was_model_validated(),
        "{details:?}"
    );
}

#[test]
fn native_seq_empty_recursively_lowers_nested_nominal_carriers() {
    let mut solver = Solver::new(Logic::All);
    let dt = datatype();
    solver.try_declare_datatypes(&[dt.clone()]).unwrap();
    let nested = Sort::array(Sort::Int, Sort::seq(Sort::Datatype(dt)));
    let element = solver.declare_const("nested_empty_element", nested.clone());
    let singleton = solver.try_seq_unit(element).unwrap();
    let empty = solver.try_seq_empty(nested).unwrap();
    assert!(solver.try_seq_concat(empty, singleton).is_ok());
}

#[test]
fn native_seq_empty_refuses_undeclared_datatype_and_nominal_kind_confusion() {
    let mut solver = Solver::new(Logic::All);
    let dt = datatype();
    let count = solver.terms().len();
    assert!(solver.try_seq_empty(Sort::Datatype(dt.clone())).is_err());
    assert_eq!(solver.terms().len(), count);
    solver.try_declare_opaque_sort(&dt.name).unwrap();
    let count = solver.terms().len();
    assert!(solver.try_seq_empty(Sort::Datatype(dt)).is_err());
    assert_eq!(solver.terms().len(), count);
    assert!(solver
        .try_seq_empty(Sort::Uninterpreted("OrdinaryNativeU".into()))
        .is_ok());
}

#[test]
fn native_seq_empty_cancellation_and_cumulative_refusal_precede_term_creation() {
    let mut solver = Solver::new(Logic::All);
    let mut cancelled = budget(1000);
    let before = solver.terms().len();
    assert!(solver
        .try_seq_empty_with_progress(&Sort::Int, &mut cancelled, &mut |_, _| false)
        .is_err());
    assert_eq!(solver.terms().len(), before);
    assert!(solver
        .try_seq_empty_with_progress(&Sort::Int, &mut cancelled, &mut |_, _| true)
        .is_err());
    let mut limited = budget(0);
    assert!(solver
        .try_seq_empty_with_progress(&Sort::Int, &mut limited, &mut |_, _| true)
        .is_err());
    solver.try_push().unwrap();
    solver.try_pop().unwrap();
    assert!(solver
        .try_seq_empty_with_progress(&Sort::Int, &mut limited, &mut |_, _| true)
        .is_err());
    assert_eq!(solver.terms().len(), before);
    assert!(solver
        .try_seq_empty_with_progress(&Sort::Int, &mut budget(64 * 1024 * 1024), &mut |_, _| true)
        .is_ok());
}

#[test]
fn native_seq_empty_rejects_ill_formed_or_overdeep_sorts_before_copying() {
    let mut solver = Solver::new(Logic::All);
    let count = solver.terms().len();
    assert!(solver.try_seq_empty(Sort::bitvec(0)).is_err());
    let mut deep = Sort::Int;
    for _ in 0..129 {
        deep = Sort::seq(deep);
    }
    assert!(solver
        .try_seq_empty_with_progress(&deep, &mut budget(1000), &mut |_, _| true)
        .is_err());
    assert_eq!(solver.terms().len(), count);
}

#[test]
fn native_seq_empty_keeps_exact_native_replay_with_nominal_elements() {
    let mut solver = Solver::new(Logic::All);
    let dt = datatype();
    solver.try_declare_datatypes(&[dt.clone()]).unwrap();
    let empty = solver.try_seq_empty(Sort::Datatype(dt)).unwrap();
    let length = solver.try_seq_len(empty).unwrap();
    let zero = solver.int_const(0);
    let fact = solver.eq(length, zero);
    solver.assert_term(fact);
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let replay = Solver::replay_native_replay_json_str(&artifact.to_pretty_json()).unwrap();
    assert!(
        replay.result.is_sat() && replay.result.was_model_validated(),
        "{replay:?}"
    );
}

#[test]
fn native_seq_empty_replay_rejects_wrong_arity_and_recorded_sort() {
    use ay_core::term::{Symbol, TermData};

    let mut solver = Solver::new(Logic::All);
    let dt = datatype();
    solver.try_declare_datatypes(&[dt.clone()]).unwrap();
    let empty = solver.try_seq_empty(Sort::Datatype(dt.clone())).unwrap();
    let sequence = solver.declare_const("replay_empty_sequence", Sort::seq(Sort::Datatype(dt)));
    let definition = solver.eq(sequence, empty);
    solver.assert_term(definition);
    let length = solver.try_seq_len(empty).unwrap();
    let zero = solver.int_const(0);
    let fact = solver.eq(length, zero);
    solver.assert_term(fact);
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let index = artifact
        .terms
        .iter()
        .position(|node| matches!(&node.data, TermData::App(Symbol::Named(name), _) if name == "seq.empty"))
        .unwrap();
    let mut non_sequence = artifact.clone();
    non_sequence.terms[index].sort = Sort::Int;
    assert!(Solver::replay_native_replay_artifact(&non_sequence).is_err());

    // A well-formed sequence annotation must also agree with every consumer;
    // a different declared element type cannot reinterpret the original DAG.
    let mut wrong_element = artifact.clone();
    wrong_element.terms[index].sort = Sort::seq(Sort::Int);
    assert!(Solver::replay_native_replay_artifact(&wrong_element).is_err());

    let mut wrong_arity = artifact;
    let argument = wrong_arity.terms[0].id;
    let TermData::App(_, args) = &mut wrong_arity.terms[index].data else {
        unreachable!();
    };
    args.push(argument);
    assert!(Solver::replay_native_replay_artifact(&wrong_arity).is_err());
}

#[test]
fn native_seq_empty_prices_many_sort_collisions_before_comparison_and_creation() {
    let mut solver = Solver::new(Logic::All);
    for width in 1..=64 {
        solver.try_seq_empty(Sort::bitvec(width)).unwrap();
    }
    let before = solver.terms().len();
    let mut limited = budget(1000);
    assert!(matches!(
        solver.try_seq_empty_with_progress(&Sort::Int, &mut limited, &mut |_, _| true),
        Err(NativeDeclarationError::Refused(
            NativeDeclarationRefusal::Work { .. }
        ))
    ));
    assert!(limited.usage().work <= 1000);
    assert_eq!(solver.terms().len(), before);
    solver.try_push().unwrap();
    solver.try_pop().unwrap();
    assert!(solver
        .try_seq_empty_with_progress(&Sort::Int, &mut limited, &mut |_, _| true)
        .is_err());
    assert_eq!(solver.terms().len(), before);
    let empty = solver.try_seq_empty(Sort::Int).unwrap();
    let length = solver.try_seq_len(empty).unwrap();
    let zero = solver.int_const(0);
    let correct = solver.eq(length, zero);
    solver.assert_term(correct);
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat() && details.result.was_model_validated(),
        "{details:?}"
    );
}

#[test]
fn native_seq_empty_cancellation_inside_collision_scan_is_sticky_and_precommit() {
    let mut solver = Solver::new(Logic::All);
    for width in 1..=32 {
        solver.try_seq_empty(Sort::bitvec(width)).unwrap();
    }
    let before = solver.terms().len();
    let mut owner = budget(1 << 20);
    let mut comparisons = 0;
    let result = solver.try_seq_empty_with_progress(&Sort::Int, &mut owner, &mut |work, _| {
        // Core256-unit collision base plus the two physical Seq/Int sort nodes.
        if work == 258 {
            comparisons += 1;
        }
        comparisons < 3
    });
    assert!(matches!(
        result,
        Err(NativeDeclarationError::Refused(
            NativeDeclarationRefusal::Cancelled
        ))
    ));
    assert_eq!(comparisons, 3);
    assert_eq!(solver.terms().len(), before);
    assert!(solver
        .try_seq_empty_with_progress(&Sort::Int, &mut owner, &mut |_, _| true)
        .is_err());
    assert_eq!(solver.terms().len(), before);
}

#[test]
fn native_seq_empty_nominal_redeclaration_keeps_old_and_new_carriers_distinct() {
    let mut solver = Solver::new(Logic::All);
    let dt = datatype();
    solver.try_push().unwrap();
    solver
        .executor
        .execute_all(
            &ay_frontend::parse("(declare-datatype EmptyElement ((empty_element)))").unwrap(),
        )
        .unwrap();
    let old_element = solver
        .try_datatype_constructor(&dt, "empty_element", &[])
        .unwrap();
    let old_singleton = solver.try_seq_unit(old_element).unwrap();
    let old_empty = solver.try_seq_empty(Sort::Datatype(dt.clone())).unwrap();
    solver.try_pop().unwrap();
    assert!(solver.try_seq_empty(Sort::Datatype(dt.clone())).is_err());
    solver
        .executor
        .execute_all(
            &ay_frontend::parse("(declare-datatype EmptyElement ((empty_element)))").unwrap(),
        )
        .unwrap();
    let new_empty = solver.try_seq_empty(Sort::Datatype(dt)).unwrap();
    assert_ne!(solver.get_sort(old_singleton), solver.get_sort(new_empty));
    assert!(solver.try_seq_concat(old_singleton, new_empty).is_err());
    assert!(solver.try_seq_concat(old_singleton, old_empty).is_ok());
}

#[test]
fn native_seq_empty_nominal_copy_refuses_before_lowering_with_tiny_storage() {
    let mut solver = Solver::new(Logic::All);
    let element = Sort::Uninterpreted("x".repeat(32_768));
    let before = solver.terms().len();
    let mut owner = NativeDeclarationBudget::new(NativeDeclarationLimits::new(1 << 20, 1024, 128));
    assert!(matches!(
        solver.try_seq_empty_with_progress(&element, &mut owner, &mut |_, _| true),
        Err(NativeDeclarationError::Refused(
            NativeDeclarationRefusal::Storage { .. }
        ))
    ));
    assert_eq!(solver.terms().len(), before);
    assert!(solver
        .try_seq_empty_with_progress(&Sort::Int, &mut owner, &mut |_, _| true)
        .is_err());
}
