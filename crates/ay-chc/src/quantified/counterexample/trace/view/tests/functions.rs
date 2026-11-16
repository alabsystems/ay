// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::Sort;

fn source_and_models() -> (QuantifiedChcProblem, Vec<ScalarFunctionModel>) {
    let source = QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-fun f ((_ BitVec 136)) (_ BitVec 1))
         (declare-fun |unused wide| () (_ BitVec 136))
         (declare-fun P () Bool)
         (assert (=> (forall ((i (_ BitVec 64)))
           (= (f (concat (_ bv0 72) i)) #b1)) P))
         (assert (=> P false))
         (check-sat)",
    )
    .unwrap();
    let arguments = [Sort::bitvec(136)];
    let one = Sort::bitvec(1);
    let wide = Sort::bitvec(136);
    let expected = [
        ("f", arguments.as_slice(), &one),
        ("unused wide", &[][..], &wide),
    ];
    // Checked data ingress establishes types/totality, not native provenance
    // or SAT. The private trace below remains only an accessor fixture.
    let models = ScalarFunctionModel::decode_smtlib(
        "(model
           (define-fun |unused wide| () (_ BitVec 136)
             (concat (_ bv4 8) (_ bv9 128)))
           (define-fun f ((x (_ BitVec 136))) (_ BitVec 1) #b1))",
        &expected,
    )
    .unwrap();
    (source, models)
}

#[test]
fn complete_total_function_inventory_is_borrowed_once_including_unused_wide_nullary() {
    let (source, models) = source_and_models();
    let token = CancellationToken::new();
    let trace =
        fixtures::unchecked_tree_models(&source, vec![0, 1], vec![vec![], vec![0]], models, &token);
    let view = trace
        .view_for(&source, Duration::from_secs(30), &token)
        .unwrap();
    assert!(std::ptr::eq(
        view.function_models(),
        trace.function_models()
    ));
    assert_eq!(view.function_models().len(), 2);
    assert_eq!(view.function_models()[0].name(), "f");
    assert_eq!(view.function_models()[1].name(), "unused wide");
    assert_eq!(view.function_models()[1].arg_sorts(), []);
    assert_eq!(view.function_models()[1].result_sort(), &Sort::bitvec(136));
    assert_eq!(view.source().function_declarations().len(), 2);
    assert!(view.steps().all(|step| step.bindings().is_empty()));
    assert_eq!(view.step(0).unwrap().clause().premises().len(), 1);
    assert!(trace
        .replay_obligation()
        .contains("(define-fun |unused wide|"));
}

#[test]
fn missing_reordered_or_changed_total_models_do_not_join_retained_pins() {
    let (source, models) = source_and_models();
    let token = CancellationToken::new();
    let mut trace =
        fixtures::unchecked_tree_models(&source, vec![0, 1], vec![vec![], vec![0]], models, &token);
    trace.functions.swap(0, 1);
    assert!(trace
        .view_for(&source, Duration::from_secs(30), &token)
        .is_none());
    trace.functions.swap(0, 1);
    let retained = trace.functions.pop().unwrap();
    assert!(trace
        .view_for(&source, Duration::from_secs(30), &token)
        .is_none());
    trace.functions.push(retained);
    let sort = Sort::bitvec(136);
    let mut replacement = ScalarFunctionModel::decode_smtlib(
        "(model (define-fun |unused wide| () (_ BitVec 136) (_ bv0 136)))",
        &[("unused wide", &[][..], &sort)],
    )
    .unwrap();
    trace.functions[1] = replacement.remove(0);
    // Even another well-typed total interpretation of an unused function
    // changes the complete pinned assignment retained by this trace.
    assert!(trace
        .view_for(&source, Duration::from_secs(30), &token)
        .is_none());
}
