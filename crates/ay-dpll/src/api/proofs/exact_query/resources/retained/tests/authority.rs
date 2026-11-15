// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn declines(solver: &Solver, binding: &ExactSmtlibQueryBinding) {
    assert!(solver
        .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            binding,
            deadline(),
            &mut |_, _| true,
        )
        .unwrap()
        .is_none());
}

#[test]
fn retained_exact_export_rejects_foreign_missing_duplicate_and_changed_binding() {
    let (solver, binding) = solved(BOOLEAN);
    let (sibling, sibling_binding) = solved(BOOLEAN);
    declines(&solver, &sibling_binding);
    declines(&sibling, &binding);
    let mut missing = binding.clone();
    missing.assertions.clear();
    declines(&solver, &missing);
    let mut duplicate = binding.clone();
    duplicate.assertions.push(duplicate.assertions[0]);
    declines(&solver, &duplicate);
    let mut foreign_handle = binding.clone();
    foreign_handle.assertions[0] = sibling_binding.assertions[0];
    declines(&solver, &foreign_handle);
    let mut foreign_context = binding.clone();
    foreign_context.source_context = sibling_binding.source_context;
    declines(&solver, &foreign_context);
}

#[test]
fn retained_exact_export_rejects_new_assertions_declarations_and_query_assumptions() {
    let (mut assertion_solver, assertion_binding) = solved(BOOLEAN);
    assertion_solver.parse_smtlib2("(assert true)").unwrap();
    assert!(assertion_solver.check_sat().is_unsat());
    declines(&assertion_solver, &assertion_binding);
    let (mut declaration_solver, declaration_binding) = solved(BOOLEAN);
    declaration_solver
        .try_declare_const("late", Sort::Int)
        .unwrap();
    assert!(declaration_solver.check_sat().is_unsat());
    declines(&declaration_solver, &declaration_binding);
    let (mut assumption_solver, assumption_binding) = solved(BOOLEAN);
    let assumption = assumption_binding.assertions[0];
    assert!(assumption_solver
        .check_sat_assuming(&[assumption])
        .is_unsat());
    declines(&assumption_solver, &assumption_binding);
    let (mut reset_solver, reset_binding) = solved(BOOLEAN);
    reset_solver.try_reset().unwrap();
    declines(&reset_solver, &reset_binding);
}

#[test]
fn missing_proof_and_explicit_datatype_wire_refusal_have_no_retained_artifact() {
    let (solver, binding) = parsed(Logic::All, BOOLEAN, Presentation::StrictWire);
    declines(&solver, &binding);
    let (mut solver, binding) = parsed(Logic::All, DATATYPE, Presentation::StrictWire);
    assert!(solver.check_sat().is_unknown());
    assert!(solver.last_proof().is_none());
    declines(&solver, &binding);
}

#[test]
fn present_stale_native_bv_lia_seal_never_falls_back_to_raw_v3() {
    let (mut solver, binding) = parsed(Logic::QfUfbvlia, PINNED, Presentation::StrictWire);
    assert!(solver.check_sat().is_unsat());
    assert!(solver.executor.has_strict_native_bv_lia_bundle_state());
    assert!(solver
        .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            &binding,
            deadline(),
            &mut |_, _| true,
        )
        .unwrap()
        .is_some());
    let _late = solver.fresh_var("late_arena_append", Sort::Bool);
    assert!(solver.executor.has_strict_native_bv_lia_bundle_state());
    declines(&solver, &binding);
}

#[test]
fn present_stale_native_sos_seal_never_falls_back_to_raw_v3() {
    let (mut solver, binding) = parsed(
        Logic::All,
        "(declare-const x Real) (assert (< (* x x) 0.0))",
        Presentation::StrictWire,
    );
    assert!(solver
        .executor
        .certify_native_sos_provisional_for_test()
        .is_unsat());
    assert!(solver.executor.has_strict_native_nra_sos_bundle_state());
    assert!(solver
        .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            &binding,
            deadline(),
            &mut |_, _| true,
        )
        .unwrap()
        .is_some());
    let _late = solver.fresh_var("late_arena_append", Sort::Bool);
    assert!(solver.executor.has_strict_native_nra_sos_bundle_state());
    declines(&solver, &binding);
}
