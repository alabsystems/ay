// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded exact finite-array closure regressions.

use super::*;
use ay_core::{Sort, Symbol, TermData};
use ay_frontend::parse;

#[test]
fn candidate_free_deep_scan_is_stack_safe_and_bounded() {
    let mut exec = Executor::new();
    let mut root = exec.ctx.terms.mk_var("deep_scan_leaf", Sort::Bool);
    for index in 0..(crate::executor::FiniteArrayExpansionLedger::MAX_SCAN_NODES + 32) {
        let condition = exec
            .ctx
            .terms
            .mk_var(format!("deep_scan_condition_{index}"), Sort::Bool);
        let ite = exec.ctx.terms.mk_ite_raw(condition, root, condition);
        root = exec.ctx.terms.mk_not_raw(ite);
    }
    exec.ctx.assertions.push(root);

    let report = exec.add_finite_index_array_closure();

    assert_eq!(report.candidate_equalities, 0);
    assert_eq!(report.candidate_selects, 0);
    assert_eq!(report.candidate_scan_truncated, 1);
    assert_eq!(exec.finite_array_expansion.remaining_scan_nodes, 0);
    assert!(!report.is_complete());
}

#[test]
fn repeated_scans_do_not_reinspect_or_recharge_stamped_dag() {
    let mut exec = Executor::new();
    let mut root = exec.ctx.terms.mk_var("repeat_scan_leaf", Sort::Bool);
    let per_scan = crate::executor::FiniteArrayExpansionLedger::MAX_SCAN_NODES / 4;
    for index in 0..per_scan {
        let condition = exec
            .ctx
            .terms
            .mk_var(format!("repeat_scan_condition_{index}"), Sort::Bool);
        let ite = exec.ctx.terms.mk_ite_raw(condition, root, condition);
        root = exec.ctx.terms.mk_not_raw(ite);
    }
    exec.ctx.assertions.push(root);

    let first = exec.add_finite_index_array_closure();
    let nodes_after_first = exec.finite_array_expansion.remaining_scan_nodes;
    let edges_after_first = exec.finite_array_expansion.remaining_scan_edges;
    let inspections_after_first = exec.finite_array_expansion.discovery_term_inspections;
    assert!(first.is_complete());
    assert!(nodes_after_first < per_scan);
    assert!(inspections_after_first > per_scan);

    let second = exec.add_finite_index_array_closure();
    assert!(second.is_complete());
    assert_eq!(second.candidate_scan_truncated, 0);
    assert_eq!(
        exec.finite_array_expansion.remaining_scan_nodes,
        nodes_after_first
    );
    assert_eq!(
        exec.finite_array_expansion.remaining_scan_edges,
        edges_after_first
    );
    assert_eq!(
        exec.finite_array_expansion.discovery_term_inspections, inspections_after_first,
        "the second closure must stop at its indexed root without reading TermData/sorts"
    );
}

#[test]
fn enum_constructor_select_noop_is_not_recharged_on_closure_replay() {
    let mut exec = Executor::new();
    let commands = parse("(declare-datatype E ((e0) (e1)))").expect("parse enum datatype");
    assert!(exec
        .execute_all(&commands)
        .expect("register enum datatype")
        .is_empty());
    let enum_sort = Sort::Uninterpreted("E".to_owned());
    let array = exec.ctx.terms.mk_var(
        "enum_noop_array",
        Sort::array(enum_sort.clone(), Sort::Bool),
    );
    // Nullary constructors use Var representation in the term store. The
    // expansion recognizes this exact constructor after building the enum
    // ITE and simplifies back to the authored select.
    let constructor = exec.ctx.terms.mk_var("e0", enum_sort);
    let select = exec.ctx.terms.mk_select(array, constructor);
    exec.ctx.assertions.push(select);

    let first = exec.add_finite_index_array_extensionality_with_budget(2);
    assert!(first.is_complete(), "first enum select closure: {first:?}");
    assert_eq!(first.candidate_selects, 1);
    assert_eq!(first.emitted_selects, 0);
    assert_eq!(exec.finite_array_expansion.remaining_index_points, 0);
    assert_eq!(
        exec.finite_array_expansion.trivially_covered_selects.len(),
        1
    );

    let replay = exec.add_finite_index_array_closure();
    assert!(
        replay.is_complete(),
        "replayed enum select closure: {replay:?}"
    );
    assert_eq!(
        replay.candidate_selects, 0,
        "candidate telemetry is query-unique: the covered select must not be rediscovered"
    );
    assert_eq!(replay.already_covered_selects, 1);
    assert_eq!(replay.budget_deferred_selects, 0);
    assert_eq!(
        exec.finite_array_expansion.remaining_index_points, 0,
        "a stamped no-op select must not reserve its domain a second time"
    );
}

#[test]
fn malformed_builtin_signatures_fail_closed_without_indexing_invalid_children() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Bool);
    let array = exec.ctx.terms.mk_var("malformed_array", array_sort.clone());
    let integer = exec.ctx.terms.mk_var("malformed_integer", Sort::Int);
    let malformed_equality =
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), [array, integer], Sort::Bool);
    exec.ctx.assertions.push(malformed_equality);

    let report = exec.add_finite_index_array_closure();

    assert_eq!(report.candidate_scan_truncated, 1);
    assert_eq!(report.candidate_equalities, 0);
    assert_eq!(report.emitted_equalities, 0);
    assert!(!report.is_complete());
}

#[test]
fn invalid_root_handle_fails_closed_without_term_store_indexing() {
    let mut exec = Executor::new();
    exec.ctx.assertions.push(TermId::new(u32::MAX - 1));

    let report = exec.add_finite_index_array_closure();

    assert_eq!(report.candidate_scan_truncated, 1);
    assert_eq!(report.candidate_equalities, 0);
    assert_eq!(report.candidate_selects, 0);
    assert!(!report.is_complete());
}

#[test]
fn malformed_discovery_index_entry_fails_closed_before_term_indexing() {
    let mut exec = Executor::new();
    let live = exec
        .ctx
        .terms
        .mk_var("malformed_discovery_index_live", Sort::Bool);
    let live_stamp = exec.ctx.terms.entry_stamp(live).expect("live term stamp");
    // A valid birth stamp attached to an invalid slot exercises the replay
    // authentication boundary directly. It must decline before `get` or
    // `sort` can index the invalid handle.
    exec.finite_array_expansion
        .discovered_candidates
        .push((TermId::new(u32::MAX - 1), live_stamp));

    let report = exec.add_finite_index_array_closure();

    assert_eq!(report.candidate_scan_truncated, 1);
    assert_eq!(report.candidate_equalities, 0);
    assert_eq!(report.candidate_selects, 0);
    assert!(!report.is_complete());
}

#[test]
fn malformed_select_signature_fails_closed() {
    let mut exec = Executor::new();
    let array = exec.ctx.terms.mk_var(
        "malformed_select_array",
        Sort::array(Sort::Bool, Sort::Bool),
    );
    let bad_index = exec.ctx.terms.mk_var("malformed_select_index", Sort::Int);
    let malformed = exec
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [array, bad_index], Sort::Bool);
    exec.ctx.assertions.push(malformed);

    let report = exec.add_finite_index_array_closure();

    assert_eq!(report.candidate_scan_truncated, 1);
    assert_eq!(report.candidate_selects, 0);
    assert_eq!(report.emitted_selects, 0);
    assert!(!report.is_complete());
}

#[test]
fn authored_binders_are_opaque_without_poisoning_ground_closure() {
    let mut exec = Executor::new();
    let body = exec
        .ctx
        .terms
        .mk_var("retained_quantifier_body", Sort::Bool);
    let quantified = exec
        .ctx
        .terms
        .mk_forall(vec![("i".to_owned(), Sort::Bool)], body);
    exec.ctx.assertions.push(quantified);

    let report = exec.add_finite_index_array_closure();

    assert!(report.is_complete());
    assert_eq!(report.candidate_scan_truncated, 0);
    assert_eq!(report.candidate_equalities, 0);
    assert_eq!(report.candidate_selects, 0);
}

#[test]
fn surviving_nonempty_let_fails_finite_array_scan_closed() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Bool);
    let value = exec
        .ctx
        .terms
        .mk_var("retained_let_value", array_sort.clone());
    let local = exec
        .ctx
        .terms
        .mk_var("retained_let_local", array_sort.clone());
    let other = exec.ctx.terms.mk_var("retained_let_other", array_sort);
    let body = exec.ctx.terms.mk_eq(local, other);
    let retained_let = exec
        .ctx
        .terms
        .mk_let(vec![("retained_let_local".to_owned(), value)], body);
    exec.ctx.assertions.push(retained_let);

    let report = exec.add_finite_index_array_closure();

    assert_eq!(report.candidate_scan_truncated, 1);
    assert!(!report.is_complete());
    assert!(exec.finite_array_expansion.candidate_scan_truncated);
}

#[test]
fn recursive_array_authorization_is_bounded_read_only_and_binder_conservative() {
    let mut exec = Executor::new();
    let nested_sort = Sort::array(Sort::Bool, Sort::array(Sort::bitvec(1), Sort::Int));
    let nested = exec
        .ctx
        .terms
        .mk_var("authorized_nested_array", nested_sort);
    let nodes_before = exec.finite_array_expansion.remaining_scan_nodes;
    let edges_before = exec.finite_array_expansion.remaining_scan_edges;
    assert!(exec.roots_have_only_recursively_finite_arrays(&[nested]));
    assert_eq!(
        exec.finite_array_expansion.remaining_scan_nodes,
        nodes_before
    );
    assert_eq!(
        exec.finite_array_expansion.remaining_scan_edges,
        edges_before
    );

    let wide_sort = Sort::array(Sort::bitvec(9), Sort::Bool);
    let wide = exec.ctx.terms.mk_var("nonfinite_wide_array", wide_sort);
    assert!(!exec.roots_have_only_recursively_finite_arrays(&[wide]));

    let binder_body = exec.ctx.terms.mk_var("opaque_auth_body", Sort::Bool);
    let binder = exec.ctx.terms.mk_exists(
        vec![("a".to_owned(), Sort::array(Sort::Bool, Sort::Bool))],
        binder_body,
    );
    assert!(!exec.roots_have_only_recursively_finite_arrays(&[binder]));
}

#[test]
fn array_valued_symbolic_select_queues_generated_equality_in_same_fixed_point() {
    let mut exec = Executor::new();
    let cell_sort = Sort::array(Sort::Bool, Sort::Bool);
    let outer_sort = Sort::array(Sort::Bool, cell_sort.clone());
    let outer = exec.ctx.terms.mk_var("symbolic_outer", outer_sort);
    let index = exec.ctx.terms.mk_var("symbolic_outer_index", Sort::Bool);
    let symbolic_cell = exec.ctx.terms.mk_select(outer, index);
    let observed_cell = exec.ctx.terms.mk_var("symbolic_observed_cell", cell_sort);
    let assertion = exec.ctx.terms.mk_eq(symbolic_cell, observed_cell);
    exec.ctx.assertions.push(assertion);
    let base_assertions = exec.ctx.assertions.len();

    let report = exec.add_finite_index_array_closure();

    assert!(
        report.is_complete(),
        "array-valued select closure: {report:?}"
    );
    assert_eq!(report.emitted_selects, 1);
    assert_eq!(
        report.emitted_equalities, 2,
        "the authored cell equality and the generated select/ITE equality must both close"
    );
    let cached = exec
        .finite_array_expansion
        .select_axioms
        .get(&symbolic_cell)
        .expect("symbolic select must retain its structural axiom");
    assert!(matches!(
        exec.ctx.terms.get(cached.axiom),
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2
    ));

    let points_after_first = exec.finite_array_expansion.remaining_index_points;
    exec.ctx.assertions.truncate(base_assertions);
    let replay = exec.add_finite_index_array_closure();
    assert!(replay.is_complete());
    assert_eq!(replay.emitted_selects, 0);
    assert_eq!(replay.emitted_equalities, 0);
    assert_eq!(replay.already_covered_selects, 1);
    assert_eq!(replay.already_covered_equalities, 2);
    assert_eq!(exec.ctx.assertions.len(), base_assertions + 3);
    assert_eq!(
        exec.finite_array_expansion.remaining_index_points, points_after_first,
        "cached fixed-point replay must not recharge exact expansion"
    );
}

#[test]
fn array_valued_store_cell_ite_queues_one_structural_equality() {
    let mut exec = Executor::new();
    let cell_sort = Sort::array(Sort::Bool, Sort::Bool);
    let outer_sort = Sort::array(Sort::Bool, cell_sort.clone());
    let base = exec
        .ctx
        .terms
        .mk_var("ite_cell_outer_base", outer_sort.clone());
    let rhs = exec.ctx.terms.mk_var("ite_cell_outer_rhs", outer_sort);
    let inner_a = exec.ctx.terms.mk_var("ite_cell_inner_a", cell_sort.clone());
    let inner_b = exec.ctx.terms.mk_var("ite_cell_inner_b", cell_sort);
    let condition = exec.ctx.terms.mk_var("ite_cell_condition", Sort::Bool);
    let inner_ite = exec.ctx.terms.mk_ite(condition, inner_a, inner_b);
    let true_index = exec.ctx.terms.mk_bool(true);
    let lhs = exec.ctx.terms.mk_store(base, true_index, inner_ite);
    let equality = exec.ctx.terms.mk_eq(lhs, rhs);
    exec.ctx.assertions.push(equality);

    let report = exec.add_finite_index_array_closure();

    assert!(report.is_complete(), "array-valued ITE cell: {report:?}");
    assert_eq!(
        report.emitted_equalities, 3,
        "outer equality plus its two array-valued cells must each be one obligation"
    );
    let structural_cell = exec
        .finite_array_expansion
        .equality_axioms
        .keys()
        .copied()
        .find(|&candidate| {
            matches!(
                exec.ctx.terms.get(candidate),
                TermData::App(Symbol::Named(name), args)
                    if name == "="
                        && args.len() == 2
                        && (args[0] == inner_ite || args[1] == inner_ite)
            )
        });
    assert!(
        structural_cell.is_some(),
        "the selected array-valued ITE must remain one cached equality candidate"
    );
}

#[test]
fn generic_skolem_extensionality_skips_recursively_finite_equalities() {
    let mut exec = Executor::new();
    let nested_sort = Sort::array(Sort::Bool, Sort::array(Sort::Bool, Sort::Bool));
    let lhs = exec
        .ctx
        .terms
        .mk_var("finite_skolem_lhs", nested_sort.clone());
    let rhs = exec.ctx.terms.mk_var("finite_skolem_rhs", nested_sort);
    let equality = exec.ctx.terms.mk_eq(lhs, rhs);
    let disequality = exec.ctx.terms.mk_not(equality);
    exec.ctx.assertions.push(disequality);

    let report = exec.add_finite_index_array_closure();
    assert!(report.is_complete());
    assert_eq!(report.emitted_equalities, 3);
    let assertions_after_exact = exec.ctx.assertions.len();

    exec.add_array_extensionality_axioms();

    assert_eq!(
        exec.ctx.assertions.len(),
        assertions_after_exact,
        "the exact three-obligation closure supersedes a generic difference Skolem"
    );
}

#[test]
fn generic_skolem_extensionality_covers_finite_equality_before_exact_closure() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Bool);
    let lhs = exec
        .ctx
        .terms
        .mk_var("finite_uncovered_skolem_lhs", array_sort.clone());
    let rhs = exec
        .ctx
        .terms
        .mk_var("finite_uncovered_skolem_rhs", array_sort);
    let equality = exec.ctx.terms.mk_eq(lhs, rhs);
    let disequality = exec.ctx.terms.mk_not(equality);
    exec.ctx.assertions.push(disequality);
    let assertions_before_generic = exec.ctx.assertions.len();

    exec.add_array_extensionality_axioms();

    assert!(
        exec.ctx.assertions.len() > assertions_before_generic,
        "an enumerable sort without active exact coverage still needs generic extensionality"
    );
}

#[test]
fn generic_skolem_extensionality_covers_budget_deferred_finite_equality() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Bool);
    let lhs = exec
        .ctx
        .terms
        .mk_var("finite_deferred_skolem_lhs", array_sort.clone());
    let rhs = exec
        .ctx
        .terms
        .mk_var("finite_deferred_skolem_rhs", array_sort);
    let equality = exec.ctx.terms.mk_eq(lhs, rhs);
    let disequality = exec.ctx.terms.mk_not(equality);
    exec.ctx.assertions.push(disequality);

    let report = exec.add_finite_index_array_extensionality_with_budget(0);
    assert_eq!(report.budget_deferred_equalities, 1);
    assert!(!report.is_complete());
    assert!(!exec
        .finite_array_expansion
        .covered_equalities
        .iter()
        .any(|(term, _)| *term == equality));
    let assertions_before_generic = exec.ctx.assertions.len();

    exec.add_array_extensionality_axioms();

    assert!(
        exec.ctx.assertions.len() > assertions_before_generic,
        "a budget-deferred exact candidate still needs generic extensionality"
    );
}
