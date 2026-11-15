// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::sort::Sort;

fn estimate(expr: Expr, cap: usize) -> usize {
    let mut program = AYProgram::new();
    program.assert(expr);
    program.serialized_node_estimate(cap)
}

fn boolean_dag(depth: usize) -> Expr {
    let variable = Expr::var("x", Sort::bool());
    let mut node = variable.clone();
    for _ in 0..depth {
        node = Expr::ite(variable.clone(), node.clone(), node);
    }
    node
}

#[test]
fn separate_commands_and_rule_roots_count_separate_sharing_regions() {
    let value = Expr::var("x", Sort::bool()).eq(Expr::bool_const(true));
    assert_eq!(estimate(value.clone(), 100), 3);
    let mut program = AYProgram::new();
    program.assert(value.clone());
    program.assert(value.clone());
    assert_eq!(program.serialized_node_estimate(100), 6);
    program.commands.push(Constraint::Rule {
        head: Some(value.clone()),
        body: value,
    });
    assert_eq!(program.serialized_node_estimate(100), 12);
    assert_eq!(program.serialized_node_estimate(7), 7);
}

#[test]
fn reused_arcs_below_distinct_binders_are_counted_in_each_region() {
    let value = Expr::var("x", Sort::bool());
    let forall = Expr::forall(vec![("i".into(), Sort::bool())], value.clone());
    let exists = Expr::exists(vec![("j".into(), Sort::bool())], value.clone());
    assert_eq!(estimate(value.clone().and(forall), 100), 4);
    let forall = Expr::forall(vec![("i".into(), Sort::bool())], value);
    assert_eq!(estimate(forall.and(exists), 100), 5);
}

#[test]
fn repeated_whole_quantifiers_have_memoized_scope_costs() {
    let mut node = Expr::var("x", Sort::bool());
    for index in 0..40 {
        node = Expr::forall(
            vec![(format!("i_{index}"), Sort::bool())],
            node.clone().and(node),
        );
    }
    // Each layer adds a forall plus an and. The repeated entire inner forall
    // can be shared at the enclosing matrix without expanding its body twice.
    assert_eq!(estimate(node.clone(), usize::MAX), 81);
    assert_eq!(estimate(node.clone(), 30), 30);
    assert_eq!(estimate(node, 0), 0);
}

#[test]
fn plain_patterns_saturate_without_unfolding_their_exponential_tree() {
    let pattern = boolean_dag(40);
    let quantified = Expr::forall_with_triggers(
        vec![("x".into(), Sort::bool())],
        Expr::bool_const(true),
        vec![vec![pattern]],
    );
    assert_eq!(estimate(quantified.clone(), 1_000_000), 1_000_000);
    assert_eq!(estimate(quantified, 0), 0);
}

#[test]
fn plain_assumptions_and_shared_get_value_have_different_costs() {
    let value = boolean_dag(40);
    let mut program = AYProgram::new();
    program
        .commands
        .push(Constraint::GetValue(vec![value.clone(), value.clone()]));
    assert_eq!(program.serialized_node_estimate(1_000_000), 82);
    program
        .commands
        .push(Constraint::CheckSatAssuming(vec![value]));
    assert_eq!(program.serialized_node_estimate(1_000_000), 1_000_000);
}

#[test]
fn an_empty_program_and_zero_budget_have_zero_cost() {
    assert_eq!(AYProgram::new().serialized_node_estimate(usize::MAX), 0);
    assert_eq!(estimate(boolean_dag(40), 0), 0);
}
