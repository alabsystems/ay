// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn fixture() -> (ChcExpr, Vec<ChcVar>) {
    let memory = array("memory", ChcSort::BitVec(1), ChcSort::BitVec(2));
    let local = var("local", 2);
    let value = var("value", 2);
    let formula = op(
        ChcOp::And,
        vec![
            eq(expr(&local), expr(&value)),
            eq(expr(&memory), constant(ChcSort::BitVec(1), expr(&local))),
        ],
    );
    (formula, vec![memory, value])
}

#[test]
fn every_array_admission_rewrite_and_export_poll_can_stop_without_candidate() {
    let (formula, keep) = fixture();
    super::super::resources::assert_poll_boundaries(&formula, &keep);
}

#[test]
fn array_sort_nodes_defaults_and_export_share_one_growth_work_ledger() {
    let (formula, keep) = fixture();
    super::super::resources::assert_numeric_boundaries(&formula, &keep);
}

#[test]
fn alternatives_cannot_restart_an_exhausted_array_scope() {
    let (formula, keep) = fixture();
    let alternatives = op(ChcOp::Or, vec![formula.clone(), formula]);
    let mut scope = Scope::new(
        Limits {
            branches: 1,
            ..Limits::default()
        },
        &|| true,
    );
    assert!(matches!(
        run(&alternatives, &keep, &mut scope),
        Projection::Stopped
    ));
    let remaining = scope.remaining;
    assert!(matches!(
        run(&ChcExpr::Bool(true), &keep, &mut scope),
        Projection::Stopped
    ));
    assert_eq!(scope.remaining.work, remaining.work);
    assert_eq!(scope.remaining.growth, remaining.growth);
}
