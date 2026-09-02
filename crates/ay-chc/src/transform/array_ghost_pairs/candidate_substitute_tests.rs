// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use serial_test::serial;

use super::*;

fn future() -> Instant {
    Instant::now() + Duration::from_secs(5)
}

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

fn repeated_candidate(formal: &ChcVar) -> ChcExpr {
    let first = ChcExpr::eq(ChcExpr::var(formal.clone()), ChcExpr::Int(0));
    let second = ChcExpr::gt(ChcExpr::var(formal.clone()), ChcExpr::Int(1));
    ChcExpr::Op(ChcOp::And, vec![Arc::new(first), Arc::new(second)])
}

#[test]
fn exact_count_charges_each_occurrence_but_shares_actual_root() {
    let formal = int_var("x");
    let left = ChcExpr::var(int_var("left"));
    let right = ChcExpr::var(int_var("right"));
    let actual = ChcExpr::add(left, right);
    let cancellation = CancellationToken::new();

    let substituted = exact_substitute_scalar_candidate(
        &repeated_candidate(&formal),
        std::slice::from_ref(&formal),
        std::slice::from_ref(&actual),
        &cancellation,
        future(),
        11,
    )
    .expect("eleven-node expanded result fits exactly");
    assert_eq!(substituted.expanded_nodes, 11);
    assert_eq!(substituted.formula.node_count(usize::MAX), 11);

    let ChcExpr::Op(ChcOp::And, conjuncts) = &substituted.formula else {
        panic!("expected conjunction");
    };
    let ChcExpr::Op(_, first_args) = conjuncts[0].as_ref() else {
        panic!("expected first comparison");
    };
    let ChcExpr::Op(_, second_args) = conjuncts[1].as_ref() else {
        panic!("expected second comparison");
    };
    assert!(
        Arc::ptr_eq(&first_args[0], &second_args[0]),
        "repeated actual roots must share storage"
    );

    assert!(exact_substitute_scalar_candidate(
        &repeated_candidate(&formal),
        std::slice::from_ref(&formal),
        std::slice::from_ref(&actual),
        &cancellation,
        future(),
        10,
    )
    .is_none());
}

#[test]
fn rejects_unmapped_formals_sort_mismatches_and_unsupported_templates() {
    let formal = int_var("x");
    let cancellation = CancellationToken::new();
    assert!(exact_substitute_scalar_candidate(
        &ChcExpr::eq(ChcExpr::var(formal.clone()), ChcExpr::Int(0)),
        &[],
        &[],
        &cancellation,
        future(),
        32,
    )
    .is_none());

    assert!(exact_substitute_scalar_candidate(
        &ChcExpr::eq(ChcExpr::var(formal.clone()), ChcExpr::Int(0)),
        std::slice::from_ref(&formal),
        &[ChcExpr::Bool(false)],
        &cancellation,
        future(),
        32,
    )
    .is_none());

    let unsupported = ChcExpr::FuncApp("f".to_string(), ChcSort::Bool, Vec::new());
    assert!(
        exact_substitute_scalar_candidate(&unsupported, &[], &[], &cancellation, future(), 32,)
            .is_none()
    );
}

#[test]
fn permits_unused_array_formals_from_the_full_raw_signature() {
    let key_sort = ChcSort::BitVec(32);
    let value_sort = ChcSort::BitVec(8);
    let array_sort = ChcSort::Array(Box::new(key_sort.clone()), Box::new(value_sort));
    let array_formal = ChcVar::new("memory", array_sort);
    let scalar_formal = int_var("count");
    let formula = ChcExpr::eq(ChcExpr::var(scalar_formal.clone()), ChcExpr::Int(0));
    let array_actual = ChcExpr::const_array(key_sort, ChcExpr::BitVec(0, 8));
    let scalar_actual = ChcExpr::var(int_var("actual_count"));

    let substituted = exact_substitute_scalar_candidate(
        &formula,
        &[array_formal, scalar_formal],
        &[array_actual, scalar_actual.clone()],
        &CancellationToken::new(),
        future(),
        3,
    )
    .expect("unused array formal must not disqualify a scalar candidate");
    assert_eq!(substituted.expanded_nodes, 3);
    assert_eq!(
        substituted.formula,
        ChcExpr::eq(scalar_actual, ChcExpr::Int(0))
    );
}

#[test]
fn cancellation_and_deadline_fail_closed() {
    let cancellation = CancellationToken::new();
    cancellation.cancel();
    assert!(exact_substitute_scalar_candidate(
        &ChcExpr::Bool(true),
        &[],
        &[],
        &cancellation,
        future(),
        1,
    )
    .is_none());

    assert!(exact_substitute_scalar_candidate(
        &ChcExpr::Bool(true),
        &[],
        &[],
        &CancellationToken::new(),
        Instant::now(),
        1,
    )
    .is_none());
}

struct GlobalMemoryGuard;

impl Drop for GlobalMemoryGuard {
    fn drop(&mut self) {
        TermStore::reset_process_memory_limit_for_testing();
    }
}

#[test]
#[serial(global_term_memory)]
fn global_memory_pressure_fails_closed() {
    TermStore::force_process_memory_exceeded_for_testing();
    let _guard = GlobalMemoryGuard;
    assert!(exact_substitute_scalar_candidate(
        &ChcExpr::Bool(true),
        &[],
        &[],
        &CancellationToken::new(),
        future(),
        1,
    )
    .is_none());
}
