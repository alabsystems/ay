// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmissionError};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

mod controls;

fn owner(work: u64, storage: usize) -> CountedAdmission {
    let _ = ay_core::misc_cli_flags();
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, storage),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

fn lit(variable: u32, negative: bool) -> Literal {
    Literal(variable * 2 + u32::from(negative))
}

fn construct(
    n: usize,
    rows: &[&[Literal]],
    owner: CountedAdmission,
) -> Result<CountedInitialSolver> {
    CountedInitialCnf::try_new(n, rows, owner)?.construct()
}

// Semantic differential only, not evidence that the complete solve is paid.
// Production ownership deliberately provides no equivalent mutable escape.
fn solve_for_semantics(mut loaded: CountedInitialSolver) -> SolverSatResult {
    loaded.solver.solve()
}

#[test]
fn real_constructor_installs_originals_ids_and_binary_watches() {
    let rows = [
        &[lit(0, false), lit(1, false)][..],
        &[lit(0, true), lit(1, false)][..],
    ];
    let original = owner(10_000_000, 10_000_000);
    let built = construct(2, &rows, original.clone()).unwrap();
    assert_eq!(built.solver.arena.num_clauses(), 2);
    assert_eq!(built.solver.cold.original_ledger.num_clauses(), 2);
    assert_eq!(built.solver.cold.original_ledger.clause_ids(), &[1, 2]);
    assert_eq!(built.solver.watches.len_of(lit(1, false)), 2);
    assert_eq!(built.initial_assigned_variables().unwrap(), 0);
    assert!(!built.initial_conflict().unwrap());
    assert!(original.usage().unwrap().storage_admitted > 0);
}

#[test]
fn real_constructor_preserves_variable_buffers_and_clause_id_capacity_policy() {
    for n in [0, 1, 3, 17] {
        let original = owner(10_000_000, 10_000_000);
        let counted = Solver::build_with_hint(
            n,
            None,
            Some(13),
            &super::super::construction::Counted(&original),
        )
        .unwrap();
        let ordinary = Solver::with_clause_hint(n, 13);
        assert_eq!(counted.vals, ordinary.vals);
        assert_eq!(counted.vals.capacity(), ordinary.vals.capacity());
        assert_eq!(counted.phase.capacity(), ordinary.phase.capacity());
        assert_eq!(counted.cold.e2i, ordinary.cold.e2i);
        assert_eq!(counted.cold.i2e, ordinary.cold.i2e);
        assert_eq!(
            counted.cold.clause_ids_reserve_hint,
            ordinary.cold.clause_ids_reserve_hint
        );
        assert_eq!(counted.arena.memory_bytes(), ordinary.arena.memory_bytes());
    }
}

#[test]
fn actual_cdcl_engine_returns_nonvacuous_positive_and_negative_results() {
    let positive = [
        &[lit(0, false), lit(1, false)][..],
        &[lit(0, true), lit(1, false)][..],
        &[lit(0, false), lit(1, true)][..],
    ];
    let sat = construct(2, &positive, owner(100_000_000, 100_000_000)).unwrap();
    assert_eq!(sat.initial_assigned_variables().unwrap(), 0);
    let result = solve_for_semantics(sat);
    assert_eq!(result.model(), Some(&[true, true][..]));
    let negative = [
        positive[0],
        positive[1],
        positive[2],
        &[lit(0, true), lit(1, true)],
    ];
    let unsat = construct(2, &negative, owner(100_000_000, 100_000_000)).unwrap();
    assert!(!unsat.initial_conflict().unwrap());
    assert!(solve_for_semantics(unsat).is_unsat());
}

#[test]
fn admitted_exact_watch_build_preserves_normal_binary_long_order_and_capacity() {
    let rows = [
        &[lit(0, false), lit(1, false)][..],
        &[lit(0, false), lit(2, false), lit(3, false)][..],
        &[lit(0, false), lit(3, false), lit(4, false)][..],
        &[lit(0, false), lit(4, false)][..],
        &[lit(0, false), lit(5, false)][..],
    ];
    let built = construct(6, &rows, owner(10_000_000, 10_000_000)).unwrap();
    let mut ordinary = Solver::with_clause_hint(6, rows.len());
    for clause in rows {
        ordinary.add_clause(clause.to_vec());
    }
    ordinary.initialize_watches();
    assert_eq!(
        built.solver.watches.heap_bytes(),
        ordinary.watches.heap_bytes()
    );
    for index in 0..12 {
        let literal = Literal(index);
        let len = ordinary.watches.len_of(literal);
        assert_eq!(built.solver.watches.len_of(literal), len);
        for watch in 0..len {
            assert_eq!(
                built.solver.watches.entry_raw(literal, watch),
                ordinary.watches.entry_raw(literal, watch)
            );
        }
    }
}

#[test]
fn original_units_drive_real_binary_and_long_clause_propagation() {
    let rows = [
        &[lit(0, false)][..],
        &[lit(0, true), lit(1, false)][..],
        &[lit(0, true), lit(1, true), lit(2, false)][..],
        &[lit(2, true), lit(3, false)][..],
    ];
    let built = construct(4, &rows, owner(10_000_000, 10_000_000)).unwrap();
    assert_eq!(built.initial_assigned_variables().unwrap(), 4);
    assert!(!built.initial_conflict().unwrap());
    assert_eq!(built.solver.vals, [1, -1, 1, -1, 1, -1, 1, -1]);
    assert_eq!(built.solver.trail.len(), built.solver.qhead);
    assert!(solve_for_semantics(built).is_sat());
}

#[test]
fn real_root_conflict_is_not_confused_with_refusal() {
    let rows = [
        &[lit(0, false)][..],
        &[lit(0, true), lit(1, false)][..],
        &[lit(1, true)][..],
    ];
    let original = owner(10_000_000, 10_000_000);
    let built = construct(2, &rows, original.clone()).unwrap();
    assert!(built.initial_conflict().unwrap());
    assert_eq!(original.usage().unwrap().refusal, None);
    assert!(solve_for_semantics(built).is_unsat());
}

#[test]
fn empty_and_tautological_authored_rows_remain_exact() {
    let raw = [lit(1, false), lit(0, false), lit(1, false)];
    let tautology = [lit(0, false), lit(0, true)];
    let rows = [&raw[..], &tautology[..], &[]];
    let built = construct(2, &rows, owner(10_000_000, 10_000_000)).unwrap();
    assert_eq!(built.input.clause(0).unwrap().unwrap().original(), &raw);
    assert_eq!(
        built.input.clause(1).unwrap().unwrap().original(),
        &tautology
    );
    assert_eq!(built.solver.cold.original_ledger.clause_ids(), &[1, 2]);
    assert_eq!(built.solver.arena.num_clauses(), 1);
    assert!(built.initial_conflict().unwrap());
    assert!(solve_for_semantics(built).is_unsat());
}

#[test]
fn long_implication_chain_is_paid_and_actually_propagated() {
    let n = 2049;
    let mut clauses = vec![vec![lit(0, false)]];
    for variable in 1..n {
        clauses.push(vec![lit(variable - 1, true), lit(variable, false)]);
    }
    let views: Vec<_> = clauses.iter().map(Vec::as_slice).collect();
    let built = construct(n as usize, &views, owner(100_000_000, 100_000_000)).unwrap();
    assert_eq!(built.initial_assigned_variables().unwrap(), n as usize);
    assert_eq!(built.solver.qhead, n as usize);
    assert!(!built.initial_conflict().unwrap());
}
