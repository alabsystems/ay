// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::bv_cache::BvKeyMemo;
use crate::smt::context::{PersistentBvCache, MAX_PERSISTENT_CACHE_ENTRIES};
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_bv::BvSolver;
use ay_core::resource::enter_check_stop;
use ay_sat::{Literal, SatResult};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

fn state(ctx: &mut SmtContext, count: usize, width: u32) -> (ExprFeatures, CnfState, Vec<TermId>) {
    let mut variables = Vec::new();
    let mut roots = Vec::new();
    let mut features = None;
    for index in 0..count {
        let var = ChcExpr::var(ChcVar::new(
            format!("transient_{index}"),
            ChcSort::BitVec(width),
        ));
        let atom = ChcExpr::eq(var.clone(), ChcExpr::BitVec(1, width));
        features = Some(atom.scan_features());
        variables.push(ctx.convert_expr(&var));
        roots.push(ctx.convert_expr(&atom));
    }
    let mut sat = ay_sat::Solver::new(count);
    sat.set_preprocess_enabled(false);
    sat.set_unsat_certificate_enabled(false);
    for index in 0..count {
        sat.add_clause(vec![Literal::from_dimacs((index + 1) as i32)]);
    }
    let state = CnfState {
        term_to_var: roots
            .iter()
            .enumerate()
            .map(|(i, &term)| (term, (i + 1) as u32))
            .collect(),
        var_to_term: roots
            .iter()
            .enumerate()
            .map(|(i, &term)| ((i + 1) as u32, term))
            .collect(),
        num_vars: count as u32,
        sat,
        assumptions: None,
        assumption_map: None,
        bv_var_offset: 0,
        bv_term_to_bits: Default::default(),
        roots,
    };
    (features.expect("nonempty fixture"), state, variables)
}

fn offset(lit: i32, by: i32) -> i32 {
    if lit > 0 {
        lit + by
    } else {
        lit - by
    }
}

#[test]
#[serial_test::serial]
fn oversized_transient_circuit_keeps_sat_model_and_unsat_constraints() {
    let _scope = crate::smt::ScopedNoProgressBreaker::new();
    let mut ctx = SmtContext::new();
    let (features, mut state, variables) = state(&mut ctx, 2_000, 256);
    crate::smt::check_sat::reset_reuse_counters_for_tests();
    assert!(ctx.attach_bv_bitblasting(&features, &mut state));
    assert!(crate::smt::check_sat::bv_new_clause_count_for_tests() > MAX_PERSISTENT_CACHE_ENTRIES);
    assert_eq!(ctx.persistent_bv_cache.total_entries(), 0);
    assert!(ctx.persistent_bv_cache.keys.is_empty());
    let SatResult::Sat(model) = state.sat.solve().into_inner() else {
        panic!("complete oversized circuit must remain satisfiable");
    };
    for term in &variables {
        let bits = &state.bv_term_to_bits[term];
        assert_eq!(bits.len(), 256);
        for (bit, &lit) in bits.iter().enumerate() {
            let lit = offset(lit, state.bv_var_offset);
            let value = model[lit.unsigned_abs() as usize - 1] == (lit > 0);
            assert_eq!(value, bit == 0, "source word must equal one");
        }
    }
    let low_bit = state.bv_term_to_bits[&variables[0]][0];
    state.sat.add_clause(vec![Literal::from_dimacs(-offset(
        low_bit,
        state.bv_var_offset,
    ))]);
    assert!(matches!(
        state.sat.solve().into_inner(),
        SatResult::Unsat(_)
    ));
    assert!(!crate::smt::no_progress_breaker_tripped());
}

#[test]
fn combined_dimacs_layout_refuses_unrepresentable_circuits() {
    assert_eq!(checked_bv_layout(7, 11), Some((7, 18)));
    assert_eq!(
        checked_bv_layout(i32::MAX as u32 - 1, 1),
        Some((i32::MAX - 1, i32::MAX as u32))
    );
    assert_eq!(checked_bv_layout(i32::MAX as u32, 1), None);
    assert_eq!(checked_bv_layout(i32::MAX as u32 + 1, 0), None);
    assert_eq!(checked_bv_layout(u32::MAX, 1), None);
}

#[test]
fn exact_retention_boundary_counts_the_full_circuit_once_and_never_trips_queries() {
    let _scope = crate::smt::ScopedNoProgressBreaker::new();
    let mut ctx = SmtContext::new();
    let (_, state, _) = state(&mut ctx, 1, 8);
    let atom = state.roots[0];
    let mut solver = BvSolver::new(&ctx.terms);
    assert!(solver.bitblast_predicate(atom).is_some());
    let expected = solver.minted_entries_estimate();
    let mut cache = PersistentBvCache::default();
    let mut memo = BvKeyMemo::default();
    let signature = ctx.bv_cache_signature(&mut cache.keys, [atom], &mut memo);
    let clauses = solver.clauses().to_vec();
    ctx.capture_cached_bv_state_with_limit(
        &mut cache,
        &solver,
        signature,
        &mut memo,
        clauses.clone(),
        expected,
    );
    assert_eq!(
        cache.total_entries(),
        expected,
        "live clauses are not counted twice"
    );
    assert_eq!(solver.take_clauses(), clauses);
    for attempt in 0..10 {
        memo.clear();
        let signature = ctx.bv_cache_signature(&mut cache.keys, [atom], &mut memo);
        let limit = if attempt == 0 { expected } else { expected - 1 };
        ctx.capture_cached_bv_state_with_limit(
            &mut cache,
            &solver,
            signature,
            &mut memo,
            clauses.clone(),
            limit,
        );
        if attempt == 0 {
            assert_eq!(
                cache.total_entries(),
                expected,
                "drained circuit remains complete"
            );
        } else {
            assert_eq!(cache.total_entries(), 0);
            assert!(cache.keys.is_empty());
        }
        assert!(!crate::smt::no_progress_breaker_tripped());
        assert!(solver.encoding_complete());
    }
}

#[test]
fn refused_original_owner_cannot_publish_or_revive_a_retained_circuit() {
    let mut ctx = SmtContext::new();
    let (_, state, _) = state(&mut ctx, 1, 8);
    let atom = state.roots[0];
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&stopped);
    let scope = enter_check_stop(Arc::new(move || observed.load(Ordering::Relaxed)));
    let mut solver = BvSolver::new(&ctx.terms);
    assert!(solver.bitblast_predicate(atom).is_some());
    let clauses = solver.take_clauses();
    drop(scope);
    stopped.store(true, Ordering::Relaxed);
    let mut cache = PersistentBvCache::default();
    let mut memo = BvKeyMemo::default();
    for _ in 0..2 {
        memo.clear();
        let signature = ctx.bv_cache_signature(&mut cache.keys, [atom], &mut memo);
        ctx.capture_cached_bv_state_with_limit(
            &mut cache,
            &solver,
            signature,
            &mut memo,
            clauses.clone(),
            usize::MAX,
        );
        assert_eq!(cache.total_entries(), 0);
        assert!(cache.keys.is_empty());
        assert!(!solver.encoding_complete());
        stopped.store(false, Ordering::Relaxed);
    }
}
