// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::resource::enter_check_stop;
use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc,
};

fn state(ctx: &mut SmtContext) -> (ExprFeatures, CnfState) {
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(128)));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(128)));
    let product = ChcExpr::Op(ChcOp::BvMul, vec![Arc::new(x.clone()), Arc::new(y)]);
    let expression = ChcExpr::eq(product, x);
    let term = ctx.convert_expr(&expression);
    (
        expression.scan_features(),
        CnfState {
            term_to_var: [(term, 1)].into_iter().collect(),
            var_to_term: [(1, term)].into_iter().collect(),
            num_vars: 1,
            sat: ay_sat::Solver::new(1),
            assumptions: None,
            assumption_map: None,
            bv_var_offset: 0,
            bv_term_to_bits: Default::default(),
            roots: vec![term],
        },
    )
}

#[test]
fn independently_stopped_owner_refuses_before_cache_or_cnf_admission() {
    let mut ctx = SmtContext::new();
    let (features, mut state) = state(&mut ctx);
    let old_vars = state.sat.total_num_vars();
    let _scope = enter_check_stop(Arc::new(|| true));
    assert!(!ctx.attach_bv_bitblasting(&features, &mut state));
    assert_eq!(state.sat.total_num_vars(), old_vars);
    assert!(state.bv_term_to_bits.is_empty());
    assert_eq!(ctx.persistent_bv_cache.total_entries(), 0);
}

#[test]
fn mid_single_predicate_stop_does_not_publish_partial_persistent_cache() {
    let mut ctx = SmtContext::new();
    let (features, mut state) = state(&mut ctx);
    let count = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&count);
    let _scope = enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::Relaxed) >= 39
    }));
    assert!(!ctx.attach_bv_bitblasting(&features, &mut state));
    assert_eq!(count.load(Ordering::Relaxed), 40);
    assert!(state.bv_term_to_bits.is_empty());
    assert_eq!(ctx.persistent_bv_cache.total_entries(), 0);
}

#[test]
fn lane_raw_stop_is_used_even_when_lane_token_is_healthy() {
    let mut ctx = SmtContext::new();
    let (features, mut state) = state(&mut ctx);
    let raw = Arc::new(AtomicBool::new(true));
    let token = crate::CancellationToken::new();
    let _lane = crate::smt::deadline::ScopedLaneCancellation::install(
        token.clone(),
        Some(Arc::clone(&raw)),
    );
    assert!(!ctx.attach_bv_bitblasting(&features, &mut state));
    assert!(!token.is_cancelled());
    assert!(state.bv_term_to_bits.is_empty());
    assert_eq!(ctx.persistent_bv_cache.total_entries(), 0);
    assert!(raw.load(Ordering::Relaxed));
}

#[test]
fn healthy_cache_reuse_under_a_new_original_scope_does_not_keep_old_callbacks() {
    use crate::smt::deadline::ScopedSmtDeadline;
    let mut ctx = SmtContext::new();
    let (features, mut first_state) = state(&mut ctx);
    let old_end = ay_core::time::Instant::now() + std::time::Duration::from_secs(20);
    let wall = ScopedSmtDeadline::install_until(old_end);
    let old_flag = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&old_flag);
    let first = enter_check_stop(Arc::new(move || {
        observed.load(Ordering::Relaxed) || ay_core::time::Instant::now() >= old_end
    }));
    assert!(ctx.attach_bv_bitblasting(&features, &mut first_state));
    assert!(ctx.persistent_bv_cache.total_entries() > 0);
    drop(first);
    drop(wall);
    old_flag.store(true, Ordering::Relaxed);
    let new_end = ay_core::time::Instant::now() + std::time::Duration::from_secs(20);
    let _wall = ScopedSmtDeadline::install_until(new_end);
    let _second = enter_check_stop(Arc::new(move || ay_core::time::Instant::now() >= new_end));
    let (features, mut next_state) = state(&mut ctx);
    assert!(ctx.attach_bv_bitblasting(&features, &mut next_state));
    assert!(!next_state.bv_term_to_bits.is_empty());
    assert!(ctx.persistent_bv_cache.total_entries() > 0);
}
