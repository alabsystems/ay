// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pins for the pinned-slot retry in a solver that writes no proof
//! (#pinned-retry-no-proof): it has exactly the full retry's effect, it
//! no longer attempts the additions that cannot succeed, and a solver with
//! a proof output keeps the full retry.

use super::*;
use crate::literal::Variable;
use crate::ProofOutput;

const SUPPORT: usize = 0;
const TARGETS: [usize; 4] = [1, 2, 3, 4];
const NUM_VARS: usize = 5;

fn lit(var: usize) -> Literal {
    Literal::positive(Variable(var as u32))
}

fn assign_root(solver: &mut Solver, pos: usize, var: usize, reason: u32) {
    let l = lit(var);
    solver.var_data[var].level = 0;
    solver.var_data[var].trail_pos = pos as u32;
    solver.var_data[var].reason = reason;
    solver.vals[l.index()] = 1;
    solver.vals[l.negated().index()] = -1;
}

/// A root trail `s, t1..t4`: `s` is a reasonless root assignment with no
/// proof id, and each `t` is implied by the binary reason `t ∨ ¬s`, so no
/// `t` can be materialized and every one is pinned.
fn pinned_root_trail(mut solver: Solver) -> Solver {
    let mut reasons = Vec::new();
    for &t in &TARGETS {
        let idx = solver.add_clause_db(&[lit(t), lit(SUPPORT).negated()], false);
        assert_ne!(solver.clause_id(ClauseRef(idx as u32)), 0);
        reasons.push(idx as u32);
    }
    solver.trail = std::iter::once(SUPPORT).chain(TARGETS).map(lit).collect();
    solver.trail_lim = vec![];
    assign_root(&mut solver, 0, SUPPORT, NO_REASON);
    for (pos, (&t, &reason)) in TARGETS.iter().zip(&reasons).enumerate() {
        assign_root(&mut solver, pos + 1, t, reason);
    }
    solver
}

/// A clause-trace solver (LRAT ids, no proof manager) with an armed #A2b
/// meter, so the waste charge is compared too.
fn trace_solver() -> Solver {
    let mut solver = Solver::new(NUM_VARS);
    solver.enable_clause_trace();
    solver.set_proof_bookkeeping_budget(Some(1_000_000));
    assert!(solver.cold.lrat_enabled && solver.proof_manager.is_none());
    pinned_root_trail(solver)
}

/// Everything a retry may change, apart from diagnostic counters.
#[derive(Debug, PartialEq, Eq)]
struct Observed {
    pinned: Vec<usize>,
    cursor: usize,
    level0_ids: Vec<(u64, i8)>,
    unit_ids: Vec<(u64, i8)>,
    budget: Option<u64>,
    completed: bool,
}

fn observe(solver: &Solver, completed: bool) -> Observed {
    let pair = |ids: &[u64], signs: &[i8], v: usize| (ids[v], signs[v]);
    Observed {
        pinned: solver.cold.lrat_level0_unit_materialize_pinned.clone(),
        cursor: solver.cold.lrat_level0_unit_materialize_cursor,
        level0_ids: (0..NUM_VARS)
            .map(|v| {
                pair(
                    &solver.cold.level0_proof_id,
                    &solver.cold.level0_proof_sign,
                    v,
                )
            })
            .collect(),
        unit_ids: (0..NUM_VARS)
            .map(|v| pair(&solver.unit_proof_id, &solver.unit_proof_sign, v))
            .collect(),
        budget: solver.cold.proof_bookkeeping_budget,
        completed,
    }
}

/// The three materializer entries, each followed by an observation.
fn materialize_all(solver: &mut Solver) -> Vec<Observed> {
    solver.materialize_level0_unit_proofs();
    let first = observe(solver, true);
    solver.materialize_level0_minimize_unit_proofs();
    let second = observe(solver, true);
    let completed = solver.materialize_level0_unit_proofs_interruptible();
    vec![first, second, observe(solver, completed)]
}

/// One step of the differential script: a state change, then all three
/// materializers. Every branch of the retry is reached: a slot that stays
/// pinned with an incomplete chain, one that leaves because it gained a
/// proof id, one whose reason became a unit clause, one that leaves because
/// it lost its reason, and one whose chain is complete but whose derived
/// emission cannot succeed.
fn script(solver: &mut Solver) -> Vec<Vec<Observed>> {
    let mut seen = vec![materialize_all(solver), materialize_all(solver)];
    let first_reason = solver.var_data[TARGETS[0]].reason;
    let first_id = solver.clause_id(ClauseRef(first_reason));
    solver.record_level0_proof_id_for_lit(lit(TARGETS[0]), first_id);
    seen.push(materialize_all(solver));
    let unit_idx = solver.add_clause_db(&[lit(TARGETS[1])], false);
    solver.var_data[TARGETS[1]].reason = unit_idx as u32;
    seen.push(materialize_all(solver));
    solver.var_data[TARGETS[2]].reason = NO_REASON;
    seen.push(materialize_all(solver));
    let support_idx = solver.add_clause_db(&[lit(SUPPORT)], false);
    let support_id = solver.clause_id(ClauseRef(support_idx as u32));
    solver.record_unit_proof_id_for_lit(lit(SUPPORT), support_id);
    seen.push(materialize_all(solver));
    seen.push(materialize_all(solver));
    seen
}

/// The short retry has exactly the full retry's effect on every branch:
/// the same pinned list, cursor, recorded proof ids, waste charge and return
/// value after every call of every materializer.
#[test]
fn the_short_retry_has_the_full_retrys_effect() {
    let mut short = trace_solver();
    let mut full = trace_solver();
    let short_seen = script(&mut short);
    let full_seen = with_full_pinned_retry(|| script(&mut full));
    assert_eq!(short_seen, full_seen);

    // Anti-vacuity: the script reached the retry's branches.
    let last = short_seen
        .last()
        .and_then(|step| step.last())
        .expect("steps");
    assert_eq!(last.pinned, vec![4], "only the complete-chain slot stays");
    // A slot whose reason became a unit clause leaves the list: its proof id
    // now resolves through that unit reason (`level0_var_proof_id`'s unit
    // fallback, checked before the record-only branch).
    let unit_reason_id = short.clause_id(ClauseRef(short.var_data[TARGETS[1]].reason));
    assert_ne!(unit_reason_id, 0);
    assert_eq!(short.level0_var_proof_id(TARGETS[1]), Some(unit_reason_id));
    assert_eq!(
        short_seen[3][0].pinned,
        vec![3, 4],
        "the gained id and the unit reason"
    );
    assert_eq!(short_seen[4][0].pinned, vec![4], "the lost reason");
    let first = &short_seen[1][0];
    assert_eq!(first.pinned, vec![1, 2, 3, 4], "every target was pinned");
    assert!(
        matches!(first.budget, Some(left) if left < 1_000_000),
        "the waste charge fired, so it was compared"
    );
}

fn proof_adds(solver: &Solver) -> u64 {
    solver
        .proof_add_profile()
        .into_iter()
        .filter(|(name, _)| name.starts_with("sat.proof_adds_"))
        .map(|(_, count)| count)
        .sum()
}

/// In a solver that writes no proof, a retry attempts no addition: only the
/// first, fresh visit of each slot does. The full retry attempted one per
/// pinned slot per call (the trusted-transform fallback, always 0), which is
/// what made `fac28`'s step-(3) BV lane spend 16-18 s re-walking about 1465
/// slots.
#[test]
fn a_retry_in_a_solver_that_writes_no_proof_attempts_no_addition() {
    let mut short = trace_solver();
    let before = proof_adds(&short);
    short.materialize_level0_unit_proofs();
    let after_fresh = proof_adds(&short);
    assert_eq!(
        after_fresh - before,
        TARGETS.len() as u64,
        "one attempt per fresh slot"
    );
    for _ in 0..10 {
        short.materialize_level0_unit_proofs();
        short.materialize_level0_minimize_unit_proofs();
    }
    assert_eq!(proof_adds(&short), after_fresh);
    assert_eq!(
        short.cold.lrat_level0_unit_materialize_pinned.len(),
        TARGETS.len()
    );

    let mut full = trace_solver();
    let before = proof_adds(&full);
    with_full_pinned_retry(|| {
        full.materialize_level0_unit_proofs();
        full.materialize_level0_unit_proofs();
    });
    assert_eq!(
        proof_adds(&full) - before,
        2 * TARGETS.len() as u64,
        "the full retry attempts every pinned slot again"
    );
}

/// The stay-pinned memo has exactly the unmemoized short retry's effect:
/// same pinned list, cursor, recorded proof ids, waste charge and return
/// value after every call of every materializer, across the same script
/// that reaches every retry branch — including the steps that must defeat
/// the memo (a recorded proof id, a reason becoming a unit clause, a lost
/// reason), so a stale memo would diverge here.
#[test]
fn the_stay_pinned_memo_has_the_unmemoized_retrys_effect() {
    let mut memoized = trace_solver();
    let mut plain = trace_solver();
    let memoized_seen = script(&mut memoized);
    let plain_seen = with_pin_memo_disabled(|| script(&mut plain));
    assert_eq!(memoized_seen, plain_seen);

    // Anti-vacuity: the memo actually engaged for the slots that stay
    // pinned, and the slot the script resolves ends with no memo.
    let last_pinned = memoized_seen
        .last()
        .and_then(|step| step.last())
        .expect("steps")
        .pinned
        .clone();
    assert_eq!(last_pinned, vec![4]);
    let still_pinned_var = TARGETS[3];
    assert_ne!(
        memoized.cold.lrat_pin_retry_memo_fingerprint[still_pinned_var], 0,
        "the permanently pinned slot carries a memo"
    );
    assert_eq!(
        memoized.cold.lrat_pin_retry_memo_fingerprint[TARGETS[0]], 0,
        "the slot that gained a proof id has no memo"
    );
}

/// NEGATIVE TWIN: with a proof output a retry can succeed, so it stays the
/// full retry. Once the support gains a visible unit id, the pinned targets
/// are materialized as visible derived units on the next call.
#[test]
fn a_solver_with_a_proof_output_keeps_the_full_retry() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver = pinned_root_trail(Solver::with_proof_output(NUM_VARS, proof));
    assert!(!solver.level0_retry_writes_no_proof());
    solver.materialize_level0_unit_proofs();
    assert_eq!(
        solver.cold.lrat_level0_unit_materialize_pinned.len(),
        TARGETS.len()
    );
    let support_idx = solver.add_clause_db(&[lit(SUPPORT)], false);
    let support_id = solver.clause_id(ClauseRef(support_idx as u32));
    solver.record_unit_proof_id_for_lit(lit(SUPPORT), support_id);
    solver.materialize_level0_unit_proofs();
    assert_eq!(solver.cold.lrat_level0_unit_materialize_pinned.len(), 0);
    for &t in &TARGETS {
        let id = solver.level0_var_proof_id(t).expect("materialized");
        assert!(solver.lrat_hint_id_visible(id));
    }
    assert_eq!(
        solver
            .lrat_materialization_stats()
            .materialize_emitted_unit_lines,
        TARGETS.len() as u64
    );
}
