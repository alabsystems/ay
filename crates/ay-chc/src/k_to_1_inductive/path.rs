// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One-proof k-inductive → 1-inductive conversion by path interpolation.
//!
//! CHC-COMP 2026 Workstream D, Rung 1 (the development design notes
//! DESIGN_lra_interp_tpa.md` at `9598c4206`, §4.1, contract **C-P1**). **Owner: WP-D1-P.**
//! Rung 1 calls it only from IMC; `convert_with_timeout` is unchanged.

use crate::interpolant_validation::is_unsat_result;
use crate::interpolation::proof_groups::{
    proof_check_groups, ItpRecipe, ProofCheck, ValidatePolicy, DEFAULT_DAG_CAPS,
};
use crate::interpolation::proof_script::dag_var_names;
use crate::interpolation::stats::{EngineTag, ScopedEngineTag};
use crate::smt::SmtContext;
use crate::transition_system::TransitionSystem;
use crate::ChcExpr;
use ay_core::time::Instant;
use std::sync::atomic::{AtomicUsize, Ordering};

/// `convert_path` calls, inputs refused for non-state variables, candidates
/// served (self-validated).
static CALLS: AtomicUsize = AtomicUsize::new(0);
static NON_STATE_INPUT: AtomicUsize = AtomicUsize::new(0);
static SERVED: AtomicUsize = AtomicUsize::new(0);

/// Snapshot `(calls, non_state_input, served)`.
pub(crate) fn convert_path_stats() -> (usize, usize, usize) {
    (
        CALLS.load(Ordering::Relaxed),
        NON_STATE_INPUT.load(Ordering::Relaxed),
        SERVED.load(Ordering::Relaxed),
    )
}

fn trace(event: &str, k: usize) {
    if ay_core::misc_cli_flags().chc_proof_itp_stats {
        let (calls, non_state, served) = convert_path_stats();
        safe_eprintln!(
            "[K-TO-1-PATH] {event} k={k} calls={calls} non_state_input={non_state} served={served}"
        );
    }
}

/// `UNSAT(query)` on the Verification lane within the deadline.
fn unsat_by(query: &ChcExpr, deadline: Instant) -> bool {
    let remaining = deadline.saturating_duration_since(Instant::now());
    if remaining.is_zero() {
        return false;
    }
    let mut ctx = SmtContext::new();
    is_unsat_result(&ctx.check_sat_with_timeout(query, remaining))
}

/// `init ⇒ c`, `c ∧ T ⇒ c'` and `c ⇒ k_inv`, each on `SmtContext::new()`.
fn self_validate(c: &ChcExpr, k_inv: &ChcExpr, ts: &TransitionSystem, deadline: Instant) -> bool {
    let init_implies = ChcExpr::and_vec(vec![ts.init.clone(), ChcExpr::not(c.clone())]);
    if !unsat_by(&init_implies, deadline) {
        return false;
    }
    let c_next = TransitionSystem::version_expr(c, ts.state_vars(), 1);
    let inductive = ChcExpr::and_vec(vec![c.clone(), ts.transition_at(0), ChcExpr::not(c_next)]);
    if !unsat_by(&inductive, deadline) {
        return false;
    }
    let strengthens = ChcExpr::and_vec(vec![c.clone(), ChcExpr::not(k_inv.clone())]);
    unsat_by(&strengthens, deadline)
}

/// Golem kinductiveToInductive (TransitionSystem.cc:320-365): groups
/// G_j = init@j ∨ (Inv@(j-1) ∧ T@(j-1)), j = 1..=k, G_{k+1} = ¬Inv@k; ONE
/// proof; Farkas-leaf path interpolants I_1..I_k shifted to x; candidate
/// C = ∧ I_j. SELF-VALIDATING: returns Some(C) only if C is 1-inductive,
/// init ⇒ C and C ⇒ k_inv (on SmtContext::new()); else None.
/// Precondition: vars(k_inv) ⊆ state vars (non-state vars ⇒ None, counted).
pub(crate) fn convert_path(
    k_inv: &ChcExpr,
    k: usize,
    ts: &TransitionSystem,
    deadline: Instant,
) -> Option<ChcExpr> {
    let _tag = ScopedEngineTag::install(EngineTag::KTo1);
    CALLS.fetch_add(1, Ordering::Relaxed);
    let state = ts.state_var_names();
    if !dag_var_names(k_inv).iter().all(|v| state.contains(v)) {
        NON_STATE_INPUT.fetch_add(1, Ordering::Relaxed);
        trace("non_state_input", k);
        return None;
    }
    if k == 0 {
        return None;
    }
    if k == 1 {
        // Already a 1-step claim: serve it only if it IS 1-inductive.
        return if self_validate(k_inv, k_inv, ts, deadline) {
            SERVED.fetch_add(1, Ordering::Relaxed);
            Some(k_inv.clone())
        } else {
            None
        };
    }

    let mut groups: Vec<Vec<ChcExpr>> = Vec::with_capacity(k + 1);
    for j in 1..=k {
        let step = ChcExpr::and_vec(vec![
            ts.send_through_time(k_inv, j - 1),
            ts.transition_at(j - 1),
        ]);
        groups.push(vec![ChcExpr::or_vec(vec![ts.init_at(j), step])]);
    }
    groups.push(vec![ChcExpr::not(ts.send_through_time(k_inv, k))]);
    let group_refs: Vec<&[ChcExpr]> = groups.iter().map(Vec::as_slice).collect();

    let remaining = deadline.saturating_duration_since(Instant::now());
    let ProofCheck::Unsat(mut refutation) =
        proof_check_groups(&group_refs, remaining, DEFAULT_DAG_CAPS)
    else {
        trace("proof_solve_not_unsat", k);
        return None;
    };
    // Cut i (A = G_1..G_{i+1}) shares exactly the state at time i + 1.
    let shared: Vec<_> = (1..=k).map(|t| ts.state_var_names_at(t)).collect();
    let Ok(itps) =
        refutation.path_interpolants(ItpRecipe::McMillan, &shared, ValidatePolicy::OracleGuarded)
    else {
        trace("extraction_failed", k);
        return None;
    };
    let conjuncts: Vec<ChcExpr> = itps
        .iter()
        .enumerate()
        .map(|(i, itp)| ts.rename_state_vars_at(itp, i + 1, 0))
        .collect();
    let candidate = ChcExpr::and_vec(conjuncts);
    if self_validate(&candidate, k_inv, ts, deadline) {
        SERVED.fetch_add(1, Ordering::Relaxed);
        trace("served", k);
        Some(candidate)
    } else {
        trace("self_validation_failed", k);
        None
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::panic)]
mod tests {
    use super::*;
    use crate::{ChcSort, ChcVar, PredicateId};
    use std::time::Duration;

    fn rv(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Real))
    }

    /// State (a, b) over Reals, init a = b = 0, T swaps a and b, query a > 0.
    /// `a <= 0` is 2-inductive but not 1-inductive (b is unconstrained).
    fn swap_system() -> TransitionSystem {
        let a = ChcVar::new("a", ChcSort::Real);
        let b = ChcVar::new("b", ChcSort::Real);
        TransitionSystem::new(
            PredicateId(0),
            vec![a, b],
            ChcExpr::and_vec(vec![
                ChcExpr::eq(rv("a"), ChcExpr::Real(0, 1)),
                ChcExpr::eq(rv("b"), ChcExpr::Real(0, 1)),
            ]),
            ChcExpr::and_vec(vec![
                ChcExpr::eq(rv("a_next"), rv("b")),
                ChcExpr::eq(rv("b_next"), rv("a")),
            ]),
            ChcExpr::gt(rv("a"), ChcExpr::Real(0, 1)),
        )
    }

    fn deadline() -> Instant {
        Instant::now() + Duration::from_secs(30)
    }

    #[test]
    fn two_inductive_swap_becomes_one_inductive() {
        let ts = swap_system();
        let k_inv = ChcExpr::le(rv("a"), ChcExpr::Real(0, 1));
        // Not 1-inductive on its own ...
        assert!(!self_validate(&k_inv, &k_inv, &ts, deadline()));
        // ... but the one-proof path conversion strengthens it to one that is.
        let c = convert_path(&k_inv, 2, &ts, deadline())
            .expect("the 2-inductive swap invariant must convert");
        assert!(self_validate(&c, &k_inv, &ts, deadline()));
        assert!(dag_var_names(&c).iter().all(|v| v == "a" || v == "b"));
    }

    #[test]
    fn non_state_input_is_refused() {
        let ts = swap_system();
        let (_, before, _) = convert_path_stats();
        let k_inv = ChcExpr::and_vec(vec![
            ChcExpr::le(rv("a"), ChcExpr::Real(0, 1)),
            ChcExpr::le(rv("ghost"), ChcExpr::Real(0, 1)),
        ]);
        assert!(convert_path(&k_inv, 2, &ts, deadline()).is_none());
        let (_, after, _) = convert_path_stats();
        assert!(after > before, "the refusal is counted");
    }

    #[test]
    fn k1_input_is_served_only_when_already_one_inductive() {
        let ts = swap_system();
        let weak = ChcExpr::le(rv("a"), ChcExpr::Real(0, 1));
        assert!(convert_path(&weak, 1, &ts, deadline()).is_none());
        let strong = ChcExpr::and_vec(vec![
            ChcExpr::le(rv("a"), ChcExpr::Real(0, 1)),
            ChcExpr::le(rv("b"), ChcExpr::Real(0, 1)),
        ]);
        assert!(convert_path(&strong, 1, &ts, deadline()).is_some());
    }
}
