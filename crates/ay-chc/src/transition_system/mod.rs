// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transition system utilities for CHC solvers.
//!
//! This module provides a shared `TransitionSystem` abstraction used by
//! multiple CHC engines (KIND, PDKIND, PDR, TPA).
//!
//! A transition system represents a linear CHC problem:
//! - `init`: Initial state constraint
//! - `transition`: One-step transition relation (current → next)
//! - `query`: Bad state constraint (safety property to check)
//!
//! # Time-Indexed Variables
//!
//! State variables are time-indexed to build unrolled transition relations:
//! - Time 0: `x` (original variable name)
//! - Time t>0: `x_t` (suffixed with timestep)
//!
//! The `_next` convention is used in transition relations:
//! - `x` refers to the current state
//! - `x_next` refers to the next state
//!
//! # Example
//!
//! ```text
//! TransitionSystem::new(
//!     predicate_id,
//!     vec![ChcVar::new("x", ChcSort::Int)],
//!     ChcExpr::eq(x, 0),           // init: x = 0
//!     ChcExpr::eq(x_next, x + 1),  // trans: x' = x + 1
//!     ChcExpr::ge(x, 10),          // query: x >= 10 (unsafe)
//! );
//!
//! // Build unrolled transition for 3 steps:
//! // ts.k_transition(3) produces:
//! //   trans(x, x_1) ∧ trans(x_1, x_2) ∧ trans(x_2, x_3)
//! ```
//!
//! # Reference
//!
//! Part of #430. Consolidates code from:
//! - `pdkind.rs:218-353`
//! - `kind.rs:73-141`
//! - `pdr/solver.rs:1010-1020`

mod extract;
#[allow(dead_code)] // #8879 foundation: runtime enqueue/install wiring is out of scope.
pub(crate) mod transition_cluster;
// Trust: temporal-logic backend uses the public `tla2` name. The module is now
// `transition_cluster`; keep the legacy `tla2_cluster` path as a back-compat alias so
// in-crate consumers that have not migrated (e.g. the `#[cfg(test)]` suite)
// keep resolving. Only exercised under test builds, hence the allow.
#[allow(unused_imports)]
pub(crate) use transition_cluster as tla2_cluster;
mod versioning;

use crate::{ChcExpr, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// A transition system extracted from a linear CHC problem.
///
/// This is the standard representation used by transition-system-based CHC engines.
#[derive(Debug, Clone)]
pub(crate) struct TransitionSystem {
    /// The predicate being analyzed
    pub predicate: PredicateId,
    /// State variables (includes aux vars from mod elimination)
    pub vars: Vec<ChcVar>,
    /// Initial state constraint (mod-eliminated for positive occurrences)
    pub init: ChcExpr,
    /// Raw initial state constraint (pre-mod-elimination, for negative occurrences).
    ///
    /// When init contains mod/div, the mod-eliminated form introduces auxiliary
    /// variables (quotient, remainder) that are registered in `vars` for versioning.
    /// In positive occurrences (`init_at(k)`), the aux vars are existentially bound
    /// by the conjunctive structure. In negative occurrences (`neg_init_at(k)`),
    /// the negation makes aux vars FREE — they can be set to trivially satisfy
    /// the disjunction (e.g., r ≠ 0 satisfied by r=1). This makes backward
    /// induction always SAT when it should sometimes be UNSAT.
    ///
    /// The raw init avoids this: `check_sat` handles mod elimination internally
    /// with properly scoped aux vars per call.
    ///
    /// Part of #2273.
    init_raw: ChcExpr,
    /// Transition relation (uses `x` for current, `x_next` for next state)
    pub transition: ChcExpr,
    /// Query/bad state constraint (mod-eliminated for positive occurrences)
    pub query: ChcExpr,
    /// Raw query constraint (pre-mod-elimination, for negative occurrences).
    /// Same reasoning as `init_raw`. See doc comment above.
    query_raw: ChcExpr,
}

/// Fail-closed recognition result for a deterministic Bool/BV transition system.
///
/// This is metadata only. It does not prove safety/unsafety and is intentionally
/// detached from adaptive routing until a BMC+k-induction backend consumes it.
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub(crate) struct DeterministicBvBoolTransitionSystem {
    pub predicate: PredicateId,
    pub vars: Vec<ChcVar>,
    pub init: ChcExpr,
    pub transition: ChcExpr,
    pub query: ChcExpr,
    pub next_assignments: Vec<NextStateAssignment>,
    pub has_transition_guard: bool,
    pub metadata: DeterministicBvBoolTransitionMetadata,
}

/// Routing metadata for a recognized deterministic Bool/BV system.
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeterministicBvBoolTransitionMetadata {
    pub bool_state_vars: usize,
    pub bv_state_vars: usize,
    pub total_bv_width: u64,
    pub total_state_bits: u64,
    pub max_bv_width: u32,
    pub transition_conjuncts: usize,
    pub guard_conjuncts: usize,
}

/// Canonical assignment for one next-state variable.
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NextStateAssignment {
    pub current: ChcVar,
    pub next: ChcVar,
    pub value: ChcExpr,
}

impl TransitionSystem {
    /// Create a new transition system.
    ///
    /// Pre-eliminates mod/div in `init` and `query`, registering any new
    /// auxiliary variables in `vars` so that `version_expr()` versions them
    /// correctly across timesteps. This matches Golem's approach where
    /// `ConstraintSimplifier` eliminates mod ONCE during preprocessing,
    /// before the transition system is built.
    ///
    /// All three expressions (init, transition, query) are mod-eliminated
    /// to ensure TRL/TPA/PDKind/BMC engines receive pure LIA. The transition
    /// was previously skipped (concern about `_next` aux vars), but since
    /// #7048 moved mod elimination from portfolio to per-engine level, mod
    /// terms in clauses now reach the TS transition via `from_chc_problem`,
    /// causing crashes in `BvSolver::bitblast_predicate` (#1362).
    ///
    /// Part of #2273 (menlo_park 55/55), #1362 (transition mod elimination).
    pub(crate) fn new(
        predicate: PredicateId,
        mut vars: Vec<ChcVar>,
        init: ChcExpr,
        transition: ChcExpr,
        query: ChcExpr,
    ) -> Self {
        let init_raw = init.clone();
        let query_raw = query.clone();
        let init = Self::eliminate_mod_tracking_vars(&init, &mut vars);
        let query = Self::eliminate_mod_tracking_vars(&query, &mut vars);
        let transition = Self::eliminate_mod_tracking_vars(&transition, &mut vars);
        Self {
            predicate,
            vars,
            init,
            init_raw,
            transition,
            query,
            query_raw,
        }
    }

    /// Eliminate mod/div and register any new auxiliary variables in `vars`.
    ///
    /// After `eliminate_mod()`, new aux vars (e.g., `_mod_q_0`, `_mod_r_0`)
    /// are detected by comparing the variable set before and after elimination.
    /// These are added to `vars` so `version_expr()` versions them at each
    /// timestep, preventing hidden equality constraints between timesteps.
    fn eliminate_mod_tracking_vars(expr: &ChcExpr, vars: &mut Vec<ChcVar>) -> ChcExpr {
        if !expr.contains_mod_or_div() {
            return expr.clone();
        }
        let before_vars: FxHashSet<String> = expr.vars().iter().map(|v| v.name.clone()).collect();
        let eliminated = expr.eliminate_mod();
        // Find new aux vars introduced by eliminate_mod
        for v in eliminated.vars() {
            if !before_vars.contains(&v.name)
                && !vars.iter().any(|existing| existing.name == v.name)
            {
                vars.push(v);
            }
        }
        eliminated
    }

    // ========================================================================
    // System Reversal
    // ========================================================================

    /// Create the reverse of this transition system.
    ///
    /// Reversal swaps init/query and reverses the transition relation (swaps
    /// current and next state variables). Used by Kind backward induction to
    /// convert k-inductive invariants via the standard k-to-1 algorithm.
    ///
    /// Reference: Golem TransitionSystem.cc:132-138
    pub(crate) fn reverse(&self) -> Self {
        let reversed_transition = self.reverse_transition_relation();
        Self {
            predicate: self.predicate,
            vars: self.vars.clone(),
            init: self.query.clone(),
            init_raw: self.query_raw.clone(),
            transition: reversed_transition,
            query: self.init.clone(),
            query_raw: self.init_raw.clone(),
        }
    }

    /// Reverse the transition relation by swapping current and next state variables.
    ///
    /// Uses a three-phase substitution to avoid variable capture:
    /// 1. current vars → temp vars
    /// 2. next vars → current vars
    /// 3. temp vars → next vars
    ///
    /// Reference: Golem TransitionSystem.cc:140-170
    fn reverse_transition_relation(&self) -> ChcExpr {
        // Phase 1: current vars (v0, v1, ...) → temp vars (__tmp_v0, __tmp_v1, ...)
        let phase1: Vec<(ChcVar, ChcExpr)> = self
            .vars
            .iter()
            .map(|v| {
                let temp = ChcVar::new(format!("__tmp_{}", v.name), v.sort.clone());
                (v.clone(), ChcExpr::var(temp))
            })
            .collect();
        let after_phase1 = self.transition.substitute(&phase1);

        // Phase 2: next vars (v0_next, v1_next, ...) → current vars (v0, v1, ...)
        let phase2: Vec<(ChcVar, ChcExpr)> = self
            .vars
            .iter()
            .map(|v| {
                let next = ChcVar::new(format!("{}_next", v.name), v.sort.clone());
                (next, ChcExpr::var(v.clone()))
            })
            .collect();
        let after_phase2 = after_phase1.substitute(&phase2);

        // Phase 3: temp vars (__tmp_v0, ...) → next vars (v0_next, v1_next, ...)
        let phase3: Vec<(ChcVar, ChcExpr)> = self
            .vars
            .iter()
            .map(|v| {
                let temp = ChcVar::new(format!("__tmp_{}", v.name), v.sort.clone());
                let next = ChcVar::new(format!("{}_next", v.name), v.sort.clone());
                (temp, ChcExpr::var(next))
            })
            .collect();
        after_phase2.substitute(&phase3)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;
