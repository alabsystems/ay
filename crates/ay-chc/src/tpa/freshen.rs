// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Variable shifting and freshening for TPA compositions.
//!
//! When TPA composes transitions (e.g., T(v,v_1) ∧ T(v_1,v_2)), the shifted
//! copy must have independent body-local variables. Without freshening,
//! body-local variables (from clause inlining, like `J`, `K`, `V__inline_28`)
//! are shared between copies, creating false constraints.
//!
//! SOUNDNESS FIX (#5508): All TPA composition sites use `shift_and_freshen`
//! instead of plain `shift_expr` to prevent variable collision.

use std::sync::atomic::{AtomicU64, Ordering};

use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcVar};

use super::solver::TpaSolver;

/// Global counter for freshening body-local variables in TPA compositions.
static TPA_FRESHEN_COUNTER: AtomicU64 = AtomicU64::new(0);

impl TpaSolver {
    /// Shift expression by given number of time steps.
    ///
    /// Shifts all state variables in the expression:
    /// - steps > 0: v → v_{steps}, v_1 → v_{1+steps}, etc.
    /// - steps < 0: v_{k} → v_{max(0, k+steps)}
    ///
    /// `ts` is passed by reference to avoid accessing `self.transition_system`
    /// which may be `None` during `check_power`'s take/put-back window (#5574).
    pub(super) fn shift_expr(&self, expr: &ChcExpr, steps: i32, ts: &TransitionSystem) -> ChcExpr {
        ts.shift_versioned_state_vars(expr, steps)
    }

    /// Shift expression by given time steps AND freshen body-local variables.
    ///
    /// SOUNDNESS FIX (#5508): When TPA composes transitions (e.g.,
    /// T(v,v_1) ∧ T(v_1,v_2)), the shifted copy must have independent
    /// body-local variables. Without freshening, body-local variables
    /// (from clause inlining, like `J`, `K`, `V__inline_28`) are shared
    /// between copies, creating false constraints that make compositions
    /// artificially UNSAT. This caused car_6 benchmarks to get wrong `sat`.
    ///
    /// `ts` is passed by reference to avoid accessing `self.transition_system`
    /// which may be `None` during `check_power`'s take/put-back window (#5574).
    pub(super) fn shift_and_freshen(
        &self,
        expr: &ChcExpr,
        steps: i32,
        ts: &TransitionSystem,
    ) -> ChcExpr {
        let shifted = self.shift_expr(expr, steps, ts);
        Self::freshen_body_locals(&shifted, ts)
    }

    /// Rename all non-state-variable free variables to fresh unique names.
    ///
    /// Body-local variables (from clause inlining) must be existentially
    /// quantified per transition step. This method ensures they don't clash
    /// when multiple copies of the transition are composed.
    fn freshen_body_locals(expr: &ChcExpr, ts: &TransitionSystem) -> ChcExpr {
        let state_bases: ay_core::kani_compat::DetHashSet<&str> =
            ts.state_vars().iter().map(|v| v.name.as_str()).collect();

        let tag = TPA_FRESHEN_COUNTER.fetch_add(1, Ordering::Relaxed);

        let subst: Vec<(ChcVar, ChcExpr)> = expr
            .vars()
            .into_iter()
            .filter(|v| {
                // Keep only variables that are NOT state variables at any time step.
                crate::transition_system::state_var_time(&v.name, &state_bases).is_none()
            })
            .map(|v| {
                let fresh_name = format!("{}_f{}", v.name, tag);
                let fresh_var = ChcVar::new(fresh_name, v.sort.clone());
                (v, ChcExpr::var(fresh_var))
            })
            .collect();

        if subst.is_empty() {
            return expr.clone();
        }
        expr.substitute(&subst)
    }

    /// Shift only the "next" variables (position 1) to next-next (position 2).
    ///
    /// This transforms a relation from (0→1) to (0→2), keeping current variables
    /// at position 0 unchanged. Used for direct path checks in TPA.
    ///
    /// Reference: Golem TPA.cc:shiftOnlyNextVars
    ///
    /// `ts` is passed by reference to avoid accessing `self.transition_system`
    /// which may be `None` during `check_power`'s take/put-back window (#5574).
    pub(super) fn shift_only_next_vars(&self, expr: &ChcExpr, ts: &TransitionSystem) -> ChcExpr {
        // Only shift variables at position 1 to position 2
        // Variables at position 0 stay at position 0
        ts.rename_state_vars_at(expr, 1, 2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcSort, PredicateId};

    /// SingleLoop state names end in `_<digits>`; only the clause locals of
    /// the shifted copy may be freshened.
    #[test]
    fn single_loop_state_names_are_never_freshened() {
        let state = |name: &str| ChcVar::new(name, ChcSort::Int);
        let ts = TransitionSystem::new(
            PredicateId::new(0),
            vec![state(".loc_0"), state(".loc_1"), state(".arg_1_2")],
            ChcExpr::Bool(true),
            ChcExpr::Bool(true),
            ChcExpr::Bool(true),
        );
        let expr = ChcExpr::and_all([
            ChcExpr::eq(
                ChcExpr::var(state(".loc_1")),
                ChcExpr::var(state(".arg_1_2_1")),
            ),
            ChcExpr::eq(ChcExpr::var(state(".loc_0_2")), ChcExpr::var(state("J"))),
        ]);
        let freshened = TpaSolver::freshen_body_locals(&expr, &ts);
        let mut names: Vec<String> = freshened.vars().into_iter().map(|v| v.name).collect();
        names.sort();
        assert_eq!(names.len(), 4);
        assert_eq!(&names[..3], [".arg_1_2_1", ".loc_0_2", ".loc_1"]);
        assert!(names[3].starts_with("J_f"), "{names:?}");
    }
}
