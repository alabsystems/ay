// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Explanation extraction for PDKIND reachability checking.
//!
//! Contains the Boolean UNSAT core path (#5877 Wave 2) and model
//! generalization via MBP.

use super::reachability::ReachabilityChecker;
use crate::engine_utils::check_sat_with_timeout;
use crate::mbp::Mbp;
use crate::smt::{SmtResult, SmtValue};
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Maximum number of drop-and-recheck iterations for Boolean generalization.
/// Prevents excessive SMT calls on large state spaces (e.g., 160+ Boolean
/// vars from 32-bit BV bit-blasting).
const MAX_GENERALIZATION_DROPS: usize = 512;

impl ReachabilityChecker {
    /// For all-Bool state spaces (after BvToBool), compute an interpolant
    /// via B-side minimization (#5877 Wave 2).
    ///
    /// Strategy: decompose B into individual conjuncts, then use
    /// drop-and-recheck to find a minimal subset of B that is still
    /// inconsistent with A. The negation of this minimal subset is
    /// a valid interpolant over shared variables.
    ///
    /// This mirrors Z3 Spacer's `lemma_bool_inductive_generalizer`
    /// (spacer_generalizers.cpp:62-142) which drops literals from
    /// blocking cubes and rechecks.
    ///
    /// ENSURES: If `Some(I)` is returned:
    ///   - `A ⊨ I` (A implies I — because A ∧ ¬I is UNSAT)
    ///   - `I ∧ B` is UNSAT (I blocks B — because B implies the minimized subset)
    ///   - `I` mentions only variables in `shared_vars` (B-conjuncts are
    ///     already over shared vars)
    pub(super) fn boolean_unsat_core_explanation(
        &mut self,
        a_constraints: &[ChcExpr],
        b_constraints: &[ChcExpr],
        _shared_vars: &FxHashSet<String>,
    ) -> Option<ChcExpr> {
        // Phase 1: Confirm UNSAT via assumption-based SAT and get B-side core.
        let result = self
            .smt
            .check_sat_with_assumption_conjuncts(a_constraints, b_constraints);

        let b_core: Vec<ChcExpr> = match result {
            SmtResult::Sat(_) | SmtResult::Unknown => return None,
            SmtResult::UnsatWithCore(core) if !core.conjuncts.is_empty() => core.conjuncts,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                b_constraints.to_vec()
            }
        };

        // Phase 2: Decompose B-core into individual conjuncts for minimization.
        let mut b_literals: Vec<ChcExpr> = Vec::new();
        for c in &b_core {
            for conj in c.conjuncts() {
                b_literals.push(conj.clone());
            }
        }

        if b_literals.is_empty() {
            return None;
        }

        // Phase 3: Drop-and-recheck generalization.
        // Try removing each B-literal; if A ∧ (remaining B) is still UNSAT,
        // the literal is redundant and can be dropped.
        let a_conj = if a_constraints.len() == 1 {
            a_constraints[0].clone()
        } else {
            ChcExpr::and_all(a_constraints.to_vec())
        };

        let mut drops = 0usize;
        let mut i = 0;
        while i < b_literals.len() && drops < MAX_GENERALIZATION_DROPS {
            if b_literals.len() <= 1 {
                break;
            }

            let remaining_b: Vec<ChcExpr> = b_literals
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, e)| e.clone())
                .collect();

            let b_without_i = if remaining_b.len() == 1 {
                remaining_b.into_iter().next().expect("len == 1")
            } else {
                ChcExpr::and_all(remaining_b)
            };

            let query = ChcExpr::and(a_conj.clone(), b_without_i);
            let check = if let Some(timeout) = self.smt_timeout {
                check_sat_with_timeout(&query, timeout)
            } else {
                self.smt.check_sat(&query)
            };

            drops += 1;

            match check {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    b_literals.swap_remove(i);
                }
                _ => {
                    i += 1;
                }
            }
        }

        // Phase 4: Build interpolant as not(minimized B conjunction).
        // B-conjuncts are over shared variables (time-1 state vars for k-step,
        // state vars for zero-step), so not(B) is automatically over shared vars.
        let minimized_b = if b_literals.len() == 1 {
            b_literals.pop().expect("len == 1")
        } else {
            ChcExpr::and_all(b_literals)
        };

        Some(ChcExpr::not(minimized_b))
    }

    /// Generalize a model to a formula (using MBP)
    ///
    /// This implements Golem's generalize() from PDKind.cc:238-242.
    /// MBP needs BOTH the transition relation AND the step-k formula to derive
    /// step-0 constraints. The transition connects step-k variables to step-0
    /// variables, allowing projection to produce meaningful generalizations.
    pub(super) fn generalize(
        &self,
        model: &FxHashMap<String, SmtValue>,
        transition: &ChcExpr,
        target: &ChcExpr,
    ) -> ChcExpr {
        let mbp = Mbp::new();

        // Conjoin transition AND target before projection (matches Golem)
        let conj = ChcExpr::and(transition.clone(), target.clone());

        // Find variables not in state vars to eliminate
        let state_vars = self.ts.state_var_names();
        let vars_to_elim: Vec<_> = model
            .keys()
            .filter(|k| !state_vars.contains(*k))
            .filter_map(|k| {
                model.get(k).and_then(|v| {
                    let sort = match v {
                        SmtValue::Bool(_) => ChcSort::Bool,
                        // Beyond-i128 BigInt witnesses are Int-sorted; MBP's own
                        // evaluation abstains fail-closed where it cannot read them.
                        SmtValue::Int(_) | SmtValue::BigInt(_) => ChcSort::Int,
                        SmtValue::Real(_) => ChcSort::Real,
                        SmtValue::BitVec(_, w) | SmtValue::BigBitVec(_, w) => ChcSort::BitVec(*w),
                        // Skip array/DT/opaque values — not projected by arithmetic MBP
                        SmtValue::Opaque(_)
                        | SmtValue::ConstArray(_)
                        | SmtValue::ArrayMap { .. }
                        | SmtValue::Datatype(..) => return None,
                    };
                    Some(ChcVar::new(k, sort))
                })
            })
            .collect();

        if vars_to_elim.is_empty() {
            return conj;
        }

        mbp.project(&conj, &vars_to_elim, model)
    }
}
