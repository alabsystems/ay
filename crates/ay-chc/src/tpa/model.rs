// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Model extraction for TPA.
//!
//! Extracts midpoints, counterexample traces, and refined targets from
//! SMT models produced during TPA reachability queries.

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcVar, SmtValue};

use super::solver::TpaSolver;

impl TpaSolver {
    /// Refine target state from model - extracts concrete values at time 2.
    pub(super) fn refine_two_step_target(
        &self,
        model: &FxHashMap<String, SmtValue>,
        ts: &TransitionSystem,
    ) -> ChcExpr {
        extract_state_from_model(model, ts, 2, 0)
    }

    /// Extract midpoint state from SAT model.
    ///
    /// The model contains values for state variables at times 0, 1, and 2.
    /// The midpoint is the state at time 1 - we extract equalities for
    /// all state variables at time 1.
    ///
    /// Reference: Golem TPA.cc:extractMidPoint (uses MBP for more general result)
    pub(super) fn extract_midpoint_from_model(
        &self,
        model: &FxHashMap<String, SmtValue>,
        ts: &TransitionSystem,
    ) -> ChcExpr {
        extract_state_from_model(model, ts, 1, 0)
    }

    /// Extract counterexample trace from SAT model.
    ///
    /// Attempts to extract variable assignments at time steps 0, 1, and 2.
    /// Only states with values present in the model are included.
    ///
    /// For TPA queries, the trace structure depends on the query type:
    /// - Immediate counterexample (init ∧ query): only time 0 present
    /// - Power query: times 0, 1, 2 present (each step = 2^power transitions)
    ///
    /// The returned trace contains concrete variable assignments at each step boundary.
    pub(super) fn extract_trace_from_model(
        &self,
        model: &FxHashMap<String, SmtValue>,
        ts: &TransitionSystem,
    ) -> Vec<FxHashMap<String, SmtValue>> {
        let mut trace = Vec::new();

        // Extract states at times 0, 1, and 2 from the model
        for time in 0..=2 {
            let mut state = FxHashMap::default();

            for var in ts.state_vars() {
                // Variables are named: base (time 0), base_1 (time 1), base_2 (time 2)
                let var_name = if time == 0 {
                    var.name.clone()
                } else {
                    format!("{}_{}", var.name, time)
                };

                if let Some(value) = model.get(&var_name) {
                    // Store with the base variable name (without time suffix)
                    state.insert(var.name.clone(), value.clone());
                }
            }

            if !state.is_empty() {
                trace.push(state);
            }
        }

        trace
    }
}

/// Extract state variable values from an SMT model at the given `from_time`,
/// expressed as equalities over time-`to_time` variable names.
///
/// This is the shared implementation for both `refine_two_step_target` (time 2 -> 0)
/// and `extract_midpoint_from_model` (time 1 -> 0).
fn extract_state_from_model(
    model: &FxHashMap<String, SmtValue>,
    ts: &TransitionSystem,
    from_time: u32,
    to_time: u32,
) -> ChcExpr {
    let mut conjuncts = Vec::new();
    for var in ts.state_vars() {
        let source_name = if from_time == 0 {
            var.name.clone()
        } else {
            format!("{}_{from_time}", var.name)
        };
        if let Some(value) = model.get(&source_name) {
            let target_var = if to_time == 0 {
                ChcVar::new(var.name.clone(), var.sort.clone())
            } else {
                ChcVar::new(format!("{}_{to_time}", var.name), var.sort.clone())
            };
            let eq = match value {
                SmtValue::Int(i) => ChcExpr::eq(ChcExpr::var(target_var), ChcExpr::int(*i)),
                // Beyond-i128 witness: exact Horner encoding (never wraps).
                SmtValue::BigInt(b) => ChcExpr::eq(
                    ChcExpr::var(target_var),
                    ChcExpr::from_bigint(b.as_ref().clone()),
                ),
                SmtValue::Bool(b) => {
                    if *b {
                        ChcExpr::var(target_var)
                    } else {
                        ChcExpr::not(ChcExpr::var(target_var))
                    }
                }
                SmtValue::Real(r) => {
                    use num_traits::ToPrimitive;
                    let n = r.numer().to_i64().unwrap_or(0);
                    let d = r.denom().to_i64().unwrap_or(1);
                    ChcExpr::eq(ChcExpr::var(target_var), ChcExpr::Real(n, d))
                }
                // #5523: Preserve bitvector sort to avoid BV→Int sort mismatches.
                SmtValue::BitVec(v, w) => {
                    ChcExpr::eq(ChcExpr::var(target_var), ChcExpr::BitVec(*v, *w))
                }
                // Array, DT, and opaque values skipped — no scalar equality representation.
                SmtValue::Opaque(_)
                | SmtValue::ConstArray(_)
                | SmtValue::ArrayMap { .. }
                | SmtValue::Datatype(..) => continue,
            };
            conjuncts.push(eq);
        }
    }
    ChcExpr::and_all(conjuncts)
}
