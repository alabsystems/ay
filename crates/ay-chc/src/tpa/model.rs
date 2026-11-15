// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Model extraction for TPA.
//!
//! Extracts midpoints, counterexample traces, and refined targets from
//! SMT models produced during TPA reachability queries.

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcSort, ChcVar, SmtValue};

use super::solver::{ConcretePath, TpaSolver};
use crate::ground_derivation::linear_trace::{ts_locals_with_suffix, ts_state_at};

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

    /// Concrete segment of a power-0 exact query model,
    /// `from(0) ∧ T(0→1) ∧ T'(1→2) ∧ to(2)`: three states and both
    /// transitions' locals (`T` = `transition_at(0)`, locals `…__t0`; `T'` its
    /// shifted, freshened copy, locals `…__t0_f{tag}`).
    pub(super) fn exact_base_path(
        &self,
        model: &FxHashMap<String, SmtValue>,
        ts: &TransitionSystem,
    ) -> ConcretePath {
        ConcretePath {
            states: (0..=2).map(|step| ts_state_at(ts, model, step)).collect(),
            transition_locals: vec![
                ts_locals_with_suffix(model, "__t0"),
                freshened_ts_locals(model, "__t0"),
            ],
            endpoint_locals: endpoint_locals(model),
        }
    }

    /// Concrete segment of a power-0 less-than query model whose DIRECT
    /// disjunct held: `from(0) ∧ id(0→2) ∧ to(2)`, zero transitions.
    pub(super) fn identity_base_path(
        &self,
        model: &FxHashMap<String, SmtValue>,
        ts: &TransitionSystem,
    ) -> ConcretePath {
        ConcretePath {
            states: vec![merge_states(
                ts_state_at(ts, model, 0),
                ts_state_at(ts, model, 2),
            )],
            transition_locals: Vec::new(),
            endpoint_locals: endpoint_locals(model),
        }
    }

    /// Concrete segment of a power-0 less-than query model whose COMPOSED
    /// disjunct held: `from(0) ∧ id(0→1) ∧ T'(1→2) ∧ to(2)`, one transition.
    pub(super) fn composed_base_path(
        &self,
        model: &FxHashMap<String, SmtValue>,
        ts: &TransitionSystem,
    ) -> ConcretePath {
        ConcretePath {
            states: vec![
                merge_states(ts_state_at(ts, model, 0), ts_state_at(ts, model, 1)),
                ts_state_at(ts, model, 2),
            ],
            transition_locals: vec![freshened_ts_locals(model, "__t0")],
            endpoint_locals: endpoint_locals(model),
        }
    }

    /// Concrete state of an `init ∧ query` model (the depth-0 counterexample).
    pub(super) fn trivial_path(
        &self,
        model: &FxHashMap<String, SmtValue>,
        ts: &TransitionSystem,
    ) -> ConcretePath {
        ConcretePath {
            states: vec![ts_state_at(ts, model, 0)],
            transition_locals: Vec::new(),
            endpoint_locals: endpoint_locals(model),
        }
    }
}

/// Model entries under their own (unversioned) names, for the init and query
/// locals of a path's endpoints. Freshened copies (`…_f{tag}`) are left out:
/// every composed transition mints new ones, so they would only grow the map.
fn endpoint_locals(model: &FxHashMap<String, SmtValue>) -> FxHashMap<String, SmtValue> {
    model
        .iter()
        .filter(|(name, _)| {
            !name
                .rsplit_once("_f")
                .is_some_and(|(_, tag)| !tag.is_empty() && tag.bytes().all(|b| b.is_ascii_digit()))
        })
        .map(|(name, value)| (name.clone(), value.clone()))
        .collect()
}

/// Two readings of one state (identity-linked time copies): each value from
/// whichever reading has it.
fn merge_states(
    mut primary: Vec<Option<SmtValue>>,
    secondary: Vec<Option<SmtValue>>,
) -> Vec<Option<SmtValue>> {
    for (value, other) in primary.iter_mut().zip(secondary) {
        if value.is_none() {
            *value = other;
        }
    }
    primary
}

/// Locals of a shifted, freshened transition copy: model names
/// `{local}{step_suffix}_f{tag}`, returned under `{local}`.
fn freshened_ts_locals(
    model: &FxHashMap<String, SmtValue>,
    step_suffix: &str,
) -> FxHashMap<String, SmtValue> {
    model
        .iter()
        .filter_map(|(name, value)| {
            let (head, tag) = name.rsplit_once("_f")?;
            if tag.is_empty() || !tag.bytes().all(|b| b.is_ascii_digit()) {
                return None;
            }
            let base = head.strip_suffix(step_suffix)?;
            (!base.is_empty()).then(|| (base.to_string(), value.clone()))
        })
        .collect()
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
            let eq = match (&var.sort, value) {
                (ChcSort::Int, SmtValue::Int(i)) => {
                    ChcExpr::eq(ChcExpr::var(target_var), ChcExpr::int(*i))
                }
                // Beyond-i128 witness: exact Horner encoding (never wraps).
                (ChcSort::Int, SmtValue::BigInt(b)) => ChcExpr::eq(
                    ChcExpr::var(target_var),
                    ChcExpr::from_bigint(b.as_ref().clone()),
                ),
                (ChcSort::Bool, SmtValue::Bool(b)) => {
                    if *b {
                        ChcExpr::var(target_var)
                    } else {
                        ChcExpr::not(ChcExpr::var(target_var))
                    }
                }
                (ChcSort::Real, SmtValue::Real(r)) => {
                    use num_traits::ToPrimitive;
                    let Some(n) = r.numer().to_i64() else {
                        continue;
                    };
                    let Some(d) = r.denom().to_i64() else {
                        continue;
                    };
                    ChcExpr::eq(ChcExpr::var(target_var), ChcExpr::Real(n, d))
                }
                // #5523: Preserve bitvector sort to avoid BV→Int sort mismatches.
                (
                    ChcSort::BitVec(expected_width),
                    value @ (SmtValue::BitVec(_, actual_width)
                    | SmtValue::BigBitVec(_, actual_width)),
                ) if expected_width == actual_width => {
                    let Some(literal) = value.bitvec_to_chc_expr() else {
                        continue;
                    };
                    ChcExpr::eq(ChcExpr::var(target_var), literal)
                }
                // Array, DT, and opaque values skipped — no scalar equality representation.
                _ => continue,
            };
            conjuncts.push(eq);
        }
    }
    ChcExpr::and_all(conjuncts)
}
