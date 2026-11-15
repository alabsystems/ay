// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reading a [`LinearTrace`] off a model of a transition-system unrolling.

use super::{coerce_to_sort, LinearTrace, TraceEdgeHint};
use crate::smt::SmtValue;
use crate::transition_system::TransitionSystem;
use ay_core::kani_compat::DetHashMap as FxHashMap;

impl LinearTrace {
    /// Read the per-step canonical states `v{i}` / `v{i}_{j}` of a
    /// transition-system unrolling off `model`, for steps `0..=n`.
    pub(crate) fn states_from_ts_model(
        ts: &TransitionSystem,
        model: &FxHashMap<String, SmtValue>,
        n: usize,
    ) -> Vec<Vec<Option<SmtValue>>> {
        (0..=n).map(|step| ts_state_at(ts, model, step)).collect()
    }

    /// The trace a model of the standard `k`-step unrolling describes:
    /// `init ∧ Tr@0 ∧ … ∧ Tr@(k-1) ∧ query@k`, versioned by
    /// [`TransitionSystem::transition_at`] / [`TransitionSystem::query_at`]
    /// (locals `…__t{j}`, `…__q{k}`), with `init` either unversioned or
    /// `init_at(0)` (locals `…__i0`). `k = 0` covers `init ∧ query`.
    pub(crate) fn from_ts_unrolling(
        ts: &TransitionSystem,
        model: &FxHashMap<String, SmtValue>,
        k: usize,
    ) -> Self {
        let with_bare = |mut locals: FxHashMap<String, SmtValue>| {
            for (name, value) in model {
                locals.entry(name.clone()).or_insert_with(|| value.clone());
            }
            locals
        };
        let mut edges = Vec::with_capacity(k + 2);
        edges.push(TraceEdgeHint {
            ts_locals: with_bare(ts_locals_with_suffix(model, "__i0")),
            ..TraceEdgeHint::default()
        });
        for step in 0..k {
            edges.push(TraceEdgeHint {
                ts_locals: ts_locals_with_suffix(model, &format!("__t{step}")),
                ..TraceEdgeHint::default()
            });
        }
        edges.push(TraceEdgeHint {
            ts_locals: with_bare(ts_locals_with_suffix(model, &format!("__q{k}"))),
            ..TraceEdgeHint::default()
        });
        Self {
            predicate: ts.predicate,
            states: Self::states_from_ts_model(ts, model, k),
            edges,
        }
    }
}

/// The canonical state at unrolling step `step` (`v{i}` at 0, `v{i}_{step}`
/// otherwise), coerced to each variable's sort.
pub(crate) fn ts_state_at(
    ts: &TransitionSystem,
    model: &FxHashMap<String, SmtValue>,
    step: usize,
) -> Vec<Option<SmtValue>> {
    ts.state_vars()
        .iter()
        .map(|var| {
            model
                .get(&TransitionSystem::version_var(var, step).name)
                .and_then(|value| coerce_to_sort(value, &var.sort))
        })
        .collect()
}

/// Model entries whose name ends in `suffix`, with the suffix stripped: the
/// transition-system locals of one versioned step (`__t3`, `__i0`, `__q2`).
pub(crate) fn ts_locals_with_suffix(
    model: &FxHashMap<String, SmtValue>,
    suffix: &str,
) -> FxHashMap<String, SmtValue> {
    model
        .iter()
        .filter_map(|(name, value)| {
            let base = name.strip_suffix(suffix)?;
            (!base.is_empty()).then(|| (base.to_string(), value.clone()))
        })
        .collect()
}
