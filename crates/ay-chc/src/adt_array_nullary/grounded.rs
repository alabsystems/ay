// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original-clause ground evidence, never an all-true marker witness.

use super::{control::Control, names::Names, MarkerDagNode};
use crate::ground_derivation::{
    validate_ground_derivation_with_progress, GroundDerivation, GroundDerivationStep,
};
use crate::{ChcExpr, ChcProblem, Counterexample, CounterexampleStep, PredicateId, SmtValue};
use ay_core::kani_compat::DetHashMap;

pub(super) fn from_fact(
    problem: &ChcProblem,
    predicate: PredicateId,
    fact: usize,
    query: usize,
    instances: DetHashMap<String, SmtValue>,
    control: &Control,
) -> Option<Counterexample> {
    control.admit(instances.len(), 256)?;
    for value in instances.values() {
        admit_value(value, control)?;
    }
    publish(
        problem,
        GroundDerivation {
            steps: vec![
                GroundDerivationStep {
                    clause_index: fact,
                    env: instances,
                    premises: Vec::new(),
                },
                GroundDerivationStep {
                    clause_index: query,
                    env: DetHashMap::default(),
                    premises: vec![0],
                },
            ],
            query_step: 1,
        },
        predicate,
        fact,
        control,
    )
}

pub(super) fn from_model(
    problem: &ChcProblem,
    query: usize,
    nodes: &[MarkerDagNode],
    root: usize,
    names: &Names,
    model: &DetHashMap<String, SmtValue>,
    control: &Control,
) -> Option<Counterexample> {
    control.admit(nodes.len(), nodes.len().checked_add(1)?.checked_mul(128)?)?;
    let mut steps = Vec::new();
    if steps
        .try_reserve_exact(nodes.len().checked_add(1)?)
        .is_err()
    {
        return control.refuse();
    }
    for (index, node) in nodes.iter().enumerate() {
        control.admit(node.children.len(), node.children.len().checked_mul(8)?)?;
        if node.children.iter().any(|child| *child >= index) {
            return None;
        }
        steps.push(GroundDerivationStep {
            clause_index: node.clause_idx,
            env: environment(names.node(index)?, model, control)?,
            premises: node.children.clone(),
        });
    }
    let root_node = nodes.get(root)?;
    let query_step = steps.len();
    steps.push(GroundDerivationStep {
        clause_index: query,
        env: environment(names.query(), model, control)?,
        premises: vec![root],
    });
    publish(
        problem,
        GroundDerivation { steps, query_step },
        root_node.predicate,
        root_node.clause_idx,
        control,
    )
}

fn environment(
    names: &DetHashMap<String, ChcExpr>,
    model: &DetHashMap<String, SmtValue>,
    control: &Control,
) -> Option<DetHashMap<String, SmtValue>> {
    control.admit(names.len(), names.len().checked_mul(128)?)?;
    let mut env = DetHashMap::default();
    if env.try_reserve(names.len()).is_err() {
        return control.refuse();
    }
    for (original, replacement) in names {
        control.admit(
            original.len().checked_add(1)?,
            original.len().checked_add(128)?,
        )?;
        let ChcExpr::Var(scoped) = replacement else {
            return None;
        };
        let value = model.get(&scoped.name)?;
        admit_value(value, control)?;
        env.insert(original.clone(), value.clone());
    }
    // Preserve the finite interpretation shared by all steps, just as BMC's
    // ground-evidence producer does. Original-variable keys remain distinct
    // from these private NUL-prefixed application observations. Unsupported
    // or inconsistent UF models are still rejected by the ground validator.
    for (name, value) in model {
        control.admit(name.len().checked_add(1)?, 0)?;
        if name.starts_with("\0ay.uf-") {
            control.admit(name.len(), name.len().checked_add(128)?)?;
            admit_metadata(name, value, control)?;
            if env.try_reserve(1).is_err() {
                return control.refuse();
            }
            env.insert(name.clone(), value.clone());
        }
    }
    control.poll()?;
    Some(env)
}

fn publish(
    problem: &ChcProblem,
    derivation: GroundDerivation,
    predicate: PredicateId,
    clause: usize,
    control: &Control,
) -> Option<Counterexample> {
    validate_ground_derivation_with_progress(problem, &derivation, &mut || {
        control.admit(1, 0).is_some()
    })
    .ok()?;
    control.poll()?;
    // No fabricated DerivationWitness: the fully checked ground object is
    // the evidence. The unchanged vacuity guard continues rejecting legacy
    // all-true witnesses, including ones with satisfying local assignments.
    let candidate = Counterexample::new(vec![CounterexampleStep::new(
        predicate,
        DetHashMap::default(),
    )
    .with_clause(clause)])
    .with_ground_derivation(derivation);
    let derivation = candidate.ground_derivation.as_ref()?;
    admit_presentation(problem, derivation, control)?;
    let restated = candidate.restated_by_derivation(problem, derivation);
    control.poll()?;
    Some(restated.unwrap_or(candidate))
}

fn admit_metadata(name: &str, value: &SmtValue, control: &Control) -> Option<()> {
    use crate::expr::evaluate::{
        UF_APPLICATION_MODEL_MARKER_KEY, UF_APPLICATION_MODEL_MARKER_VALUE,
    };
    if name == UF_APPLICATION_MODEL_MARKER_KEY {
        let SmtValue::Opaque(marker) = value else {
            return None;
        };
        control.admit(marker.len(), marker.len())?;
        return (marker == UF_APPLICATION_MODEL_MARKER_VALUE).then_some(());
    }
    admit_value(value, control)
}

fn admit_presentation(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
    control: &Control,
) -> Option<()> {
    control.admit(
        derivation.steps.len(),
        derivation.steps.len().checked_mul(256)?,
    )?;
    for step in &derivation.steps {
        control.admit(step.premises.len(), step.premises.len().checked_mul(8)?)?;
        for (name, value) in &step.env {
            control.admit(name.len().checked_add(1)?, name.len().checked_add(256)?)?;
            admit_metadata(name, value, control)?;
        }
        let clause = problem.clauses().get(step.clause_index)?;
        if let crate::ClauseHead::Predicate(_, arguments) = &clause.head {
            control.admit(arguments.len(), arguments.len().checked_mul(256)?)?;
            for argument in arguments {
                admit_head(argument, &step.env, control)?;
            }
        }
    }
    control.poll()
}

/// Restatement evaluates each head position separately, including shared ASTs.
/// Visit occurrences, not unique nodes: a constructor/store may retain all its
/// children's aggregate payloads, and selectors/memoization can clone them at
/// each ancestor. Eight copies per ancestor cover direct/retried evaluation,
/// memo/result copies and selector extraction; source nodes are also charged
/// without an environment, so literal aggregate heads are not free.
fn admit_head(root: &ChcExpr, env: &DetHashMap<String, SmtValue>, control: &Control) -> Option<()> {
    control.admit(1, 32)?;
    let mut pending = vec![(root, 0usize)];
    let mut widths = Vec::new();
    while let Some((node, depth)) = pending.pop() {
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
            return control.refuse();
        }
        let Some(copies) = depth.checked_add(1).and_then(|n| n.checked_mul(8)) else {
            return control.refuse();
        };
        control.admit(copies, copies.checked_mul(256)?)?;
        match node {
            ChcExpr::Var(variable) => {
                control.admit(variable.name.len(), variable.name.len())?;
                admit_sort_copy(&variable.sort, copies, control)?;
                let value = env.get(&variable.name)?;
                for _ in 0..copies {
                    admit_value(value, control)?;
                }
            }
            ChcExpr::FuncApp(name, sort, _) => {
                control.admit(name.len(), name.len().checked_mul(copies)?)?;
                admit_sort_copy(sort, copies, control)?;
                // A finite UF result may itself be an aggregate; do not assume
                // its payload occurs in an ordinary variable binding.
                for (key, value) in env {
                    control.admit(key.len(), 0)?;
                    if key.starts_with("\0ay.uf-") {
                        for _ in 0..copies {
                            admit_metadata(key, value, control)?;
                        }
                    }
                }
            }
            ChcExpr::BitVec(_, width) => {
                let bytes = usize::try_from(u64::from(*width).div_ceil(8)).ok()?;
                control.admit(bytes, bytes.checked_mul(copies)?)?;
            }
            ChcExpr::ConstArray(sort, _) => admit_sort_copy(sort, copies, control)?,
            ChcExpr::Op(
                crate::ChcOp::BvRepeat(_)
                | crate::ChcOp::BvZeroExtend(_)
                | crate::ChcOp::BvSignExtend(_)
                | crate::ChcOp::Int2Bv(_)
                | crate::ChcOp::BvConcat,
                _,
            ) => {
                reserve(&mut widths, 1, control)?;
                widths.push((node, copies));
            }
            _ => {}
        }
        let children = crate::expr::dag::children(node);
        reserve(&mut pending, children.len(), control)?;
        pending.extend(children.iter().map(|child| (child.as_ref(), depth + 1)));
    }
    // As in GroundSourceSurfaceCache, derive result widths only AFTER the
    // complete occurrence walk has bounded/charged recursive sort traversal.
    // Borrowed sort-clone admission above covers nested array/select inputs;
    // wide outputs must be priced even when their concrete input payload is 0.
    for (node, copies) in widths {
        control.poll()?;
        let crate::ChcSort::BitVec(width) = node.sort() else {
            return None;
        };
        if !(1..=crate::MAX_BITVECTOR_WIDTH).contains(&width) {
            return None;
        }
        let bytes = usize::try_from(u64::from(width).div_ceil(8)).ok()?;
        control.admit(bytes, bytes.checked_mul(copies)?)?;
    }
    control.poll()
}

fn admit_sort_copy(sort: &crate::ChcSort, copies: usize, control: &Control) -> Option<()> {
    control.admit(1, 16)?;
    let mut pending = vec![sort];
    while let Some(sort) = pending.pop() {
        control.admit(copies, copies.checked_mul(128)?)?;
        match sort {
            crate::ChcSort::Array(index, value) => {
                reserve(&mut pending, 2, control)?;
                pending.extend([index.as_ref(), value.as_ref()]);
            }
            crate::ChcSort::Datatype { name, .. } | crate::ChcSort::Uninterpreted(name) => {
                // Datatype constructor registries are Arc-backed, not copied.
                control.admit(name.len(), name.len().checked_mul(copies)?)?;
            }
            _ => {}
        }
    }
    control.poll()
}

/// Precharge concrete aggregate cloning; unsupported/opaque leaves never
/// become zero, and the original validator remains the sort/semantic judge.
fn admit_value(root: &SmtValue, control: &Control) -> Option<()> {
    control.admit(1, 32)?;
    let mut pending = vec![(root, 0usize)];
    while let Some((value, depth)) = pending.pop() {
        control.admit(1, 128)?;
        if depth >= 128 {
            return None;
        }
        match value {
            SmtValue::Opaque(name) => {
                control.admit(name.len(), 0)?;
                return None;
            }
            SmtValue::ConstArray(default) => {
                reserve(&mut pending, 1, control)?;
                pending.push((default, depth + 1));
            }
            SmtValue::ArrayMap { default, entries } => {
                control.admit(entries.len(), entries.len().checked_mul(256)?)?;
                reserve(
                    &mut pending,
                    entries.len().checked_mul(2)?.checked_add(1)?,
                    control,
                )?;
                pending.push((default, depth + 1));
                for (key, value) in entries {
                    pending.push((key, depth + 1));
                    pending.push((value, depth + 1));
                }
            }
            SmtValue::Datatype(name, fields) => {
                control.admit(
                    name.len().checked_add(fields.len())?,
                    name.len().checked_add(fields.len().checked_mul(128)?)?,
                )?;
                reserve(&mut pending, fields.len(), control)?;
                pending.extend(fields.iter().map(|field| (field, depth + 1)));
            }
            SmtValue::Real(value) => {
                let bits = value.numer().bits().checked_add(value.denom().bits())?;
                number(bits, control)?;
            }
            SmtValue::BigInt(value) => number(value.bits(), control)?,
            SmtValue::BigBitVec(value, width) => {
                number(value.bits().max(u64::from(*width)), control)?;
            }
            SmtValue::Bool(_) | SmtValue::Int(_) | SmtValue::BitVec(_, _) => {}
        }
    }
    control.poll()
}

fn number(bits: u64, control: &Control) -> Option<()> {
    let Some(bytes) = usize::try_from(bits.div_ceil(8)).ok() else {
        return control.refuse();
    };
    // Arc-backed integers clone cheaply, but replay still reads their limbs.
    // Debit those reads and a conservative owned copy before handing them off.
    control.admit(bytes, bytes)
}

fn reserve<T>(pending: &mut Vec<T>, count: usize, control: &Control) -> Option<()> {
    let Some(bytes) = count.checked_mul(std::mem::size_of::<T>()) else {
        return control.refuse();
    };
    control.admit(count, bytes)?;
    if pending.try_reserve(count).is_err() {
        return control.refuse();
    }
    Some(())
}

#[cfg(test)]
mod tests;
