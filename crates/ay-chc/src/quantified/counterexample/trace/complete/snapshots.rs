// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One original prepaid DATA ledger and one complete global topological DAG.

use super::*;
use ay_model_check::{SnapshotKind, SnapshotTopology};

mod intern;
mod literal;
pub(super) use intern::Environment;

const MAX_NODES: usize = 4096;
const TOPOLOGY_WORK: usize = 1_048_576;

struct Borrowed<'a> {
    source: &'a Arc<ArraySnapshot>,
    topology: SnapshotTopology<'a>,
}

pub(super) fn build(
    rendered: &render::Rendered<'_>,
    bindings: &[QuantifiedChcCompleteTraceBinding],
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<Environment> {
    let (data, requests) = gather(bindings, control)?;
    control.debit(data.len(), 0)?;
    let count = data.iter().try_fold(0usize, |count, entry| {
        count.checked_add(entry.topology.nodes().len())
    })?;
    if count > MAX_NODES {
        control.stop();
        return None;
    }
    let names = render::complete_names(problem, rendered, count.checked_mul(2)?, control).ok()?;
    let mut environment = Environment::new(names, count, control)?;
    let mut roots = Vec::new();
    control.bytes(data.len().checked_mul(std::mem::size_of::<usize>())?)?;
    roots.try_reserve_exact(data.len()).ok()?;
    for entry in &data {
        roots.push(environment.import(&entry.topology, control)?);
    }
    control.bytes(
        requests
            .len()
            .checked_mul(std::mem::size_of::<Option<usize>>())?,
    )?;
    environment
        .bindings
        .try_reserve_exact(requests.len())
        .ok()?;
    for request in requests {
        environment.bindings.push(match request {
            Some(request) => Some(*roots.get(request)?),
            None => None,
        });
    }
    drop(data);
    control.poll()?;
    Some(environment)
}

fn gather<'a>(
    bindings: &'a [QuantifiedChcCompleteTraceBinding],
    control: &SourceControl<'_>,
) -> Option<(Vec<Borrowed<'a>>, Vec<Option<usize>>)> {
    let mut data: Vec<Borrowed<'a>> = Vec::new();
    let mut requests = Vec::new();
    control.bytes(
        bindings
            .len()
            .checked_mul(std::mem::size_of::<Option<usize>>())?,
    )?;
    requests.try_reserve_exact(bindings.len()).ok()?;
    control.debit(bindings.len(), 0)?;
    let has_arrays = bindings.iter().any(|binding| {
        matches!(
            &binding.value,
            QuantifiedChcCompleteValue::FunctionalArray(_)
        )
    });
    // ONE prepaid subbudget, for ALL exports in this batch. No refund, per-read
    // renewal or extra native-model allowance; source refusal remains sticky.
    let mut work = if has_arrays {
        control.debit(TOPOLOGY_WORK, TOPOLOGY_WORK)?;
        TOPOLOGY_WORK
    } else {
        0
    };
    for binding in bindings {
        control.charge(data.len().checked_add(1)?)?;
        let QuantifiedChcCompleteValue::FunctionalArray(snapshot) = &binding.value else {
            requests.push(None);
            continue;
        };
        if !acquire::snapshot_sort(&binding.variable.sort, snapshot.sort()) {
            return None;
        }
        if let Some(prior) = data
            .iter()
            .position(|entry| Arc::ptr_eq(entry.source, snapshot))
        {
            requests.push(Some(prior));
            continue;
        }
        let topology = match snapshot.topology(&mut work, &mut || control.poll().is_none()) {
            Ok(topology) => topology,
            Err(_) => {
                control.stop();
                return None;
            }
        };
        // Reserve may move all existing initialized records. Charge both
        // prior and new backing populations before growing the vector.
        let records = data.len().checked_mul(2)?.checked_add(1)?.max(2);
        control.bytes(records.checked_mul(std::mem::size_of::<Borrowed<'_>>())?)?;
        data.try_reserve_exact(1).ok()?;
        requests.push(Some(data.len()));
        data.push(Borrowed {
            source: snapshot,
            topology,
        });
    }
    control.poll()?;
    Some((data, requests))
}

pub(super) fn scalar(
    value: &ay_model_check::ModelValue,
    sort: &ay_core::Sort,
    control: &SourceControl<'_>,
) -> Option<String> {
    literal::scalar(value, sort, control)
}

pub(super) fn unsigned(value: &num_bigint::BigInt, control: &SourceControl<'_>) -> Option<u64> {
    literal::unsigned(value, control)
}
