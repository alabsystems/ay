// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{fixed, key, preimage, FunctionalArrayError, Meter, SnapshotKind, SnapshotTopology, N};

pub(super) fn push(
    cuts: &mut Vec<u128>,
    cut: u128,
    meter: &mut Meter<'_>,
) -> Result<(), FunctionalArrayError> {
    meter.reserve(cuts, 1)?;
    meter.pay(64)?;
    cuts.push(cut);
    Ok(())
}

pub(super) fn append(
    cuts: &mut Vec<u128>,
    from: &[u128],
    meter: &mut Meter<'_>,
) -> Result<(), FunctionalArrayError> {
    meter.reserve(cuts, from.len())?;
    for cut in from {
        meter.pay(64)?;
        cuts.push(*cut);
    }
    Ok(())
}

pub(super) fn canonical(
    cuts: &mut Vec<u128>,
    meter: &mut Meter<'_>,
) -> Result<(), FunctionalArrayError> {
    meter.pay(64)?;
    // Paid stable insertion sort; no opaque sort allocation or guessed average.
    for i in 1..cuts.len() {
        let mut j = i;
        while j > 0 {
            meter.pay(128)?;
            if cuts[j - 1] <= cuts[j] {
                break;
            }
            cuts.swap(j - 1, j);
            j -= 1;
        }
    }
    let mut kept = 0;
    for index in 0..cuts.len() {
        meter.pay(128)?;
        if kept == 0 || cuts[index] != cuts[kept - 1] {
            cuts[kept] = cuts[index];
            kept += 1;
        }
    }
    cuts.truncate(kept);
    Ok(())
}

pub(super) fn derive(
    topology: &SnapshotTopology<'_>,
    meter: &mut Meter<'_>,
) -> Result<Vec<u128>, FunctionalArrayError> {
    let mut plans: Vec<Vec<u128>> = Vec::new();
    meter.pay(64)?;
    meter.reserve(&mut plans, topology.nodes().len())?;
    for description in topology.nodes() {
        meter.pay(128)?;
        let mut cuts = Vec::new();
        push(&mut cuts, 0, meter)?;
        push(&mut cuts, N, meter)?;
        match description.kind {
            SnapshotKind::Finite(value) => {
                for (index, _) in &value.store {
                    let k = u128::from(key(index, meter)?);
                    push(&mut cuts, k, meter)?;
                    push(&mut cuts, k + 1, meter)?;
                }
            }
            SnapshotKind::Store { base, index, .. } => {
                append(
                    &mut cuts,
                    plans.get(base).ok_or(FunctionalArrayError::Value)?,
                    meter,
                )?;
                let k = u128::from(key(index, meter)?);
                push(&mut cuts, k, meter)?;
                push(&mut cuts, k + 1, meter)?;
            }
            SnapshotKind::Range {
                destination,
                source,
                lo,
                hi,
                source_lo,
            } => {
                let lo = fixed(lo, meter)?;
                let hi = fixed(hi, meter)?;
                let source_lo = fixed(source_lo, meter)?;
                append(
                    &mut cuts,
                    plans.get(destination).ok_or(FunctionalArrayError::Value)?,
                    meter,
                )?;
                let source = plans.get(source).ok_or(FunctionalArrayError::Value)?;
                // Keeping untransformed child cuts globally is harmless
                // overrefinement; transformed source cuts cover every read edge.
                append(&mut cuts, source, meter)?;
                push(&mut cuts, u128::from(lo), meter)?;
                push(&mut cuts, u128::from(hi), meter)?;
                for cut in source {
                    meter.pay(128)?;
                    push(&mut cuts, preimage(*cut, lo, source_lo), meter)?;
                }
            }
        }
        canonical(&mut cuts, meter)?;
        meter.pay(64)?;
        plans.push(cuts);
    }
    meter.pay(128)?;
    if topology.root() + 1 != plans.len() {
        return Err(FunctionalArrayError::Value);
    }
    plans.pop().ok_or(FunctionalArrayError::Value)
}
