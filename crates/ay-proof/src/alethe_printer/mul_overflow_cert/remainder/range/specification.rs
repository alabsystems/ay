// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Instantiate the range theorem along the exact original divider circuit.

use super::super::super::clean::ult_bits;
use super::super::super::helpers::{instantiate, split_or};
use super::super::super::horner::ground;
use super::*;

impl RangeStage {
    pub(in super::super) fn specification(
        &self,
        p: &mut Proof<'_>,
        xb: &[T],
        yb: &[T],
        nonzero: S,
    ) -> Option<(Vec<T>, S)> {
        p.observe()?;
        if xb.len() != self.n as usize || yb.len() != self.n as usize {
            return None;
        }
        let stages = remainder_stages(p, xb, yb)?;
        p.observe()?;
        let mut fact = base(p, yb, nonzero)?;
        for k in (0..self.n as usize).rev() {
            p.observe()?;
            let mut xk = xb[k..].to_vec();
            xk.resize(self.n as usize, p.t.ff);
            let expected = invariant(p, &stages[k], &xk, yb);
            // The shared divider stops immediately on an all-false suffix.
            // Its already-proved zero base is the exact current invariant;
            // instantiating a non-simplified stage circuit would not be it.
            if xk.iter().all(|&bit| bit == p.t.ff) {
                if p.unit(fact) != expected {
                    return None;
                }
                continue;
            }
            // Only the incoming remainder and the original X/Y bits occur
            // in the quantified range lemma. No quotient is presumed zero.
            let mut args = stages[k + 1].clone();
            args.extend(&xk);
            args.extend(yb);
            let instance = instantiate(p, self.fact, &args)?;
            let split = split_or(p, instance);
            let parts = p.t.args(p.unit(instance)).to_vec();
            if parts.len() != 2 || parts[1] != expected {
                return None;
            }
            fact = p.derive(&[expected], &[Prem::Step(split), Prem::Step(fact)], &[])?;
        }
        let remainder = stages.first()?.clone();
        drop(stages);
        p.observe()?;
        Some((remainder, fact))
    }
}

/// The remainder projection of `clean::udiv_stages`, using its very same
/// stage constructor. R never reads Q, so do not retain or recursively build
/// the unused quotient DAG. This is not a different division circuit.
pub(super) fn remainder_stages(p: &mut Proof<'_>, xb: &[T], yb: &[T]) -> Option<Vec<Vec<T>>> {
    p.observe()?;
    if xb.is_empty() || xb.len() != yb.len() {
        return None;
    }
    let zero = vec![p.t.ff; xb.len()];
    let mut stages = vec![zero.clone(); xb.len() + 1];
    for k in (0..xb.len()).rev() {
        p.observe()?;
        let mut shifted = xb[k..].to_vec();
        shifted.resize(xb.len(), p.t.ff);
        if !shifted.iter().all(|&bit| bit == p.t.ff) {
            stages[k] = udiv_stage(&mut p.t, &shifted, yb, &zero, &stages[k + 1]).rem;
        }
    }
    p.observe()?;
    Some(stages)
}

fn base(p: &mut Proof<'_>, yb: &[T], nonzero: S) -> Option<S> {
    p.observe()?;
    let (ff, tt) = (p.t.ff, p.t.tt);
    let zero = vec![ff; yb.len()];
    let inv = invariant(p, &zero, &zero, yb);
    let parts = p.t.args(inv).to_vec();
    let chain = ult_bits(&mut p.t, &zero, yb);
    let last = *chain.last()?;
    let blast = eq_step(p, parts[0], last, "bitblast_ult", &[]);
    let mut premises = Vec::new();
    for &gate in &chain {
        p.observe()?;
        premises.extend(gates_rec(p, gate, 3));
    }
    let equalities: Vec<_> = yb.iter().map(|&bit| p.t.eq(bit, ff)).collect();
    let is_zero = p.t.and(&equalities);
    premises.extend(p.gate(is_zero));
    for &equality in &equalities {
        p.observe()?;
        premises.extend(p.gate(equality));
    }
    premises.extend(p.gate(ff));
    premises.extend(p.gate(tt));
    premises.push(Prem::Step(nonzero));
    let range_bits = p.derive(&[last], &premises, &[])?;
    let range = transfer(p, blast, range_bits)?;
    let upper = ground(p, parts[1])?;
    let result = and_from(p, inv, &[range, upper])?;
    p.observe()?;
    Some(result)
}
