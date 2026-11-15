// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lossless whole-CNF transfer and explicit LSB-first free-input links.

use std::sync::Arc;

use ay_core::original_query::WorkBudget;
use ay_core::CnfLit;
use ay_fp::{FpBuiltEncoding, FpEncodingCache};

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};

use super::encoding::Built;
use super::namespace::PREFIX;
use super::source::Plan;
use super::{FpAdapterError, FpInputBinding};

pub(super) fn run(
    built: Built,
    bindings: &[FpInputBinding<'_>],
    plan: &Plan,
    budget: &mut WorkBudget<'_>,
) -> Result<(ChcExpr, Vec<ChcVar>), FpAdapterError> {
    budget.charge(0)?;
    let Built { roots, encoding } = built;
    let FpBuiltEncoding {
        clauses,
        pending_condition_links,
        cache,
        has_encoding_gap,
    } = encoding;
    if has_encoding_gap || !pending_condition_links.is_empty() || clauses.len() > plan.clauses {
        return Err(FpAdapterError::Encoding("incomplete transfer"));
    }
    let count = cache
        .next_var
        .checked_sub(1)
        .map(|v| v as usize)
        .filter(|&v| v <= plan.gates)
        .ok_or(FpAdapterError::Encoding("variable frontier"))?;
    let (positive, negative, variables) = variables(count, budget)?;
    let capacity = clauses
        .len()
        .checked_add(roots.len())
        .and_then(|v| {
            bindings
                .len()
                .checked_mul(64)
                .and_then(|w| v.checked_add(w))
        })
        .ok_or_else(|| budget.refuse_exhaustion())?;
    let mut constraints = Vec::new();
    constraints
        .try_reserve_exact(capacity)
        .map_err(|_| budget.refuse_exhaustion())?;
    for (index, clause) in clauses.into_iter().enumerate() {
        if index % 128 == 0 {
            budget.charge(0)?;
        }
        if clause.0.len() > 4 {
            return Err(FpAdapterError::Encoding("unexpected clause width"));
        }
        let mut disjunction = Vec::new();
        disjunction
            .try_reserve_exact(clause.0.len())
            .map_err(|_| budget.refuse_exhaustion())?;
        for lit in clause.0 {
            disjunction.push(literal(lit, &positive, &negative)?);
        }
        constraints.push(Arc::new(ChcExpr::Op(ChcOp::Or, disjunction)));
    }
    for root in roots {
        constraints.push(literal(root, &positive, &negative)?);
    }
    input_links(
        bindings,
        &cache,
        &positive,
        &negative,
        &mut constraints,
        budget,
    )?;
    // No future export/cache access or pending native work survives admission.
    drop(cache);
    drop(pending_condition_links);
    drop(positive);
    drop(negative);
    budget.charge(0)?;
    Ok((ChcExpr::Op(ChcOp::And, constraints), variables))
}

fn variables(
    count: usize,
    budget: &mut WorkBudget<'_>,
) -> Result<(Vec<Arc<ChcExpr>>, Vec<Arc<ChcExpr>>, Vec<ChcVar>), FpAdapterError> {
    let capacity = count
        .checked_add(1)
        .ok_or_else(|| budget.refuse_exhaustion())?;
    let mut positive = Vec::new();
    let mut negative = Vec::new();
    let mut variables = Vec::new();
    positive
        .try_reserve_exact(capacity)
        .map_err(|_| budget.refuse_exhaustion())?;
    negative
        .try_reserve_exact(capacity)
        .map_err(|_| budget.refuse_exhaustion())?;
    variables
        .try_reserve_exact(count)
        .map_err(|_| budget.refuse_exhaustion())?;
    // Index zero is an inaccessible sentinel; native literals must be nonzero.
    positive.push(Arc::new(ChcExpr::Bool(false)));
    negative.push(Arc::new(ChcExpr::Bool(false)));
    for id in 1..=count {
        if id % 128 == 0 {
            budget.charge(0)?;
        }
        let variable = ChcVar::new(format!("{PREFIX}{id}"), ChcSort::Bool);
        let expr = Arc::new(ChcExpr::Var(variable.clone()));
        let mut child = Vec::new();
        child
            .try_reserve_exact(1)
            .map_err(|_| budget.refuse_exhaustion())?;
        child.push(Arc::clone(&expr));
        negative.push(Arc::new(ChcExpr::Op(ChcOp::Not, child)));
        positive.push(expr);
        variables.push(variable);
    }
    Ok((positive, negative, variables))
}

fn literal(
    lit: CnfLit,
    positive: &[Arc<ChcExpr>],
    negative: &[Arc<ChcExpr>],
) -> Result<Arc<ChcExpr>, FpAdapterError> {
    if lit == 0 || lit == i32::MIN {
        return Err(FpAdapterError::Encoding("invalid native literal"));
    }
    let values = if lit > 0 { positive } else { negative };
    values
        .get(lit.unsigned_abs() as usize)
        .map(Arc::clone)
        .ok_or(FpAdapterError::Encoding("dangling native literal"))
}

fn input_links(
    bindings: &[FpInputBinding<'_>],
    cache: &FpEncodingCache,
    positive: &[Arc<ChcExpr>],
    negative: &[Arc<ChcExpr>],
    constraints: &mut Vec<Arc<ChcExpr>>,
    budget: &mut WorkBudget<'_>,
) -> Result<(), FpAdapterError> {
    for binding in bindings {
        budget.charge(0)?;
        let target = Arc::new(ChcExpr::Var(binding.target.clone()));
        if let Some(fp) = cache.term_to_fp.get(&binding.source) {
            let width = fp.total_bits();
            if binding.target.sort != ChcSort::BitVec(width as u32)
                || !matches!(
                    (fp.exponent.len(), fp.significand.len()),
                    (8, 23) | (11, 52)
                )
            {
                return Err(FpAdapterError::Encoding("FP input decomposition width"));
            }
            for (bit, lit) in fp
                .significand
                .iter()
                .chain(&fp.exponent)
                .chain(std::iter::once(&fp.sign))
                .copied()
                .enumerate()
            {
                link_bit(bit, lit, &target, positive, negative, constraints, budget)?;
            }
        } else if let Some(bits) = cache.bv_term_bits.get(&binding.source) {
            if binding.target.sort != ChcSort::BitVec(bits.len() as u32) {
                return Err(FpAdapterError::Encoding("BV input width"));
            }
            for (bit, lit) in bits.iter().copied().enumerate() {
                link_bit(bit, lit, &target, positive, negative, constraints, budget)?;
            }
        } else if let Some(&lit) = cache.bool_input_lits.get(&binding.source) {
            if binding.target.sort != ChcSort::Bool {
                return Err(FpAdapterError::Encoding("Bool input width"));
            }
            constraints.push(Arc::new(ChcExpr::Op(
                ChcOp::Eq,
                pair(literal(lit, positive, negative)?, target, budget)?,
            )));
        }
    }
    Ok(())
}

fn link_bit(
    bit: usize,
    lit: CnfLit,
    target: &Arc<ChcExpr>,
    positive: &[Arc<ChcExpr>],
    negative: &[Arc<ChcExpr>],
    constraints: &mut Vec<Arc<ChcExpr>>,
    budget: &mut WorkBudget<'_>,
) -> Result<(), FpAdapterError> {
    let mut child = Vec::new();
    child
        .try_reserve_exact(1)
        .map_err(|_| budget.refuse_exhaustion())?;
    child.push(Arc::clone(target));
    let extract = Arc::new(ChcExpr::Op(ChcOp::BvExtract(bit as u32, bit as u32), child));
    let is_one = Arc::new(ChcExpr::Op(
        ChcOp::Eq,
        pair(extract, Arc::new(ChcExpr::BitVec(1, 1)), budget)?,
    ));
    constraints.push(Arc::new(ChcExpr::Op(
        ChcOp::Eq,
        pair(literal(lit, positive, negative)?, is_one, budget)?,
    )));
    Ok(())
}

fn pair(
    left: Arc<ChcExpr>,
    right: Arc<ChcExpr>,
    budget: &mut WorkBudget<'_>,
) -> Result<Vec<Arc<ChcExpr>>, FpAdapterError> {
    let mut args = Vec::new();
    args.try_reserve_exact(2)
        .map_err(|_| budget.refuse_exhaustion())?;
    args.push(left);
    args.push(right);
    Ok(args)
}
