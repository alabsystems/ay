// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact read-only positional arena; no simplification, interning or mint API.

use ay_bindings::{Expr, ExprValue};
use ay_chc::fp_adapter::{lower_fp_clause, FpClauseData, FpInputBinding};
use ay_chc::ChcProblem;
use ay_core::original_query::WorkBudget;
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::Sort;

use super::{source, typed, FpAdapterError, FpExprInputBinding};

const MODES: [&str; 5] = ["RNE", "RNA", "RTP", "RTN", "RTZ"];

pub(super) fn lower(
    roots: &[Expr],
    bindings: &[FpExprInputBinding<'_>],
    namespace: &ChcProblem,
    budget: &mut WorkBudget<'_>,
) -> Result<FpClauseData, FpAdapterError> {
    let plan = source::plan(roots, bindings, budget)?;
    plan.prepay(budget)?;
    let entries = entries(&plan, budget)?;
    let mut refusal = None;
    let copied = TermStore::from_entries_with_progress(
        &entries,
        Some(TermId(0)),
        Some(TermId(1)),
        entries.len() as u32,
        &mut |work, bytes| match budget.admit(work, bytes) {
            Ok(()) => true,
            Err(error) => {
                refusal = Some(error);
                false
            }
        },
    );
    let terms = copied.map_err(|_| {
        FpAdapterError::Owner(refusal.unwrap_or_else(|| budget.refuse_exhaustion()))
    })?;
    // The constructor is allocation preflight only. Our complete typed census
    // supplied every exact kind/sort/positional child; no producer metadata is
    // consulted and the snapshot remains read-only throughout native encoding.
    let mut root_ids = Vec::new();
    root_ids
        .try_reserve_exact(roots.len())
        .map_err(|_| budget.refuse_exhaustion())?;
    for root in roots {
        budget.charge(256)?;
        root_ids.push(id(&plan, root)?);
    }
    let mut inputs = Vec::new();
    inputs
        .try_reserve_exact(bindings.len())
        .map_err(|_| budget.refuse_exhaustion())?;
    for binding in bindings {
        budget.charge(256)?;
        inputs.push(FpInputBinding {
            source: id(&plan, binding.source)?,
            target: binding.target,
        });
    }
    let result =
        lower_fp_clause(&terms, &root_ids, &inputs, namespace, budget)?.into_data(budget)?;
    drop(inputs);
    drop(root_ids);
    drop(terms);
    drop(entries);
    drop(plan);
    budget.charge(0)?;
    Ok(result)
}

fn id(plan: &source::Plan<'_>, expr: &Expr) -> Result<TermId, FpAdapterError> {
    let index = plan
        .index(expr)?
        .checked_add(source::COMMON)
        .and_then(|v| u32::try_from(v).ok())
        .ok_or(FpAdapterError::Invalid("typed positional index"))?;
    Ok(TermId(index))
}

fn entries(
    plan: &source::Plan<'_>,
    budget: &mut WorkBudget<'_>,
) -> Result<Vec<(TermData, Sort)>, FpAdapterError> {
    let mut entries = Vec::new();
    entries
        .try_reserve_exact(plan.nodes.len() + source::COMMON)
        .map_err(|_| budget.refuse_exhaustion())?;
    entries.push((TermData::Const(Constant::Bool(true)), Sort::Bool));
    entries.push((TermData::Const(Constant::Bool(false)), Sort::Bool));
    for mode in MODES {
        budget.charge(512)?;
        entries.push((
            TermData::App(Symbol::named(mode), Vec::new()),
            Sort::Uninterpreted("RoundingMode".into()),
        ));
    }
    for expr in &plan.nodes {
        budget.charge(8192)?;
        let shape = typed::describe(expr)?;
        let mut children = Vec::new();
        children
            .try_reserve_exact(64)
            .map_err(|_| budget.refuse_exhaustion())?;
        for child in shape.children {
            budget.charge(256)?;
            let child_id = id(plan, child)?;
            if child_id.0 as usize >= entries.len() {
                return Err(FpAdapterError::Invalid("nonpreceding typed child"));
            }
            children.push(child_id);
        }
        let term = record(expr, shape.op, children, entries.len())?;
        entries.push((term, typed::scalar(expr)?.core()));
    }
    budget.charge(0)?;
    Ok(entries)
}

fn record(
    expr: &Expr,
    op: typed::Operator,
    mut children: Vec<TermId>,
    index: usize,
) -> Result<TermData, FpAdapterError> {
    Ok(match op {
        typed::Operator::Bool(v) => TermData::Const(Constant::Bool(v)),
        typed::Operator::Bv => {
            let ExprValue::BitVecConst { value, width } = expr.value() else {
                return Err(FpAdapterError::Invalid("typed BV record"));
            };
            TermData::Const(Constant::BitVec {
                value: value.clone(),
                width: *width,
            })
        }
        typed::Operator::Var => {
            let ExprValue::Var { name } = expr.value() else {
                return Err(FpAdapterError::Invalid("typed free record"));
            };
            TermData::Var(name.clone(), index as u32)
        }
        typed::Operator::Not => TermData::Not(children[0]),
        typed::Operator::Ite => TermData::Ite(children[0], children[1], children[2]),
        typed::Operator::Apply(name, mode) => {
            if let Some(mode) = mode {
                children.insert(0, TermId((2 + mode) as u32));
            }
            TermData::App(Symbol::named(name), children)
        }
        typed::Operator::Special(name, e, s) => {
            TermData::App(Symbol::indexed(name, vec![e, s]), children)
        }
        typed::Operator::Numeric(name, e, s) => {
            children.insert(0, TermId(2));
            TermData::App(Symbol::indexed(name, vec![e, s]), children)
        }
        typed::Operator::Extract(high, low) => {
            TermData::App(Symbol::indexed("extract", vec![high, low]), children)
        }
    })
}
