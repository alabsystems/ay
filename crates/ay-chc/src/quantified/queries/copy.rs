// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed census before copying any selected clause or declaration registry.

use super::*;
use crate::quantified::records::{registry_bytes, sort_bytes};
use crate::quantified::UniversalPremise;
use crate::{ChcExpr, ChcProblem, ClauseHead, HornClause};

#[derive(Default, Clone, Copy)]
struct Cost {
    work: usize,
    bytes: usize,
}

impl Cost {
    fn add(&mut self, work: usize, bytes: usize, control: &Control<'_>) -> ChcResult<()> {
        control.charge(work, 0)?;
        let (Some(work), Some(bytes)) =
            (self.work.checked_add(work), self.bytes.checked_add(bytes))
        else {
            return control.refuse("copy census overflow");
        };
        self.work = work;
        self.bytes = bytes;
        Ok(())
    }

    fn charge(self, control: &Control<'_>) -> ChcResult<()> {
        control.charge(self.work, self.bytes)
    }
}

pub(super) struct Census {
    declarations: Cost,
    clauses: Vec<Cost>,
    pub(super) definitions: Vec<Vec<usize>>,
}

impl Census {
    pub(super) fn new(source: &QuantifiedChcProblem, control: &Control<'_>) -> ChcResult<Self> {
        let problem = source.source_problem();
        if problem.clauses().len() != source.premises().len() {
            return control.refuse("premise alignment");
        }
        control.charge(
            problem.predicates().len(),
            problem.predicates().len().saturating_mul(32),
        )?;
        let mut definitions = vec![Vec::new(); problem.predicates().len()];
        let mut declarations = Cost::default();
        let bytes = registry_bytes(problem).ok_or_else(|| invalid("declaration census"))?;
        control.poll()?;
        // Independently reserve declaration copying, authenticated Registry
        // rebuilding and rendering. This is a conservative charged allowance,
        // not an exact allocator/RSS measurement.
        let bytes = bytes
            .checked_mul(3)
            .ok_or_else(|| invalid("registry copy allowance"))?;
        declarations.add(1, bytes.saturating_add(1024), control)?;
        // Preserve every ordinary UF, including unused and premise-only
        // declarations, through cloning, authenticated rebuilding and output.
        declarations.add(
            source.functions.work(),
            source
                .functions
                .copy_bytes()
                .checked_mul(3)
                .ok_or_else(|| invalid("function copy allowance"))?,
            control,
        )?;
        for predicate in problem.predicates() {
            declarations.add(
                1,
                predicate.name.len().saturating_mul(4).saturating_add(256),
                control,
            )?;
            for sort in &predicate.arg_sorts {
                control.poll()?;
                let bytes = sort_bytes(sort).ok_or_else(|| invalid("sort census"))?;
                declarations.add(1, bytes.saturating_mul(3), control)?;
            }
        }
        control.charge(
            problem.clauses().len(),
            problem.clauses().len().saturating_mul(32),
        )?;
        let mut clauses = Vec::new();
        clauses
            .try_reserve_exact(problem.clauses().len())
            .map_err(|_| invalid("census allocation"))?;
        for (index, (clause, premises)) in
            problem.clauses().iter().zip(source.premises()).enumerate()
        {
            if let ClauseHead::Predicate(id, _) = &clause.head {
                let Some(entries) = definitions.get_mut(id.index()) else {
                    return control.refuse("unknown defining predicate");
                };
                control.charge(1, std::mem::size_of::<usize>())?;
                entries
                    .try_reserve(1)
                    .map_err(|_| invalid("definition index allocation"))?;
                entries.push(index);
            }
            clauses.push(clause_cost(problem, clause, premises, control)?);
        }
        control.poll()?;
        Ok(Self {
            declarations,
            clauses,
            definitions,
        })
    }

    /// Reserve the entire selected copy/formatter allowance BEFORE cloning.
    pub(super) fn charge_slice(
        &self,
        selected: &[bool],
        query: usize,
        control: &Control<'_>,
    ) -> ChcResult<()> {
        self.declarations.charge(control)?;
        for (selected, cost) in selected.iter().zip(&self.clauses) {
            control.poll()?;
            if *selected {
                cost.charge(control)?;
            }
        }
        self.clauses
            .get(query)
            .ok_or_else(|| invalid("selected query census"))?
            .charge(control)
    }

    /// Structural conservation comparisons use known source ordinals, never
    /// search for a matching clause. Charge complete expression/name/metadata
    /// work before recursive equality on these independently bounded values.
    pub(super) fn charge_conservation(
        &self,
        selected: &[bool],
        query: usize,
        control: &Control<'_>,
    ) -> ChcResult<()> {
        for (selected, cost) in selected.iter().zip(&self.clauses) {
            if *selected {
                control.charge(
                    cost.work
                        .checked_add(cost.bytes)
                        .ok_or_else(|| invalid("comparison allowance"))?,
                    0,
                )?;
            }
        }
        let cost = self
            .clauses
            .get(query)
            .ok_or_else(|| invalid("query comparison census"))?;
        control.charge(
            cost.work
                .checked_add(cost.bytes)
                .ok_or_else(|| invalid("comparison allowance"))?,
            0,
        )
    }
}

fn clause_cost(
    problem: &ChcProblem,
    clause: &HornClause,
    premises: &[UniversalPremise],
    control: &Control<'_>,
) -> ChcResult<Cost> {
    let mut cost = Cost::default();
    cost.add(1, 512, control)?;
    for (id, args) in clause
        .body
        .predicates
        .iter()
        .map(|(id, args)| (id, args.as_slice()))
        .chain(match &clause.head {
            ClauseHead::Predicate(id, args) => Some((id, args.as_slice())),
            ClauseHead::False => None,
        })
    {
        let predicate = problem
            .get_predicate(*id)
            .ok_or_else(|| invalid("predicate census"))?;
        cost.add(
            1,
            predicate.name.len().saturating_mul(4).saturating_add(256),
            control,
        )?;
        for expression in args {
            expression_cost(expression, &mut cost, control)?;
        }
    }
    if let Some(expression) = &clause.body.constraint {
        expression_cost(expression, &mut cost, control)?;
    }
    for premise in premises {
        for binder in premise.binders() {
            cost.add(
                1,
                binder.name.len().saturating_mul(4).saturating_add(256),
                control,
            )?;
        }
        expression_cost(premise.matrix(), &mut cost, control)?;
    }
    Ok(cost)
}

fn expression_cost(root: &ChcExpr, cost: &mut Cost, control: &Control<'_>) -> ChcResult<()> {
    let mut pending = vec![(root, 0usize)];
    while let Some((expression, depth)) = pending.pop() {
        control.charge(1, 0)?;
        if depth > 64 {
            return control.refuse("source expression depth");
        }
        let mut bytes = 256usize;
        let children: &[std::sync::Arc<ChcExpr>] = match expression {
            ChcExpr::Var(var) => {
                let sort = sort_bytes(&var.sort).ok_or_else(|| invalid("variable sort census"))?;
                bytes = bytes
                    .saturating_add(var.name.len().saturating_mul(4))
                    .saturating_add(sort);
                &[]
            }
            ChcExpr::FuncApp(name, sort, args) => {
                let sort = sort_bytes(sort).ok_or_else(|| invalid("operation sort census"))?;
                bytes = bytes
                    .saturating_add(name.len().saturating_mul(4))
                    .saturating_add(sort);
                args
            }
            ChcExpr::Op(_, args) => args,
            ChcExpr::ConstArray(_, value) => std::slice::from_ref(value),
            ChcExpr::Bool(_) | ChcExpr::BitVec(_, _) => &[],
            _ => return control.refuse("unsupported source census expression"),
        };
        let Some(bytes) = bytes.checked_mul(depth + 1) else {
            return control.refuse("expression copy overflow");
        };
        cost.add(1, bytes, control)?;
        control.charge(children.len(), children.len().saturating_mul(16))?;
        pending
            .try_reserve(children.len())
            .map_err(|_| invalid("expression census allocation"))?;
        pending.extend(
            children
                .iter()
                .rev()
                .map(|child| (child.as_ref(), depth + 1)),
        );
    }
    control.poll()
}

pub(super) fn declarations(source: &ChcProblem, control: &Control<'_>) -> ChcResult<ChcProblem> {
    let mut result = ChcProblem::new();
    for predicate in source.predicates() {
        control.poll()?;
        if result.declare_predicate(&predicate.name, predicate.arg_sorts.clone()) != predicate.id {
            return control.refuse("predicate identity changed");
        }
    }
    for (name, constructors) in source.datatype_defs() {
        control.poll()?;
        result.add_datatype_def(name.clone(), constructors.clone());
    }
    if source.is_fixedpoint_format() {
        result.set_fixedpoint_format();
    }
    control.poll()?;
    Ok(result)
}

/// Caller has reserved this complete immutable declaration vector in Census.
pub(super) fn functions(
    source: &QuantifiedChcProblem,
    control: &Control<'_>,
) -> ChcResult<Vec<super::super::QuantifiedChcFunction>> {
    control.poll()?;
    let mut functions = Vec::new();
    functions
        .try_reserve_exact(source.function_declarations().len())
        .map_err(|_| invalid("function declaration allocation"))?;
    for function in source.function_declarations() {
        control.poll()?;
        functions.push(function.clone());
    }
    control.poll()?;
    Ok(functions)
}

pub(super) struct CopiedClauses {
    pub(super) clauses: Vec<QuantifiedHornClause>,
    pub(super) origins: Vec<QuantifiedChcClauseOrigin>,
}

pub(super) fn clauses(
    source: &QuantifiedChcProblem,
    plan: &plan::Plan,
    selected: &[bool],
    control: &Control<'_>,
) -> ChcResult<CopiedClauses> {
    if selected.len() != source.source_problem().clauses().len() || plan.query >= selected.len() {
        return control.refuse("selected source alignment");
    }
    let count = selected
        .iter()
        .filter(|selected| **selected)
        .count()
        .saturating_add(1);
    control.charge(count, count.saturating_mul(128))?;
    let mut result = Vec::new();
    let mut origins = origins::reserve(count, control)?;
    result
        .try_reserve_exact(count)
        .map_err(|_| invalid("slice allocation"))?;
    for (index, selected) in selected.iter().enumerate() {
        control.poll()?;
        if *selected {
            result.push(copy_clause(source, index, control)?);
            origins.push(QuantifiedChcClauseOrigin::Source {
                clause_index: index,
            });
        }
        if index == plan.query {
            let mut query = copy_clause(source, plan.selected(), control)?;
            query.clause.head = ClauseHead::False;
            result.push(query);
            origins.push(origins::query_origin(plan));
        }
    }
    control.poll()?;
    Ok(CopiedClauses {
        clauses: result,
        origins,
    })
}

fn copy_clause(
    source: &QuantifiedChcProblem,
    index: usize,
    control: &Control<'_>,
) -> ChcResult<QuantifiedHornClause> {
    control.poll()?;
    let mut clause = source.source_problem().clauses()[index].clone();
    clause.source_query_ordinal = None;
    let mut premises = Vec::new();
    premises
        .try_reserve_exact(source.premises()[index].len())
        .map_err(|_| invalid("premise allocation"))?;
    for premise in &source.premises()[index] {
        control.poll()?;
        premises.push(premise.clone());
    }
    control.poll()?;
    Ok(QuantifiedHornClause::new(clause, premises))
}
