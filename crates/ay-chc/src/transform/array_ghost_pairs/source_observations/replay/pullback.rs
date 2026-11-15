// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct Fresh<'a> {
    source: &'a str,
    next: usize,
}

impl<'a> Fresh<'a> {
    pub(super) fn new(source: &'a str) -> Self {
        Self { source, next: 0 }
    }

    fn axes(&mut self, sorts: &[ChcSort], control: &SourceControl<'_>) -> Option<Vec<ChcVar>> {
        control.charge(sorts.len())?;
        let mut out = Vec::new();
        out.try_reserve_exact(sorts.len()).ok()?;
        for sort in sorts {
            if !matches!(sort, ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)) {
                return None;
            }
            control.bytes(sort_bytes(sort)?)?;
            let name = loop {
                // Conservatively exclude the entire canonical source namespace,
                // including unused declarations and every lexical binder.
                control.bytes(self.source.len().checked_add(256)?)?;
                // Replay is elaborated as ordinary SMT-LIB, so its generated
                // symbols must not use the frontend's reserved `__ay_` space.
                let name = format!("ay!observation!replay!{}", self.next);
                self.next = self.next.checked_add(1)?;
                if !self.source.contains(&name) {
                    break name;
                }
            };
            out.push(ChcVar::new(name, sort.clone()));
        }
        control.poll()?;
        Some(out)
    }
}

pub(super) fn instance(
    model: &ObservationModel,
    id: PredicateId,
    original: &[ChcExpr],
    axes: &[ChcExpr],
    control: &SourceControl<'_>,
) -> Option<ChcExpr> {
    let interpretation = model.model.get(&id)?;
    let canonical = model.layout.canonical(id)?;
    if interpretation.vars.as_slice() != canonical {
        return None;
    }
    let actuals = model.layout.actuals(id, original, axes, control)?;
    if actuals.len() != canonical.len() {
        return None;
    }
    let mut formula_bytes = 0;
    source_premises::preflight(&interpretation.formula, control, &mut formula_bytes)?;
    let mut largest = 0;
    for actual in &actuals {
        let mut bytes = 0;
        source_premises::preflight(actual, control, &mut bytes)?;
        largest = largest.max(bytes);
    }
    // Each formula occurrence contributes at least 256 preflight bytes. Debit
    // replacement fanout before allocating the substituted formula skeleton.
    control.bytes(
        formula_bytes
            .checked_add(255)?
            .checked_div(256)?
            .checked_mul(largest)?,
    )?;
    replace(&interpretation.formula, canonical, &actuals, control, 0)
}

fn replace(
    expr: &ChcExpr,
    vars: &[ChcVar],
    actuals: &[ChcExpr],
    control: &SourceControl<'_>,
    depth: usize,
) -> Option<ChcExpr> {
    control.charge(1)?;
    if depth > 128 {
        return None;
    }
    match expr {
        ChcExpr::Var(var) => {
            control.charge(vars.len())?;
            let actual = actuals.get(vars.iter().position(|v| v == var)?)?;
            source_premises::preflight(actual, control, &mut 0)?;
            // Replacement is simultaneous: never rewrite variables inside it.
            Some(actual.clone())
        }
        ChcExpr::Bool(_) | ChcExpr::BitVec(_, _) => Some(expr.clone()),
        ChcExpr::Op(op, args) => {
            control.charge(args.len())?;
            let mut out = Vec::new();
            out.try_reserve_exact(args.len()).ok()?;
            for arg in args {
                out.push(Arc::new(replace(arg, vars, actuals, control, depth + 1)?));
            }
            Some(ChcExpr::Op(*op, out))
        }
        _ => None,
    }
}

pub(super) fn head(
    model: &ObservationModel,
    clause: &HornClause,
    fresh: &mut Fresh<'_>,
    control: &SourceControl<'_>,
) -> Option<(Option<ChcExpr>, Vec<ChcVar>)> {
    let ClauseHead::Predicate(id, args) = &clause.head else {
        return Some((None, Vec::new()));
    };
    let axes = fresh.axes(model.layout.axes(*id)?, control)?;
    let terms = axis_terms(&axes, control)?;
    let formula = instance(model, *id, args, &terms, control)?;
    Some((Some(ChcExpr::Op(ChcOp::Not, vec![Arc::new(formula)])), axes))
}

pub(super) type Body = (Vec<ChcVar>, ChcExpr);

pub(super) fn bodies(
    model: &ObservationModel,
    clause: &HornClause,
    head: &[ChcExpr],
    indices: &[ChcExpr],
    fresh: &mut Fresh<'_>,
    control: &SourceControl<'_>,
) -> Option<(Vec<Body>, Vec<ChcExpr>)> {
    let mut quantified = Vec::new();
    let mut hints = Vec::new();
    control.charge(clause.body.predicates.len())?;
    for (id, args) in &clause.body.predicates {
        let sorts = model.layout.axes(*id)?;
        let axes = fresh.axes(sorts, control)?;
        let terms = axis_terms(&axes, control)?;
        let formula = instance(model, *id, args, &terms, control)?;
        quantified.push((axes, formula));
        if sorts.is_empty() {
            hints.push(instance(model, *id, args, &[], control)?);
            continue;
        }
        tuple_scratch(sorts.len(), head, indices, control)?;
        let tuples = super::super::super::instantiation_tuples(
            sorts,
            head,
            indices,
            super::super::super::BODY_INSTANCE_CAP,
        );
        for tuple in tuples {
            hints.push(instance(model, *id, args, &tuple, control)?);
        }
    }
    control.poll()?;
    Some((quantified, hints))
}

/// These generated invariant binders can have the full source key width.
/// They are not original UniversalPremise binders, whose admission stays BV64.
pub(super) fn axis_terms(axes: &[ChcVar], control: &SourceControl<'_>) -> Option<Vec<ChcExpr>> {
    control.charge(axes.len())?;
    let mut terms = Vec::new();
    terms.try_reserve_exact(axes.len()).ok()?;
    for axis in axes {
        control.bytes(axis.name.len().checked_add(sort_bytes(&axis.sort)?)?)?;
        terms.push(ChcExpr::var(axis.clone()));
    }
    control.poll()?;
    Some(terms)
}

fn tuple_scratch(
    slots: usize,
    head: &[ChcExpr],
    indices: &[ChcExpr],
    control: &SourceControl<'_>,
) -> Option<()> {
    let sources = head.len().checked_add(indices.len())?;
    let mut bytes = 512usize;
    for expr in head.iter().chain(indices) {
        let mut size = 0;
        source_premises::preflight(expr, control, &mut size)?;
        bytes = bytes.max(size);
    }
    let pairs = if slots == 2 {
        sources.checked_mul(sources)?
    } else {
        0
    };
    let tuples = 4usize
        .checked_add(slots)?
        .checked_add(sources.checked_mul(slots)?)?
        .checked_add(sources)?
        .checked_add(pairs)?;
    control.bytes(
        tuples
            .checked_mul(slots.checked_add(1)?)?
            .checked_mul(bytes)?,
    )
}
