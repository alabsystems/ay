// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed-over-parameters sequence expressions for checked UF witnesses.
//!
//! This is model DATA, never certificate authority. The producer still has to
//! refute every original assertion's negation under one shared interpretation.
//! No expression may refer to another UF or an ambient free variable.

use super::{
    evaluation_copies, EvalValue, Executor, HashMap, HashSet, Model, Sort, Symbol, TermData, TermId,
};
use ay_core::term::{Constant, TermEntryStamp};
use ay_frontend::{Context, DeclarationKind};

const MAX_BODY_NODES: usize = 1_024;
const MAX_BODY_DEPTH: usize = 128;
const MAX_PARAMETERS: usize = 6;

#[derive(Debug)]
pub(in crate::executor) struct CertifiedExpressionBody {
    parameters: Box<[TermId]>,
    root: TermId,
    slots: Box<[(TermId, TermEntryStamp)]>,
    operators: Box<[String]>,
}

impl Executor {
    pub(super) fn evaluate_expression_application(
        &self,
        model: &Model,
        body: &CertifiedExpressionBody,
        arguments: Vec<TermId>,
    ) -> EvalValue {
        if !evaluation_copies::cells(arguments.len()) {
            return EvalValue::Unknown;
        }
        let values = arguments
            .into_iter()
            .map(|argument| self.evaluate_term(model, argument))
            .collect();
        self.evaluate_certified_expression(model, body, values)
    }

    pub(super) fn evaluate_certified_expression(
        &self,
        model: &Model,
        body: &CertifiedExpressionBody,
        values: Vec<EvalValue>,
    ) -> EvalValue {
        if values.len() != body.parameters.len()
            || values
                .iter()
                .any(|value| matches!(value, EvalValue::Unknown))
        {
            return EvalValue::Unknown;
        }
        for (&parameter, value) in body.parameters.iter().zip(&values) {
            let scalar = |value: &EvalValue, sort: &Sort| match (value, sort) {
                (EvalValue::Rational(value), Sort::Int) => value.is_integer(),
                (EvalValue::Bool(_), Sort::Bool) => true,
                _ => false,
            };
            let valid = match (value, self.ctx.terms.sort(parameter)) {
                (EvalValue::Seq(elements), Sort::Seq(sort)) => elements
                    .iter()
                    .all(|element| evaluation_copies::cells(1) && scalar(element, sort)),
                (value, sort) => scalar(value, sort),
            };
            if !valid {
                return EvalValue::Unknown;
            }
        }
        fn bound(
            exec: &Executor,
            model: &Model,
            root: TermId,
            parameters: &[TermId],
            values: &mut std::vec::IntoIter<EvalValue>,
        ) -> EvalValue {
            let Some((&parameter, rest)) = parameters.split_first() else {
                return exec.evaluate_term(model, root);
            };
            let Some(value) = values.next() else {
                return EvalValue::Unknown;
            };
            super::dt_model::with_scoped_term_override(parameter, value, || {
                bound(exec, model, root, rest, values)
            })
        }
        bound(
            self,
            model,
            body.root,
            &body.parameters,
            &mut values.into_iter(),
        )
    }
}

impl CertifiedExpressionBody {
    pub(in crate::executor) fn capture(
        ctx: &Context,
        parameters: Vec<TermId>,
        root: TermId,
    ) -> Option<Self> {
        if ctx.terms.entry_stamp(root).is_none()
            || parameters.len() > MAX_PARAMETERS
            || !supported_sort(ctx.terms.sort(root))
            || !evaluation_copies::cells(parameters.len())
        {
            return None;
        }
        let mut parameter_set = HashSet::default();
        for &parameter in &parameters {
            if !parameter_set.insert(parameter)
                || ctx.terms.entry_stamp(parameter).is_none()
                || !matches!(ctx.terms.get(parameter), TermData::Var(_, _))
                || !supported_sort(ctx.terms.sort(parameter))
            {
                return None;
            }
        }

        let mut slots = Vec::new();
        let mut operators: Vec<String> = Vec::new();
        let mut seen = HashSet::default();
        let mut active = HashSet::default();
        let mut expansion: HashMap<TermId, (usize, usize)> = HashMap::default();
        let mut pending = vec![(root, false)];
        while let Some((term, complete)) = pending.pop() {
            if complete {
                // Rendering and lexical evaluation expand shared edges. Bound
                // that actual tree as well as the compact source DAG, before
                // either consumer can be made to do exponential work.
                let mut count = 1usize;
                let mut depth = 1usize;
                if let TermData::App(_, arguments) = ctx.terms.get(term) {
                    for argument in arguments {
                        let &(child_count, child_depth) = expansion.get(argument)?;
                        count = count.checked_add(child_count)?;
                        depth = depth.max(child_depth.checked_add(1)?);
                        if count > MAX_BODY_NODES || depth > MAX_BODY_DEPTH {
                            return None;
                        }
                    }
                }
                expansion.insert(term, (count, depth));
                active.remove(&term);
                seen.insert(term);
                continue;
            }
            if seen.contains(&term) {
                continue;
            }
            // Low-level TermIds can name a future/self slot. A seen-set alone
            // terminates that walk but does not establish a well-founded body.
            if !active.insert(term) || slots.len() >= MAX_BODY_NODES || !evaluation_copies::cells(6)
            {
                return None;
            }
            let stamp = ctx.terms.entry_stamp(term)?;
            pending.push((term, true));
            match ctx.terms.get(term) {
                TermData::Var(_, _) if parameter_set.contains(&term) => {}
                TermData::Const(Constant::Int(_)) if ctx.terms.sort(term) == &Sort::Int => {}
                TermData::Const(Constant::Bool(_)) if ctx.terms.sort(term) == &Sort::Bool => {}
                TermData::App(Symbol::Named(operator), arguments)
                    if coherent_operator(ctx, operator)
                        && valid_sequence_application(ctx, term, operator, arguments) =>
                {
                    if arguments.len() > MAX_BODY_NODES
                        || !evaluation_copies::cells(arguments.len() + operator.len())
                    {
                        return None;
                    }
                    if !operators
                        .iter()
                        .any(|known| known.as_str() == operator.as_str())
                    {
                        operators.push(operator.to_string());
                    }
                    pending.extend(arguments.iter().rev().map(|&argument| (argument, false)));
                }
                _ => return None,
            }
            slots.push((term, stamp));
        }
        // Even an unused formal parameter has declaration-local lifetime.
        for &parameter in &parameters {
            if seen.insert(parameter) {
                if slots.len() >= MAX_BODY_NODES || !evaluation_copies::cells(1) {
                    return None;
                }
                slots.push((parameter, ctx.terms.entry_stamp(parameter)?));
            }
        }
        Some(Self {
            parameters: parameters.into_boxed_slice(),
            root,
            slots: slots.into_boxed_slice(),
            operators: operators.into_boxed_slice(),
        })
    }

    pub(in crate::executor) fn is_current(
        &self,
        ctx: &Context,
        parameter_sorts: &[Sort],
        result_sort: &Sort,
    ) -> bool {
        self.parameters.len() == parameter_sorts.len()
            && ctx.terms.entry_stamp(self.root).is_some()
            && ctx.terms.sort(self.root) == result_sort
            && self
                .slots
                .iter()
                .all(|&(term, stamp)| ctx.terms.entry_stamp(term) == Some(stamp))
            && self
                .parameters
                .iter()
                .zip(parameter_sorts)
                .all(|(&parameter, sort)| ctx.terms.sort(parameter) == sort)
            && self
                .operators
                .iter()
                .all(|operator| coherent_operator(ctx, operator))
    }

    pub(in crate::executor) fn parameters(&self) -> &[TermId] {
        &self.parameters
    }

    pub(in crate::executor) fn root(&self) -> TermId {
        self.root
    }

    pub(super) fn slots(&self) -> &[(TermId, TermEntryStamp)] {
        &self.slots
    }
}

fn supported_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Int | Sort::Bool)
        || matches!(sort, Sort::Seq(element) if matches!(element.as_ref(), Sort::Int | Sort::Bool))
}

fn coherent_operator(ctx: &Context, operator: &str) -> bool {
    !ctx.terms.is_declared_function(operator)
        && ctx.canonical_operator_binding_is_unambiguous(operator)
        && ctx.symbol_info_by_identity(operator).is_none_or(|info| {
            ctx.effective_declaration_kind(info.declaration_id()) == Some(DeclarationKind::Theory)
        })
}

fn valid_sequence_application(
    ctx: &Context,
    term: TermId,
    operator: &str,
    arguments: &[TermId],
) -> bool {
    let result_sort = ctx.terms.sort(term);
    if !supported_sort(result_sort)
        || arguments
            .iter()
            .any(|&argument| ctx.terms.entry_stamp(argument).is_none())
    {
        return false;
    }
    match (operator, arguments) {
        ("seq.empty", []) => matches!(result_sort, Sort::Seq(_)),
        ("seq.unit", [element]) => {
            matches!(result_sort, Sort::Seq(sort) if ctx.terms.sort(*element) == sort.as_ref())
        }
        ("seq.++", parts) if parts.len() >= 2 => {
            matches!(result_sort, Sort::Seq(_))
                && parts
                    .iter()
                    .all(|&part| ctx.terms.sort(part) == result_sort)
        }
        ("seq.len", [sequence]) => {
            result_sort == &Sort::Int
                && matches!(ctx.terms.sort(*sequence), Sort::Seq(element)
                    if matches!(element.as_ref(), Sort::Int | Sort::Bool))
        }
        ("seq.contains", [sequence, needle]) => {
            result_sort == &Sort::Bool
                && matches!(ctx.terms.sort(*sequence), Sort::Seq(element)
                    if matches!(element.as_ref(), Sort::Int | Sort::Bool))
                && ctx.terms.sort(*sequence) == ctx.terms.sort(*needle)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests;
